#!/usr/bin/env python3
"""
Market Hunter Bot V1

Read-only public market scanner with a local paper-trading ledger.
This module intentionally has no wallet, credential, or order-placement code.
"""

from __future__ import annotations

import json
import logging
import math
import os
import re
import sqlite3
import threading
import urllib.error
import urllib.parse
import urllib.request
import uuid
from collections import defaultdict
from datetime import datetime, timezone
from difflib import SequenceMatcher
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any


API_PREFIX = "/mh-api"
DATABASE_PATH = os.environ.get("MARKET_HUNTER_DB", os.path.join(os.path.dirname(__file__), "market_hunter.sqlite3"))
STARTING_BALANCE = 1000.0
NOTIONAL = 100.0
FETCH_TIMEOUT = 12
POLYMARKET_PAGE_SIZE = 100
POLYMARKET_MAX_PAGES = 21
KALSHI_PAGE_SIZE = 1000
KALSHI_MAX_PAGES = 10
MAX_CANDIDATES_RETURNED = 100
LOGGER = logging.getLogger("market_hunter")
STOP_WORDS = {
    "will",
    "be",
    "the",
    "a",
    "an",
    "in",
    "on",
    "of",
    "to",
    "for",
    "by",
    "at",
    "this",
    "that",
    "before",
    "after",
    "from",
    "and",
    "or",
    "who",
    "what",
    "which",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def json_dumps(value: Any) -> str:
    return json.dumps(value, separators=(",", ":"), sort_keys=True)


def safe_float(value: Any) -> float | None:
    try:
        if value is None or value == "":
            return None
        number = float(value)
        return number if math.isfinite(number) else None
    except (TypeError, ValueError):
        return None


def clamp_price(value: float | None) -> float | None:
    if value is None or value < 0 or value > 1:
        return None
    return value


class PublicApiError(Exception):
    def __init__(self, endpoint: str, message: str, http_status: int | None = None):
        self.endpoint = endpoint
        self.http_status = http_status
        self.detail = message
        status_text = f" HTTP {http_status}" if http_status is not None else ""
        super().__init__(f"{endpoint}{status_text}: {message}")


def fetch_json(url: str) -> Any:
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": "MarketHunterBotV1/1.0 (public-data-scanner)",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=FETCH_TIMEOUT) as response:
            body = response.read()
            LOGGER.info("public_api_response endpoint=%s http_status=%s bytes=%s", url, response.status, len(body))
            try:
                return json.loads(body.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise PublicApiError(url, f"invalid JSON response: {error}", response.status) from error
    except urllib.error.HTTPError as error:
        response_body = error.read(512).decode("utf-8", errors="replace").strip()
        detail = f"{error.reason}" + (f"; body={response_body}" if response_body else "")
        LOGGER.error("public_api_failure endpoint=%s http_status=%s error=%s", url, error.code, detail)
        raise PublicApiError(url, detail, error.code) from error
    except urllib.error.URLError as error:
        detail = str(error.reason)
        LOGGER.error("public_api_failure endpoint=%s http_status=none error=%s", url, detail)
        raise PublicApiError(url, detail) from error
    except TimeoutError as error:
        LOGGER.error("public_api_failure endpoint=%s http_status=none error=timeout", url)
        raise PublicApiError(url, "timeout") from error


def parse_jsonish(value: Any) -> Any:
    if isinstance(value, str):
        try:
            return json.loads(value)
        except json.JSONDecodeError:
            return value
    return value


def normalize_text(value: str) -> str:
    text = value.lower()
    text = re.sub(r"\b(yes|no|market|question|probability|will|would|could|be|the)\b", " ", text)
    text = re.sub(r"[^a-z0-9%]+", " ", text)
    tokens = [token for token in text.split() if token not in STOP_WORDS]
    return " ".join(tokens)


def text_tokens(value: str) -> set[str]:
    return set(normalize_text(value).split())


def extract_years(value: str) -> set[str]:
    return set(re.findall(r"\b(?:19|20)\d{2}\b", value))


def extract_numeric_terms(value: str) -> set[str]:
    terms = set(re.findall(r"\b\d+(?:\.\d+)?%?\b", value))
    return {term for term in terms if not re.fullmatch(r"(?:19|20)\d{2}", term)}


def parse_iso_date(value: Any) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    except ValueError:
        return None


def market_match(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any] | None:
    left_title = str(left.get("title") or "")
    right_title = str(right.get("title") or "")
    left_normalized = normalize_text(left_title)
    right_normalized = normalize_text(right_title)
    if not left_normalized or not right_normalized:
        return None

    left_tokens = text_tokens(left_title)
    right_tokens = text_tokens(right_title)
    shared_tokens = sorted(left_tokens & right_tokens)
    union = left_tokens | right_tokens
    overlap = len(shared_tokens) / len(union) if union else 0.0
    sequence = SequenceMatcher(None, left_normalized, right_normalized).ratio()
    left_years = extract_years(left_title)
    right_years = extract_years(right_title)
    left_numbers = extract_numeric_terms(left_title)
    right_numbers = extract_numeric_terms(right_title)

    # A different explicit year or threshold is a strong signal that two
    # similarly worded markets resolve different questions.
    if left_years and right_years and not left_years.intersection(right_years):
        return None
    if left_numbers and right_numbers and left_numbers != right_numbers:
        return None

    left_end = parse_iso_date(left.get("endDate"))
    right_end = parse_iso_date(right.get("endDate"))
    close_dates_compatible = True
    if left_end and right_end:
        close_dates_compatible = abs((left_end - right_end).total_seconds()) <= 14 * 86400
        if not close_dates_compatible and not left_years.intersection(right_years):
            return None

    # Do not match on a generic shared word. Require several semantic anchors
    # and either strong phrase similarity or substantial token overlap.
    score = (sequence * 0.55) + (overlap * 0.45)
    if left_years and left_years.intersection(right_years):
        score += 0.06
    if left_numbers and left_numbers == right_numbers:
        score += 0.06
    score = min(1.0, score)
    if len(shared_tokens) < 3 or (score < 0.72 and not (score >= 0.66 and len(shared_tokens) >= 5)):
        return None

    reasons = [f"shared subject terms: {', '.join(shared_tokens[:8])}"]
    if left_years.intersection(right_years):
        reasons.append(f"same explicit year: {', '.join(sorted(left_years.intersection(right_years)))}")
    if left_numbers and left_numbers == right_numbers:
        reasons.append(f"same thresholds: {', '.join(sorted(left_numbers))}")
    if left_end and right_end and close_dates_compatible:
        reasons.append("resolution dates within 14 days")
    return {
        "score": round(score, 4),
        "matchReason": "; ".join(reasons),
        "evidence": {
            "sharedTokens": shared_tokens,
            "sameYears": sorted(left_years.intersection(right_years)),
            "sameThresholds": sorted(left_numbers.intersection(right_numbers)),
            "closeDatesCompatible": close_dates_compatible,
        },
    }


def match_score(left: str, right: str) -> float:
    """Compatibility wrapper retained for callers outside the scanner."""
    left_market = {"title": left}
    right_market = {"title": right}
    result = market_match(left_market, right_market)
    return float(result["score"]) if result else 0.0


def parse_polymarket_market(item: dict[str, Any]) -> dict[str, Any] | None:
    title = str(item.get("question") or item.get("title") or "").strip()
    market_id = str(item.get("id") or item.get("conditionId") or item.get("slug") or "").strip()
    if not title or not market_id:
        return None
    prices = parse_jsonish(item.get("outcomePrices"))
    outcomes = parse_jsonish(item.get("outcomes"))
    if not isinstance(prices, list):
        prices = []
    parsed_prices = [clamp_price(safe_float(price)) for price in prices]
    yes_index = 0
    no_index = 1
    if isinstance(outcomes, list):
        lowered = [str(outcome).lower() for outcome in outcomes]
        if "yes" in lowered:
            yes_index = lowered.index("yes")
        if "no" in lowered:
            no_index = lowered.index("no")
    yes_price = parsed_prices[yes_index] if yes_index < len(parsed_prices) else None
    no_price = parsed_prices[no_index] if no_index < len(parsed_prices) else None
    if yes_price is not None and no_price is None:
        no_price = clamp_price(1 - yes_price)
    if no_price is not None and yes_price is None:
        yes_price = clamp_price(1 - no_price)
    slug = item.get("slug")
    return {
        "source": "Polymarket",
        "marketId": market_id,
        "title": title,
        "yesPrice": yes_price,
        "noPrice": no_price,
        "feeRate": safe_float(item.get("feeRate")) or 0.0,
        "quoteType": "indicative mid",
        "url": f"https://polymarket.com/event/{slug}" if slug else "https://polymarket.com",
        "description": str(item.get("description") or ""),
        "endDate": item.get("endDate") or item.get("endDateIso"),
        "eventId": str(item.get("eventId") or item.get("slug") or ""),
    }


def parse_kalshi_market(item: dict[str, Any]) -> dict[str, Any] | None:
    title = str(item.get("title") or item.get("subtitle") or "").strip()
    market_id = str(item.get("ticker") or item.get("id") or "").strip()
    if not title or not market_id:
        return None

    def first_price(*keys: str) -> float | None:
        for key in keys:
            parsed = clamp_price(safe_float(item.get(key)))
            if parsed is not None:
                return parsed
        return None

    yes_ask = first_price("yes_ask", "yes_ask_dollars")
    no_ask = first_price("no_ask", "no_ask_dollars")
    yes_bid = first_price("yes_bid", "yes_bid_dollars")
    no_bid = first_price("no_bid", "no_bid_dollars")
    last_price = first_price("last_price", "last_price_dollars")
    yes_price = yes_ask or last_price or yes_bid
    no_price = no_ask or (clamp_price(1 - last_price) if last_price is not None else None) or no_bid
    if yes_price is None and no_price is not None:
        yes_price = clamp_price(1 - no_price)
    if no_price is None and yes_price is not None:
        no_price = clamp_price(1 - yes_price)
    quote_type = "public ask" if yes_ask is not None and no_ask is not None else "indicative last price"
    return {
        "source": "Kalshi",
        "marketId": market_id,
        "title": title,
        "yesPrice": yes_price,
        "noPrice": no_price,
        "feeRate": safe_float(item.get("fee_rate")) or 0.0,
        "quoteType": quote_type,
        "url": f"https://kalshi.com/markets/{market_id}",
        "description": str(item.get("subtitle") or ""),
        "endDate": item.get("expiration_time") or item.get("close_time"),
        "eventId": str(item.get("event_ticker") or ""),
    }


def raw_market_id(item: dict[str, Any], index: int) -> str:
    return str(item.get("id") or item.get("conditionId") or item.get("ticker") or item.get("slug") or f"unknown-{index}")


def error_status(error: Exception, endpoint: str | None = None) -> tuple[str | None, int | None, str]:
    if isinstance(error, PublicApiError):
        return error.endpoint, error.http_status, error.detail
    return endpoint, None, str(error)[:300]


def fetch_polymarket() -> tuple[list[dict[str, Any]], dict[str, Any], list[dict[str, Any]]]:
    fetched_at = utc_now()
    raw_markets: list[dict[str, Any]] = []
    last_endpoint: str | None = None
    pages_fetched = 0
    try:
        for page in range(POLYMARKET_MAX_PAGES):
            offset = page * POLYMARKET_PAGE_SIZE
            last_endpoint = f"https://gamma-api.polymarket.com/markets?active=true&closed=false&limit={POLYMARKET_PAGE_SIZE}&offset={offset}"
            payload = fetch_json(last_endpoint)
            pages_fetched += 1
            page_items = payload.get("data", payload) if isinstance(payload, dict) else payload
            if not isinstance(page_items, list):
                raise PublicApiError(last_endpoint, "unexpected market-list response", 200)
            active_items = [
                item for item in page_items
                if isinstance(item, dict) and item.get("active") is not False and item.get("closed") is not True and item.get("archived") is not True
            ]
            raw_markets.extend(active_items)
            if len(page_items) < POLYMARKET_PAGE_SIZE:
                break
        markets = [parsed for item in raw_markets if (parsed := parse_polymarket_market(item))]
        return markets, {
            "source": "Polymarket",
            "status": "ok",
            "marketCount": len(raw_markets),
            "parsedMarketCount": len(markets),
            "fetchedAt": fetched_at,
            "endpoint": last_endpoint,
            "httpStatus": 200,
            "pagesFetched": pages_fetched,
            "error": None,
        }, raw_markets
    except Exception as error:
        endpoint, http_status, detail = error_status(error, last_endpoint)
        LOGGER.error(
            "source_fetch_failed source=Polymarket endpoint=%s http_status=%s error=%s pages_fetched=%s",
            endpoint,
            http_status,
            detail,
            pages_fetched,
        )
        markets = [parsed for item in raw_markets if (parsed := parse_polymarket_market(item))]
        return markets, {
            "source": "Polymarket",
            "status": "error",
            "marketCount": len(raw_markets),
            "parsedMarketCount": len(markets),
            "fetchedAt": fetched_at,
            "endpoint": endpoint,
            "httpStatus": http_status,
            "pagesFetched": pages_fetched,
            "error": detail,
        }, raw_markets


def fetch_kalshi() -> tuple[list[dict[str, Any]], dict[str, Any], list[dict[str, Any]]]:
    fetched_at = utc_now()
    base_urls = [
        "https://external-api.kalshi.com/trade-api/v2/markets",
        "https://external-api.kalshi.com/trade-api/v2/markets",
    ]
    last_error = "No Kalshi endpoint responded"
    last_endpoint: str | None = None
    last_http_status: int | None = None
    for base_url in base_urls:
        raw_markets: list[dict[str, Any]] = []
        pages_fetched = 0
        try:
            cursor = ""
            for _page in range(KALSHI_MAX_PAGES):
                params = f"?status=open&limit={KALSHI_PAGE_SIZE}" + (f"&cursor={urllib.parse.quote(cursor)}" if cursor else "")
                last_endpoint = base_url + params
                payload = fetch_json(last_endpoint)
                pages_fetched += 1
                page_items = payload.get("markets", []) if isinstance(payload, dict) else []
                if not isinstance(page_items, list):
                    raise PublicApiError(last_endpoint, "unexpected market-list response", 200)
                raw_markets.extend(
                    item for item in page_items
                    if isinstance(item, dict) and str(item.get("status", "active")).lower() in {"active", "open"}
                )
                cursor = str(payload.get("cursor") or "") if isinstance(payload, dict) else ""
                if not cursor or not page_items:
                    break
            markets = [parsed for item in raw_markets if isinstance(item, dict) and (parsed := parse_kalshi_market(item))]
            return markets, {
                "source": "Kalshi",
                "status": "ok",
                "marketCount": len(raw_markets),
                "parsedMarketCount": len(markets),
                "fetchedAt": fetched_at,
                "endpoint": last_endpoint,
                "httpStatus": 200,
                "pagesFetched": pages_fetched,
                "error": None,
            }, raw_markets
        except Exception as error:
            endpoint, http_status, detail = error_status(error, last_endpoint)
            last_error = detail
            last_http_status = http_status
            LOGGER.error(
                "source_fetch_failed source=Kalshi endpoint=%s http_status=%s error=%s pages_fetched=%s",
                endpoint,
                http_status,
                detail,
                pages_fetched,
            )
            if raw_markets:
                markets = [parsed for item in raw_markets if (parsed := parse_kalshi_market(item))]
                return markets, {
                    "source": "Kalshi",
                    "status": "error",
                    "marketCount": len(raw_markets),
                    "parsedMarketCount": len(markets),
                    "fetchedAt": fetched_at,
                    "endpoint": endpoint,
                    "httpStatus": http_status,
                    "pagesFetched": pages_fetched,
                    "error": detail,
                }, raw_markets
    return [], {
        "source": "Kalshi",
        "status": "error",
        "marketCount": 0,
        "parsedMarketCount": 0,
        "fetchedAt": fetched_at,
        "endpoint": last_endpoint,
        "httpStatus": last_http_status,
        "pagesFetched": 0,
        "error": last_error,
    }, []


def build_opportunity(left: dict[str, Any], right: dict[str, Any], score: float) -> dict[str, Any] | None:
    directions = [
        ("Buy YES on Polymarket / NO on Kalshi", left, right, left["yesPrice"], right["noPrice"]),
        ("Buy YES on Kalshi / NO on Polymarket", right, left, right["yesPrice"], left["noPrice"]),
    ]
    candidates: list[dict[str, Any]] = []
    for direction, buy_yes, buy_no, yes_price, no_price in directions:
        if yes_price is None or no_price is None:
            continue
        combined_cost = float(yes_price + no_price)
        gross_per_contract = max(0.0, 1.0 - combined_cost)
        gross_edge = gross_per_contract * NOTIONAL
        estimated_fees = NOTIONAL * (float(buy_yes["feeRate"]) + float(buy_no["feeRate"]))
        net_edge = gross_edge - estimated_fees
        candidates.append({
            "direction": direction,
            "buyYes": buy_yes,
            "buyNo": buy_no,
            "combinedCost": round(combined_cost, 6),
            "grossEdge": round(gross_edge, 4),
            "estimatedFees": round(estimated_fees, 4),
            "netEdge": round(net_edge, 4),
        })
    if not candidates:
        return None
    best = max(candidates, key=lambda candidate: candidate["netEdge"])
    if best["netEdge"] <= 0.01:
        return None
    detected_at = utc_now()
    return {
        "id": f"opp_{uuid.uuid4().hex[:12]}",
        "detectedAt": detected_at,
        "title": left["title"],
        "matchScore": round(score, 4),
        "direction": best["direction"],
        "buyYes": best["buyYes"],
        "buyNo": best["buyNo"],
        "combinedCost": best["combinedCost"],
        "grossEdge": best["grossEdge"],
        "estimatedFees": best["estimatedFees"],
        "netEdge": best["netEdge"],
        "notional": NOTIONAL,
        "status": "potential",
        "sourceMarkets": [f'{left["source"]}:{left["marketId"]}', f'{right["source"]}:{right["marketId"]}'],
    }


class Ledger:
    def __init__(self, path: str):
        self.connection = sqlite3.connect(path, check_same_thread=False)
        self.connection.row_factory = sqlite3.Row
        self.lock = threading.Lock()
        self._initialize()

    def _initialize(self) -> None:
        with self.connection:
            self.connection.executescript(
                """
                CREATE TABLE IF NOT EXISTS settings (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS scan_runs (
                    id TEXT PRIMARY KEY,
                    scanned_at TEXT NOT NULL,
                    status TEXT NOT NULL,
                    matched_markets INTEGER NOT NULL,
                    logged_count INTEGER NOT NULL,
                    source_status TEXT NOT NULL,
                    candidate_matches TEXT NOT NULL DEFAULT '[]'
                );
                CREATE TABLE IF NOT EXISTS raw_market_data (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    scan_id TEXT NOT NULL,
                    source TEXT NOT NULL,
                    market_id TEXT NOT NULL,
                    fetched_at TEXT NOT NULL,
                    payload TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS opportunities (
                    id TEXT PRIMARY KEY,
                    detected_at TEXT NOT NULL,
                    title TEXT NOT NULL,
                    payload TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS paper_trades (
                    id TEXT PRIMARY KEY,
                    opportunity_id TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    amount REAL NOT NULL,
                    expected_pnl REAL NOT NULL,
                    status TEXT NOT NULL,
                    legs TEXT NOT NULL,
                    note TEXT NOT NULL
                );
                """
            )
            columns = {row["name"] for row in self.connection.execute("PRAGMA table_info(scan_runs)").fetchall()}
            if "candidate_matches" not in columns:
                self.connection.execute("ALTER TABLE scan_runs ADD COLUMN candidate_matches TEXT NOT NULL DEFAULT '[]'")
            self.connection.execute(
                "INSERT OR IGNORE INTO settings(key, value) VALUES (?, ?)",
                ("virtual_balance", str(STARTING_BALANCE)),
            )

    def latest_scan(self) -> sqlite3.Row | None:
        return self.connection.execute("SELECT * FROM scan_runs ORDER BY scanned_at DESC LIMIT 1").fetchone()

    def save_scan(
        self,
        source_status: list[dict[str, Any]],
        candidate_matches: list[dict[str, Any]],
        opportunities: list[dict[str, Any]],
        raw_market_data: list[tuple[str, dict[str, Any], str]],
    ) -> None:
        scan_status = "ok" if all(source["status"] == "ok" for source in source_status) else "partial"
        scanned_at = utc_now()
        scan_id = f"scan_{uuid.uuid4().hex[:12]}"
        with self.lock, self.connection:
            self.connection.execute(
                "INSERT INTO scan_runs(id, scanned_at, status, matched_markets, logged_count, source_status, candidate_matches) VALUES (?, ?, ?, ?, ?, ?, ?)",
                (scan_id, scanned_at, scan_status, len(candidate_matches), len(opportunities), json_dumps(source_status), json_dumps(candidate_matches)),
            )
            for opportunity in opportunities:
                self.connection.execute(
                    "INSERT OR REPLACE INTO opportunities(id, detected_at, title, payload) VALUES (?, ?, ?, ?)",
                    (opportunity["id"], opportunity["detectedAt"], opportunity["title"], json_dumps(opportunity)),
                )
            self.connection.executemany(
                "INSERT INTO raw_market_data(scan_id, source, market_id, fetched_at, payload) VALUES (?, ?, ?, ?, ?)",
                [(scan_id, source, market_id, scanned_at, json_dumps(payload)) for source, payload, market_id in raw_market_data],
            )

    def opportunities(self, limit: int = 50) -> list[dict[str, Any]]:
        rows = self.connection.execute("SELECT payload FROM opportunities ORDER BY detected_at DESC LIMIT ?", (max(1, min(200, limit)),)).fetchall()
        return [json.loads(row["payload"]) for row in rows]

    def raw_markets(self, source: str | None = None, limit: int = 20) -> list[dict[str, Any]]:
        safe_limit = max(1, min(100, limit))
        if source:
            rows = self.connection.execute(
                "SELECT scan_id, source, market_id, fetched_at, payload FROM raw_market_data WHERE source = ? ORDER BY id DESC LIMIT ?",
                (source, safe_limit),
            ).fetchall()
        else:
            rows = self.connection.execute(
                "SELECT scan_id, source, market_id, fetched_at, payload FROM raw_market_data ORDER BY id DESC LIMIT ?",
                (safe_limit,),
            ).fetchall()
        return [
            {
                "scanId": row["scan_id"],
                "source": row["source"],
                "marketId": row["market_id"],
                "fetchedAt": row["fetched_at"],
                "payload": json.loads(row["payload"]),
            }
            for row in rows
        ]

    def find_opportunity(self, opportunity_id: str) -> dict[str, Any] | None:
        row = self.connection.execute("SELECT payload FROM opportunities WHERE id = ?", (opportunity_id,)).fetchone()
        return json.loads(row["payload"]) if row else None

    def trades(self) -> list[dict[str, Any]]:
        rows = self.connection.execute(
            "SELECT id, opportunity_id, created_at, amount, expected_pnl, status, legs, note FROM paper_trades ORDER BY created_at DESC LIMIT 100"
        ).fetchall()
        return [
            {
                "id": row["id"],
                "opportunityId": row["opportunity_id"],
                "createdAt": row["created_at"],
                "amount": row["amount"],
                "expectedPnl": row["expected_pnl"],
                "status": row["status"],
                "legs": json.loads(row["legs"]),
                "note": row["note"],
            }
            for row in rows
        ]

    def balances(self) -> tuple[float, float, float]:
        virtual_balance = float(self.connection.execute("SELECT value FROM settings WHERE key = 'virtual_balance'").fetchone()["value"])
        committed = float(self.connection.execute("SELECT COALESCE(SUM(amount), 0) AS total FROM paper_trades WHERE status = 'open'").fetchone()["total"])
        return virtual_balance, max(0.0, virtual_balance - committed), committed

    def create_trade(self, opportunity_id: str, amount: float) -> dict[str, Any]:
        opportunity = self.find_opportunity(opportunity_id)
        if opportunity is None:
            raise ValueError("Opportunity was not found in the local ledger.")
        _, available, _ = self.balances()
        if amount <= 0 or amount > available:
            raise ValueError(f"Amount must be greater than zero and no more than the available balance of ${available:.2f}.")
        expected_pnl = amount * (opportunity["netEdge"] / opportunity["notional"])
        trade_id = f"trade_{uuid.uuid4().hex[:12]}"
        created_at = utc_now()
        legs = [
            f'YES on {opportunity["buyYes"]["source"]} @ {opportunity["buyYes"]["yesPrice"]:.4f}',
            f'NO on {opportunity["buyNo"]["source"]} @ {opportunity["buyNo"]["noPrice"]:.4f}',
        ]
        note = "Paper reservation only; no live order, wallet, credential, or private key is used."
        with self.lock, self.connection:
            self.connection.execute(
                "INSERT INTO paper_trades(id, opportunity_id, created_at, amount, expected_pnl, status, legs, note) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                (trade_id, opportunity_id, created_at, amount, expected_pnl, "open", json_dumps(legs), note),
            )
        return {
            "id": trade_id,
            "opportunityId": opportunity_id,
            "createdAt": created_at,
            "amount": amount,
            "expectedPnl": round(expected_pnl, 4),
            "status": "open",
            "legs": legs,
            "note": note,
        }


ledger = Ledger(DATABASE_PATH)


def run_scan() -> dict[str, Any]:
    polymarket, polymarket_status, polymarket_raw = fetch_polymarket()
    kalshi, kalshi_status, kalshi_raw = fetch_kalshi()
    source_status = [polymarket_status, kalshi_status]
    opportunities: list[dict[str, Any]] = []
    candidate_matches: list[dict[str, Any]] = []
    if polymarket_status["status"] == "ok" and kalshi_status["status"] == "ok":
        LOGGER.info(
            "market_matching_started polymarket_markets=%s kalshi_markets=%s",
            len(polymarket),
            len(kalshi),
        )
        kalshi_token_index: dict[str, set[int]] = defaultdict(set)
        for index, kalshi_market in enumerate(kalshi):
            for token in text_tokens(kalshi_market["title"]):
                kalshi_token_index[token].add(index)
        for polymarket_market in polymarket:
            best_match: tuple[float, dict[str, Any], dict[str, Any]] | None = None
            candidate_indexes: set[int] = set()
            for token in text_tokens(polymarket_market["title"]):
                candidate_indexes.update(kalshi_token_index.get(token, set()))
            for kalshi_index in candidate_indexes:
                kalshi_market = kalshi[kalshi_index]
                match = market_match(polymarket_market, kalshi_market)
                if match is None:
                    continue
                score = float(match["score"])
                candidate = {
                    "id": f"candidate_{polymarket_market['marketId']}_{kalshi_market['marketId']}",
                    "matchScore": round(score, 4),
                    "matchReason": match["matchReason"],
                    "evidence": match["evidence"],
                    "polymarket": {
                        "marketId": polymarket_market["marketId"],
                        "title": polymarket_market["title"],
                        "hasQuote": polymarket_market["yesPrice"] is not None and polymarket_market["noPrice"] is not None,
                    },
                    "kalshi": {
                        "marketId": kalshi_market["marketId"],
                        "title": kalshi_market["title"],
                        "hasQuote": kalshi_market["yesPrice"] is not None and kalshi_market["noPrice"] is not None,
                    },
                }
                opportunity = build_opportunity(polymarket_market, kalshi_market, score)
                if opportunity is not None:
                    candidate["opportunityId"] = opportunity["id"]
                if best_match is None or score > best_match[0]:
                    best_match = (score, candidate, opportunity)
            if best_match is not None:
                candidate_matches.append(best_match[1])
                if best_match[2] is not None:
                    opportunities.append(best_match[2])
        LOGGER.info("market_matching_finished candidate_matches=%s opportunities=%s", len(candidate_matches), len(opportunities))
    else:
        LOGGER.warning(
            "market_matching_skipped polymarket_status=%s kalshi_status=%s",
            polymarket_status["status"],
            kalshi_status["status"],
        )
    candidate_matches.sort(key=lambda candidate: candidate["matchScore"], reverse=True)
    opportunities.sort(key=lambda opportunity: opportunity["netEdge"], reverse=True)
    opportunities = opportunities[:100]
    raw_market_data = [
        ("Polymarket", item, raw_market_id(item, index))
        for index, item in enumerate(polymarket_raw)
    ] + [
        ("Kalshi", item, raw_market_id(item, index))
        for index, item in enumerate(kalshi_raw)
    ]
    for status in source_status:
        status["rawStoredCount"] = sum(1 for source, _payload, _market_id in raw_market_data if source == status["source"])
    ledger.save_scan(source_status, candidate_matches, opportunities, raw_market_data)
    return {
        "scannedAt": utc_now(),
        "opportunities": opportunities,
        "sourceStatus": source_status,
        "matchedMarkets": len(candidate_matches),
        "candidateMatchCount": len(candidate_matches),
        "candidateMatches": candidate_matches[:MAX_CANDIDATES_RETURNED],
        "loggedCount": len(opportunities),
    }


def dashboard() -> dict[str, Any]:
    virtual_balance, available_balance, committed_capital = ledger.balances()
    latest = ledger.latest_scan()
    source_status = json.loads(latest["source_status"]) if latest else []
    candidate_matches = json.loads(latest["candidate_matches"]) if latest and latest["candidate_matches"] else []
    return {
        "virtualBalance": virtual_balance,
        "availableBalance": available_balance,
        "committedCapital": committed_capital,
        "opportunityCount": len(ledger.opportunities(200)),
        "lastScanAt": latest["scanned_at"] if latest else None,
        "lastScanStatus": latest["status"] if latest else "waiting",
        "sourceStatus": source_status,
        "candidateMatchCount": int(latest["matched_markets"]) if latest else 0,
        "candidateMatches": candidate_matches[:MAX_CANDIDATES_RETURNED],
        "opportunities": ledger.opportunities(25),
        "recentTrades": ledger.trades()[:10],
    }


class ApiHandler(BaseHTTPRequestHandler):
    server_version = "MarketHunterBotV1/1.0"

    def log_message(self, _format: str, *_args: Any) -> None:
        return

    def send_json(self, status_code: int, payload: Any) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status_code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    def read_body(self) -> dict[str, Any]:
        length = int(self.headers.get("Content-Length", "0"))
        if length > 10000:
            raise ValueError("Request body is too large.")
        raw = self.rfile.read(length) if length else b"{}"
        payload = json.loads(raw.decode("utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("Request body must be a JSON object.")
        return payload

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self) -> None:
        path = urllib.parse.urlparse(self.path).path
        query = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
        try:
            if path == f"{API_PREFIX}/healthz":
                return self.send_json(200, {"status": "healthy"})
            if path == f"{API_PREFIX}/dashboard":
                return self.send_json(200, dashboard())
            if path == f"{API_PREFIX}/opportunities":
                limit = int(query.get("limit", ["50"])[0])
                return self.send_json(200, ledger.opportunities(limit))
            if path == f"{API_PREFIX}/paper-trades":
                return self.send_json(200, ledger.trades())
            if path == f"{API_PREFIX}/raw-markets":
                source = query.get("source", [None])[0]
                limit = int(query.get("limit", ["20"])[0])
                return self.send_json(200, ledger.raw_markets(source, limit))
            return self.send_json(404, {"message": "Route not found."})
        except Exception as error:
            return self.send_json(500, {"message": str(error)})

    def do_POST(self) -> None:
        path = urllib.parse.urlparse(self.path).path
        try:
            if path == f"{API_PREFIX}/scan":
                return self.send_json(200, run_scan())
            if path == f"{API_PREFIX}/paper-trades":
                payload = self.read_body()
                opportunity_id = str(payload.get("opportunityId", "")).strip()
                amount = safe_float(payload.get("amount"))
                if not opportunity_id or amount is None:
                    return self.send_json(400, {"message": "opportunityId and a numeric amount are required."})
                return self.send_json(201, ledger.create_trade(opportunity_id, amount))
            return self.send_json(404, {"message": "Route not found."})
        except ValueError as error:
            return self.send_json(400, {"message": str(error)})
        except Exception as error:
            return self.send_json(500, {"message": str(error)})


def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s %(message)s",
    )
    port = int(os.environ.get("PORT", "8000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), ApiHandler)
    print(f"Market Hunter API listening on {port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()