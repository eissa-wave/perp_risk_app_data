"""
Risk monitor: fetches positions from Hyperliquid, Binance, Bybit, OKX and
writes a snapshot to the 'perp_monitor' tab of the 'Portfolios' Google Sheet.

Jenkins setup:
  Required environment variables (inject via Credentials Binding plugin):
    BYBIT_KEY, BYBIT_SECRET
    BINANCE_KEY, BINANCE_SECRET
    OKX_KEY, OKX_SECRET, OKX_PASS
    GOOGLE_APPLICATION_CREDENTIALS  -- path to the service-account JSON file

  Optional environment variables:
    HL_USER          -- Hyperliquid wallet to monitor
    HL_DEXS          -- comma-separated dexs; "" is main, add HIP-3 builders (default ",xyz")
    LIGHTER_ACCOUNT_INDEX  -- Lighter account index to monitor; unset skips Lighter entirely
    LIGHTER_BASE_URL       -- default "https://mainnet.zklighter.elliot.ai"
    SHEET_NAME       -- default "Portfolios"
    TAB_RISK         -- default "perp_monitor"

Exit codes:
  0  -- snapshot written successfully
  1  -- sheet write failed
  2  -- all four exchange fetches failed (nothing to write)
"""

import os
import sys
import requests
import time
import hmac
import hashlib
import base64
from datetime import datetime, timezone
from typing import Union, Dict, Any
from urllib.parse import urlencode

import gspread
from google.oauth2.service_account import Credentials


# ============================================================
#  CONFIG (all secrets via env)
# ============================================================
def _required_env(name: str) -> str:
    val = os.environ.get(name)
    if not val:
        print(f"[FATAL] Required environment variable {name} is not set.", file=sys.stderr)
        sys.exit(2)
    return val


BYBIT_API_KEY = _required_env("BYBIT_KEY")
BYBIT_API_SECRET = _required_env("BYBIT_SECRET")
BINANCE_KEY = _required_env("BINANCE_KEY")
BINANCE_SECRET = _required_env("BINANCE_SECRET")
OKX_API_KEY = _required_env("OKX_KEY")
OKX_API_SECRET = _required_env("OKX_SECRET")
OKX_PASSPHRASE = _required_env("OKX_PASS")
GOOGLE_CREDS_FILE = _required_env("GOOGLE_APPLICATION_CREDENTIALS")

HL_USER = os.environ.get("HL_USER", "0x64Ffaa34FffC59e84D3E7731812b3A63397Af7c6")
# DEXs to query. "" is the main validator-operated perp dex. Add HIP-3 builder
# dex names (e.g. "xyz" for xyz:CL). Each dex margins independently, so it is
# fetched separately and reported as its own account row "Hyperliquid:<dex>".
HL_DEXS = [d.strip() for d in os.environ.get("HL_DEXS", ",xyz").split(",")]
# The account runs HL's unified account mode: one USDC balance collateralizes
# spot plus all cross-margin perps across every dex. When True, HL is reported
# as a single account row using the unified balance as equity, and removable is
# computed against the unified balance. Set False (or env HL_UNIFIED=0) if the
# account is switched back to standard mode with separate per-dex balances.
HL_UNIFIED = os.environ.get("HL_UNIFIED", "1") not in ("0", "false", "False")
SHEET_NAME = os.environ.get("SHEET_NAME", "Portfolios")
TAB_RISK = os.environ.get("TAB_RISK", "perp_monitor")

HL_INFO_URL = "https://api.hyperliquid.xyz/info"
LIQ_DISTANCE_THRESHOLD_PCT = 25.0
TARGET_LIQ_DISTANCE_PCT = 20.0

BYBIT_BASE_URL = "https://api.bybit.com"
BYBIT_RECV_WINDOW = "5000"

OKX_BASE_URL = "https://www.okx.com"
OKX_MGN_RATIO_FLOOR = 1.5
OKX_MGN_RATIO_TARGET = 1.33

# Same framing as OKX, applied to Binance account-level marginBalance/maintMargin.
# Used as the fallback when Binance cross positions don't return a liq price.
BN_MGN_RATIO_FLOOR = 1.5
BN_MGN_RATIO_TARGET = 1.33

LIGHTER_BASE_URL = os.environ.get("LIGHTER_BASE_URL", "https://mainnet.zklighter.elliot.ai")
# Account/position data on Lighter is public (query by account index, no API
# key or request signing needed). Leave unset to skip Lighter entirely.
LIGHTER_ACCOUNT_INDEX = os.environ.get("LIGHTER_ACCOUNT_INDEX")
# Same framing as OKX/Binance: account equity / maintenance margin requirement.
LIGHTER_MGN_RATIO_FLOOR = 1.5
LIGHTER_MGN_RATIO_TARGET = 1.33

# ============================================================
#  STRATEGY START DATES (hardcoded, by base ticker)
# ============================================================
# Trade entry date per funding-arb strategy, keyed by the normalized base
# ticker (the same key the Strategy PnL section groups on, e.g. "VVV", "XMR",
# "CL"). Two uses:
#   1. Annualizing collected funding: ann% = (funding / avg notional)
#      * (365 / days since start) * 100.
#   2. Anchoring the funding window: for a mapped ticker, only funding events
#      on or after its start date are summed, so each strategy's funding is
#      measured since entry, never a trailing window.
# Strategies missing from this map show a blank annualized column and use the
# global FUNDING_START_MS window. Update when entering/rolling a new strategy.
STRATEGY_START_DATES = {
    # "TICKER": "YYYY-MM-DD",
    "VVV": "2026-06-10",
    "JTO": "2026-07-10",
    "LIT": "2026-07-10",
    "SPCX": "2026-07-14",
    "BRENT": "2026-07-22",
    "CL" : "2026-07-23"
}

# Venue-specific tickers that refer to the same underlying strategy but don't
# share a common normalized base symbol (e.g. HL lists it as "BRENTOIL", while
# Binance's spot/perp symbol for the same crude-oil proxy is "BZUSDT" -> "BZ").
# Map each raw normalized key to the canonical STRATEGY_START_DATES key so both
# legs group into one Strategy PnL row. Add future mismatches here.
STRATEGY_ALIASES = {
    "BRENTOIL": "BRENT",   # Hyperliquid xyz:xyz:BRENTOIL
    "BZ": "BRENT",         # Binance BZUSDT
}


def _date_to_ms(date_str: str):
    try:
        dt = datetime.strptime(date_str, "%Y-%m-%d").replace(tzinfo=timezone.utc)
        return int(dt.timestamp() * 1000)
    except (TypeError, ValueError):
        return None


def _min_strategy_start_ms() -> int:
    """Earliest strategy start date in ms. Fixed anchor for the funding fetch
    window so totals are stable run to run (the old now-90d default rolled
    forward every run, silently dropping old events and swinging the sums)."""
    starts = [ms for ms in (_date_to_ms(s) for s in STRATEGY_START_DATES.values()) if ms]
    if starts:
        return min(starts)
    # No strategies mapped: fall back to a fixed epoch, NOT a rolling window.
    return _date_to_ms("2026-01-01")


# Funding: collected funding is summed per symbol from FUNDING_START_MS to now,
# further clipped per symbol to that strategy's start date when mapped in
# STRATEGY_START_DATES. Override the global start with an absolute ms epoch via
# env (FUNDING_START_MS); default is the earliest strategy start date (fixed).
FUNDING_START_MS = int(
    os.environ.get("FUNDING_START_MS", str(_min_strategy_start_ms()))
)


def _period_start_ms(period: str) -> int:
    """UTC epoch ms for the start of the current calendar month ("mtd") or
    current calendar year ("ytd"), evaluated at run time."""
    now = datetime.now(timezone.utc)
    if period == "mtd":
        start = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    elif period == "ytd":
        start = now.replace(month=1, day=1, hour=0, minute=0, second=0, microsecond=0)
    else:
        raise ValueError(period)
    return int(start.timestamp() * 1000)


MTD_START_MS = _period_start_ms("mtd")
YTD_START_MS = _period_start_ms("ytd")

# The per-symbol funding fetchers below need raw events back to at least
# YTD_START_MS so the Strategy PnL "MTD"/"YTD" columns are complete, even
# though FUNDING_START_MS (earliest mapped strategy start) can be later in the
# year than Jan 1. This is the actual start passed into each exchange's
# funding fetch call; FUNDING_START_MS itself keeps its original meaning
# (used for the per-strategy clipped total that feeds annualization).
FUNDING_FETCH_START_MS = min(FUNDING_START_MS, YTD_START_MS)

# Hide dust: position rows with absolute notional below this are excluded from
# the sheet (Per-Position Detail and Strategy PnL legs). They still count in
# the fetchers' risk math (equity, deltas, removable). Env override
# MIN_POSITION_USD; set 0 to show everything.
MIN_POSITION_USD = float(os.environ.get("MIN_POSITION_USD", "300"))

GSHEET_SCOPES = [
    "https://www.googleapis.com/auth/spreadsheets",
    "https://www.googleapis.com/auth/drive",
]


def _log(msg: str) -> None:
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    print(f"[{ts}] {msg}", flush=True)


def _summary_line(r: dict) -> str:
    s = (
        f"{r['exchange']}: {r['positions_count']} positions, "
        f"excess={r['excess_collateral']}, "
        f"removable={r['removable_total']:,.2f} {r['currency']}, "
        f"leverage={r['leverage']:.2f}x"
    )
    if r['mgn_ratio'] is not None:
        s += f", mgnRatio={r['mgn_ratio']:.2f}x"
    return s


def _removable_isolated_position(direction: str, size: float, mark: float, liq: float) -> float:
    if size == 0 or mark <= 0 or liq <= 0:
        return 0.0
    if direction == "LONG":
        target_liq = mark * (1 - TARGET_LIQ_DISTANCE_PCT / 100.0)
        if target_liq <= liq:
            return 0.0
        return (target_liq - liq) * abs(size)
    else:
        target_liq = mark * (1 + TARGET_LIQ_DISTANCE_PCT / 100.0)
        if target_liq >= liq:
            return 0.0
        return (liq - target_liq) * abs(size)


def _removable_cross_binding(cross_positions: list, account_equity: float) -> float:
    if not cross_positions or account_equity <= 0:
        return 0.0
    target = TARGET_LIQ_DISTANCE_PCT / 100.0
    per_pos_caps = []
    for p in cross_positions:
        size = p["size"]
        mark = p["mark"]
        liq = p["liq"]
        if size == 0 or mark <= 0 or liq <= 0:
            continue
        current_dist = abs(mark - liq) / mark
        if current_dist <= target:
            return 0.0
        max_delta = (current_dist - target) * mark * abs(size)
        per_pos_caps.append(max_delta)
    if not per_pos_caps:
        return 0.0
    return max(0.0, min(min(per_pos_caps), account_equity))


# ============================================================
#  FUNDING (collected funding per symbol, clipped per strategy)
# ============================================================
def _now_ms() -> int:
    return int(time.time() * 1000)


def _chunks(start_ms: int, end_ms: int, chunk_ms: int):
    """Yield (chunk_start, chunk_end) pairs covering [start_ms, end_ms]."""
    cur = start_ms
    while cur <= end_ms:
        yield cur, min(cur + chunk_ms - 1, end_ms)
        cur += chunk_ms


def _funding_start_for(symbol: str) -> int:
    """Effective funding-window start for a venue symbol: the strategy start
    date when the normalized ticker is mapped, else the global window start."""
    start_str = STRATEGY_START_DATES.get(_strategy_key(symbol))
    if start_str:
        ms = _date_to_ms(start_str)
        if ms:
            return max(ms, 0)
    return FUNDING_START_MS


def _hl_funding_by_coin(session, dex: str, start_ms: int, end_ms: int,
                        timeout: int, retries: int, backoff_s: float) -> dict:
    """Sum HL funding (delta.usdc, positive = received) per coin for one dex,
    paginating via the last event time. Keyed by raw coin name.

    Pagination re-fetches from the last timestamp inclusive (cur = last_time,
    not last_time + 1) and dedups on (time, coin, usdc) so events sharing the
    boundary timestamp of a full page are never dropped. Per-coin clipping to
    the strategy start date happens here.

    Returns (totals, totals_24h, totals_mtd, totals_ytd): funding since the
    clipped strategy-start window, funding over the trailing 24 hours,
    funding month-to-date, and funding year-to-date. All four are computed in
    one pass over the same fetched events, so no extra requests are needed."""
    totals: dict = {}
    totals_24h: dict = {}
    totals_mtd: dict = {}
    totals_ytd: dict = {}
    cutoff_24h = end_ms - 86_400_000
    seen = set()
    cur = start_ms
    pages = 0
    while pages < 10_000:
        pages += 1
        payload = {"type": "userFunding", "user": HL_USER, "startTime": cur, "endTime": end_ms}
        if dex:
            payload["dex"] = dex
        data = _hl_post(session, payload, timeout, retries, backoff_s)
        if not data:
            break
        for ev in data:
            t = ev.get("time")
            delta = ev.get("delta") or {}
            coin = delta.get("coin")
            usdc = delta.get("usdc")
            if coin is None or usdc is None:
                continue
            key = (t, coin, usdc)
            if key in seen:
                continue
            seen.add(key)
            amt = float(usdc)
            if t is not None:
                ti = int(t)
                if ti >= cutoff_24h:
                    totals_24h[coin] = totals_24h.get(coin, 0.0) + amt
                if ti >= MTD_START_MS:
                    totals_mtd[coin] = totals_mtd.get(coin, 0.0) + amt
                if ti >= YTD_START_MS:
                    totals_ytd[coin] = totals_ytd.get(coin, 0.0) + amt
            if t is not None and int(t) < _funding_start_for(coin):
                continue
            totals[coin] = totals.get(coin, 0.0) + amt
        if len(data) < 500:
            break
        last_time = data[-1].get("time")
        if last_time is None:
            break
        next_cur = int(last_time)
        if next_cur <= cur:
            # whole page at one timestamp: forced bump to escape, else we loop
            next_cur = cur + 1
        cur = next_cur
        if cur > end_ms:
            break
    return totals, totals_24h, totals_mtd, totals_ytd


def _binance_funding_by_symbol(start_ms: int, end_ms: int) -> tuple:
    """Sum Binance FUNDING_FEE income (negative = paid) per symbol across all
    symbols, paginating via the last event time.

    Pagination re-fetches from the last timestamp inclusive and dedups on
    tranId (fallback: time/symbol/income tuple) so boundary-timestamp events
    are never dropped. Per-symbol clipping to the strategy start date happens
    here.

    Returns (totals, totals_24h, totals_mtd, totals_ytd)."""
    base_url = "https://fapi.binance.com"
    path = "/fapi/v1/income"
    limit = 1000
    totals: dict = {}
    totals_24h: dict = {}
    totals_mtd: dict = {}
    totals_ytd: dict = {}
    cutoff_24h = end_ms - 86_400_000
    seen = set()
    current_start = start_ms
    while True:
        params = {
            "timestamp": int(time.time() * 1000),
            "incomeType": "FUNDING_FEE",
            "limit": limit,
            "startTime": current_start,
            "endTime": end_ms,
        }
        qs = urlencode(params)
        params["signature"] = hmac.new(
            BINANCE_SECRET.encode("utf-8"), qs.encode("utf-8"), digestmod=hashlib.sha256
        ).hexdigest()
        headers = {"X-MBX-APIKEY": BINANCE_KEY}
        r = requests.get(base_url + path, params=params, headers=headers, timeout=10)
        r.raise_for_status()
        batch = r.json()
        if not batch:
            break
        for x in batch:
            if x.get("incomeType") != "FUNDING_FEE":
                continue
            key = x.get("tranId") or (x.get("time"), x.get("symbol"), x.get("income"))
            if key in seen:
                continue
            seen.add(key)
            sym = x.get("symbol")
            t = x.get("time")
            amt = float(x.get("income") or 0)
            if t is not None:
                ti = int(t)
                if ti >= cutoff_24h:
                    totals_24h[sym] = totals_24h.get(sym, 0.0) + amt
                if ti >= MTD_START_MS:
                    totals_mtd[sym] = totals_mtd.get(sym, 0.0) + amt
                if ti >= YTD_START_MS:
                    totals_ytd[sym] = totals_ytd.get(sym, 0.0) + amt
            if t is not None and int(t) < _funding_start_for(sym):
                continue
            totals[sym] = totals.get(sym, 0.0) + amt
        if len(batch) < limit:
            break
        last_time = max(int(x["time"]) for x in batch)
        if last_time <= current_start:
            # whole page at one timestamp: forced bump to escape, else we loop
            current_start = current_start + 1
        else:
            current_start = last_time
        time.sleep(0.2)
    return totals, totals_24h, totals_mtd, totals_ytd


def _okx_funding_by_inst(start_ms: int, end_ms: int, timeout: int) -> tuple:
    """Sum OKX funding-fee bills (type=8, amount in `pnl`, negative = paid) per
    instId. Queries both the 7-day and archive endpoints and dedups by billId.
    Per-instId clipping to the strategy start date is applied via each bill's
    ts. Returns (totals, totals_24h, totals_mtd, totals_ytd)."""
    limit = 100
    all_rows = []
    for path in ("/api/v5/account/bills", "/api/v5/account/bills-archive"):
        after = None
        guard = 0
        while guard < 1000:
            guard += 1
            params = {"instType": "SWAP", "type": "8", "limit": str(limit)}
            if start_ms is not None:
                params["begin"] = str(start_ms)
            if end_ms is not None:
                params["end"] = str(end_ms)
            if after is not None:
                params["after"] = str(after)
            try:
                data = _okx_signed_get(path, params, timeout_s=timeout)
            except RuntimeError as exc:
                print(f"  [OKX bills warning] {path}: {exc}")
                break
            rows = data.get("data", []) or []
            if not rows:
                break
            all_rows.extend(rows)
            try:
                after = min(int(r["billId"]) for r in rows if r.get("billId"))
            except (ValueError, KeyError):
                break
            if len(rows) < limit:
                break

    seen = set()
    totals: dict = {}
    totals_24h: dict = {}
    totals_mtd: dict = {}
    totals_ytd: dict = {}
    cutoff_24h = end_ms - 86_400_000
    for r in all_rows:
        bid = r.get("billId")
        if bid in seen:
            continue
        seen.add(bid)
        inst = r.get("instId")
        try:
            ts = int(r.get("ts") or 0)
        except (TypeError, ValueError):
            ts = 0
        amt = float(r.get("pnl") or 0)
        if ts >= cutoff_24h:
            totals_24h[inst] = totals_24h.get(inst, 0.0) + amt
        if ts >= MTD_START_MS:
            totals_mtd[inst] = totals_mtd.get(inst, 0.0) + amt
        if ts >= YTD_START_MS:
            totals_ytd[inst] = totals_ytd.get(inst, 0.0) + amt
        if ts and ts < _funding_start_for(inst):
            continue
        totals[inst] = totals.get(inst, 0.0) + amt
    return totals, totals_24h, totals_mtd, totals_ytd


def _hl_post(session, payload: dict, timeout: int, retries: int, backoff_s: float) -> Union[list, dict]:
    for attempt in range(retries):
        try:
            resp = session.post(HL_INFO_URL, json=payload, timeout=timeout)
            resp.raise_for_status()
            return resp.json()
        except (requests.RequestException, ValueError) as exc:
            if attempt == retries - 1:
                raise
            time.sleep(backoff_s * (2 ** attempt))


def _get_hl_dex_positions(session, dex: str, timeout: int, retries: int, backoff_s: float) -> dict:
    """Fetch one HL perp dex. dex="" is the main validator-operated dex; a
    non-empty name is a HIP-3 builder dex with independent margining. Builder-dex
    symbols are prefixed dex:coin (e.g. xyz:CL) and the account is reported as
    its own row "Hyperliquid:<dex>" since equity/withdrawable are dex-scoped."""
    label = "Hyperliquid" if not dex else f"Hyperliquid:{dex}"
    prefix = f"{dex}:" if dex else ""

    ch_payload = {"type": "clearinghouseState", "user": HL_USER}
    if dex:
        ch_payload["dex"] = dex
    state = _hl_post(session, ch_payload, timeout, retries, backoff_s)

    meta_payload = {"type": "metaAndAssetCtxs"}
    if dex:
        meta_payload["dex"] = dex
    meta_resp = _hl_post(session, meta_payload, timeout, retries, backoff_s)

    universe = meta_resp[0]["universe"]
    ctxs = meta_resp[1]
    mark_prices = {asset["name"]: float(ctx["markPx"]) for asset, ctx in zip(universe, ctxs)}

    positions = []
    for ap in state.get("assetPositions", []):
        pos = ap.get("position", {})
        if float(pos.get("szi", "0")) == 0:
            continue
        positions.append(pos)

    try:
        funding_by_coin, funding_24h_by_coin, funding_mtd_by_coin, funding_ytd_by_coin = _hl_funding_by_coin(
            session, dex, FUNDING_FETCH_START_MS, _now_ms(), timeout, retries, backoff_s
        )
    except Exception as exc:
        print(f"  [Hyperliquid funding warning] dex={dex or '(main)'}: {exc}")
        funding_by_coin = None
        funding_24h_by_coin = None
        funding_mtd_by_coin = None
        funding_ytd_by_coin = None

    long_delta = short_delta = 0.0
    position_rows = []
    isolated_removables = []
    cross_position_inputs = []

    for pos in positions:
        coin = pos["coin"]
        szi = float(pos["szi"])
        direction = "LONG" if szi > 0 else "SHORT"
        mark_px = mark_prices.get(coin) or 0.0
        signed_notional = szi * mark_px
        if signed_notional > 0:
            long_delta += signed_notional
        else:
            short_delta += signed_notional

        liq_px_str = pos.get("liquidationPx")
        liq_px = float(liq_px_str) if liq_px_str else None
        dist_pct = abs((mark_px - liq_px) / mark_px) * 100 if (liq_px and mark_px) else None

        lev = pos.get("leverage", {}) or {}
        is_isolated = lev.get("type") == "isolated"
        margin_mode = lev.get("type", "unknown")

        iso_rem = None
        if is_isolated and liq_px and mark_px:
            iso_rem = _removable_isolated_position(direction, szi, mark_px, liq_px)
            isolated_removables.append((coin, iso_rem))
        elif (not is_isolated) and liq_px and mark_px:
            cross_position_inputs.append({"name": coin, "size": szi, "mark": mark_px, "liq": liq_px})

        position_rows.append({
            "exchange": label, "symbol": f"{prefix}{coin}", "direction": direction,
            "size": abs(szi), "notional": signed_notional, "mark": mark_px,
            "liq": liq_px, "dist_pct": dist_pct, "margin_mode": margin_mode,
            "isolated_removable": iso_rem,
            "funding_collected": funding_by_coin.get(coin, 0.0) if funding_by_coin is not None else None,
            "funding_24h": funding_24h_by_coin.get(coin, 0.0) if funding_24h_by_coin is not None else None,
            "funding_mtd": funding_mtd_by_coin.get(coin, 0.0) if funding_mtd_by_coin is not None else None,
            "funding_ytd": funding_ytd_by_coin.get(coin, 0.0) if funding_ytd_by_coin is not None else None,
        })

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)
    margin = state.get("marginSummary", {})
    try:
        account_equity = float(margin.get("accountValue") or 0)
    except (TypeError, ValueError):
        account_equity = 0.0
    try:
        withdrawable = float(state.get("withdrawable") or 0)
    except (TypeError, ValueError):
        withdrawable = 0.0
    hl_leverage = gross_notional / account_equity if account_equity > 0 else 0.0

    measurable = [r for r in position_rows if r["dist_pct"] is not None]
    if not positions:
        excess = True
    elif not measurable:
        excess = False
    else:
        excess = min(r["dist_pct"] for r in measurable) > LIQ_DISTANCE_THRESHOLD_PCT

    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    cross_cap = _removable_cross_binding(cross_position_inputs, account_equity)
    pos_constrained = iso_sum + cross_cap
    # withdrawable=0 means truly can't pull anything out; always apply the cap.
    removable_total = max(0.0, min(pos_constrained, withdrawable))

    return {
        "exchange": label, "currency": "USDC", "positions_count": len(positions),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": hl_leverage,
        "account_equity": account_equity, "withdrawable": withdrawable,
        "excess_collateral": excess, "removable_total": removable_total, "mgn_ratio": None,
        # Full per-symbol MTD/YTD funding for this dex, across every coin that
        # had funding activity in the window -- NOT limited to currently open
        # positions. Used for the top-level Funding Totals figure and the
        # Past Strategies table (closed/rolled-off legs still show up here).
        "funding_mtd_by_symbol": {f"{prefix}{c}": v for c, v in (funding_mtd_by_coin or {}).items()},
        "funding_ytd_by_symbol": {f"{prefix}{c}": v for c, v in (funding_ytd_by_coin or {}).items()},
        # raw components for the unified-mode combiner (stripped before sheet write)
        "_iso_removables": isolated_removables,
        "_cross_inputs": cross_position_inputs,
        "_upl": sum(
            float((ap.get("position") or {}).get("unrealizedPnl") or 0)
            for ap in state.get("assetPositions", []) or []
        ),
    }


def _get_hl_unified(session, per_dex: list, timeout: int, retries: int, backoff_s: float) -> dict:
    """Combine per-dex results into one unified-account row. In unified mode a
    single USDC balance backs spot plus all cross perps on every dex, so equity,
    leverage, withdrawable, and removable are computed against the unified
    balance, not the per-dex margin allocations. Isolated positions (e.g.
    xyz:CL) keep their own ring-fenced margin and are unaffected by the mode."""
    spot = _hl_post(session, {"type": "spotClearinghouseState", "user": HL_USER},
                    timeout, retries, backoff_s)
    usdc_total = 0.0
    usdc_hold = 0.0
    for b in spot.get("balances", []) or []:
        if b.get("coin") == "USDC":
            try:
                usdc_total += float(b.get("total") or 0)
                usdc_hold += float(b.get("hold") or 0)
            except (TypeError, ValueError):
                pass

    position_rows = []
    isolated_removables = []
    cross_inputs = []
    long_delta = short_delta = 0.0
    total_upl = 0.0
    funding_mtd_by_symbol: dict = {}
    funding_ytd_by_symbol: dict = {}
    for r in per_dex:
        for row in r["position_rows"]:
            row = dict(row)
            row["exchange"] = "Hyperliquid"   # one account row in unified mode
            position_rows.append(row)
        isolated_removables += r.get("_iso_removables", [])
        cross_inputs += r.get("_cross_inputs", [])
        long_delta += r["long_delta"]
        short_delta += r["short_delta"]
        total_upl += r.get("_upl", 0.0)
        for k, v in r.get("funding_mtd_by_symbol", {}).items():
            funding_mtd_by_symbol[k] = funding_mtd_by_symbol.get(k, 0.0) + v
        for k, v in r.get("funding_ytd_by_symbol", {}).items():
            funding_ytd_by_symbol[k] = funding_ytd_by_symbol.get(k, 0.0) + v

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)

    # Unified equity = unified USDC balance + mark-to-market on open perps.
    # (The spot USDC total is the settled unified balance; uPnL sits on top.)
    account_equity = usdc_total + total_upl
    # Exchange-level pullable cash: unified balance not held by spot orders and
    # not allocated as margin. The UI "Available Balance" analog.
    withdrawable = max(0.0, usdc_total - usdc_hold)
    hl_leverage = gross_notional / account_equity if account_equity > 0 else 0.0

    measurable = [r for r in position_rows if r["dist_pct"] is not None]
    if not position_rows:
        excess = True
    elif not measurable:
        excess = False
    else:
        excess = min(r["dist_pct"] for r in measurable) > LIQ_DISTANCE_THRESHOLD_PCT

    # Removable: how much can be pulled from the unified account while keeping
    # every cross position at >= TARGET_LIQ_DISTANCE_PCT, evaluated against the
    # unified equity (all cross positions on all dexs share it). Isolated
    # release amounts are additive since freeing isolated margin returns it to
    # the unified balance.
    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    cross_cap = _removable_cross_binding(cross_inputs, account_equity)
    removable_total = max(0.0, min(iso_sum + cross_cap, withdrawable + iso_sum))

    return {
        "exchange": "Hyperliquid", "currency": "USDC", "positions_count": len(position_rows),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": hl_leverage,
        "account_equity": account_equity, "withdrawable": withdrawable,
        "excess_collateral": excess, "removable_total": removable_total, "mgn_ratio": None,
        "funding_mtd_by_symbol": funding_mtd_by_symbol,
        "funding_ytd_by_symbol": funding_ytd_by_symbol,
    }


def get_hl_positions():
    """Standard mode: one result dict per dex (independent margining).
    Unified mode (HL_UNIFIED): one combined dict computed against the unified
    USDC balance."""
    timeout, retries, backoff_s = 20, 5, 0.4
    session = requests.Session()
    session.headers.update({"Content-Type": "application/json"})

    per_dex = []
    for dex in HL_DEXS:
        try:
            r = _get_hl_dex_positions(session, dex, timeout, retries, backoff_s)
        except Exception as exc:
            _log(f"  [Hyperliquid dex={dex or '(main)'} ERROR] {type(exc).__name__}: {exc}")
            continue
        if dex == "" or r["positions_count"] > 0:
            per_dex.append(r)

    if HL_UNIFIED:
        try:
            return [_get_hl_unified(session, per_dex, timeout, retries, backoff_s)]
        except Exception as exc:
            _log(f"  [Hyperliquid unified ERROR] {type(exc).__name__}: {exc}; "
                 "falling back to per-dex rows")

    # strip private fields before returning per-dex rows
    for r in per_dex:
        for k in ("_iso_removables", "_cross_inputs", "_upl"):
            r.pop(k, None)
    return per_dex


def get_binance_positions():
    base_url = "https://fapi.binance.com"
    timeout = 10

    def _signed_get(path: str) -> Union[list, dict]:
        params = {"timestamp": int(time.time() * 1000), "recvWindow": 5000}
        qs = urlencode(params)
        params["signature"] = hmac.new(
            BINANCE_SECRET.encode("utf-8"), qs.encode("utf-8"), digestmod=hashlib.sha256
        ).hexdigest()
        headers = {"X-MBX-APIKEY": BINANCE_KEY}
        r = requests.get(base_url + path, params=params, headers=headers, timeout=timeout)
        r.raise_for_status()
        return r.json()

    all_positions = _signed_get("/fapi/v2/positionRisk")
    positions = [p for p in all_positions if float(p.get("positionAmt", "0")) != 0]

    try:
        funding_by_symbol, funding_24h_by_symbol, funding_mtd_by_symbol, funding_ytd_by_symbol = (
            _binance_funding_by_symbol(FUNDING_FETCH_START_MS, _now_ms())
        )
    except Exception as exc:
        print(f"  [Binance funding warning] {exc}")
        funding_by_symbol = None
        funding_24h_by_symbol = None
        funding_mtd_by_symbol = None
        funding_ytd_by_symbol = None

    long_delta = short_delta = 0.0
    position_rows = []
    isolated_removables = []
    cross_position_inputs = []

    for p in positions:
        symbol = p["symbol"]
        amt = float(p["positionAmt"])
        direction = "LONG" if amt > 0 else "SHORT"
        mark = float(p["markPrice"])
        notional = float(p.get("notional") or amt * mark)
        liq_px = float(p["liquidationPrice"])
        margin_type = (p.get("marginType") or "").lower()
        is_isolated = margin_type == "isolated"

        if notional > 0:
            long_delta += notional
        else:
            short_delta += notional

        liq_out = liq_px if liq_px != 0 else None
        dist_pct = abs((mark - liq_px) / mark) * 100 if (liq_out and mark != 0) else None

        iso_rem = None
        if is_isolated and liq_out and mark != 0:
            iso_rem = _removable_isolated_position(direction, amt, mark, liq_out)
            isolated_removables.append((symbol, iso_rem))
        elif (not is_isolated) and liq_out and mark != 0:
            cross_position_inputs.append({"name": symbol, "size": amt, "mark": mark, "liq": liq_out})

        position_rows.append({
            "exchange": "Binance", "symbol": symbol, "direction": direction,
            "size": abs(amt), "notional": notional, "mark": mark, "liq": liq_out,
            "dist_pct": dist_pct, "margin_mode": margin_type or "unknown",
            "isolated_removable": iso_rem,
            "funding_collected": funding_by_symbol.get(symbol, 0.0) if funding_by_symbol is not None else None,
            "funding_24h": funding_24h_by_symbol.get(symbol, 0.0) if funding_24h_by_symbol is not None else None,
            "funding_mtd": funding_mtd_by_symbol.get(symbol, 0.0) if funding_mtd_by_symbol is not None else None,
            "funding_ytd": funding_ytd_by_symbol.get(symbol, 0.0) if funding_ytd_by_symbol is not None else None,
        })

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)
    acct = _signed_get("/fapi/v2/account")
    try:
        account_equity = float(acct.get("totalMarginBalance") or 0)
    except (TypeError, ValueError):
        account_equity = 0.0
    try:
        withdrawable = float(acct.get("availableBalance") or 0)
    except (TypeError, ValueError):
        withdrawable = 0.0
    try:
        maint_margin = float(acct.get("totalMaintMargin") or 0)
    except (TypeError, ValueError):
        maint_margin = 0.0

    # Account-level margin ratio: marginBalance / maintMargin.
    # Mirrors OKX mgnRatio. Liquidation at 1.0x. Used as a fallback for cross
    # positions where Binance returns liquidationPrice=0 (large cushion case).
    bn_mgn_ratio = account_equity / maint_margin if maint_margin > 0 else float("inf")

    bn_leverage = gross_notional / account_equity if account_equity > 0 else 0.0

    # Count cross positions without a per-position liq price. For these,
    # account-level mgnRatio is the only safety signal we have.
    cross_no_liq_count = sum(
        1 for r in position_rows
        if r["dist_pct"] is None and r["margin_mode"] != "isolated"
    )

    # Hybrid excess: per-position dist OK AND account-level mgnRatio OK.
    measurable = [r for r in position_rows if r["dist_pct"] is not None]
    if not positions:
        excess = True
    else:
        if measurable:
            per_pos_ok = min(r["dist_pct"] for r in measurable) > LIQ_DISTANCE_THRESHOLD_PCT
        else:
            per_pos_ok = True
        if cross_no_liq_count > 0:
            account_ok = bn_mgn_ratio > BN_MGN_RATIO_FLOOR
        else:
            account_ok = True
        excess = per_pos_ok and account_ok

    # Removable: isolated sum + cross binding cap + (if cross-without-liq
    # positions exist) account-level cap from mgnRatio target.
    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    cross_cap = _removable_cross_binding(cross_position_inputs, account_equity)

    if cross_no_liq_count > 0:
        if bn_mgn_ratio > BN_MGN_RATIO_TARGET:
            account_cap = max(0.0, account_equity - maint_margin * BN_MGN_RATIO_TARGET)
        else:
            account_cap = 0.0
        pos_constrained = iso_sum + cross_cap + account_cap
    else:
        pos_constrained = iso_sum + cross_cap

    removable_total = max(0.0, min(pos_constrained, withdrawable))

    return {
        "exchange": "Binance", "currency": "USDT", "positions_count": len(positions),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": bn_leverage,
        "account_equity": account_equity, "withdrawable": withdrawable,
        "excess_collateral": excess, "removable_total": removable_total,
        "mgn_ratio": bn_mgn_ratio if bn_mgn_ratio != float("inf") else None,
        # Full per-symbol MTD/YTD funding across every symbol traded, not just
        # currently open positions -- see note on the HL result above.
        "funding_mtd_by_symbol": funding_mtd_by_symbol or {},
        "funding_ytd_by_symbol": funding_ytd_by_symbol or {},
    }


def _bybit_signed_get(path, params, timeout_s=10):
    recv_window = str(BYBIT_RECV_WINDOW)
    timestamp = str(int(time.time() * 1000))
    query_string = urlencode(params)
    pre_sign = timestamp + BYBIT_API_KEY + recv_window + query_string
    signature = hmac.new(
        BYBIT_API_SECRET.encode("utf-8"), pre_sign.encode("utf-8"), hashlib.sha256
    ).hexdigest()
    headers = {
        "X-BAPI-API-KEY": BYBIT_API_KEY, "X-BAPI-TIMESTAMP": timestamp,
        "X-BAPI-SIGN": signature, "X-BAPI-RECV-WINDOW": recv_window,
        "Content-Type": "application/json",
    }
    resp = requests.get(f"{BYBIT_BASE_URL}{path}", params=params, headers=headers, timeout=timeout_s)
    resp.raise_for_status()
    data = resp.json()
    if data.get("retCode") != 0:
        raise RuntimeError(f"Bybit error {data.get('retCode')}: {data.get('retMsg')} (path={path})")
    return data


def _bybit_txlog_pages(acct_type: str, params_base: dict, timeout_s: int = 10):
    """Yield transaction-log rows for one account type, following the cursor."""
    cursor = None
    guard = 0
    while guard < 1000:
        guard += 1
        params = dict(params_base)
        if cursor:
            params["cursor"] = cursor
        data = _bybit_signed_get("/v5/account/transaction-log", params, timeout_s=timeout_s)
        result = data.get("result", {})
        rows = result.get("list", []) or []
        for r in rows:
            yield r
        cursor = result.get("nextPageCursor")
        if not cursor or not rows:
            break


def _bybit_funding_mtd_ytd(timeout_s: int = 10) -> tuple:
    """Sum Bybit SETTLEMENT funding per symbol for the MTD and YTD windows via
    the transaction log, chunked into 7-day windows (the endpoint caps query
    range at 7 days). This is a real per-event ledger sum, kept separate from
    the curRealisedPnl proxy used for the "Total Funding" per-position field
    elsewhere, since curRealisedPnl has no timestamp/window breakdown."""
    totals_mtd: dict = {}
    totals_ytd: dict = {}
    end_ms = _now_ms()
    for acct_type in ("UNIFIED", "CONTRACT"):
        got_any = False
        for c_start, c_end in _chunks(YTD_START_MS, end_ms, 7 * 86_400_000):
            base = {
                "accountType": acct_type, "category": "linear", "type": "SETTLEMENT",
                "startTime": str(c_start), "endTime": str(c_end), "limit": "50",
            }
            try:
                for r in _bybit_txlog_pages(acct_type, base, timeout_s=timeout_s):
                    got_any = True
                    sym = r.get("symbol")
                    if not sym:
                        continue
                    try:
                        f = float(r.get("funding") or 0)
                        ts = int(r.get("transactionTime") or 0)
                    except (TypeError, ValueError):
                        continue
                    if ts >= YTD_START_MS:
                        totals_ytd[sym] = totals_ytd.get(sym, 0.0) + f
                    if ts >= MTD_START_MS:
                        totals_mtd[sym] = totals_mtd.get(sym, 0.0) + f
            except RuntimeError as exc:
                print(f"  [Bybit funding MTD/YTD warning] {acct_type}: {exc}")
                break
        if got_any:
            break
    return totals_mtd, totals_ytd


def _bybit_fetch_wallet(timeout=10):
    for acct_type in ("UNIFIED", "CONTRACT"):
        try:
            wd = _bybit_signed_get("/v5/account/wallet-balance", {"accountType": acct_type}, timeout_s=timeout)
        except RuntimeError:
            continue
        wallet_list = wd.get("result", {}).get("list", []) or []
        if wallet_list:
            entry = wallet_list[0]
            entry["_accountType"] = acct_type
            return entry
    return {}


def get_bybit_positions():
    timeout = 10
    positions = []
    for settle in ("USDT", "USDC"):
        params: Dict[str, Any] = {"category": "linear", "settleCoin": settle, "limit": "200"}
        cursor = None
        while True:
            if cursor:
                params["cursor"] = cursor
            else:
                params.pop("cursor", None)
            data = _bybit_signed_get("/v5/position/list", params, timeout_s=timeout)
            result = data.get("result", {})
            for p in result.get("list", []) or []:
                if float(p.get("size", "0")) != 0:
                    p["_settleCoin"] = settle
                    positions.append(p)
            cursor = result.get("nextPageCursor")
            if not cursor:
                break

    try:
        funding_mtd_by_symbol, funding_ytd_by_symbol = _bybit_funding_mtd_ytd()
    except Exception as exc:
        print(f"  [Bybit funding MTD/YTD warning] {exc}")
        funding_mtd_by_symbol = None
        funding_ytd_by_symbol = None

    long_delta = short_delta = 0.0
    position_rows = []
    isolated_removables = []
    cross_position_inputs = []

    for p in positions:
        symbol = p["symbol"]
        side = p.get("side", "")
        size = float(p.get("size", "0"))
        mark = float(p.get("markPrice", "0") or 0)
        pos_value = float(p.get("positionValue", "0") or 0)
        liq_px_str = p.get("liqPrice", "") or ""
        direction = "LONG" if side == "Buy" else "SHORT"
        signed_notional = pos_value if side == "Buy" else -pos_value
        signed_size = size if side == "Buy" else -size

        if signed_notional > 0:
            long_delta += signed_notional
        else:
            short_delta += signed_notional

        try:
            is_isolated = int(p.get("tradeMode", 0)) == 1
        except (TypeError, ValueError):
            is_isolated = False
        margin_mode = "isolated" if is_isolated else "cross"

        if liq_px_str and liq_px_str not in ("", "0") and mark != 0:
            liq_px = float(liq_px_str)
            dist_pct = abs((mark - liq_px) / mark) * 100
        else:
            liq_px = None
            dist_pct = None

        iso_rem = None
        if is_isolated and liq_px and mark != 0:
            iso_rem = _removable_isolated_position(direction, signed_size, mark, liq_px)
            isolated_removables.append((symbol, iso_rem))
        elif (not is_isolated) and liq_px and mark != 0:
            cross_position_inputs.append({"name": symbol, "size": signed_size, "mark": mark, "liq": liq_px})

        # NOTE: Bybit position objects expose curRealisedPnl (cumulative realized
        # PnL for the current position: funding + closed PnL + fees), not isolated
        # funding. Unlike the other venues this is a proxy, not pure funding.
        try:
            cur_rpnl = float(p.get("curRealisedPnl") or 0)
        except (TypeError, ValueError):
            cur_rpnl = None

        position_rows.append({
            "exchange": "Bybit", "symbol": symbol, "direction": direction,
            "size": size, "notional": signed_notional, "mark": mark, "liq": liq_px,
            "dist_pct": dist_pct, "margin_mode": margin_mode, "isolated_removable": iso_rem,
            "funding_collected": cur_rpnl,
            "funding_24h": None,  # curRealisedPnl proxy has no 24h breakdown
            "funding_mtd": funding_mtd_by_symbol.get(symbol, 0.0) if funding_mtd_by_symbol is not None else None,
            "funding_ytd": funding_ytd_by_symbol.get(symbol, 0.0) if funding_ytd_by_symbol is not None else None,
        })

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)
    acct = _bybit_fetch_wallet(timeout=timeout)
    try:
        account_equity = float(acct.get("totalEquity") or 0)
    except (TypeError, ValueError):
        account_equity = 0.0
    try:
        withdrawable = float(acct.get("totalAvailableBalance") or 0)
    except (TypeError, ValueError):
        withdrawable = 0.0
    bb_leverage = gross_notional / account_equity if account_equity > 0 else 0.0

    measurable = [r for r in position_rows if r["dist_pct"] is not None]
    if not positions:
        excess = True
    elif not measurable:
        excess = False
    else:
        excess = min(r["dist_pct"] for r in measurable) > LIQ_DISTANCE_THRESHOLD_PCT

    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    cross_cap = _removable_cross_binding(cross_position_inputs, account_equity)
    pos_constrained = iso_sum + cross_cap
    # withdrawable=0 means truly nothing to pull out; always apply the cap.
    removable_total = max(0.0, min(pos_constrained, withdrawable))

    return {
        "exchange": "Bybit", "currency": "USD", "positions_count": len(positions),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": bb_leverage,
        "account_equity": account_equity, "withdrawable": withdrawable,
        "excess_collateral": excess, "removable_total": removable_total, "mgn_ratio": None,
        "funding_mtd_by_symbol": funding_mtd_by_symbol or {},
        "funding_ytd_by_symbol": funding_ytd_by_symbol or {},
    }


def _okx_timestamp() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")


def _okx_signed_get(path, params=None, timeout_s=20):
    params = params or {}
    query = urlencode(params)
    request_path = f"{path}?{query}" if query else path
    timestamp = _okx_timestamp()
    prehash = f"{timestamp}GET{request_path}"
    sign = base64.b64encode(
        hmac.new(OKX_API_SECRET.encode("utf-8"), prehash.encode("utf-8"), hashlib.sha256).digest()
    ).decode("utf-8")
    headers = {
        "OK-ACCESS-KEY": OKX_API_KEY, "OK-ACCESS-SIGN": sign,
        "OK-ACCESS-TIMESTAMP": timestamp, "OK-ACCESS-PASSPHRASE": OKX_PASSPHRASE,
        "Content-Type": "application/json",
    }
    r = requests.get(f"{OKX_BASE_URL}{request_path}", headers=headers, timeout=timeout_s)
    try:
        data = r.json()
    except ValueError:
        r.raise_for_status()
        raise RuntimeError(f"OKX non-JSON response: {r.text}")
    if r.status_code != 200:
        raise RuntimeError(f"OKX HTTP error ({r.status_code}): {data}")
    if isinstance(data, dict) and data.get("code") not in (None, "0"):
        raise RuntimeError(f"OKX API error: {data}")
    return data


def get_okx_positions():
    timeout = 20
    pos_resp = _okx_signed_get("/api/v5/account/positions", params={}, timeout_s=timeout)
    raw_positions = pos_resp.get("data", []) or []
    positions = [p for p in raw_positions if float(p.get("pos", "0") or 0) != 0]

    try:
        funding_by_inst, funding_24h_by_inst, funding_mtd_by_inst, funding_ytd_by_inst = (
            _okx_funding_by_inst(FUNDING_FETCH_START_MS, _now_ms(), timeout)
        )
    except Exception as exc:
        print(f"  [OKX funding warning] {exc}")
        funding_by_inst = None
        funding_24h_by_inst = None
        funding_mtd_by_inst = None
        funding_ytd_by_inst = None

    long_delta = short_delta = 0.0
    position_rows = []
    isolated_removables = []
    cross_pos_count = 0

    for p in positions:
        inst_id = p.get("instId", "")
        pos_qty = float(p.get("pos", "0") or 0)
        pos_side = (p.get("posSide", "") or "").lower()
        if pos_side == "long":
            direction, signed_size = "LONG", abs(pos_qty)
        elif pos_side == "short":
            direction, signed_size = "SHORT", -abs(pos_qty)
        else:
            direction = "LONG" if pos_qty > 0 else "SHORT"
            signed_size = pos_qty

        mark = float(p.get("markPx", "0") or 0)
        notional_abs = float(p.get("notionalUsd", "0") or 0)
        signed_notional = notional_abs if direction == "LONG" else -notional_abs
        liq_px_str = p.get("liqPx", "") or ""
        mgn_mode = (p.get("mgnMode", "") or "").lower()
        is_isolated = mgn_mode == "isolated"

        if signed_notional > 0:
            long_delta += signed_notional
        else:
            short_delta += signed_notional

        if is_isolated and liq_px_str and liq_px_str not in ("", "0") and mark != 0:
            liq_px = float(liq_px_str)
            dist_pct = abs((mark - liq_px) / mark) * 100
            iso_rem = _removable_isolated_position(direction, signed_size, mark, liq_px)
            isolated_removables.append((inst_id, iso_rem))
        else:
            cross_pos_count += 1
            liq_px = None
            dist_pct = None
            iso_rem = None

        position_rows.append({
            "exchange": "OKX", "symbol": inst_id, "direction": direction,
            "size": abs(pos_qty), "notional": signed_notional, "mark": mark,
            "liq": liq_px, "dist_pct": dist_pct, "margin_mode": mgn_mode or "unknown",
            "isolated_removable": iso_rem,
            "funding_collected": funding_by_inst.get(inst_id, 0.0) if funding_by_inst is not None else None,
            "funding_24h": funding_24h_by_inst.get(inst_id, 0.0) if funding_24h_by_inst is not None else None,
            "funding_mtd": funding_mtd_by_inst.get(inst_id, 0.0) if funding_mtd_by_inst is not None else None,
            "funding_ytd": funding_ytd_by_inst.get(inst_id, 0.0) if funding_ytd_by_inst is not None else None,
        })

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)
    acct_resp = _okx_signed_get("/api/v5/account/balance", params={}, timeout_s=timeout)
    acct_data = acct_resp.get("data", []) or []
    acct = acct_data[0] if acct_data else {}

    def _f(v):
        try:
            return float(v) if v is not None else 0.0
        except (TypeError, ValueError):
            return 0.0

    total_eq = _f(acct.get("totalEq"))
    adj_eq = _f(acct.get("adjEq"))
    avail_eq = _f(acct.get("availEq"))
    mmr = _f(acct.get("mmr"))
    mgn_ratio = _f(acct.get("mgnRatio"))
    okx_leverage = gross_notional / total_eq if total_eq > 0 else 0.0

    iso_rows = [r for r in position_rows if r["dist_pct"] is not None]
    if not positions:
        excess = True
    else:
        iso_ok = all(r["dist_pct"] > LIQ_DISTANCE_THRESHOLD_PCT for r in iso_rows) if iso_rows else True
        cross_ok = (cross_pos_count == 0) or (mgn_ratio > OKX_MGN_RATIO_FLOOR)
        excess = iso_ok and cross_ok

    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    if cross_pos_count > 0 and mgn_ratio > OKX_MGN_RATIO_TARGET:
        cross_removable = max(0.0, adj_eq - mmr * OKX_MGN_RATIO_TARGET)
    else:
        cross_removable = 0.0
    # availEq is the free/withdrawable portion; adjEq is total adjusted equity.
    # cross_removable above is correctly equity-based, but the final cap must be
    # what is actually free to pull.
    wd_cap = avail_eq if avail_eq > 0 else float("inf")
    removable_total = max(0.0, min(iso_sum + cross_removable, wd_cap))

    return {
        "exchange": "OKX", "currency": "USD", "positions_count": len(positions),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": okx_leverage,
        "account_equity": total_eq, "withdrawable": avail_eq,
        "excess_collateral": excess, "removable_total": removable_total, "mgn_ratio": mgn_ratio,
        "funding_mtd_by_symbol": funding_mtd_by_inst or {},
        "funding_ytd_by_symbol": funding_ytd_by_inst or {},
    }


def get_lighter_positions():
    """Lighter is a zk-rollup orderbook perp DEX. Account/position data is
    public (GET /api/v1/account?by=index&value=<account index>), so unlike
    the other venues this needs no API key or request signing -- just an
    account index.

    Field mapping mirrors OKX's cross-margin model: cross_asset_value is
    mark-to-market equity, available_balance is withdrawable, and
    cross_maintenance_margin_requirement plays the role of OKX's mmr, so the
    same floor/target margin-ratio framing is reused here.

    NOTE ON FUNDING: the public account endpoint only exposes lifetime-
    cumulative funding per position (total_funding_paid_out). Windowed or
    24h funding requires a signed auth token (the positionFunding endpoint),
    which needs the Lighter SDK's signer and is out of scope for a read-only
    monitor. So funding_collected below is lifetime, NOT clipped to
    STRATEGY_START_DATES like the other venues, and funding_24h/funding_mtd/
    funding_ytd are always None -- see the "Strategy note" row in the sheet.
    """
    if not LIGHTER_ACCOUNT_INDEX:
        _log("  Lighter: LIGHTER_ACCOUNT_INDEX not set, skipping.")
        return []

    timeout = 15

    def _f(v):
        try:
            return float(v) if v is not None else 0.0
        except (TypeError, ValueError):
            return 0.0

    resp = requests.get(
        f"{LIGHTER_BASE_URL}/api/v1/account",
        params={"by": "index", "value": LIGHTER_ACCOUNT_INDEX, "active_only": "true"},
        timeout=timeout,
    )
    resp.raise_for_status()
    data = resp.json()
    accounts = data.get("accounts") or []
    acct = accounts[0] if accounts else {}

    raw_positions = [p for p in (acct.get("positions") or []) if _f(p.get("position")) != 0]

    long_delta = short_delta = 0.0
    position_rows = []
    isolated_removables = []
    cross_position_inputs = []

    for p in raw_positions:
        symbol = p.get("symbol", "")
        sign_val = 1 if int(p.get("sign", 1) or 1) >= 0 else -1
        direction = "LONG" if sign_val > 0 else "SHORT"
        size = abs(_f(p.get("position")))
        pos_value = abs(_f(p.get("position_value")))
        mark = pos_value / size if size > 0 else 0.0
        signed_notional = sign_val * pos_value

        if signed_notional > 0:
            long_delta += signed_notional
        else:
            short_delta += signed_notional

        liq_str = p.get("liquidation_price")
        liq_px = _f(liq_str) if liq_str not in (None, "") else 0.0
        liq_px = liq_px if liq_px > 0 else None
        dist_pct = abs((mark - liq_px) / mark) * 100 if (liq_px and mark) else None

        is_isolated = int(p.get("margin_mode", 0) or 0) == 1
        margin_mode = "isolated" if is_isolated else "cross"
        signed_size = sign_val * size

        iso_rem = None
        if is_isolated and liq_px and mark:
            iso_rem = _removable_isolated_position(direction, signed_size, mark, liq_px)
            isolated_removables.append((symbol, iso_rem))
        elif (not is_isolated) and liq_px and mark:
            cross_position_inputs.append({"name": symbol, "size": signed_size, "mark": mark, "liq": liq_px})

        funding_life = p.get("total_funding_paid_out")
        position_rows.append({
            "exchange": "Lighter", "symbol": symbol, "direction": direction,
            "size": size, "notional": signed_notional, "mark": mark, "liq": liq_px,
            "dist_pct": dist_pct, "margin_mode": margin_mode, "isolated_removable": iso_rem,
            "funding_collected": _f(funding_life) if funding_life is not None else None,
            "funding_24h": None,  # lifetime-cumulative only; see docstring
            "funding_mtd": None,  # not available without the SDK signer; see docstring
            "funding_ytd": None,  # not available without the SDK signer; see docstring
        })

    net_delta = long_delta + short_delta
    gross_notional = long_delta + abs(short_delta)
    account_equity = _f(acct.get("cross_asset_value"))
    withdrawable = _f(acct.get("available_balance"))
    mmr = _f(acct.get("cross_maintenance_margin_requirement"))
    mgn_ratio = account_equity / mmr if mmr > 0 else float("inf")
    leverage = gross_notional / account_equity if account_equity > 0 else 0.0

    # Count cross positions without a per-position liq price (edge case; Lighter
    # normally reports one even for cross). Account-level mgnRatio is the
    # fallback safety signal for these, mirroring the Binance/OKX pattern.
    cross_no_liq_count = sum(
        1 for r in position_rows if r["dist_pct"] is None and r["margin_mode"] != "isolated"
    )

    measurable = [r for r in position_rows if r["dist_pct"] is not None]
    if not raw_positions:
        excess = True
    else:
        per_pos_ok = min(r["dist_pct"] for r in measurable) > LIQ_DISTANCE_THRESHOLD_PCT if measurable else True
        account_ok = (mgn_ratio > LIGHTER_MGN_RATIO_FLOOR) if cross_no_liq_count > 0 else True
        excess = per_pos_ok and account_ok

    iso_sum = sum(max(amt, 0.0) for _, amt in isolated_removables)
    cross_cap = _removable_cross_binding(cross_position_inputs, account_equity)
    if cross_no_liq_count > 0 and mgn_ratio > LIGHTER_MGN_RATIO_TARGET:
        account_cap = max(0.0, account_equity - mmr * LIGHTER_MGN_RATIO_TARGET)
    else:
        account_cap = 0.0
    pos_constrained = iso_sum + cross_cap + account_cap
    removable_total = max(0.0, min(pos_constrained, withdrawable))

    return [{
        "exchange": "Lighter", "currency": "USDC", "positions_count": len(raw_positions),
        "position_rows": position_rows, "long_delta": long_delta, "short_delta": short_delta,
        "net_delta": net_delta, "gross_notional": gross_notional, "leverage": leverage,
        "account_equity": account_equity, "withdrawable": withdrawable,
        "excess_collateral": excess, "removable_total": removable_total,
        "mgn_ratio": mgn_ratio if mgn_ratio != float("inf") else None,
        # Lighter's public API has no windowed funding (lifetime-cumulative
        # only), so it can't contribute to MTD/YTD totals or Past Strategies.
        "funding_mtd_by_symbol": {},
        "funding_ytd_by_symbol": {},
    }]


# ============================================================
#  GOOGLE SHEETS WRITER
# ============================================================
def _get_or_create_tab(spreadsheet, title: str):
    try:
        return spreadsheet.worksheet(title)
    except gspread.WorksheetNotFound:
        return spreadsheet.add_worksheet(title=title, rows=200, cols=20)


def _fmt_num(v, decimals=2):
    if v is None:
        return ""
    try:
        return round(float(v), decimals)
    except (TypeError, ValueError):
        return v


def _strategy_key(symbol: str) -> str:
    """Normalize a venue symbol to its base asset so legs of the same funding-arb
    strategy group together. Examples:
      VVVUSDT -> VVV, XMRUSDT -> XMR, VVV -> VVV,
      xyz:xyz:CL -> CL, CL-USDT-SWAP -> CL,
      xyz:xyz:BRENTOIL -> BRENT (alias), BZUSDT -> BZ -> BRENT (alias).

    Some venues label the same underlying strategy with different tickers
    (e.g. HL's BRENTOIL vs Binance's BZUSDT). After normalizing venue prefixes
    and quote suffixes, STRATEGY_ALIASES maps such raw keys onto one canonical
    key so both legs land in the same Strategy PnL row."""
    s = symbol or ""
    if ":" in s:           # HL builder/dex prefixes: keep the trailing coin
        s = s.split(":")[-1]
    if "-" in s:           # OKX BASE-QUOTE-SWAP
        s = s.split("-")[0]
    for q in ("USDT", "USDC", "USD"):   # Binance BASEUSDT style
        if s.endswith(q) and len(s) > len(q):
            s = s[: -len(q)]
            break
    return STRATEGY_ALIASES.get(s, s)


def write_to_sheet(results: list) -> None:
    creds = Credentials.from_service_account_file(GOOGLE_CREDS_FILE, scopes=GSHEET_SCOPES)
    gc = gspread.authorize(creds)
    sh = gc.open(SHEET_NAME)
    ws = _get_or_create_tab(sh, TAB_RISK)
    ws.clear()

    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

    rows = []
    rows.append(["Risk monitor snapshot", ts])
    rows.append([])
    rows.append(["Per-Exchange Summary"])
    rows.append([
        "Exchange", "Positions", "Excess Collat",
        "Removable", "Currency", "Leverage",
        "Gross Notional", "Net Delta",
        "Account Equity", "Withdrawable / adjEq", "Account mgnRatio",
    ])
    for r in results:
        rows.append([
            r["exchange"], r["positions_count"],
            "YES" if r["excess_collateral"] else "NO",
            _fmt_num(r["removable_total"]), r["currency"],
            _fmt_num(r["leverage"], 4), _fmt_num(r["gross_notional"]),
            _fmt_num(r["net_delta"]), _fmt_num(r["account_equity"]),
            _fmt_num(r["withdrawable"]),
            _fmt_num(r["mgn_ratio"], 4) if r["mgn_ratio"] is not None else "",
        ])

    rows.append([])
    rows.append(["Per-Position Detail"])
    rows.append([
        "Exchange", "Symbol", "Direction",
        "Size", "Notional (signed)", "Mark", "Liq Price",
        "Dist to Liq %", "Margin Mode", "Isolated Removable",
        "Funding Collected", "Type",
    ])
    all_positions = []
    hidden_count = 0
    for r in results:
        for p in r["position_rows"]:
            try:
                small = abs(float(p["notional"])) < MIN_POSITION_USD
            except (TypeError, ValueError):
                small = False
            if small:
                hidden_count += 1
                continue
            all_positions.append(p)

    def _sort_key(p):
        dist = p["dist_pct"]
        return (p["exchange"], 0 if dist is not None else 1, dist if dist is not None else 0)

    # A funding-arb strategy has two legs (long one venue, short another). A base
    # ticker that appears as only a single leg in the (dust-filtered) book is an
    # unhedged single-sided position, i.e. cash and carry. Tag those rows.
    legs_per_strategy: dict = {}
    for p in all_positions:
        legs_per_strategy.setdefault(_strategy_key(p["symbol"]), 0)
        legs_per_strategy[_strategy_key(p["symbol"])] += 1
    single_leg_keys = {k for k, n in legs_per_strategy.items() if n == 1}

    for p in sorted(all_positions, key=_sort_key):
        pos_type = "Cash and carry" if _strategy_key(p["symbol"]) in single_leg_keys else ""
        rows.append([
            p["exchange"], p["symbol"], p["direction"],
            _fmt_num(p["size"], 6), _fmt_num(p["notional"]),
            _fmt_num(p["mark"], 6),
            _fmt_num(p["liq"], 6) if p["liq"] is not None else "",
            _fmt_num(p["dist_pct"], 2) if p["dist_pct"] is not None else "",
            p["margin_mode"] + (" (see mgnRatio)" if p["dist_pct"] is None and p["margin_mode"] == "cross" else ""),
            _fmt_num(p["isolated_removable"]) if p["isolated_removable"] is not None else "",
            _fmt_num(p.get("funding_collected")) if p.get("funding_collected") is not None else "",
            pos_type,
        ])

    # ---- Funding Totals: top-level MTD/YTD figures across every symbol that
    # had funding activity in the window, at any account -- including symbols
    # with no currently open position (closed/rolled-off strategies). This is
    # deliberately NOT broken out per strategy; it's a single combined number
    # per window, matching how it should read on the dashboard's top line. ----
    grand_mtd_total = sum(sum((r.get("funding_mtd_by_symbol") or {}).values()) for r in results)
    grand_ytd_total = sum(sum((r.get("funding_ytd_by_symbol") or {}).values()) for r in results)

    rows.append([])
    rows.append(["Funding Totals (MTD/YTD, all accounts, all positions ever traded)"])
    rows.append(["Metric", "Value"])
    rows.append(["Total Funding Collected MTD", _fmt_num(grand_mtd_total)])
    rows.append(["Total Funding Collected YTD", _fmt_num(grand_ytd_total)])

    # ---- Active Strategies: group currently-open legs by base asset, sum
    # funding since each strategy's hardcoded start date, normalize ----
    rows.append([])
    rows.append(["Active Strategies (currently open positions)"])
    rows.append([
        "Strategy", "Legs (venue:dir)", "Total Funding", "24 Hr Funding",
        "Avg Leg Size", "Funding / Notional (%)", "Start Date", "Funding Annualized (%)",
    ])

    strat: dict = {}
    for p in all_positions:
        key = _strategy_key(p["symbol"])
        g = strat.setdefault(key, {"legs": [], "funding": 0.0, "has_funding": False,
                                   "funding_24h": 0.0, "has_funding_24h": False,
                                   "abs_sizes": [], "abs_notionals": []})
        g["legs"].append(f"{p['exchange']}:{p['direction'][:1]}")
        fc = p.get("funding_collected")
        if fc is not None:
            g["funding"] += fc
            g["has_funding"] = True
        f24 = p.get("funding_24h")
        if f24 is not None:
            g["funding_24h"] += f24
            g["has_funding_24h"] = True
        try:
            g["abs_sizes"].append(abs(float(p["size"])))
        except (TypeError, ValueError):
            pass
        try:
            g["abs_notionals"].append(abs(float(p["notional"])))
        except (TypeError, ValueError):
            pass

    for key in sorted(strat):
        g = strat[key]
        # "position size" of a delta-neutral pair = the matched per-leg size,
        # estimated by the average of the absolute leg sizes.
        avg_size = sum(g["abs_sizes"]) / len(g["abs_sizes"]) if g["abs_sizes"] else 0.0
        avg_notional = sum(g["abs_notionals"]) / len(g["abs_notionals"]) if g["abs_notionals"] else 0.0
        f_per_notional_pct = (g["funding"] / avg_notional * 100) if avg_notional > 0 else None

        # Annualize using the hardcoded strategy start date.
        start_str = STRATEGY_START_DATES.get(key)
        ann_pct = None
        if start_str and f_per_notional_pct is not None:
            try:
                start_dt = datetime.strptime(start_str, "%Y-%m-%d").replace(tzinfo=timezone.utc)
                days = (datetime.now(timezone.utc) - start_dt).total_seconds() / 86400.0
                if days > 0:
                    ann_pct = f_per_notional_pct * (365.0 / days)
            except ValueError:
                pass

        rows.append([
            key, ", ".join(g["legs"]),
            _fmt_num(g["funding"]) if g["has_funding"] else "",
            _fmt_num(g["funding_24h"]) if g["has_funding_24h"] else "",
            _fmt_num(avg_size, 6),
            _fmt_num(f_per_notional_pct, 4) if (f_per_notional_pct is not None and g["has_funding"]) else "",
            start_str or "",
            _fmt_num(ann_pct, 2) if (ann_pct is not None and g["has_funding"]) else "",
        ])

    # ---- Past Strategies: symbols with MTD/YTD funding activity but no
    # currently open position at that venue (closed or rolled-off legs).
    # Grouped by base asset like Active Strategies, but funding-only -- there
    # is no live size/notional to normalize against, so no annualization. ----
    closed_strat: dict = {}
    for r in results:
        open_syms = {p["symbol"] for p in r["position_rows"]}
        mtd_dict = r.get("funding_mtd_by_symbol") or {}
        ytd_dict = r.get("funding_ytd_by_symbol") or {}
        for sym in set(mtd_dict) | set(ytd_dict):
            if sym in open_syms:
                continue
            fmtd = mtd_dict.get(sym, 0.0)
            fytd = ytd_dict.get(sym, 0.0)
            if fmtd == 0.0 and fytd == 0.0:
                continue
            key = _strategy_key(sym)
            entry = closed_strat.setdefault(key, {"venues": set(), "funding_mtd": 0.0, "funding_ytd": 0.0})
            entry["venues"].add(r["exchange"])
            entry["funding_mtd"] += fmtd
            entry["funding_ytd"] += fytd

    rows.append([])
    rows.append(["Past Strategies (funding activity, no currently open position)"])
    rows.append(["Strategy", "Venues", "Funding MTD", "Funding YTD"])
    for key in sorted(closed_strat, key=lambda k: -abs(closed_strat[k]["funding_ytd"])):
        entry = closed_strat[key]
        rows.append([
            key, ", ".join(sorted(entry["venues"])),
            _fmt_num(entry["funding_mtd"]), _fmt_num(entry["funding_ytd"]),
        ])

    rows.append([])
    rows.append(["Thresholds"])
    rows.append(["Liq distance threshold", f">{LIQ_DISTANCE_THRESHOLD_PCT:.0f}%"])
    rows.append(["Removable target buffer", f">{TARGET_LIQ_DISTANCE_PCT:.0f}%"])
    rows.append(["OKX mgnRatio floor", f"{OKX_MGN_RATIO_FLOOR:.2f}x  (liquidates at 1.00x, OKX warns at 3.00x)"])
    rows.append(["OKX mgnRatio target", f"{OKX_MGN_RATIO_TARGET:.2f}x"])
    rows.append(["Binance mgnRatio floor", f"{BN_MGN_RATIO_FLOOR:.2f}x  (for cross positions without per-position liq prices)"])
    rows.append(["Binance mgnRatio target", f"{BN_MGN_RATIO_TARGET:.2f}x"])
    _fund_since = datetime.fromtimestamp(FUNDING_START_MS / 1000, tz=timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    rows.append(["Funding window", f"fixed global start {_fund_since}; mapped strategies clipped to their STRATEGY_START_DATES entry"])
    if MIN_POSITION_USD > 0:
        rows.append(["Small balance filter", f"positions under ${MIN_POSITION_USD:,.0f} notional hidden ({hidden_count} hidden this run); still included in risk math"])
    rows.append(["Strategy note",
        "Funding Totals MTD/YTD = funding events since the start of the current calendar "
        "month/year (UTC), summed across every symbol traded at any account -- including "
        "symbols with no currently open position. This is a single top-level figure, not "
        "broken out per strategy. Active Strategies' Total Funding is cumulative funding "
        "since each strategy's hardcoded start date (STRATEGY_START_DATES); Funding/Notional "
        "(%) and Funding Annualized (%) are derived from that figure, not from MTD/YTD, so "
        "they stay meaningful for strategies that didn't start this month or year. 24 Hr "
        "Funding = funding events in the trailing 24h; Bybit and Lighter legs are excluded "
        "from that column (no time breakdown available there). Past Strategies lists symbols "
        "with MTD/YTD funding activity but no currently open position (closed or rolled-off "
        "legs), so the top-level Funding Totals figure reconciles against Active Strategies' "
        "24h/since-start numbers plus Past Strategies' MTD/YTD numbers. Bybit's MTD/YTD "
        "figures (in both Funding Totals and Past Strategies) come from its transaction log "
        "(a real per-event ledger sum), separate from and not necessarily matching the "
        "curRealisedPnl proxy used for Active Strategies. Lighter has no windowed funding "
        "available from its public API (lifetime-cumulative only), so it never contributes "
        "to Funding Totals or Past Strategies."])

    max_cols = max(len(row) for row in rows) if rows else 1
    rows = [row + [""] * (max_cols - len(row)) for row in rows]

    ws.update(values=rows, range_name="A1")
    _log(f"Wrote {len(rows)} rows to '{TAB_RISK}' tab in '{SHEET_NAME}'.")


# ============================================================
#  MAIN
# ============================================================
def main() -> int:
    results = []
    failures = []

    fetchers = [
        ("Hyperliquid", get_hl_positions),
        ("Binance", get_binance_positions),
        ("Bybit", get_bybit_positions),
        ("OKX", get_okx_positions),
        ("Lighter", get_lighter_positions),
    ]

    for name, fn in fetchers:
        _log(f"Fetching {name}...")
        try:
            r = fn()
            batch = r if isinstance(r, list) else [r]
            if not batch:
                _log(f"  {name}: no account rows returned.")
            for item in batch:
                results.append(item)
                _log("  " + _summary_line(item))
        except Exception as exc:
            failures.append((name, exc))
            _log(f"  [{name} ERROR] {type(exc).__name__}: {exc}")

    if not results:
        _log("All exchange fetches failed; nothing to write. Exiting with code 2.")
        return 2

    _log("Writing to Google Sheet...")
    try:
        write_to_sheet(results)
    except Exception as exc:
        _log(f"[SHEET WRITE ERROR] {type(exc).__name__}: {exc}")
        return 1

    if failures:
        _log(
            f"Snapshot written, but {len(failures)} exchange fetch(es) failed: "
            f"{', '.join(name for name, _ in failures)}. "
            "Sheet reflects only successful exchanges."
        )

    _log("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
