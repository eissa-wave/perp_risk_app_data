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

# Funding: collected funding is summed per symbol from FUNDING_START_MS to now.
# This is funding accrued on currently-open positions over the lookback window,
# not strictly "since this position opened". Override with an absolute ms epoch
# via env (FUNDING_START_MS); default is a 90-day lookback.
FUNDING_START_MS = int(
    os.environ.get("FUNDING_START_MS", str(int((time.time() - 90 * 86400) * 1000)))
)

# ============================================================
#  STRATEGY START DATES (hardcoded, by base ticker)
# ============================================================
# Trade entry date per funding-arb strategy, keyed by the normalized base
# ticker (the same key the Strategy PnL section groups on, e.g. "VVV", "XMR",
# "CL"). Used to annualize collected funding: ann% = (funding / avg notional)
# * (365 / days since start) * 100. Strategies missing from this map show a
# blank annualized column. Update when entering/rolling a new strategy.
STRATEGY_START_DATES = {
    # "TICKER": "YYYY-MM-DD",
    "VVV": "2026-06-10",
    "CL": "2026-06-10",
    "MU": "2026-06-11",
    "TRUMP": "2026-06-16",
    "ZEC": "2026-06-19",

}

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
#  FUNDING (collected funding per symbol over the lookback window)
# ============================================================
def _now_ms() -> int:
    return int(time.time() * 1000)


def _hl_funding_by_coin(session, dex: str, start_ms: int, end_ms: int,
                        timeout: int, retries: int, backoff_s: float) -> dict:
    """Sum HL funding (delta.usdc, positive = received) per coin for one dex,
    paginating via the last event time. Keyed by raw coin name."""
    totals: dict = {}
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
            delta = ev.get("delta") or {}
            coin = delta.get("coin")
            usdc = delta.get("usdc")
            if coin is not None and usdc is not None:
                totals[coin] = totals.get(coin, 0.0) + float(usdc)
        if len(data) < 500:
            break
        last_time = data[-1].get("time")
        if last_time is None:
            break
        cur = int(last_time) + 1
        if cur > end_ms:
            break
    return totals


def _binance_funding_by_symbol(start_ms: int, end_ms: int) -> dict:
    """Sum Binance FUNDING_FEE income (negative = paid) per symbol across all
    symbols, paginating via the last event time."""
    base_url = "https://fapi.binance.com"
    path = "/fapi/v1/income"
    limit = 1000
    totals: dict = {}
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
            if x.get("incomeType") == "FUNDING_FEE":
                sym = x.get("symbol")
                totals[sym] = totals.get(sym, 0.0) + float(x.get("income") or 0)
        if len(batch) < limit:
            break
        last_time = max(int(x["time"]) for x in batch)
        current_start = last_time + 1
        time.sleep(0.2)
    return totals


def _okx_funding_by_inst(start_ms: int, end_ms: int, timeout: int) -> dict:
    """Sum OKX funding-fee bills (type=8, amount in `pnl`, negative = paid) per
    instId. Queries both the 7-day and archive endpoints and dedups by billId."""
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
    for r in all_rows:
        bid = r.get("billId")
        if bid in seen:
            continue
        seen.add(bid)
        inst = r.get("instId")
        totals[inst] = totals.get(inst, 0.0) + float(r.get("pnl") or 0)
    return totals


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
        funding_by_coin = _hl_funding_by_coin(
            session, dex, FUNDING_START_MS, _now_ms(), timeout, retries, backoff_s
        )
    except Exception as exc:
        print(f"  [Hyperliquid funding warning] dex={dex or '(main)'}: {exc}")
        funding_by_coin = None

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
        funding_by_symbol = _binance_funding_by_symbol(FUNDING_START_MS, _now_ms())
    except Exception as exc:
        print(f"  [Binance funding warning] {exc}")
        funding_by_symbol = None

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
        funding_by_inst = _okx_funding_by_inst(FUNDING_START_MS, _now_ms(), timeout)
    except Exception as exc:
        print(f"  [OKX funding warning] {exc}")
        funding_by_inst = None

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
    }


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
      xyz:xyz:CL -> CL, CL-USDT-SWAP -> CL."""
    s = symbol or ""
    if ":" in s:           # HL builder/dex prefixes: keep the trailing coin
        s = s.split(":")[-1]
    if "-" in s:           # OKX BASE-QUOTE-SWAP
        s = s.split("-")[0]
    for q in ("USDT", "USDC", "USD"):   # Binance BASEUSDT style
        if s.endswith(q) and len(s) > len(q):
            return s[: -len(q)]
    return s


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

    # ---- Strategy PnL: group legs by base asset, sum funding, normalize ----
    rows.append([])
    rows.append(["Strategy PnL (funding arb)"])
    rows.append([
        "Strategy", "Legs (venue:dir)", "Total Funding",
        "Avg Leg Size", "Funding / Notional (%)", "Start Date", "Funding Annualized (%)",
    ])

    strat: dict = {}
    for p in all_positions:
        key = _strategy_key(p["symbol"])
        g = strat.setdefault(key, {"legs": [], "funding": 0.0, "has_funding": False,
                                   "abs_sizes": [], "abs_notionals": []})
        g["legs"].append(f"{p['exchange']}:{p['direction'][:1]}")
        fc = p.get("funding_collected")
        if fc is not None:
            g["funding"] += fc
            g["has_funding"] = True
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
            _fmt_num(avg_size, 6),
            _fmt_num(f_per_notional_pct, 4) if (f_per_notional_pct is not None and g["has_funding"]) else "",
            start_str or "",
            _fmt_num(ann_pct, 2) if (ann_pct is not None and g["has_funding"]) else "",
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
    rows.append(["Funding window", f"collected since {_fund_since}"])
    if MIN_POSITION_USD > 0:
        rows.append(["Small balance filter", f"positions under ${MIN_POSITION_USD:,.0f} notional hidden ({hidden_count} hidden this run); still included in risk math"])
    rows.append(["Strategy note", "Funding/Notional (%) = total funding / avg abs leg notional. Annualized = that % * 365/days since hardcoded start date (STRATEGY_START_DATES). Funding window must cover the start date or the annualized figure understates."])

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
