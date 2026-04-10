"""
Kalshi Options Flow Bot
Monitor unusual options activity on stocks with Kalshi markets as a leading indicator.
Uses Yahoo Finance options chains (free, no API key needed).
"""

import asyncio
import os
from flask import Flask, jsonify
import threading
import json
import time
import uuid
import logging
import hashlib
import hmac
import base64
import re
from datetime import datetime, timezone, timedelta
from dataclasses import dataclass, field
from typing import Optional
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import padding
import httpx
from dotenv import load_dotenv

load_dotenv()

# ── Quant Fund Shadow Evaluators ─────────────────────────────────────────
try:
    from bayesian_updater import BayesianUpdater
    from ensemble_model import EnsembleModel
    from time_decay_edge import calculate_time_weighted_edge
    from correlation_matrix import CorrelationTracker
    from vpin_toxicity import VPINTracker
    from market_impact import estimate_market_impact
    from feature_engine import FeatureEngine
    from portfolio_optimizer import PortfolioOptimizer
    _quant_modules_available = True
    _bayesian = BayesianUpdater()
    _ensemble = EnsembleModel()
    _correlation = CorrelationTracker()
    _vpin = VPINTracker()
    _features = FeatureEngine()
    _portfolio = PortfolioOptimizer()
except ImportError:
    _quant_modules_available = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("options_flow")

from risk_guard import RiskManager
risk_manager = RiskManager()

# ── Shadow Logging ────────────────────────────────────────────────────────────
SHADOW_LOG_FILE = os.getenv("SHADOW_LOG_FILE", "shadow_log.jsonl")

def shadow_log(opportunity: dict, taken: bool, reason: str = ""):
    entry = {"ts": time.time(), "taken": taken, "reason": reason, **opportunity}
    try:
        with open(SHADOW_LOG_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except:
        pass




# ── Virtual Portfolio Testing ─────────────────────────────────────────────
VIRTUAL_PORTFOLIO_FILE = os.getenv("VIRTUAL_PORTFOLIO_FILE", "virtual_portfolios.jsonl")

VIRTUAL_PORTFOLIOS = [
    {"name": "aggressive", "kelly": 1.0, "min_edge": 0.02, "early_exit": 0.99},
    {"name": "moderate", "kelly": 0.5, "min_edge": 0.05, "early_exit": 0.93},
    {"name": "conservative", "kelly": 0.25, "min_edge": 0.08, "early_exit": 0.90},
    {"name": "original_v1", "kelly": 1.0, "min_edge": 0.03, "early_exit": 0.99},
    {"name": "high_edge", "kelly": 0.5, "min_edge": 0.10, "early_exit": 0.93},
    {"name": "ultra_conservative", "kelly": 0.25, "min_edge": 0.12, "early_exit": 0.90},
]

def evaluate_virtual_portfolios(opportunity: dict):
    """Evaluate what each virtual portfolio would do with this opportunity."""
    import json, time as _time
    edge = opportunity.get("edge", 0)
    price = opportunity.get("price", 0)
    results = []
    for vp in VIRTUAL_PORTFOLIOS:
        would_trade = edge >= vp["min_edge"]
        would_exit_early = price >= vp["early_exit"] * 100
        results.append({
            "portfolio": vp["name"],
            "would_trade": would_trade,
            "would_exit_early": would_exit_early,
            "kelly": vp["kelly"],
            "min_edge": vp["min_edge"],
        })
    entry = {
        "ts": _time.time(),
        "opportunity": opportunity,
        "portfolios": results,
    }
    try:
        with open(VIRTUAL_PORTFOLIO_FILE, "a") as f:
            f.write(json.dumps(entry) + "\n")
    except:
        pass

# ─── Regime Detection — pause trading during extreme volatility ────────────
import statistics as _stats

REGIME_WINDOW = int(os.getenv("REGIME_WINDOW", "20"))
REGIME_THRESHOLD = float(os.getenv("REGIME_THRESHOLD", "3.0"))
_regime_prices: list[float] = []

def check_regime(price: float) -> str:
    """Returns 'CALM', 'ELEVATED', or 'CRASH'. Skip trades during CRASH."""
    _regime_prices.append(price)
    if len(_regime_prices) > REGIME_WINDOW:
        _regime_prices.pop(0)
    if len(_regime_prices) < 5:
        return "CALM"
    rets = [(b - a) / a for a, b in zip(_regime_prices[:-1], _regime_prices[1:])]
    if not rets:
        return "CALM"
    mu = _stats.mean(rets)
    sd = _stats.stdev(rets) if len(rets) > 1 else 0.01
    z = abs(rets[-1] - mu) / max(sd, 0.0001)
    if z > REGIME_THRESHOLD:
        return "CRASH"
    elif z > REGIME_THRESHOLD * 0.6:
        return "ELEVATED"
    return "CALM"



# ── Early Exit Logic ─────────────────────────────────────────────────────────
EARLY_EXIT_THRESHOLD = float(os.getenv("EARLY_EXIT_THRESHOLD", "0.93"))

def should_early_exit(current_price_cents: float) -> bool:
    """Exit position early at 93c+ to lock in profit instead of holding to settlement."""
    return current_price_cents >= EARLY_EXIT_THRESHOLD * 100

# ── Circuit Breakers ─────────────────────────────────────────────────────────
CONSECUTIVE_LOSS_PAUSE = int(os.getenv("CONSECUTIVE_LOSS_PAUSE", "3"))
DAILY_DRAWDOWN_PAUSE_PCT = float(os.getenv("DAILY_DRAWDOWN_PAUSE_PCT", "0.05"))

_consecutive_losses = 0
_daily_pnl = 0.0
_circuit_paused_until = 0

def check_circuit_breaker() -> bool:
    """Returns True if trading should be paused."""
    import time as _time
    global _consecutive_losses, _daily_pnl, _circuit_paused_until
    if _time.time() < _circuit_paused_until:
        return True
    if _consecutive_losses >= CONSECUTIVE_LOSS_PAUSE:
        return True
    # Use PAPER_BALANCE if available, else 5000
    _balance = globals().get("PAPER_BALANCE", 2000)
    if _daily_pnl < -DAILY_DRAWDOWN_PAUSE_PCT * _balance:
        return True
    return False

def record_trade_result(won: bool, pnl: float):
    """Update circuit breaker state after each trade result."""
    global _consecutive_losses, _daily_pnl
    _daily_pnl += pnl
    if won:
        _consecutive_losses = 0
    else:
        _consecutive_losses += 1
def _normalize_market(m: dict) -> dict:
    """Normalize Kalshi API v2 dollar-denominated fields to legacy field names."""
    if "yes_bid_dollars" in m and "yes_bid" not in m:
        m["yes_bid"] = m.get("yes_bid_dollars")
        m["yes_ask"] = m.get("yes_ask_dollars")
        m["no_bid"] = m.get("no_bid_dollars")
        m["no_ask"] = m.get("no_ask_dollars")
        m["last_price"] = m.get("last_price_dollars")
        m["volume"] = m.get("volume_fp") or m.get("volume_24h_fp") or m.get("volume", 0)
        m["open_interest"] = m.get("open_interest_fp") or m.get("open_interest", 0)
    for k in ["yes_bid", "yes_ask", "no_bid", "no_ask", "last_price"]:
        v = m.get(k)
        if isinstance(v, str):
            try: m[k] = float(v)
            except: pass
    return m


# ── CONFIG ──────────────────────────────────────────────────────────────────
KALSHI_BASE       = os.getenv("KALSHI_BASE", "https://api.elections.kalshi.com")
KALSHI_API_URL    = os.getenv("KALSHI_API_URL", f"{KALSHI_BASE}/trade-api/v2")
KALSHI_API_KEY    = os.getenv("KALSHI_API_KEY", "")
KALSHI_KEY_ID     = os.getenv("KALSHI_KEY_ID", "")
PAPER_MODE        = os.getenv("PAPER_MODE", "true").lower() == "true"
PAPER_BALANCE     = float(os.getenv("PAPER_BALANCE", "2000"))
BET_SIZE_USD      = float(os.getenv("BET_SIZE_USD", "12"))
MAX_BET_USD       = float(os.getenv("MAX_BET_USD", "30"))
KELLY_FRACTION    = float(os.getenv("KELLY_FRACTION", "0.25"))
MIN_EDGE          = float(os.getenv("MIN_EDGE", "0.05"))      # 3% minimum edge
MAKER_FEE         = float(os.getenv("MAKER_FEE", "0.0175"))
VOLUME_RATIO_MIN  = float(os.getenv("VOLUME_RATIO_MIN", "1.5"))  # 1.5x normal volume = unusual
POLL_INTERVAL_SEC = int(os.getenv("POLL_INTERVAL_SEC", "300"))   # 5 min

# Tracked tickers → Kalshi series mapping
# Maps Yahoo Finance ticker → Kalshi market series prefix
TICKER_SERIES = {
    "NVDA": ["KXNVDA", "KXNVDAS"],
    "AAPL": ["KXAAPL", "KXAAPLS"],
    "MSFT": ["KXMSFT", "KXMSFTS"],
    "TSLA": ["KXTSLA", "KXTSLAP"],
    "META": ["KXMETA", "KXMETAS"],
    "AMZN": ["KXAMZN", "KXAMZNS"],
    "GOOGL": ["KXGOOGL", "KXGOOGLS"],
    "AMD":  ["KXAMD", "KXAMDS"],
    "SPY":  ["KXSPY", "KXSPYX", "KXSPYS"],
    "QQQ":  ["KXQQQ", "KXQQQX"],
}

# ── AUTH ────────────────────────────────────────────────────────────────────
def _load_private_key():
    pem_str = os.getenv("KALSHI_PRIVATE_KEY", "")
    if not pem_str:
        return None
    if "\\n" in pem_str:
        pem_str = pem_str.replace("\\n", "\n")
    return serialization.load_pem_private_key(pem_str.encode(), password=None)

_PRIVATE_KEY = _load_private_key()

def _sign_request(method: str, path: str, ts: int, body: str = "") -> str:
    if not _PRIVATE_KEY:
        return ""
    try:
        msg = f"{ts}{method.upper()}{path}{body}".encode()
        sig = _PRIVATE_KEY.sign(msg, padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32), hashes.SHA256())
        return base64.b64encode(sig).decode()
    except Exception:
        return ""

def _auth_headers(method: str, path: str, body: str = "") -> dict:
    ts = int(time.time() * 1000)
    sig = _sign_request(method, path, ts, body)
    return {
        "Content-Type": "application/json",
        "KALSHI-ACCESS-KEY": KALSHI_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": str(ts),
        "KALSHI-ACCESS-SIGNATURE": sig,
    }

# ── PAPER LEDGER ─────────────────────────────────────────────────────────────
@dataclass
class PaperLedger:
    balance: float = PAPER_BALANCE
    trades: list = field(default_factory=list)
    wins: int = 0
    losses: int = 0

    def record(self, market: str, side: str, contracts: int, price_cents: int, signal: str):
        cost = contracts * price_cents / 100
        self.balance -= cost
        self.trades.append({
            "ts": datetime.now(timezone.utc).isoformat(),
            "market": market,
            "side": side,
            "contracts": contracts,
            "price_cents": price_cents,
            "cost": cost,
            "signal": signal,
        })
        log.info(f"[PAPER] {side} {contracts}ct @ {price_cents}¢ on {market} | {signal} | balance=${self.balance:.2f}")

    def settle(self, market: str, won: bool):
        for t in self.trades:
            if t["market"] == market and "settled" not in t:
                t["settled"] = won
                if won:
                    self.balance += t["contracts"] * 1.00  # $1 per contract
                    self.wins += 1
                else:
                    self.losses += 1
        total = self.wins + self.losses
        wr = self.wins / total * 100 if total else 0
        log.info(f"[PAPER] Settled {market} {'WIN' if won else 'LOSS'} | W/L={self.wins}/{self.losses} ({wr:.0f}%) | balance=${self.balance:.2f}")

# ── OPTIONS DATA ─────────────────────────────────────────────────────────────
@dataclass
class OptionsSignal:
    ticker: str
    direction: str       # "bullish" or "bearish"
    confidence: float    # 0-1
    details: str
    current_price: float

async def get_yahoo_options(client: httpx.AsyncClient, ticker: str) -> Optional[dict]:
    """
    Fetch options chain data, trying multiple free sources.
    Falls back to stock quote + volume-based estimation if options APIs are blocked.
    """
    headers = {
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Accept": "application/json",
    }

    # Strategy 1: Yahoo v7 options endpoint (query2 — sometimes works without auth)
    for base in ["https://query2.finance.yahoo.com", "https://query1.finance.yahoo.com"]:
        url = f"{base}/v7/finance/options/{ticker}"
        try:
            r = await client.get(url, headers=headers, timeout=15)
            if r.status_code == 200:
                data = r.json()
                if data.get("optionChain", {}).get("result"):
                    log.debug(f"Yahoo options OK for {ticker} via {base}")
                    return data
            elif r.status_code not in (401, 403):
                log.debug(f"Yahoo options {ticker} via {base}: HTTP {r.status_code}")
        except Exception as e:
            log.debug(f"Yahoo options {base} error {ticker}: {e}")

    # Strategy 2: CBOE delayed options data
    try:
        cboe_url = f"https://cdn.cboe.com/api/global/delayed_quotes/options/{ticker}.json"
        r = await client.get(cboe_url, headers=headers, timeout=15)
        if r.status_code == 200:
            cboe_data = r.json()
            options_list = cboe_data.get("data", {}).get("options", [])
            if options_list:
                log.info(f"Using CBOE delayed data for {ticker} ({len(options_list)} contracts)")
                return _convert_cboe_to_yahoo_format(cboe_data, ticker)
    except Exception as e:
        log.debug(f"CBOE options error {ticker}: {e}")

    # Strategy 3: Fall back to stock quote for price/volume-based signal estimation
    log.info(f"No options data available for {ticker}, falling back to stock quote estimation")
    return await _get_stock_quote_fallback(client, ticker, headers)


def _convert_cboe_to_yahoo_format(cboe_data: dict, ticker: str) -> Optional[dict]:
    """Convert CBOE delayed options JSON to Yahoo-compatible format."""
    try:
        options = cboe_data.get("data", {}).get("options", [])
        current_price = cboe_data.get("data", {}).get("close", 0)

        calls = []
        puts = []
        for opt in options:
            opt_type = opt.get("option_type", "").upper()
            entry = {
                "strike": opt.get("strike", 0),
                "volume": opt.get("volume", 0) or 0,
                "openInterest": opt.get("open_interest", 0) or 0,
                "lastPrice": opt.get("last_sale_price", 0),
                "bid": opt.get("bid", 0),
                "ask": opt.get("ask", 0),
            }
            if opt_type == "C":
                calls.append(entry)
            elif opt_type == "P":
                puts.append(entry)

        return {
            "optionChain": {
                "result": [{
                    "quote": {"regularMarketPrice": current_price},
                    "options": [{"calls": calls, "puts": puts}],
                }]
            }
        }
    except Exception as e:
        log.warning(f"CBOE conversion error: {e}")
        return None


async def _get_stock_quote_fallback(client: httpx.AsyncClient, ticker: str, headers: dict) -> Optional[dict]:
    """
    Fetch stock quote from Yahoo (still works) and synthesize a minimal options-like
    signal from price action and volume patterns.
    """
    try:
        url = f"https://query2.finance.yahoo.com/v8/finance/chart/{ticker}?interval=5m&range=1d"
        r = await client.get(url, headers=headers, timeout=15)
        if r.status_code != 200:
            # Try alternate endpoint
            url = f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker}?interval=5m&range=1d"
            r = await client.get(url, headers=headers, timeout=15)
        if r.status_code != 200:
            log.warning(f"Stock quote fallback also failed for {ticker}: HTTP {r.status_code}")
            return None

        chart = r.json().get("chart", {}).get("result", [])
        if not chart:
            return None

        meta = chart[0].get("meta", {})
        current_price = meta.get("regularMarketPrice", 0)
        prev_close = meta.get("chartPreviousClose") or meta.get("previousClose", 0)

        indicators = chart[0].get("indicators", {}).get("quote", [{}])[0]
        volumes = [v for v in (indicators.get("volume") or []) if v is not None]
        closes = [c for c in (indicators.get("close") or []) if c is not None]

        if not current_price or not volumes or len(volumes) < 4:
            return None

        # Estimate directional flow from intraday price/volume patterns
        avg_vol = sum(volumes) / len(volumes)
        recent_vol = sum(volumes[-3:]) / 3 if len(volumes) >= 3 else avg_vol
        vol_ratio = recent_vol / avg_vol if avg_vol > 0 else 1.0

        price_change_pct = ((current_price - prev_close) / prev_close * 100) if prev_close else 0

        # Synthesize fake "options" signal based on volume surge + price direction
        # High volume + up = simulates bullish call flow
        # High volume + down = simulates bearish put flow
        synthetic_call_vol = int(recent_vol * max(1.0, 1.0 + price_change_pct * 0.1))
        synthetic_put_vol = int(recent_vol * max(1.0, 1.0 - price_change_pct * 0.1))

        # Only produce a signal if there's notable volume AND directional move
        if vol_ratio < 1.3 or abs(price_change_pct) < 0.3:
            return None

        calls = [{"strike": current_price * 1.02, "volume": synthetic_call_vol,
                   "openInterest": int(synthetic_call_vol * 0.5)}]
        puts = [{"strike": current_price * 0.98, "volume": synthetic_put_vol,
                  "openInterest": int(synthetic_put_vol * 0.5)}]

        log.info(f"[FALLBACK] {ticker} price=${current_price:.2f} chg={price_change_pct:+.2f}% "
                 f"vol_ratio={vol_ratio:.1f}x → synthetic calls={synthetic_call_vol} puts={synthetic_put_vol}")

        return {
            "optionChain": {
                "result": [{
                    "quote": {"regularMarketPrice": current_price},
                    "options": [{"calls": calls, "puts": puts}],
                }]
            }
        }

    except Exception as e:
        log.warning(f"Stock quote fallback error {ticker}: {e}")
        return None

def analyze_options_flow(data: dict, ticker: str) -> Optional[OptionsSignal]:
    """
    Analyze options chain for unusual activity.
    Returns bullish signal if calls dominate, bearish if puts dominate.
    """
    try:
        result = data.get("optionChain", {}).get("result", [])
        if not result:
            return None

        chain = result[0]
        quote = chain.get("quote", {})
        current_price = quote.get("regularMarketPrice", 0)
        if not current_price:
            return None

        options = chain.get("options", [])
        if not options:
            return None

        opt = options[0]
        calls = opt.get("calls", [])
        puts = opt.get("puts", [])

        if not calls and not puts:
            return None

        # Calculate metrics
        call_vol = sum(c.get("volume", 0) or 0 for c in calls)
        put_vol  = sum(p.get("volume", 0) or 0 for p in puts)
        call_oi  = sum(c.get("openInterest", 0) or 0 for c in calls)
        put_oi   = sum(p.get("openInterest", 0) or 0 for p in puts)

        total_vol = call_vol + put_vol
        if total_vol < 100:  # Too little data
            return None

        # Put/Call ratio
        pcr = put_vol / call_vol if call_vol > 0 else 999

        # Find unusual single contracts (volume >> OI or very large volume)
        unusual_calls = [c for c in calls
                        if (c.get("volume", 0) or 0) > 100
                        and (c.get("openInterest", 0) or 0) > 0
                        and (c.get("volume", 0) or 0) / max(c.get("openInterest", 0) or 1, 1) > 0.2]
        unusual_puts  = [p for p in puts
                        if (p.get("volume", 0) or 0) > 100
                        and (p.get("openInterest", 0) or 0) > 0
                        and (p.get("volume", 0) or 0) / max(p.get("openInterest", 0) or 1, 1) > 0.2]

        unusual_call_vol = sum(c.get("volume", 0) or 0 for c in unusual_calls)
        unusual_put_vol  = sum(p.get("volume", 0) or 0 for p in unusual_puts)

        # Determine signal
        # Bullish: low PCR (<0.7) or dominant unusual calls
        # Bearish: high PCR (>1.3) or dominant unusual puts
        direction = None
        confidence = 0.0

        if pcr < 0.8 or (unusual_call_vol > unusual_put_vol * 1.5 and unusual_call_vol > 200):
            direction = "bullish"
            confidence = min(0.55 + max(0, 0.8 - pcr) * 0.3, 0.82)
            details = f"PCR={pcr:.2f}, unusual_calls={unusual_call_vol:,}, calls_vol={call_vol:,}"

        elif pcr > 1.2 or (unusual_put_vol > unusual_call_vol * 1.5 and unusual_put_vol > 200):
            direction = "bearish"
            confidence = min(0.55 + max(0, pcr - 1.2) * 0.15, 0.80)
            details = f"PCR={pcr:.2f}, unusual_puts={unusual_put_vol:,}, puts_vol={put_vol:,}"

        elif unusual_call_vol > 500 and unusual_call_vol > unusual_put_vol * 2:
            direction = "bullish"
            confidence = 0.62
            details = f"Big unusual calls={unusual_call_vol:,} vs puts={unusual_put_vol:,}"

        elif unusual_put_vol > 500 and unusual_put_vol > unusual_call_vol * 2:
            direction = "bearish"
            confidence = 0.60
            details = f"Big unusual puts={unusual_put_vol:,} vs calls={unusual_call_vol:,}"

        if not direction:
            return None

        log.info(f"[SIGNAL] {ticker} {direction.upper()} conf={confidence:.2f} | {details} | price=${current_price:.2f}")
        return OptionsSignal(
            ticker=ticker,
            direction=direction,
            confidence=confidence,
            details=details,
            current_price=current_price,
        )

    except Exception as e:
        log.warning(f"Options analysis error {ticker}: {e}")
        return None

# ── KALSHI MARKET ────────────────────────────────────────────────────────────
async def get_kalshi_markets(client: httpx.AsyncClient, series_ticker: str) -> list:
    """Fetch open Kalshi markets for a given series."""
    path = f"/markets?series_ticker={series_ticker}&status=open&limit=20"
    headers = _auth_headers("GET", path) if KALSHI_KEY_ID else {"Content-Type": "application/json"}
    try:
        r = await client.get(f"{KALSHI_API_URL}{path}", headers=headers, timeout=10)
        if r.status_code == 200:
            return r.json().get("markets", [])
        return []
    except Exception:
        return []

def price_threshold_from_title(title: str) -> Optional[float]:
    """Extract stock price threshold from market title."""
    # Patterns: "above $150", "below $150", "over $200", "reach $500"
    patterns = [
        r'\$\s*([\d,]+(?:\.\d+)?)',
        r'([\d,]+(?:\.\d+)?)\s*(?:dollars?|USD)',
    ]
    for pat in patterns:
        m = re.search(pat, title, re.IGNORECASE)
        if m:
            val = m.group(1).replace(",", "")
            try:
                return float(val)
            except ValueError:
                continue
    return None

def find_kalshi_trade(markets: list, signal: OptionsSignal) -> Optional[dict]:
    """
    Find the best Kalshi market to trade based on options signal.
    Bullish → look for markets asking if price will be above X.
    Bearish → look for markets asking if price will be below X.
    """
    current = signal.current_price
    best = None
    best_edge = 0.0

    for m in markets:
        _normalize_market(m)
        title = m.get("title", "").lower()
        ticker_lower = m.get("ticker", "")
        yes_ask = m.get("yes_ask", 0)
        yes_bid = m.get("yes_bid", 0)
        no_ask  = m.get("no_ask", 0)
        no_bid  = m.get("no_bid", 0)

        if not yes_ask or not no_ask:
            continue

        # Check close date (need ≥ 1 hour remaining)
        close_ts = m.get("close_time") or m.get("expiration_time") or ""
        if close_ts:
            try:
                close_dt = datetime.fromisoformat(close_ts.replace("Z", "+00:00"))
                remaining = (close_dt - datetime.now(timezone.utc)).total_seconds()
                if remaining < 3600:
                    continue
            except Exception:
                pass

        threshold = price_threshold_from_title(m.get("title", ""))
        if threshold is None:
            continue

        is_above_market = any(w in title for w in ["above", "over", "exceed", "higher", "top", "reach"])
        is_below_market = any(w in title for w in ["below", "under", "fall", "drop", "less", "bottom"])

        if signal.direction == "bullish":
            if is_above_market and threshold > current:
                # Buy YES: options flow says stock going up, market asks if it will exceed threshold
                yes_price = yes_ask
                implied_prob = signal.confidence
                true_prob = implied_prob * (threshold / current) ** 0.3  # discount for distance
                true_prob = min(true_prob, 0.85)
                edge = true_prob - yes_price / 100
                if edge - MAKER_FEE > 0 and edge > best_edge and edge >= MIN_EDGE:
                    best_edge = edge
                    best = {"market": m, "side": "yes", "price": yes_price, "edge": edge,
                            "note": f"bullish options → YES above ${threshold:.0f} (current=${current:.2f})"}

            elif is_below_market and threshold < current:
                # Buy NO: options say going up, so price won't fall below threshold
                no_price = no_ask
                # Market is asking if price will be below threshold which is below current
                # If bullish, it won't fall below → buy NO
                true_prob_no = 1.0 - signal.confidence * 0.7
                edge = true_prob_no - no_price / 100
                if edge - MAKER_FEE > 0 and edge > best_edge and edge >= MIN_EDGE:
                    best_edge = edge
                    best = {"market": m, "side": "no", "price": no_price, "edge": edge,
                            "note": f"bullish options → NO below ${threshold:.0f} (current=${current:.2f})"}

        elif signal.direction == "bearish":
            if is_below_market and threshold < current:
                # Buy YES: options flow says stock going down, market asks if it will fall below threshold
                yes_price = yes_ask
                implied_prob = signal.confidence
                true_prob = implied_prob * (current / threshold) ** 0.3
                true_prob = min(true_prob, 0.85)
                edge = true_prob - yes_price / 100
                if edge - MAKER_FEE > 0 and edge > best_edge and edge >= MIN_EDGE:
                    best_edge = edge
                    best = {"market": m, "side": "yes", "price": yes_price, "edge": edge,
                            "note": f"bearish options → YES below ${threshold:.0f} (current=${current:.2f})"}

            elif is_above_market and threshold > current:
                # Buy NO: options say going down, so price won't exceed threshold → buy NO
                no_price = no_ask
                true_prob_no = 1.0 - signal.confidence * 0.7
                edge = true_prob_no - no_price / 100
                if edge - MAKER_FEE > 0 and edge > best_edge and edge >= MIN_EDGE:
                    best_edge = edge
                    best = {"market": m, "side": "no", "price": no_price, "edge": edge,
                            "note": f"bearish options → NO above ${threshold:.0f} (current=${current:.2f})"}

    return best

# ── ORDER EXECUTION ──────────────────────────────────────────────────────────
async def place_order(client: httpx.AsyncClient, ticker: str, side: str,
                      price_cents: int, contracts: int, ledger: PaperLedger,
                      signal_note: str) -> bool:
    if PAPER_MODE:
        ledger.record(ticker, side, contracts, price_cents, signal_note)
        return True

    body_obj = {
        "ticker": ticker,
        "action": "buy",
        "side": side,
        "type": "limit",
        "count": contracts,
        "yes_price" if side == "yes" else "no_price": price_cents,
        "client_order_id": str(uuid.uuid4()),
    }
    body_str = json.dumps(body_obj)
    path = "/portfolio/orders"
    headers = _auth_headers("POST", path, body_str)
    try:
        r = await client.post(f"{KALSHI_API_URL}{path}", headers=headers,
                              content=body_str, timeout=10)
        if r.status_code in (200, 201):
            log.info(f"[ORDER] Placed {side} {contracts}ct @ {price_cents}¢ on {ticker}")
            return True
        else:
            log.warning(f"[ORDER] Failed {ticker}: {r.status_code} {r.text[:200]}")
            return False
    except Exception as e:
        log.error(f"[ORDER] Exception {ticker}: {e}")
        return False

# ── COOLDOWN TRACKER ─────────────────────────────────────────────────────────
class CooldownTracker:
    """Prevent re-trading same ticker within cooldown window."""
    def __init__(self, minutes: int = 60):
        self.minutes = minutes
        self._last: dict[str, datetime] = {}

    def can_trade(self, key: str) -> bool:
        if key not in self._last:
            return True
        elapsed = (datetime.now(timezone.utc) - self._last[key]).total_seconds()
        return elapsed > self.minutes * 60

    def mark(self, key: str):
        self._last[key] = datetime.now(timezone.utc)

# ── Stats HTTP server ─────────────────────────────────────────────────────────
_stats_app = Flask(__name__)
_bot_stats = {"trades": 0, "wins": 0, "pnl": 0.0, "balance": 0.0, "start": time.time()}

@_stats_app.route("/stats")
def _stats_endpoint():
    t = _bot_stats
    total = t["trades"]
    return jsonify({"bot": "kalshi-options-flow-bot", "paper_mode": True,
        "balance": t["balance"], "trades": total, "wins": t["wins"],
        "losses": total - t["wins"], "win_rate": round(t["wins"]/max(total,1), 4),
        "pnl": t["pnl"], "uptime_hours": round((time.time()-t["start"])/3600, 2)})

@_stats_app.route("/health")
def _health_endpoint():
    return jsonify({"status": "ok"})

def _run_stats_server():
    _stats_app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8080)))


# ── MAIN LOOP ────────────────────────────────────────────────────────────────
async def main():
    log.info(f"=== Kalshi Options Flow Bot starting (paper={PAPER_MODE}) ===")
    log.info(f"Tracking: {list(TICKER_SERIES.keys())}")
    log.info(f"MIN_EDGE={MIN_EDGE*100:.0f}%, VOLUME_RATIO_MIN={VOLUME_RATIO_MIN}x, BET_SIZE=${BET_SIZE_USD}")

    ledger = CooldownTracker(minutes=90)
    paper = PaperLedger()
    _bot_stats['balance'] = paper.balance
    threading.Thread(target=_run_stats_server, daemon=True).start()
    trades_this_session = 0

    async with httpx.AsyncClient() as client:
        while True:
            _bot_stats["balance"] = paper.balance
            _bot_stats["trades"] = len(paper.trades)
            _bot_stats["wins"] = paper.wins
            _bot_stats["losses"] = paper.losses
            log.info(f"--- Scan cycle start | balance=${paper.balance:.2f} | trades={trades_this_session} ---")

            for ticker, series_list in TICKER_SERIES.items():
                try:
                    # 1. Fetch options chain from Yahoo Finance
                    data = await get_yahoo_options(client, ticker)
                    if not data:
                        continue

                    # 2. Analyze for unusual flow
                    signal = analyze_options_flow(data, ticker)
                    if not signal:
                        log.debug(f"{ticker}: no unusual options signal")
                        continue

                    # 3. Check cooldown
                    cd_key = f"{ticker}_{signal.direction}"
                    if not ledger.can_trade(cd_key):
                        log.info(f"{ticker}: cooldown active, skipping")
                        continue

                    # 4. Find matching Kalshi markets
                    all_markets = []
                    for series in series_list:
                        markets = await get_kalshi_markets(client, series)
                        all_markets.extend(markets)
                        await asyncio.sleep(0.3)

                    if not all_markets:
                        log.info(f"{ticker}: no open Kalshi markets found in series {series_list}")
                        continue

                    # 5. Find best trade
                    trade = find_kalshi_trade(all_markets, signal)
                    if not trade:
                        log.info(f"{ticker}: no edge found in {len(all_markets)} markets")
                        shadow_log({"bot": "options_flow", "ticker": ticker, "direction": signal.direction}, taken=False, reason="no edge found")
                        evaluate_virtual_portfolios({"bot": "options_flow", "ticker": ticker, "direction": signal.direction})
                        if _quant_modules_available:
                            try:
                                _features.extract({"price": locals().get("price", 0), "volume": locals().get("volume", 0), "bid": locals().get("bid", 0), "ask": locals().get("ask", 0)})
                                _bayesian.update(locals().get("market_id", locals().get("ticker", "unknown")), locals().get("price", 0), time.time())
                                _td_edge = calculate_time_weighted_edge(locals().get("edge", 0), locals().get("minutes_remaining", locals().get("time_remaining", 15)), 15)
                                _vpin.update(locals().get("price", 0), locals().get("volume", 0))
                                _mi = estimate_market_impact(locals().get("contracts", 1), locals().get("volume", 100))
                            except:
                                pass
                        continue

                    # 6. Size bet — Kelly criterion
                    price = trade["price"]
                    market_prob = price / 100
                    model_prob = min(0.95, market_prob + trade["edge"])
                    kelly_f = max(0, (model_prob - market_prob) / (1 - market_prob)) if market_prob < 1 else 0
                    kelly_bet = max(1, min(ledger.balance * kelly_f * KELLY_FRACTION, MAX_BET_USD))
                    contracts = max(1, int(kelly_bet * 100 / price))
                    market_ticker = trade["market"].get("ticker", "?")

                    # 7. Execute
                    log.info(f"[TRADE] {ticker} → {market_ticker} | {trade['side'].upper()} "
                             f"{contracts}ct @ {price}¢ | edge={trade['edge']*100:.1f}% | {trade['note']}")

                    # ── Risk Guard check ──
                    if not PAPER_MODE:
                        allowed, reason, capped = risk_manager.pre_trade_check(market_ticker, price, contracts, trade["side"], bot_name="options-flow-bot")
                        if not allowed:
                            log.warning(f"Risk guard blocked: {reason}")
                            continue
                        contracts = capped
                    else:
                        allowed, reason, capped = risk_manager.pre_trade_check(market_ticker, price, contracts, trade["side"], bot_name="options-flow-bot")
                        if not allowed:
                            log.info(f"[PAPER] Risk guard would block: {reason}")

                    # ── Regime detection ──
                    regime = check_regime(float(price))
                    if regime == "CRASH":
                        log.warning("REGIME CRASH on kalshi_options_flow_bot — skipping trade")
                        shadow_log({"bot": "kalshi_options_flow_bot", "regime": regime}, taken=False, reason="crash regime")
                        evaluate_virtual_portfolios({"bot": "kalshi_options_flow_bot", "regime": regime})
                        continue

                    success = await place_order(client, market_ticker, trade["side"],
                                               price, contracts, paper, trade["note"])
                    if success:
                        shadow_log({"bot": "options_flow", "ticker": market_ticker, "side": trade["side"], "price": price, "edge": trade["edge"], "contracts": contracts}, taken=True)
                        evaluate_virtual_portfolios({"bot": "options_flow", "ticker": market_ticker, "side": trade["side"], "price": price, "edge": trade["edge"], "contracts": contracts})
                        ledger.mark(cd_key)
                        trades_this_session += 1

                    await asyncio.sleep(1.0)

                except Exception as e:
                    log.error(f"Error processing {ticker}: {e}")

            log.info(f"--- Scan complete | sleeping {POLL_INTERVAL_SEC}s ---")
            await asyncio.sleep(POLL_INTERVAL_SEC)

if __name__ == "__main__":
    asyncio.run(main())
