"""Limited-supply re-derivation of the marked count (variant (b)); vectorised nested bisection.

Bounds (exponent of U), delta = nu, p = mean slot bin / nu, kappa = plain cost, sigma = slot supply (total width),
r = inverse length, m = t - r = plain length, t = detector cutoff in [1, 3/2]  (markedcount.py of B2, Cycle25 `rowCount`):
  long   (r>=1):            (1+5r)/6 - delta r
  I0     (r<1):             1 - delta r
  I1     (needs (1-r)/2<=sigma):   1 - delta (p + (1-p) r)
  I1'    (partial z=sigma, r<1-2sigma):   1 - delta (r + 2 p sigma)          [only if partial=True]
  P0     (m>=0):            1 - 2 delta m
  P1     (m<1/2, (1-2m)/(6kappa) <= sigma):  1 - 2 delta m - 2 delta p (1-2m)/(6 kappa)
  P1'    (partial z_P=sigma): 1 - 2 delta m - 2 delta p sigma                  [only if partial=True]
count exponent R = min_t max( long(t), max_{r<1} min(I(r), P(r,t)) ).
partial=False reproduces B2's markedcount.py (full needed width only); partial=True also allows z = min(sigma, needed),
which is Lemma A_1 of the repeated-marks note (z in [0, S]).
At sigma >= 7/37 (and large) both reproduce rowCount (checked in test_supply.py).
"""
import numpy as np


def _I(delta, p, sigma, r, partial):
    I0 = 1 - delta * r
    full = 1 - delta * (p + (1 - p) * r)
    ok = (1 - r) / 2 <= sigma + 1e-12
    out = np.where(ok, np.minimum(I0, full), I0)
    if partial:
        part = 1 - delta * (r + 2 * p * sigma)
        out = np.where(ok, out, np.minimum(out, part))
    return out


def _P(delta, p, kappa, sigma, m, partial):
    P0 = 1 - 2 * delta * m
    need = (1 - 2 * m) / (6 * kappa)
    P1 = 1 - 2 * delta * m - 2 * delta * p * need
    ok = (m < 0.5) & (need <= sigma + 1e-12)
    out = np.where(ok, np.minimum(P0, P1), P0)
    if partial:
        P1p = 1 - 2 * delta * m - 2 * delta * p * sigma
        out = np.where((m < 0.5) & (need > sigma + 1e-12), np.minimum(out, P1p), out)
    return out


def crossing_value(delta, p, kappa, sigma, t, partial=False, it=48):
    """max_{r in [0,min(t,1)]} min(I(r), P(r,t))   (I decreasing, P increasing in r)"""
    lo = np.zeros_like(t * delta)
    hi = np.minimum(t, 1.0) * np.ones_like(lo)
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        g = _I(delta, p, sigma, mid, partial) - _P(delta, p, kappa, sigma, t - mid, partial)
        pos = g > 0          # I above P -> crossing to the right
        lo = np.where(pos, mid, lo)
        hi = np.where(pos, hi, mid)
    # monotone I (non-increasing) / P (non-decreasing) may jump at the crossing: take the better of both bracket ends
    vl = np.minimum(_I(delta, p, sigma, lo, partial), _P(delta, p, kappa, sigma, t - lo, partial))
    vh = np.minimum(_I(delta, p, sigma, hi, partial), _P(delta, p, kappa, sigma, t - hi, partial))
    return np.maximum(vl, vh), 0.5 * (lo + hi)


def R_supply(delta, p, kappa, sigma, partial=False, it_t=48, it_r=48):
    delta, p, sigma = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (delta, p, sigma)))
    lo = np.ones_like(delta)
    hi = 1.5 * np.ones_like(delta)
    long_ = lambda t: (1 + 5 * t) / 6 - delta * t

    def total_gap(t):
        c, _ = crossing_value(delta, p, kappa, sigma, t, partial, it_r)
        return long_(t) - c        # increasing in t

    # t* = root of long(t) = c(t) in [1, 3/2]; if long(1) >= c(1): t*=1 ; if long(3/2) <= c(3/2): t*=3/2
    for _ in range(it_t):
        mid = 0.5 * (lo + hi)
        g = total_gap(mid)
        hi = np.where(g > 0, mid, hi)
        lo = np.where(g > 0, lo, mid)
    t = 0.5 * (lo + hi)
    c, r = crossing_value(delta, p, kappa, sigma, t, partial, it_r)
    return np.maximum(c, long_(t)), t, r
