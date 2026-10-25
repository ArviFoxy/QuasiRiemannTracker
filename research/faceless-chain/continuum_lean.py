"""Continuum envelope of the source chain under the Lean gates and the Lean guards.

Self-parent limit of the fine family: the face F(s) = (E + L s, L, CAPMAX, q) is its own LOW and HIGH
parent, so the LOW excess is the allowance and a = (q e + r)/den, den = 1 - 6 q B/L. The threshold is
q = (1 - den) L/(6B), the LOW limit with a fixed denominator. Lean guards: 1/2 <= q <= 3/4 and
B >= 22/23 (the HIGH parent). The flattest slope L(s, E) passing every gate at b = s and b = CAPMAX
(best den on a grid) drives E' = -L (RK2).

usage: python3 continuum_lean.py OUT.json [ds] [margin_high] [s_end]
"""
import sys, json, time
import numpy as np
import gates as G

DENS = np.geomspace(2e-7, 3e-3, 23)


def ok_node(s, E, L, den, mh, fees=G.FINE, cap=G.CAPMAX):
    B = E + L*s
    q = (1 - den)*L/(6*B)
    if not (0.5 <= q < 0.75) or B < 22/23 or B > 1:
        return False, None
    n = G.node(B, L, cap, q, fees)
    for b in (s, cap):
        m = G.margins(n, n, n, b)
        if m['scalar'] <= 0 or m['sector'] <= 0 or m['high'] <= mh:
            return False, m
    return True, None


def ok_L(s, E, L, mh, dens=DENS):
    for den in dens:
        good, _ = ok_node(s, E, L, den, mh)
        if good:
            return den
    return None


def min_slope(s, E, Lguess, mh):
    Lmax = (1 - E)/s*(1 - 1e-12)          # B <= 1
    hi = min(Lguess*1.01, Lmax)
    if ok_L(s, E, hi, mh) is None:
        found = False
        for x in np.linspace(hi, Lmax, 40)[1:]:
            if ok_L(s, E, x, mh) is not None:
                hi = x; found = True; break
        if not found:
            return None, None
    lo = hi*0.995
    while ok_L(s, E, lo, mh) is not None:
        hi = lo; lo *= 0.995
    for _ in range(34):
        mid = 0.5*(lo + hi)
        if ok_L(s, E, mid, mh) is not None:
            hi = mid
        else:
            lo = mid
    return hi, ok_L(s, E, hi, mh)


if __name__ == "__main__":
    out = sys.argv[1]
    ds = float(sys.argv[2]) if len(sys.argv) > 2 else 2e-4
    mh = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    s_end = float(sys.argv[4]) if len(sys.argv) > 4 else 0.0435
    K = G.KN
    s = 0.0120
    while True:
        E = 1 - K*s
        L, den = min_slope(s, E, K, mh)
        if L is not None and L < K:
            break
        s += 1e-4
    # refine the switch point
    lo, hi = s - 1e-4, s
    for _ in range(20):
        mid = 0.5*(lo + hi)
        Lm, _ = min_slope(mid, 1 - K*mid, K, mh)
        if Lm is not None and Lm < K:
            hi = mid
        else:
            lo = mid
    s = hi; E = 1 - K*s
    L, den = min_slope(s, E, K, mh)
    print(f"switch at s={s:.7f} E={E:.9f} L={L:.8f} den={den:.2e}", flush=True)
    rows = []
    t0 = time.time()
    while s <= s_end + 1e-12:
        L, den = min_slope(s, E, L, mh)
        if L is None:
            print("infeasible at", s, flush=True); break
        B = E + L*s; q = (1 - den)*L/(6*B)
        rows.append(dict(s=s, E=E, B=B, L=L, q=q, den=den))
        print(f"s={s:.5f} E={E:.9f} L={L:.8f} B={B:.9f} q={q:.8f} den={den:.2e} t={time.time()-t0:.0f}",
              flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        Lm, _ = min_slope(s + ds/2, E - L*ds/2, L, mh)
        E -= (Lm if Lm is not None else L)*ds
        s = round(s + ds, 10)
