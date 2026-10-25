"""Full-gate continuum envelope with a mixed fourth/sixth-power LOW step.

Same gates as `../faceless-chain/continuum_lean.py` (float mirror of the Lean step), with the LOW
amplifier replaced by a selected fourth-power block of width d:
  payment  d(1 + q - c q B0/L0) >= q X0 + r      (e = 1 saving, c = row-scale cost per unit)
  F        = 1 - c d                              (RAW scale)
  other gates see d where they saw the pool width a (conservative: as costly as the pool).
The face is its own parent; threshold q = (1 - den)/(c B/L - 1), den = 1 + q - c q B/L.
c = 6 reproduces Collet's step only in the denominator algebra if the saving were absent (it is not);
MODE=pure runs the unmodified gates for calibration.
Started on Sil's face (0.99999, 93/25) at the tangency of the flow.
usage: python3 continuum_mixed.py OUT.json C [ds] [s_end]   (C = 4 or 6, or 'pure')"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'faceless-chain'))
import gates as G

CMODE = sys.argv[2] if len(sys.argv) > 2 else '4'
PURE = CMODE == 'pure'
CC = 6.0 if PURE else float(CMODE)

def basics_mixed(n, low, b):
    B, L, cap, q, e, r, f = n
    B0, L0 = low[0], low[1]
    t = B - L*(b - e)
    if PURE:
        den = 1 - 6*q*B0/L0
        a = (q*(b + (t - B0)/L0) + r)/den
        return t, den, a, 1 - 6*a
    den = 1 + q - CC*q*B0/L0
    d = (q*(b + (t - B0)/L0) + r)/den
    return t, den, d, 1 - CC*d
G.basics = basics_mixed

DENS = np.geomspace(2e-7, 3e-3, 23)
B0S, LAMS, CAPS = 0.99999, 3.72, 0.06

def q_of(L, B, den):
    if PURE: return (1 - den)*L/(6*B)
    x = CC*B/L - 1
    return (1 - den)/x if x > 0 else np.inf

def ok_node(s, E, L, den, mh=0.0, fees=G.FINE, cap=G.CAPMAX):
    B = E + L*s
    q = q_of(L, B, den)
    if not (0.5 <= q < 0.75) or B < 22/23 or B > 1:
        return False
    n = G.node(B, L, cap, q, fees)
    for b in (s, cap):
        m = G.margins(n, n, n, b)
        if m['scalar'] <= 0 or m['sector'] <= 0 or m['high'] <= mh:
            return False
    return True

QGRID = np.linspace(0.5, 0.749, 84)
def ok_node_q(s, E, L, q, mh=0.0, fees=G.FINE, cap=G.CAPMAX):
    B = E + L*s
    den = 1 + q - CC*q*B/L
    if den <= 1e-7 or B < 22/23 or B > 1:
        return False
    n = G.node(B, L, cap, q, fees)
    for b in (s, cap):
        m = G.margins(n, n, n, b)
        if m['scalar'] <= 0 or m['sector'] <= 0 or m['high'] <= mh:
            return False
    return True

def ok_L(s, E, L):
    if PURE:
        for den in DENS:
            if ok_node(s, E, L, den):
                return den
        return None
    for q in QGRID[::-1]:             # largest q first: it eases HIGH; LOW only needs den > 0
        if ok_node_q(s, E, L, q):
            return q
    return None

def min_slope(s, E, Lguess):
    Lmax = (1 - E)/s*(1 - 1e-12)
    hi = min(Lguess*1.01, Lmax)
    if ok_L(s, E, hi) is None:
        for x in np.linspace(hi, Lmax, 60)[1:]:
            if ok_L(s, E, x) is not None:
                hi = x; break
        else:
            return None, None
    lo = hi*0.995
    while lo > 0.3 and ok_L(s, E, lo) is not None:
        hi = lo; lo *= 0.995
    for _ in range(34):
        mid = 0.5*(lo + hi)
        if ok_L(s, E, mid) is not None: hi = mid
        else: lo = mid
    return hi, ok_L(s, E, hi)

if __name__ == '__main__':
    out = sys.argv[1]
    ds = float(sys.argv[3]) if len(sys.argv) > 3 else 5e-4
    s_end = float(sys.argv[4]) if len(sys.argv) > 4 else 0.0545
    # start: the first s where the minimal admissible slope from Sil's face drops below 93/25
    s = 0.002
    while True:
        E = B0S - LAMS*s
        L, den = min_slope(s, E, LAMS)
        if L is not None and L < LAMS: break
        s += 5e-4
        if s > 0.05: print('no tangency'); sys.exit()
    print(f"start s={s:.5f} E={E:.6f} L={L:.5f}", flush=True)
    rows = []; t0 = time.time()
    while s <= s_end + 1e-12:
        L, den = min_slope(s, E, L)
        if L is None:
            print('infeasible at', s, flush=True); break
        B = E + L*s
        if PURE: q = q_of(L, B, den)
        else: q, den = den, 1 + den - CC*den*B/L
        rows.append(dict(s=s, E=E, B=B, L=L, q=q, den=den))
        print(f"s={s:.4f} E={E:.6f} L={L:.5f} B={B:.6f} q={q:.4f} den={den:.1e} t={time.time()-t0:.0f}", flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        Lm, _ = min_slope(s + ds/2, E - L*ds/2, L)
        E -= (Lm if Lm is not None else L)*ds
        s = round(s + ds, 10)
