"""Joint float model of the final return: edge inequalities (model69 count envelope) plus
the scalar receipts of cert_return.receipt (exact), searching h and t_f.
mode 'pr69'  : all receipts as in PR #69's return (FR19, FR21, Lean 264/625 plain bound, ...)
mode 'global': drop the conservative-window receipts that the downward-closed global P face makes
               unnecessary (FR19 x2, FR21/22, plain upper 11/25 and 264/625, width lower/upper)."""
import sys, os, json, numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from pick_theta2 import gap
import cert_return as CR
from theta_of import faces

WINDOW_KEYS = {'small_width_shortening', 'short_plain_shortening', 'large_shift',
               'physical_plain_upper', 'physical_plain_upper_lean_264_625', 'physical_width_lower',
               'physical_width_upper', 'physical_plain_lower', 'shift_bound_9_50'}

def receipts_ok(c, h, BP, LP, capC, capP, sC, sPp, sP, tf, mode, theta_I=Fr(8747759, 10**7)):
    th = Fr(1) - Fr(c).limit_denominator(10**12)
    G = CR.geometry(th, Fr(h).limit_denominator(10**9), Fr(BP).limit_denominator(10**13), Fr(LP).limit_denominator(10**13), Fr(sP).limit_denominator(10**6))
    rec = CR.receipt(G, Fr(BP).limit_denominator(10**13), Fr(LP).limit_denominator(10**13), capC, capP,
                     Fr(sC).limit_denominator(10**6), Fr(sPp).limit_denominator(10**6), theta_I, Fr(tf).limit_denominator(10**6))
    bad = {k: float(v) for k, v in rec.items() if v <= 0 and not (mode == 'global' and k in WINDOW_KEYS)}
    return (len(bad) == 0), bad

def best_c(C, P, h, sC, sP, tfs, mode, dl, pp, capC=Fr(549989, 10**7), capP=Fr(549989, 10**7), sPp=43/1000):
    FC = M.Face(C[0], C[1], sC, 'C'); FP = M.Face(P[0], P[1], sPp, 'P')
    lo, hi = 0.12524, 0.1262
    def feasible(c):
        if gap(c, h, dl, pp, FC, FP, sP)[0] > -1e-9: return False
        for tf in tfs:
            ok, bad = receipts_ok(c, h, P[0], P[1], capC, capP, sC, sPp, sP, tf, mode)
            if ok: return True
        return False
    if not feasible(lo): return 0.0
    for _ in range(36):
        mid = (lo+hi)/2
        if feasible(mid): lo = mid
        else: hi = mid
    return lo

if __name__ == "__main__":
    path, mode = sys.argv[1], sys.argv[2]
    sC = float(sys.argv[3]); sP = float(sys.argv[4])
    h0, h1, nh = float(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7])
    C, P = faces(path)
    dl, pp = M.grid(301, 151)
    tfs = [1/400, 1/380, 1/360, 1/350, 1/340, 1/330, 1/320, 1/300] if mode == 'pr69' else [1/400]
    best = (0, None)
    for h in np.linspace(h0, h1, nh):
        c = best_c(C, P, h, sC, sP, tfs, mode, dl, pp)
        print(f"{mode} sC={sC} sP={sP} h={h:.5f} theta~{1-c:.9f}", flush=True)
        if c > best[0]: best = (c, h)
    print("BEST", mode, sC, sP, 1-best[0], best[1])
