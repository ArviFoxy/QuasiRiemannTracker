"""Rational chain builder for the capped K-copy gain G' = min(nu S, G_K).
usage: python3 cchain_k.py K OUT.json [OFFSET]"""
import sys, json, numpy as np, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ss_fb import gates_at, minres
from gain_fast import gain

K_FB = 4.4973108
SCHED = (1e-12, 1e-8, 1e-7)
RES = 5e-8
PS = np.unique(np.concatenate([np.linspace(0, 0.4, 81), np.linspace(0.4, 0.5, 101)]))

def gfun(HP, K):
    return gain(HP, K=K, cap=True, ps=PS, margin=0.0)

def ok(B, Lam, q, par, cap, K, nnu=201, res=RES):
    B0, L0, h0 = par
    if not Lam < L0: return False
    bx = (B0-B)/(L0-Lam)
    if not (0 <= bx <= min(cap, h0)): return False
    g_ = gfun(par, K)
    for b in (bx, cap):
        g = gates_at(b, B, Lam, q, B0, L0, h0, par, sched=SCHED, K=K_FB, gain_fn=g_, nnu=nnu)
        if minres(g)[0] <= res: return False
    return True

def solve(par, s, cap, K):
    B0, L0, h0 = par
    qcap = L0/(6*B0)
    qs = qcap*(1-np.geomspace(1e-9, 0.4, 70)); qs = qs[(qs >= 0.5) & (qs <= 0.75)]
    def okL(Lam):
        B = B0-(L0-Lam)*s
        for q in qs:
            if ok(B, Lam, q, par, cap, K): return q
        return None
    grid = L0*(1-np.geomspace(1e-9, 0.45, 90))
    hi = None; lo = None
    for Lc in grid:
        if okL(Lc) is not None: hi = Lc
        elif hi is not None: lo = Lc; break
    if hi is None: return None
    if lo is None: lo = 0.5*L0
    for _ in range(40):
        mid = (lo+hi)/2
        if okL(mid) is not None: hi = mid
        else: lo = mid
    return hi, okL(hi)

def dec(x, nd=13, up=False):
    f = Fr(str(round(x, nd))); step = Fr(1, 10**nd)
    if up and f < Fr(x): f += step
    if (not up) and f > Fr(x): f -= step
    return f

def build(pivots, capf, K, verbose=True):
    par_f = (1.0, K_FB, 0.055)
    par_q = (Fr(1), Fr(11243277, 2500000), Fr(11, 200))
    nodes = []
    for s in pivots:
        cap = capf(s)
        sol = solve(par_f, s, cap, K)
        if sol is None:
            if verbose: print(f"pivot {s}: infeasible", flush=True)
            continue
        Lam, q = sol
        LamQ = dec(Lam + 2e-12, up=True)
        Bq = dec(float(par_q[0] - (par_q[1]-LamQ)*Fr(str(s))), up=False)
        qQ = dec(q, nd=12)
        capQ = Fr(str(cap))
        if not ok(float(Bq), float(LamQ), float(qQ), par_f, float(capQ), K, nnu=801, res=RES/2):
            if verbose: print(f"pivot {s}: rounding broke gates", flush=True)
            continue
        nodes.append(dict(B=str(Bq), L=str(LamQ), q=str(qQ), cap=str(capQ), pivot=s))
        par_f = (float(Bq), float(LamQ), float(capQ)); par_q = (Bq, LamQ, capQ)
        if verbose:
            print(f"pivot {s:.5f}: B={float(Bq):.12f} L={float(LamQ):.12f} q={float(qQ):.9f} "
                  f"h@.0423={float(Bq)-float(LamQ)*0.0423245:.6f} h@.0396={float(Bq)-float(LamQ)*0.0396:.6f}", flush=True)
    return nodes

if __name__ == "__main__":
    K = int(sys.argv[1]); out = sys.argv[2]
    off = float(sys.argv[3]) if len(sys.argv) > 3 else 0.016
    capf = lambda s: min(0.0549989, round(s + off, 7))
    piv = [round(0.0135 + 0.0005*i, 4) for i in range(58)] + [0.04232]
    nodes = build(piv, capf, K)
    json.dump(nodes, open(out, 'w'), indent=1)
    print("nodes:", len(nodes))
