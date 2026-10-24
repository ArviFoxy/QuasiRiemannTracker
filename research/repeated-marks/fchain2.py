"""Accurate float chain builder (cchain search parameters) with configurable gain.
usage: python3 fchain2.py TAG K CAPFLAG OFFSET [HIGHLAG] [PIVSTEP]"""
import sys, json, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ss_fb import gates_at, minres
from gain_fast import gain

K_FB = 4.4973108
import os
QMIN = float(os.environ.get('QMIN', '0.5'))
PMAX = float(os.environ.get('PMAX', '0.04232'))
SCHED = (1e-12, 1e-8, 1e-7)
RES = 5e-8

def ok(B, Lam, q, par, cap, HP, gfn, nnu=201, res=RES):
    B0, L0, h0 = par
    if not Lam < L0: return False
    bx = (B0-B)/(L0-Lam)
    if not (0 <= bx <= min(cap, h0)): return False
    for b in (bx, cap):
        g = gates_at(b, B, Lam, q, B0, L0, h0, HP, sched=SCHED, K=K_FB, gain_fn=gfn, nnu=nnu)
        if minres(g)[0] <= res: return False
    return True

def solve(par, s, cap, HP, gfn):
    B0, L0, h0 = par
    qcap = L0/(6*B0)
    qs = qcap*(1-np.geomspace(1e-9, 0.4, 70)); qs = qs[(qs >= QMIN) & (qs <= 0.75)]
    def okL(Lam):
        B = B0-(L0-Lam)*s
        for q in qs:
            if ok(B, Lam, q, par, cap, HP, gfn): return q
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

def run(tag, K, capflag, off, lag=0, step=0.0005, verbose=True, margin=1/12):
    capf = lambda s: min(0.0549989, round(s+off, 7))
    piv = [round(0.0135+step*i, 6) for i in range(int(round((PMAX-0.0135)/step))+1)] + [0.04232]
    piv = sorted(set(piv))
    faces = [(1.0, K_FB, 0.055)]
    out = []
    t0 = time.time()
    for s in piv:
        par = faces[-1]
        HP = faces[max(0, len(faces)-1-lag)]
        gfn = gain(HP, K=K, cap=capflag, margin=margin)
        sol = solve(par, s, capf(s), HP, gfn)
        if sol is None:
            if verbose: print(f"pivot {s}: infeasible", flush=True)
            continue
        Lam, q = sol; B = par[0]-(par[1]-Lam)*s
        faces.append((B, Lam, capf(s)))
        out.append(dict(B=B, L=Lam, q=q, cap=capf(s), pivot=s))
        if verbose:
            print(f"pivot {s:.5f}: B={B:.10f} L={Lam:.10f} q={q:.6f} h@.0423={B-Lam*0.0423245:.6f} h@.0396={B-Lam*0.0396:.6f} t={time.time()-t0:.0f}", flush=True)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'fchain2_{tag}.json'), 'w'), indent=1)
    return out

if __name__ == "__main__":
    tag = sys.argv[1]; K = None if sys.argv[2] == 'inf' else int(sys.argv[2])
    capflag = sys.argv[3] == '1'; off = float(sys.argv[4])
    lag = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    step = float(sys.argv[6]) if len(sys.argv) > 6 else 0.0005
    margin = float(sys.argv[7]) if len(sys.argv) > 7 else 1/12
    run(tag, K, capflag, off, lag, step, margin=margin)
    print("done")
