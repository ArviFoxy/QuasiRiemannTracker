"""Build a dense monotone-pivot source chain with the exact gate model (ss_fb.gates_at) and
k copies of the marks in the HIGH inverse witness.  Each node: LOW parent = HIGH parent = previous node."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
from ss_fb import gates_at, minres
from replay import gain_half, SCHED, K_FB

def feasible(B, Lam, q, par, HP, cap, bud, k, nnu):
    B0, L0, h0 = par
    bx = (B0-B)/(L0-Lam)
    if not (0 <= bx <= min(cap, h0)): return False
    for b in (bx, cap):
        g = gates_at(b, B, Lam, q, B0, L0, h0, HP, sched=SCHED[bud], K=K_FB,
                     gain_fn=gain_half(k, HP), nnu=nnu)
        if minres(g)[0] <= 0: return False
    return True

def solve(par, HP, bx, cap, bud, k, nnu=161):
    B0, L0, h0 = par
    qcap = L0/(6*B0)
    qs = qcap*(1-np.geomspace(1e-10, 0.4, 60)); qs = qs[(qs >= 0.5) & (qs <= 0.75)]
    def ok(Lam):
        B = B0-(L0-Lam)*bx
        for q in qs:
            if feasible(B, Lam, q, par, HP, cap, bud, k, nnu): return q
        return None
    grid = L0*(1-np.geomspace(1e-9, 0.45, 90))
    hi = None; lo = None
    for Lc in grid:
        if ok(Lc) is not None: hi = Lc
        elif hi is not None: lo = Lc; break
    if hi is None: return None
    if lo is None: lo = 0.5*L0
    for _ in range(40):
        mid = (lo+hi)/2
        if ok(mid) is not None: hi = mid
        else: lo = mid
    return (B0-(L0-hi)*bx, hi, ok(hi))

def build(k, pivots, capf, bud='O', verbose=False, start=None):
    par = start or (1.0, K_FB, 0.055)
    nodes = []
    for s in pivots:
        cap = capf(s)
        res = solve(par, par, s, cap, bud, k)
        if res is None:
            if verbose: print(f"  pivot {s:.5f}: infeasible, skip", flush=True)
            continue
        B, L, q = res
        nodes.append(dict(B=B, L=L, q=q, cap=cap, bx=s))
        par = (B, L, cap)
        if verbose: print(f"  k={k} pivot {s:.5f} cap {cap:.5f}: B={B:.9f} L={L:.6f} q={q:.6f} h@.0423={B-L*0.0423245:.6f} h@.0396={B-L*0.0396:.6f}", flush=True)
    return nodes

if __name__ == "__main__":
    k = int(sys.argv[1]); step = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0005
    capf = lambda s: min(0.0549989, s + 0.016)
    piv = list(np.arange(0.0135, 0.04232, step)) + [0.04232]*4
    nodes = build(k, piv, capf, verbose=True)
    json.dump(nodes, open(os.path.join(HERE, f'chain_k{k}_{step}.json'), 'w'))
