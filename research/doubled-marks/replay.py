"""Replay Hailey's 222-node feedback graph (feedback.tex) with the exact gate model ss_fb.gates_at.
Each node keeps its LOW parent, HIGH parent, crossing width b_x (from Hailey's printed values), cap and budget.
The HIGH gain uses k copies of the marks in the inverse witness (k=1: PR69).  p=1/2 facets during search."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
from ss_fb import gates_at, minres

SCHED = {'O': (1e-12, 1e-8, 1e-7), 'T': (1e-17, 1e-12, 1e-10)}
K_FB = 4.4973108

def gain_half(k, HP):
    """p=1/2 HIGH gain with k copies; HP=(BH,LH,hH) earlier face for the plain, or None (natural 9/2)."""
    def g(nu, S, Fp):
        w = 5-6*nu; tn = 15-6*nu
        if HP is None:
            d = 5-2*nu
            phi = nu*w/d; A = 14*nu*w/(115-54*nu); B = 2*nu*w*w/(3*d*(115-54*nu)); C = 16*nu*w*w/(3*d*(185-138*nu))
            return np.minimum.reduce([(2*k+1)*phi*S/3, k*A*S+B*Fp,
                                      nu*w/(10+3*w)*S + 2*nu*w*w/(tn*(10+3*w))*Fp, C*Fp])
        BH, LH, hH = HP
        # solve 6 nu xi + w (r* + y*/2) = 5 Fp for each branch pair; gain = nu (xi - xi0 Fp)
        xi0 = 10/tn
        inv = [(1.0, k*S), (2.0, Fp)]                     # r* = a xi - b
        pl = [(1.0, S), (1.0, hH*Fp), (LH/(LH-1), BH*Fp/(LH-1))]
        best = None
        for ai, bi in inv:
            for aj, bj in pl:
                xi = (5*Fp + w*(bi + bj/2))/(6*nu + w*(ai + aj/2))
                best = xi if best is None else np.minimum(best, xi)
        return nu*(best - xi0*Fp)
    return g

def feasible(B, Lam, q, par, HP, cap, bud, k, nnu):
    B0, L0, h0 = par
    bx = (B0-B)/(L0-Lam)
    for b in (bx, cap):
        g = gates_at(b, B, Lam, q, B0, L0, h0, HP, sched=SCHED[bud], K=K_FB,
                     gain_fn=gain_half(k, HP), nnu=nnu)
        if minres(g)[0] <= 0:
            return False
    return True

def solve_node(par, HP, bx, cap, bud, k, nnu=201, qhint=None):
    B0, L0, h0 = par
    qcap = L0/(6*B0)
    xs = np.geomspace(1e-9, 0.35, 70)
    qs = qcap*(1-xs)
    qs = qs[(qs >= 0.5) & (qs <= 0.75)]
    def ok(Lam):
        B = B0-(L0-Lam)*bx
        for q in qs:
            if feasible(B, Lam, q, par, HP, cap, bud, k, nnu):
                return q
        return None
    hi = L0*(1-1e-12)
    if ok(hi) is None:
        return None
    lo = 0.6*L0
    if ok(lo) is not None:
        hi = lo
    for _ in range(45):
        mid = (lo+hi)/2
        if ok(mid) is not None: hi = mid
        else: lo = mid
    q = ok(hi)
    return (B0-(L0-hi)*bx, hi, q)

def replay(k, verbose=False, upto=None):
    G = json.load(open(os.path.join(HERE, 'feedback_graph.json')))
    hail = {r['name']: r for r in G}
    sim = {'natural': (1.0, K_FB, 0.055)}
    for r in G[1:upto]:
        n = r['name']; lowp = hail[r['low']]
        bx = (lowp['B']-r['B'])/(lowp['L']-r['L'])
        par = sim[r['low']]
        HP = sim[r['high']] if r['high'] else None
        res = solve_node(par, HP, bx, r['cap'], r['bud'], k)
        if res is None:
            print("FAIL", n, flush=True); return sim
        sim[n] = (res[0], res[1], r['cap'])
        if verbose:
            print(f"{n:22s} hail B={r['B']:.9f} L={r['L']:.7f} | sim B={res[0]:.9f} L={res[1]:.7f} q={res[2]:.6f}", flush=True)
    return sim

if __name__ == "__main__":
    k = int(sys.argv[1]); upto = int(sys.argv[2]) if len(sys.argv) > 2 else None
    sim = replay(k, verbose=True, upto=upto)
    json.dump(sim, open(os.path.join(HERE, f'replay_k{k}.json'), 'w'))
    for nm in ('alt_focused_g6_C', 'alt_focused_g7_P'):
        if nm in sim:
            B, L, h = sim[nm]
            print(nm, B, L, "height@0.0423245", B-L*0.0423245, "height@0.0395", B-L*0.0395)
