"""Continuum limit of the source graph (face map).

As the pivot spacing goes to 0, each face F(s) = (B, Lam, cap) is its own LOW and HIGH parent (Lemma F
in the limit). The LOW excess reduces to the allowance e, so the amplifier is a = (q e + r)/den,
den = 1 - 6 q B/Lam > 0. The envelope E(s) = B - Lam s obeys E' = -Lam(s), where Lam(s) is the
flattest slope for which some threshold q passes every source-step gate at the pivot b = s and at
the cap (same float gate model as the chain builders: ss_fb.gates_at + gain_fast K-copy gain).

usage: python3 continuum.py OUT.json [ds] [qfloor] [sched: e,r,f] [s_end]
"""
import sys, os, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from ss_fb import gates_at, minres
import cchain_k as CK

K_FB = CK.K_FB
def capf(s): return min(0.0549989, s + 0.016)

def reserve(s, E, Lam, q, sched, gcache):
    B = E + Lam*s; cap = capf(s)
    key = (round(B, 15), round(Lam, 15), cap)
    if key not in gcache:
        gcache.clear(); gcache[key] = CK.gfun((B, Lam, cap), 8)
    g_ = gcache[key]
    m = 1.0
    for b in (s, cap):
        g = gates_at(b, B, Lam, q, B, Lam, cap, (B, Lam, cap), sched=sched, K=K_FB, gain_fn=g_, nnu=201)
        r, _ = minres(g)
        m = min(m, r)
    return m

def best_q(s, E, Lam, sched, qfloor, gcache):
    """max over q < Lam/(6B) of the reserve; returns (reserve, q)."""
    B = E + Lam*s; qc = Lam/(6*B)
    xs = np.geomspace(1e-9, 0.3, 40)
    best = (-1.0, None)
    for x in xs:
        q = qc*(1 - x)
        if q < qfloor or q > 0.75: continue
        r = reserve(s, E, Lam, q, sched, gcache)
        if r > best[0]: best = (r, q)
    # refine around the best x by golden section on log x
    if best[1] is not None:
        x0 = 1 - best[1]/qc
        lo, hi = np.log(max(x0/3, 1e-12)), np.log(min(x0*3, 0.3))
        for _ in range(20):
            m1 = lo + (hi-lo)*0.382; m2 = lo + (hi-lo)*0.618
            q1 = qc*(1-np.exp(m1)); q2 = qc*(1-np.exp(m2))
            r1 = reserve(s, E, Lam, q1, sched, gcache) if q1 >= qfloor else -1
            r2 = reserve(s, E, Lam, q2, sched, gcache) if q2 >= qfloor else -1
            if r1 > r2: hi = m2
            else: lo = m1
            for (r, q) in ((r1, q1), (r2, q2)):
                if r > best[0]: best = (r, q)
    return best

def min_slope(s, E, sched, qfloor, Lhi, res=0.0):
    gcache = {}
    ok = lambda L: best_q(s, E, L, sched, qfloor, gcache)[0] > res
    hi = Lhi
    k = 0
    while not ok(hi):
        hi *= 1.02; k += 1
        if k > 60: return None, None
    lo = hi*0.97
    while ok(lo):
        hi = lo; lo *= 0.97
    for _ in range(36):
        mid = 0.5*(lo+hi)
        if ok(mid): hi = mid
        else: lo = mid
    r, q = best_q(s, E, hi, sched, qfloor, gcache)
    return hi, q

if __name__ == "__main__":
    out = sys.argv[1]
    ds = float(sys.argv[2]) if len(sys.argv) > 2 else 2e-4
    qfloor = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    sched = tuple(float(x) for x in sys.argv[4].split(',')) if len(sys.argv) > 4 else CK.SCHED
    s_end = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0505
    # start on the natural face E = 1 - K s, switch where the continuum slope drops below K
    s = 0.0100; E = 1 - K_FB*s
    t0 = time.time()
    while True:
        L, q = min_slope(s, E, sched, qfloor, K_FB)
        if L is not None and L < K_FB: break
        s += 2.5e-4; E = 1 - K_FB*s
        if s > 0.03: raise SystemExit("no switch found")
    print(f"switch at s={s:.5f} E={E:.8f} L={L:.8f} q={q:.8f}", flush=True)
    rows = []
    while s <= s_end + 1e-12:
        L, q = min_slope(s, E, sched, qfloor, L*1.001)
        if L is None: print("infeasible at", s); break
        B = E + L*s
        rows.append(dict(s=s, E=E, B=B, L=L, q=q, cap=capf(s)))
        print(f"s={s:.5f} E={E:.8f} L={L:.8f} B={B:.8f} q={q:.8f} den={1-6*q*B/L:.3e} t={time.time()-t0:.0f}", flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        # midpoint (RK2) step
        Lm, _ = min_slope(s + ds/2, E - L*ds/2, sched, qfloor, L)
        E -= (Lm if Lm is not None else L)*ds; s = round(s + ds, 10)
