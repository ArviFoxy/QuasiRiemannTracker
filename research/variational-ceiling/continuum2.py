"""Faster continuum face-map solver (same model as continuum.py), with resume.

Warm starts: the slope bisection starts from a narrow bracket around the previous slope, and the
threshold search scans the LOW denominator den = 1 - 6qB/Lam near its previous optimum.
usage: python3 continuum2.py OUT.json ds qfloor e,r,f s_end [RESUME.json]
"""
import sys, os, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import continuum as C

def best_q(s, E, Lam, sched, qfloor, gcache, x0):
    B = E + Lam*s; qc = Lam/(6*B)
    xs = x0*np.geomspace(0.25, 4.0, 9)
    best = (-1.0, None, None)
    for x in xs:
        q = qc*(1 - x)
        if q < qfloor or q > 0.75 or x >= 0.5: continue
        r = C.reserve(s, E, Lam, q, sched, gcache)
        if r > best[0]: best = (r, q, x)
    if best[1] is None: return best
    lo, hi = np.log(best[2]/1.5), np.log(min(best[2]*1.5, 0.49))
    for _ in range(12):
        m1 = lo + (hi-lo)*0.382; m2 = lo + (hi-lo)*0.618
        q1 = qc*(1-np.exp(m1)); q2 = qc*(1-np.exp(m2))
        r1 = C.reserve(s, E, Lam, q1, sched, gcache) if q1 >= qfloor else -1
        r2 = C.reserve(s, E, Lam, q2, sched, gcache) if q2 >= qfloor else -1
        if r1 > r2: hi = m2
        else: lo = m1
        for (r, q, x) in ((r1, q1, np.exp(m1)), (r2, q2, np.exp(m2))):
            if r > best[0]: best = (r, q, x)
    return best

def min_slope(s, E, sched, qfloor, Lguess, x0):
    gcache = {}
    ok = lambda L: best_q(s, E, L, sched, qfloor, gcache, x0)[0] > 0
    hi = Lguess*1.002
    while not ok(hi): hi *= 1.01
    lo = hi*0.995
    while ok(lo): hi = lo; lo *= 0.995
    for _ in range(26):
        mid = 0.5*(lo+hi)
        if ok(mid): hi = mid
        else: lo = mid
    r, q, x = best_q(s, E, hi, sched, qfloor, gcache, x0)
    return hi, q, x

if __name__ == "__main__":
    out, ds, qfloor = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
    sched = tuple(float(v) for v in sys.argv[4].split(','))
    s_end = float(sys.argv[5])
    rows = json.load(open(sys.argv[6])) if len(sys.argv) > 6 else []
    last = rows[-1]
    s = round(last['s'] + ds, 10); 
    # re-integrate the last step from the stored row with a midpoint slope
    B0 = last['B']; L0 = last['L']; E0 = last['E']; q0 = last['q']
    x0 = 1 - 6*q0*B0/L0
    Lm, _, _ = min_slope(last['s'] + ds/2, E0 - L0*ds/2, sched, qfloor, L0, x0)
    E = E0 - Lm*ds; L = Lm
    t0 = time.time()
    while s <= s_end + 1e-12:
        L, q, x = min_slope(s, E, sched, qfloor, L, x0); x0 = x
        B = E + L*s
        rows.append(dict(s=s, E=E, B=B, L=L, q=q, cap=C.capf(s)))
        print(f"s={s:.5f} E={E:.8f} L={L:.8f} B={B:.8f} q={q:.8f} den={x:.3e} t={time.time()-t0:.0f}", flush=True)
        json.dump(rows, open(out, 'w'), indent=0)
        Lm, _, _ = min_slope(s + ds/2, E - L*ds/2, sched, qfloor, L, x0)
        E -= Lm*ds; s = round(s + ds, 10)
