"""Count exponent at the binding point (nu = q, class p = 1/2, slot width s0) along the all-on floor-1/2 chain, for every count model.
R = 1 - cs/Q at Q = 1:  PR 83 rho(q);  (a) black box (padding to 7/37);  (b+) limited supply;  (cu) face-based undiluted;  Lean K = 8 gain."""
import sys, json
import numpy as np
import counts as C, variants as V, gainc as G
rows = json.load(open('logs/c2_g1_f0.50_b1_d1.000_dL0.005_q.json'))
rows = [r for r in rows if not r.get('infeasible')]
kap = 2 * (4369779 / 5000000) - 1
print('%-7s %-8s %-7s %-8s | %-8s %-8s %-8s %-8s %-8s | %-8s %-8s  %s' % ('L', 'B', 'q', 's0', 'rho(q)', 'R_a', 'R_b1', 'R_cu', 'R_K8', 'gain', 'gain/q', 'rho-R_K8 vs rho-R_a'))
for i in range(0, len(rows), 12):
    r = rows[i]
    B0, L0 = r['B0'], r['L0']
    q = L0 / (6 * B0 - L0)
    s = r['s0']
    par = dict(kappa=kap, B0=B0, L0=L0, h0=r['c0'])
    out = {}
    for var in ('pr83', 'a', 'b1', 'cu'):
        out[var] = 1 - float(V.cs(var, q, 0.5, s, 1.0, par))
    g = float(G.gainK(q, 8, B0, L0, r['c0'], s, 1.0))
    RK = out['pr83'] - g
    print('%-7.4f %-8.5f %-7.4f %-8.5f | %-8.5f %-8.5f %-8.5f %-8.5f %-8.5f | %-8.5f %-8.5f  %.5f vs %.5f' % (
        r['L'], r['B'], q, s, out['pr83'], out['a'], out['b1'], out['cu'], RK, g, g / q, out['pr83'] - RK, out['pr83'] - out['a']))
