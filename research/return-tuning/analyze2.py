"""Step 2: the binding point of newTop; counts and guards of every branch there."""
import numpy as np
from scipy.optimize import minimize_scalar
from model import P, count, guard_vals, witness, row_exponent, GUARD_NAMES

Pm = P()
target = Pm.theta - Pm.reserve


def ex(cand, d, p=0.5):
    return row_exponent(Pm, 'newTop', d, p, count(Pm, cand, d, p))


for cand in ['C', 'capC', 'weakC7', 'P', 'capP', 'old']:
    r = minimize_scalar(lambda d: -ex(cand, d), bounds=(0.3, 0.6), method='bounded', options=dict(xatol=1e-12))
    d = r.x
    print(f'{cand:7s} max_d newTop exponent at p=1/2: {-r.fun:.12f} at delta={d:.8f}; count={count(Pm, cand, d, 0.5):.10f}'
          f'  (theta-reserve) - max = {target + r.fun:+.3e}')
    if cand != 'old':
        g, br = guard_vals(Pm, cand, d, 0.5)
        t, rr, m = witness(Pm, cand, d, 0.5)
        print(f'        witness t={t:.6f} r={rr:.6f} m={m:.6f};  normalized guards:')
        J = br['J']; DJ = br['DJ']
        norm = [1, 1, 1, 1, J, J, DJ, DJ, DJ, DJ, J, J * J, 1, 1, DJ]
        print('        ' + ', '.join(f'{GUARD_NAMES[i]}={g[i] / norm[i]:+.4g}' for i in range(15)))
