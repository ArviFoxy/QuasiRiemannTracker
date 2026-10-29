"""Step 7: admissible regions of the branches (guards on {delta} x [p, 1/2]) and where the old count fails."""
import numpy as np
from model import P, count, guard_vals, row_exponent

Pm = P()
target = Pm.theta - Pm.reserve
ps = np.linspace(0, 0.5, 2001)


def pmin(cand, d):
    """least p such that all guards hold on {d} x [p, 1/2] (None if not even at p = 1/2)"""
    ok = [all(v > 0 for v in guard_vals(Pm, cand, d, p)[0]) for p in ps]
    if not ok[-1]:
        return None
    i = len(ps) - 1
    while i > 0 and ok[i - 1]:
        i -= 1
    return ps[i]


print('delta   pmin(C)  pmin(capC) pmin(weakC7) pmin(capP)   old-fails-from-p (newTop)')
for d in np.arange(0.27, 0.60, 0.01):
    pm = {c: pmin(c, d) for c in ('C', 'capC', 'weakC7', 'capP')}
    fails = [p for p in ps if row_exponent(Pm, 'newTop', d, p, count(Pm, 'old', d, p)) >= target]
    need = {c: [p for p in fails if row_exponent(Pm, 'newTop', d, p, count(Pm, c, d, p)) >= target] for c in pm}
    f = f'{fails[0]:.4f}' if fails else '  -   '
    print(f'{d:.2f}  ' + '  '.join(f'{pm[c]:.4f}' if pm[c] is not None else '  None' for c in pm) + f'    {f}  '
          + ' '.join(f'{c}:{"ok" if not need[c] else f"fails>={need[c][0]:.3f}"}' for c in pm))
