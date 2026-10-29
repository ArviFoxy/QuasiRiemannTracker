"""Step 1: where does the current return bind?  Margins of rows and guards at the merged constants."""
import numpy as np
from fractions import Fraction as Fr
from model import P, count, guard_vals, witness, row_exponent, GUARD_NAMES, old_JN, branch_vals
from windows import parse_windows, parse_rows

Pm = P()
ws = parse_windows()
rows = parse_rows()
target = Pm.theta - Pm.reserve
print('theta =', Pm.theta, ' h =', Pm.h, ' ell =', Pm.ell, ' y =', Pm.y, ' kappa =', Pm.kappa)
print('edges:', [(n, d, C) for n, d, C in Pm.edges()])


def lean_env(d, p):
    """GenericCount.envelope = min(old, available windows) (FiniteEnvelope.lean:20)"""
    v = count(Pm, 'old', d, p)
    for w in ws:
        if float(w['dlo']) <= d <= float(w['dhi']) and float(w['plo']) <= p <= 0.5:
            v = min(v, count(Pm, w['branch'], d, p))
    return v


# 1. max of each edge's exponent with the Lean envelope
for name, dd, C in Pm.edges():
    best = (-1, None)
    for d in np.linspace(0, 0.75, 751):
        for p in np.linspace(0, 0.5, 501):
            e = row_exponent(Pm, name, d, p, lean_env(d, p))
            if e > best[0]:
                best = (e, (d, p))
    print(f'{name:10s} max exponent {best[0]:.10f} at {best[1]}  slack to theta-reserve {target - best[0]:+.3e}')
