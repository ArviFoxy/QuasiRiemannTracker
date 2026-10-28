"""Count exponents at the binding point (nu = q, x = 1/2, slot width s0) of a chain, for every count model.
R_model = 1 - cs/Q  with Q = 1 (v = 0).  Also the 'needed' R: the uniform lowering of R (in the gate) that gives the same s0 as a target model."""
import sys
import numpy as np
import ode, inst, variants as V, counts as C
from scipy.optimize import brentq

MODELS = ['pr83', 'a', 'c', 'b0', 'b1', 'd1', 'd2', 'cu', 'u']


def R_at(var, nu, s, B, L, kappa, h0=0.1, x=0.5):
    par = dict(kappa=kappa, B0=B, L0=L, h0=h0)
    return 1 - float(V.cs(var, nu, x, s, 1.0, par))


def table(chain_var='pr83', boot=False, dfac=0.999, Ls=(2.34, 2.25, 2.20, 2.10, 2.00, 1.95)):
    ch = ode.Chain(chain_var, dfac=dfac, boot=boot)
    rows = []
    for L in Ls:
        if L < ch.Lmin:
            continue
        B = ch.B(L); q = ch.qinf(L); s = ch.slope(L)
        rows.append((L, B, q, s, {m: R_at(m, q, s, B, L, ch.kappa) for m in MODELS}))
    return rows


if __name__ == '__main__':
    var = sys.argv[1] if len(sys.argv) > 1 else 'pr83'
    rows = table(var)
    print('chain of variant', var, ' (binding point nu=q, x=1/2, s=s0 of that chain)')
    print('%-7s %-8s %-7s %-7s ' % ('L', 'B', 'q', 's0') + ' '.join('%8s' % m for m in MODELS))
    for L, B, q, s, d in rows:
        print('%-7.3f %-8.5f %-7.4f %-7.4f ' % (L, B, q, s) + ' '.join('%8.5f' % d[m] for m in MODELS))
