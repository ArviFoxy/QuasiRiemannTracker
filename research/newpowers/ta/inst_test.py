import sys
sys.path.insert(0, '/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/analysis/B2')
import numpy as np
from odemod import Ode
import inst, counts as C
base = Ode()
kap = 0.74791
print('L, B, q, s0(PR83) | % change vs PR83 for variants')
vars_ = ['a', 'u', 'c', 'cu', 'd1', 'd2', 'd3', 'd4']
print(' '*30 + ' '.join('%7s' % v for v in vars_))
for L in (2.3415, 2.30, 2.25, 2.20, 2.15):
    B = base.B(L); q = base.qinf(L)
    par = dict(kappa=kap, B0=B, L0=L, h0=0.1)
    s83 = inst.s0_inst('pr83', B, L, q, par)
    row = []
    for v in vars_:
        row.append(100 * (inst.s0_inst(v, B, L, q, par) / s83 - 1))
    print('L=%.4f B=%.5f q=%.4f s83=%.5f | ' % (L, B, q, s83) + ' '.join('%+6.1f%%' % r for r in row))
