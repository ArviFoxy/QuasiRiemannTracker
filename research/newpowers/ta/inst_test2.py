import sys
sys.path.insert(0, '/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/analysis/B2')
import numpy as np
from odemod import Ode
import inst, counts as C
base = Ode()
kap = 0.74791
for L in (2.3415, 2.20):
    B = base.B(L); q = base.qinf(L)
    par = dict(kappa=kap, B0=B, L0=L, h0=0.1)
    for v in ['pr83', 'a', 'c', 'cu', 'd1', 'd2', 'd3']:
        s = inst.s0_inst(v, B, L, q, par)
        nus = np.linspace(q, 0.75, 41)
        nu = nus[:, None]; x = inst.XS[None, :]
        cs = inst.cs_variant(v, nu, x, s, 1.0, par)
        J = cs - nu * B + nu * (L - 2 * x) * s
        i, j = np.unravel_index(np.argmin(J), J.shape)
        print('L=%.4f var=%-5s s0=%.7f  min J=%.2e at nu=%.4f x=%.3f ; J(nu=q) min over x=%.2e at x=%.3f; J(nu=.75) min=%.2e' % (L, v, s, J.min(), nus[i], inst.XS[j], J[0].min(), inst.XS[np.argmin(J[0])], J[-1].min()))
