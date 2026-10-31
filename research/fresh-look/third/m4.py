import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m2 import theta, DD, PP
    from kwlib import run_from_base
import numpy as np
bar = 0.8733819666133 - 5e-5
base = theta(0.99999, 2.0001, 0.99999, 2.0001)
print('base %.8f  bar %.8f' % (base, bar))
for K in (0.4877, 0.485, 0.48, 0.478, 0.475, 0.47):
    Lend, cend, why, path = run_from_base(K)
    tc = theta(0.99999, Lend, 0.99999, 2.0001, capc=min(cend, 0.16))
    tb = theta(0.99999, Lend, 0.99999, Lend, capc=min(cend, 0.16))
    print('K=%.4f Lend=%.4f cap=%.3f (%s): count-face only %.8f (vs bar %+.2e) | both faces %.8f (vs bar %+.2e)' % (K, Lend, cend, why, tc, tc-bar, tb, tb-bar))
