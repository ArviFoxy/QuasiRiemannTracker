import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m2 import theta
    from kwlib import run_from_base
bar = 0.8733819666133 - 5e-5
for K in (0.46, 0.45):
    Lend, cend, why, path = run_from_base(K)
    t = theta(0.99999, Lend, 0.99999, 2.0001, capc=min(cend, 0.16)); t2 = theta(0.99999, Lend, 0.99999, 1.9461, capc=min(cend,0.16))
    print('K=%.3f Lend=%.4f (%s): count only %+.2e vs bar; with physical at 1.9461: %+.2e' % (K, Lend, why, t - bar, t2 - bar))
