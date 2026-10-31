# fine scan: theta with the width-restricted count face (jump guard) over (Lambda_stop, s0), faces along the K=0.45 line
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m10 import env_restricted, theta, PR99, bar
    from kwlib import run_from_base
Lend, cend, why, path = run_from_base(0.45)
print('K=0.45 line ends at L=%.4f c=%.4f (%s)' % (Lend, cend, why))
for Lq in (1.95, 1.93, 1.92, 1.91, 1.90, 1.88):
    L, c, a = min(path, key=lambda q: abs(q[0]-Lq))
    row = []
    for s0 in (0.124, 0.122, 0.12, 0.118, 0.116, 0.114, 0.112, 0.11):
        t = theta(env_restricted(L, c, s0, mode='strict')[0])[0]
        row.append('%.3f:%+.1e' % (s0, t - bar))
    tu = theta(env_restricted(L, c, None)[0])[0]
    print('L %.4f cap %.4f unrestricted %+.2e | ' % (L, c, tu - bar) + ' '.join(row))
