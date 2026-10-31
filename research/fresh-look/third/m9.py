import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m2 import theta
    from kwlib import run_from_base
    from m7 import binding_info
bar = 0.8733819666133 - 5e-5
Lend, cend, why, path = run_from_base(0.45)
for Lq in (1.92, 1.90, 1.88):
    L, c, a = min(path, key=lambda p: abs(p[0]-Lq))
    t = theta(0.99999, L, 0.99999, 2.0001, capc=c)
    th, rows = binding_info(0.99999, L, 0.99999, 2.0001, capc=c)
    zs = [r[3] for r in rows]
    print('count face (0.99999, %.4f, cap %.4f): theta* %.8f  vs PR99 %+.2e  vs bar %+.2e ; read-point z near binding %.4f..%.4f' % (L, c, t, t-0.8733819666, t-bar, min(zs), max(zs)))
