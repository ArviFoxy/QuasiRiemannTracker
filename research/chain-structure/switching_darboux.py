"""Is the switching flow (binding class p*, E = a^2, s = b^2) Darboux integrable?
Vector field in (a, b): b' = W - 5 b^2 (a-2b)^2, a' = -5 a b (a-2b)^2, W = 2 - a^2 - 4ab.
Invariant algebraic curves of degree n are factors of the extactic polynomial E_n.
"""
import sympy as sp, itertools, sys, time
a, b = sp.symbols('a b')
W = 2 - a**2 - 4*a*b
Xb = sp.expand(W - 5*b**2*(a - 2*b)**2)
Xa = sp.expand(-5*a*b*(a - 2*b)**2)
X = lambda f: sp.expand(sp.diff(f, a)*Xa + sp.diff(f, b)*Xb)
for n in (1, 2):
    t = time.time()
    v = [a**i*b**j for i in range(n + 1) for j in range(n + 1 - i)]
    rows = [v]
    for k in range(len(v) - 1):
        rows.append([X(f) for f in rows[-1]])
    M = sp.Matrix(rows)
    det = sp.expand(M.det(method='berkowitz'))
    fl = sp.factor_list(det)
    print('n =', n, 'time %.1fs' % (time.time() - t), 'factors:')
    for f, m in fl[1]:
        print('   ', m, sp.Poly(f, a, b).total_degree(), str(f)[:150])
    sys.stdout.flush()
