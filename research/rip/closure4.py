"""K-wall closure with a 4th rule: the trivial Frobenius bound ||M_W||^2 <= |W| L, i.e. n(x) <= x + 1 - d.
Same grid algorithm as closure.py (rules A, R, I = theta6)."""
import numpy as np
xs = np.linspace(0, 3, 6001)
def theta6(): return np.maximum.reduce([np.ones_like(xs), xs, 5/6 + xs/3, 1/3 + 5*xs/6])
def closure(d, trivial=True, iters=2000):
    n = theta6().copy()
    if trivial: n = np.minimum(n, xs + 1 - d)
    for _ in range(iters):
        old = n.copy()
        g = n - d * xs
        g = np.minimum.accumulate(g[::-1])[::-1]
        n = np.minimum(n, g + d * xs)
        idx = np.where((xs >= 1 - 1e-12) & (xs <= 2 + 1e-12))[0]
        refl = np.interp(2 - xs[idx], xs, n)
        n[idx] = np.minimum(n[idx], np.maximum(xs[idx], xs[idx] - 1 + refl))
        if trivial: n = np.minimum(n, xs + 1 - d)
        if np.max(np.abs(old - n)) < 1e-14: break
    return n
at = lambda n, x: float(np.interp(x, xs, n))
print(' d     | 3 rules: n(0)  n(1)  | +trivial: n(0)  n(.5)  n(1)  n(1.5)  | fixed n(1)=1')
for d in (0.40, 0.45, 0.48, 0.49, 0.499, 0.501):
    a = closure(d, False); b = closure(d, True)
    print('%.3f |        %.4f %.4f |           %.4f %.4f %.4f %.4f' % (d, at(a,0), at(a,1), at(b,0), at(b,.5), at(b,1), at(b,1.5)))
