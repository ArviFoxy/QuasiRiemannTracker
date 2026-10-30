"""K-wall closure with a corrected initial bound: diagonal (max(1,x)) up to x = X0 (Dunn-Radziwill-type:
3/5 for prime vectors, 5/7 under GRH-strength twisted prime sums), Theta6 beyond. Also the 'diluted bias'
initial bound for thin W: n(x) <= max(x, 1, rank-one bias diluted: 7/6 - d + ...) is tested as variant B:
init_B(x) = max(x, 1, Theta6(x) - d) (bias part diluted by |W|/|F| = B^-d)."""
import numpy as np
xs = np.linspace(0, 3, 6001)
th6 = np.maximum.reduce([np.ones_like(xs), xs, 5/6 + xs/3, 1/3 + 5*xs/6])
def closure(d, init, iters=3000):
    n = init.copy()
    for _ in range(iters):
        old = n.copy()
        g = n - d * xs; g = np.minimum.accumulate(g[::-1])[::-1]; n = np.minimum(n, g + d * xs)
        idx = np.where((xs >= 1 - 1e-12) & (xs <= 2 + 1e-12))[0]
        refl = np.interp(2 - xs[idx], xs, n)
        n[idx] = np.minimum(n[idx], np.maximum(xs[idx], xs[idx] - 1 + refl))
        n = np.minimum(n, init)
        if np.max(np.abs(old - n)) < 1e-14: break
    return n
at = lambda n, x: float(np.interp(x, xs, n))
for d in (0.45, 0.48, 0.49):
    for X0 in (0.5, 0.6, 5/7, 0.8, 0.9, 0.96, 1.0):
        init = np.where(xs <= X0, np.maximum(1.0, xs), th6)
        n = closure(d, init)
        print('d=%.2f  diagonal up to x=%.3f:  n(0.96)=%.4f  n(1)=%.4f   [fixed point n(0.96)=%.4f]' % (d, X0, at(n, .96), at(n, 1), 1 - d + d*.96))
    initB = np.maximum.reduce([np.ones_like(xs), xs, th6 - d])
    n = closure(d, initB)
    print('d=%.2f  diluted-bias init max(1,x,Theta6-d): n(0.96)=%.4f n(1)=%.4f' % (d, at(n,.96), at(n,1)))
