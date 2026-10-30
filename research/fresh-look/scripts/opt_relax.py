import numpy as np, sys, time
from scipy.optimize import differential_evolution, minimize
from relax import Model, faces_of
mode = sys.argv[1]  # 'merged' guards or 'relaxed'
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
d = np.round(np.arange(0.30, 0.66, 0.0005), 6)
p = np.round(np.array([0.35, 0.40, 0.43, 0.45, 0.47, 0.48, 0.49, 0.495, 0.5]), 6)
M = Model(d, p)
CAPS = 0.1 + 0.06 * (5143 / 2000 - 2.02)
nmC = (1 - 4.5 * 0.03) / 2
def f(x):
    cB, cL, cCap, w, pCap = x
    fc = faces_of(cB, cL, cCap, w, 0.99999, 2.02, pCap)
    if mode == 'merged':
        return M.theta_star(fc, nm_override=nmC, upper_t=1.2499)[0]
    return M.theta_star(fc, sig=1e-4)[0]
bounds = [(0.95, 0.99999), (2.02, 2.4), (0.06, CAPS), (0.0, 0.07), (0.06, CAPS)]
t = time.time()
r = differential_evolution(f, bounds, seed=seed, popsize=16, maxiter=120, tol=1e-14, polish=False, updating='immediate')
r2 = minimize(f, r.x, method='Nelder-Mead', options=dict(xatol=1e-8, fatol=1e-13, maxiter=800, adaptive=True))
x = r2.x
fc = faces_of(*x[:4], 0.99999, 2.02, x[4])
Mf = Model(np.round(np.arange(0.28, 0.70, 0.0001), 6), np.round(np.concatenate([np.arange(0.30, 0.49, 0.005), [0.49, 0.495, 0.499, 0.5]]), 6))
res = Mf.theta_star(fc, nm_override=nmC, upper_t=1.2499) if mode == 'merged' else Mf.theta_star(fc, sig=1e-4)
print(mode, 'seed', seed, 'theta* = %.9f' % r2.fun, 'fine %.9f' % res[0], res[1], 'x =', np.round(x, 6), '%.0fs' % (time.time() - t), flush=True)
