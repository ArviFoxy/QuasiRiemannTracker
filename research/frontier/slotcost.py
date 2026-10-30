"""Common slot cost c in the inverse word and the face (LP game + newTop row), banked design.
Inverse word with slot cost ci: z <= 1 - d*r - (2*d*p/ci)*(1-r)  (ci = 2 is the proved word).
Face slot cost: Lambda (proved 2.0001 at the end face)."""
import numpy as np, time
from scipy.optimize import linprog, minimize_scalar
from scipy.interpolate import CubicSpline

def V_of_t(t, d, p, B, L, cap, ci, m_hi=0.5):
    mc = (B - L * cap) / 2; best = -np.inf
    for rp in ('I', 'Lg'):
        for mp in ('cap', 'slope'):
            A = []; b = []
            def le(cr, cm, cz, rhs): A.append([cr, cm, cz]); b.append(rhs)
            if rp == 'I':
                k = d - 2 * d * p / ci          # z <= 1 - 2dp/ci - (d - 2dp/ci) r
                le(k, 0, 1, 1 - 2 * d * p / ci); rlo, rhi = max(t - 0.5, 23 / 37), min(t, 1.0)
            else:
                le(-(5 / 6 - d), 0, 1, 1 / 6); rlo, rhi = max(t - 0.5, 1.0), t
            if rlo > rhi + 1e-15: continue
            if mp == 'cap':
                le(0, 2 * d, 1, 1 - 2 * d * p * cap); mlo, mhi = 0.0, min(mc, m_hi)
            else:
                le(0, 2 * d - 4 * d * p / L, 1, 1 - 2 * d * p * B / L); mlo, mhi = max(mc, 0.0), m_hi
            if mlo > mhi + 1e-15: continue
            le(-1, -1, 0, -t)
            res = linprog(c=[0, 0, -1], A_ub=np.array(A), b_ub=np.array(b),
                          bounds=[(rlo, rhi), (mlo, mhi), (None, None)], method='highs')
            if res.status == 0: best = max(best, -res.fun)
    return best

def count(d, p, B, L, cap, ci):
    f = lambda t: V_of_t(t, d, p, B, L, cap, ci)
    ts = np.linspace(1.0, 1.5, 121); vs = np.array([f(t) for t in ts]); i = int(np.argmin(vs))
    r = minimize_scalar(f, bounds=(ts[max(i - 1, 0)], ts[min(i + 1, len(ts) - 1)]), method='bounded',
                        options={'xatol': 1e-12})
    return min(r.fun, vs[i])

def theta_star(h, B, L, cap, ci, numcap=0.075, p=0.5, reserve=1e-8):
    dls = np.round(np.arange(0.38, 0.5001, 0.005), 4)
    cs = CubicSpline(dls, [count(dd, p, B, L, cap, ci) for dd in dls])
    dl = np.linspace(0.38, 0.50, 24001); cn = cs(dl)
    lo, hi = 0.8725, 0.8745
    for _ in range(60):
        th = (lo + hi) / 2; c = 1 - th; ell = 4 * c - 1 / 3; y = h - 2 * ell; dp = h + 1e-10
        C = min(numcap * dp, (2 * y - (2 - B) * dp) / L)
        row = (0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dp + dl / 2 + dl * p * (ell - C / 2) + 0.75 * dp * cn).max()
        if row > th - reserve: lo = th
        else: hi = th
    return hi

if __name__ == '__main__':
    cap = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
    B, h = 0.99999, 0.8097
    t0 = time.time()
    base = theta_star(h, B, 2.0001, cap(2.0001), 2.0)
    print('banked design, proved costs: theta* = %.8f  (Lean bank 0.87338228)  [%.0fs]' % (base, time.time() - t0))
    for c in (1.995, 1.992, 1.99, 1.985, 1.98):
        both = theta_star(h, B, 2.0001 * c / 2, cap(2.0001), c)
        inv = theta_star(h, B, 2.0001, cap(2.0001), c)
        print('slot cost %.3f: both words %.8f (%+.2e)   inverse only %.8f (%+.2e)' % (c, both, both - base, inv, inv - base))
    print('bar 0.87336198; [%.0fs]' % (time.time() - t0))
