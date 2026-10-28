"""Cached interpolation tables for the limited-supply count (variant (b)): R_b(nu, x, sigma; kappa, partial)."""
import os, numpy as np
from scipy.interpolate import RegularGridInterpolator
import supply as S

HERE = os.path.dirname(os.path.abspath(__file__))
NUG = np.arange(0.45, 0.8001, 0.0025)
SGG = np.arange(0.005, 0.2001, 0.001)
XG = np.array([0.0, 0.1, 0.2, 0.3, 0.4, 0.45, 0.5])
_cache = {}


def table(kappa, partial):
    key = (round(kappa, 7), bool(partial))
    if key in _cache:
        return _cache[key]
    fn = os.path.join(HERE, 'cache_Rb_k%.7f_p%d.npz' % (kappa, int(partial)))
    if os.path.exists(fn):
        T = np.load(fn)['T']
    else:
        nu, x, sg = np.meshgrid(NUG, XG, SGG, indexing='ij')
        T = S.R_supply(nu.ravel(), x.ravel(), kappa, sg.ravel(), partial)[0].reshape(nu.shape)
        np.savez(fn, T=T)
    f = RegularGridInterpolator((NUG, XG, SGG), T, method='linear', bounds_error=False, fill_value=None)
    _cache[key] = f
    return f


def R_b(nu, x, sigma, kappa, partial):
    nu, x, sigma = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, x, sigma)))
    sg = np.clip(sigma, SGG[0], SGG[-1])
    pts = np.stack([nu, x, sg], axis=-1)
    out = table(kappa, partial)(pts.reshape(-1, 3))
    return out.reshape(nu.shape)


if __name__ == '__main__':
    import time
    t0 = time.time()
    for kap in (0.75, 2 * 4369779 / 5000000 - 1):
        for part in (False, True):
            table(kap, part)
            print('built', kap, part, '%.0fs' % (time.time() - t0), flush=True)
