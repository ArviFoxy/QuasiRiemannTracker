"""Sub-square-root selection: the three-word joint count (PR 93's minimax) with a general selected-norm exponent g(w).

Rows: a family of sextic-type characters of conductor <= Y.  A word of length L = Y^w is "saturated" on a row when its
normalised square is >= L^nu.  If the selected norm over the rows is Y^{g(w)} (log base Y), the rows where the word is
saturated number <= Y^{g(w) - nu w}.  PR 93's minimax (WordCount.lean): the count is
    max_{0<=r<=1, 0<=m<=1/2, r+m>=1} min(env(r), env(2m), env(r+m)),  env(w) = g(w) - nu w.
Choices of g:
  ideal : max(w, 1 - d + d w)                      (PR 93's fixed point; proven only for d > 1/2)
  plain : sextic sieve  max(1, w, 5/6 + w/3, 1/3 + 5w/6)           (no selection used)
  amp1  : min_xi [ plain(w + xi) - d xi ]          (one amplification by the selected slot, against the sextic sieve)
[model; numerical]"""
import numpy as np
import sys


def plain(w):
    return np.maximum.reduce([np.ones_like(w), w, 5 / 6 + w / 3, 1 / 3 + 5 * w / 6])


_WG = np.linspace(0, 2, 2001)


def amp1(w, d, xis=np.linspace(0, 4, 4001)):
    """one-step amplification, tabulated on a 1-D grid of w and interpolated"""
    key = round(d, 9)
    tab = _AMP.get(key)
    if tab is None:
        tab = np.array([(plain(x + xis) - d * xis).min() for x in _WG])
        _AMP[key] = tab
    return np.interp(np.asarray(w), _WG, tab)


_AMP = {}


def ideal(w, d):
    return np.maximum(w, 1 - d + d * w)


def count(g, nu, n=401):
    r = np.linspace(0, 1, n)[:, None]
    m = np.linspace(0, 0.5, n)[None, :]
    ok = (r + m >= 1)
    env = lambda w: g(w) - nu * w
    v = np.minimum(np.minimum(env(r), env(2 * m)), env(r + m))
    v = np.where(ok, v, -np.inf)
    i = np.unravel_index(np.argmax(v), v.shape)
    return v.max(), float(r[i[0], 0]), float(m[0, i[1]])


if __name__ == '__main__':
    for nu in (0.452, 0.50, 0.55, 0.60, 0.65):
        d = nu
        ci = count(lambda w: ideal(w, d), nu)
        cp = count(plain, nu)
        ca = count(lambda w: amp1(w, d), nu)
        J = 3 * (1 - d) * (1 - nu) / (3 - nu - 2 * d)
        print('nu = d = %.3f  ideal %.4f (J formula %.4f)  plain sextic %.4f  one-step amplified %.4f' % (nu, ci[0], J, cp[0], ca[0]))
