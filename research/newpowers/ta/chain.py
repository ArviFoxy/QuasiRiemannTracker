"""Discrete greedy density chain (Delta L fixed) with a pluggable HIGH ledger (variants.py).
Replica of PR 83 `HybridGates` (14 gates; validated by B2/B3 against PR 86's 46 certified steps) in which
`high_at_q` is replaced by the joint (nu, x) gate  J_x = cs + u - nu (B - (L-2x) w - 2x u) >= 0, nu in [q,3/4].
Start: PR 86 boot face (0.99999, 2.5715, 0.1397) [bootstrapped native barrier: (0.99999, 2.56738, 0.1397)], child cap 0.1.
"""
import sys, json, time
import numpy as np
import variants as V

KAPPA_NAT = 0.75
KAPPA_BOOT = 2 * (4369779 / 5000000) - 1
BOOT = {False: (0.99999, 2.5715, 0.1397), True: (0.99999, 2.56738, 0.1397)}
XS = np.array([0.0, 0.2, 0.35, 0.45, 0.5])
NUF = np.array([0.0, 0.15, 0.4, 0.7, 1.0])
GATES = ['q_lower', 'q_upper', 'q_floor', 'H_lower', 'retained_cap', 'retained_width', 'low', 'high', 'high_deriv',
         'principal', 'second_ref', 'second_diag', 'ref_upper', 'sel_deriv']
SCALEFREE = ('low', 'sel_deriv')


class Cfg:
    def __init__(self, var='pr83', floor=0.6, dfac=0.999, boot=False, dL=0.005, eps=1e-6, N=90, cchild=0.1,
                 xs=XS, nuf=NUF, shift_R=0.0, sigma=None, qmax=0.75, c6=6.0):
        self.var, self.floor, self.dfac, self.boot, self.dL, self.eps, self.N = var, floor, dfac, boot, dL, eps, N
        self.cchild, self.xs, self.nuf, self.shift_R, self.sigma, self.qmax, self.c6 = cchild, xs, nuf, shift_R, sigma, qmax, c6
        self.kappa = KAPPA_BOOT if boot else KAPPA_NAT

    def par(self, B0, L0, c0):
        d = dict(kappa=self.kappa, B0=B0, L0=L0, h0=c0, shift_R=self.shift_R)
        if self.sigma is not None:
            d['sigma'] = self.sigma
        return d


def gmin(cfg, B0, L0, c0, s0, A, D, N=None, full=False):
    """minimum of every gate over the v-grid for the child (B,L) = (B0 - s0 dL, L0 - dL); returns dict, vmax"""
    dL = cfg.dL
    B = B0 - s0 * dL
    L = L0 - dL
    c = cfg.cchild
    vmax = c - s0
    if vmax <= 0:
        return None, vmax
    N = cfg.N if N is None else N
    t = np.linspace(0, 1, N) ** 3
    v = vmax * t
    w = s0 + v
    u = A * v / (1 + D * v)
    E = dL * (1 + D * v) + (cfg.c6 * B0 - L0) * A
    q = cfg.dfac * L0 * A / E
    H = 1 - cfg.c6 * u
    s_ret = w - u
    qq = np.minimum(q, cfg.qmax)
    nu = qq[:, None, None] + (cfg.qmax - qq)[:, None, None] * cfg.nuf[None, :, None]
    x = cfg.xs[None, None, :]
    cs = V.cs(cfg.var, nu, x, s_ret[:, None, None], H[:, None, None], cfg.par(B0, L0, c0))
    J = cs + u[:, None, None] - nu * (B - (L - 2 * x) * w[:, None, None] - 2 * x * u[:, None, None])
    g = dict(q_lower=q - 0.5, q_upper=cfg.qmax - q, q_floor=q - cfg.floor, H_lower=H - 0.9,
             retained_cap=c0 * H - s_ret, retained_width=s_ret, low=(1 - cfg.dfac) * L0 * A / (1 + D * v),
             high=J.min(axis=(1, 2)), high_deriv=25 / 24 * H - (B - (L - 1) * w - u),
             principal=1 - B + (L - 2) * w - 4.5 * u, second_ref=0.05 + 1.5 * (1 - B) + (1.5 * L - 2.5) * w - 4.5 * u,
             second_diag=1 - B + (L - 1) * w - 4 * u, ref_upper=1 / 3 - 2 * w - 3 * u, sel_deriv=A / (1 + D * v) ** 2)
    out = {k: float(val.min()) for k, val in g.items()}
    if full:
        out['_argmin_v_high'] = float(v[np.argmin(g['high'])])
        out['_q0'] = float(q[0])
    return out, vmax


def worst(cfg, B0, L0, c0, s0, A, D):
    m, vmax = gmin(cfg, B0, L0, c0, s0, A, D)
    if m is None:
        return -1.0, None, None
    best = None
    bk = None
    for k, x in m.items():
        val = (x if x <= 0 else 1.0) if k in SCALEFREE else x - cfg.eps
        if best is None or val < best:
            best, bk = val, k
    return best, bk, m


def s0_min(cfg, B0, L0, c0, A, D, lo=1e-5, hi=None, it=34):
    hi = cfg.cchild - 1e-4 if hi is None else hi
    if worst(cfg, B0, L0, c0, hi, A, D)[0] < 0:
        return None
    if worst(cfg, B0, L0, c0, lo, A, D)[0] >= 0:
        return lo
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        if worst(cfg, B0, L0, c0, mid, A, D)[0] >= 0:
            hi = mid
        else:
            lo = mid
    return hi


def best_step(cfg, B0, L0, c0, guess, maxeval=70):
    """pattern search over (log A, log D) minimising s0_min; returns (s0, A, D, nevals)"""
    cache = {}

    def f(a, d):
        key = (round(a, 6), round(d, 6))
        if key not in cache:
            s = s0_min(cfg, B0, L0, c0, float(np.exp(a)), float(np.exp(d)))
            cache[key] = 1.0 if s is None else s
        return cache[key]

    # starting points: warm start + a few generic ones if the warm start is infeasible
    starts = [guess] + [(np.log(a), np.log(d)) for a in (0.6, 0.9, 0.4) for d in (100.0, 400.0, 1500.0)]
    cur = None
    for st in starts:
        fv = f(*st)
        if fv < 0.9:
            cur = (st, fv)
            break
    if cur is None:
        return None
    (a, d), fv = cur
    sa, sd = 0.20, 0.40
    while (sa > 0.012 or sd > 0.025) and len(cache) < maxeval:
        cand = [(a + da * sa, d + dd * sd) for da in (-1, 0, 1) for dd in (-1, 0, 1) if (da, dd) != (0, 0)]
        vals = [(f(*c_), c_) for c_ in cand]
        bv, bc = min(vals)
        if bv < fv - 1e-10:
            a, d = bc
            fv = bv
        else:
            sa *= 0.5
            sd *= 0.5
    return fv, float(np.exp(a)), float(np.exp(d)), len(cache)


def run(cfg, Lend=1.80, out=None, verbose=True, maxsteps=1000, start=None):
    B0, L0, c0 = BOOT[cfg.boot] if start is None else start
    guess = (np.log(0.6), np.log(400.0))
    rows = []
    t0 = time.time()
    while L0 - cfg.dL >= Lend - 1e-12 and len(rows) < maxsteps:
        r = best_step(cfg, B0, L0, c0, guess)
        if r is None or r[0] >= 0.9:
            rows.append(dict(infeasible=True, B0=B0, L0=L0))
            if verbose:
                print('INFEASIBLE from', B0, L0, flush=True)
            break
        s0, A, D, nev = r
        B = B0 - s0 * cfg.dL
        L = L0 - cfg.dL
        _, bk, m = worst(cfg, B0, L0, c0, s0, A, D)
        rows.append(dict(B0=B0, L0=L0, c0=c0, B=B, L=L, s0=s0, A=A, D=D, bind=bk,
                         marg={k: round(x, 7) for k, x in m.items()}))
        if verbose:
            print('L=%.4f B=%.6f s0=%.5f A=%.3f D=%.1f bind=%s q0=%.4f [%d ev, %.0fs]' %
                  (L, B, s0, A, D, bk, gmin(cfg, B0, L0, c0, s0, A, D, full=True)[0]['_q0'], nev, time.time() - t0), flush=True)
        B0, L0, c0 = B, L, cfg.cchild
        guess = (np.log(A), np.log(D))
        if out:
            json.dump(rows, open(out, 'w'))
    return rows


if __name__ == '__main__':
    var = sys.argv[1]
    floor = float(sys.argv[2])
    dfac = float(sys.argv[3])
    boot = bool(int(sys.argv[4]))
    dL = float(sys.argv[5])
    out = sys.argv[6]
    cfg = Cfg(var=var, floor=floor, dfac=dfac, boot=boot, dL=dL)
    run(cfg, out=out)
