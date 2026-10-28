"""Greedy density chain with the Lean-faithful marked HIGH gate (float replica of PR 83 `HybridGates`; second generation).

Gates (Source/HybridGates.lean of PR 83 / arvi_density, 14 incl. the floor), child (B, L) = (B0 - s0 dL, L0 - dL), cap c = 0.1:
    q_lower, q_upper, q_floor, H_lower, retained_cap, retained_width, low_per_excess_width, high_at_q (**replaced**),
    high_density_derivative, principal, second_ref, second_diag, ref_upper, selection_monotonicity.
Marked HIGH gate (task statement / MARKED_LEAF.md sect. 5):
    highJ(B, L, W, u, nu) + gain * gainC(nu, B0, L0, c0, W - u, H) >= eps,   H = 1 - 6u (t = 0),   nu in [dens(v), 3/4]
with gainC the Lean repeated-mark gain (K = 8 copies; gainc.py), `gain=0` switches it off (= PR 83/86 gate).
All float; eps = 1e-6 reserve per gate (PR 86's own reserves are ~1e-5).

nu_mode: 'q'     the gate at nu = dens(v) only (PR 83's high_at_q + monotonicity)
         'range' the gate at 6 values of nu in [dens(v), 3/4] (rigorous: no monotonicity assumed)
"""
import sys, json, time
import numpy as np
import gainc as GC

KAPPA_NAT = 0.75
BOOT = {False: (0.99999, 2.5715, 0.1397), True: (0.99999, 2.56738, 0.1397)}
NUF = np.array([0.0, 0.1, 0.25, 0.45, 0.7, 1.0])
GATES = ['q_lower', 'q_upper', 'q_floor', 'H_lower', 'retained_cap', 'retained_width', 'low', 'high', 'high_deriv',
         'principal', 'second_ref', 'second_diag', 'ref_upper', 'sel_deriv']
SCALEFREE = ('low', 'sel_deriv')


def one_minus_rho(nu):
    return 10.0 * nu / (15.0 - 6.0 * nu)


def highJ(B, L, w, u, nu):
    """Source/HybridGates.lean:62  1 - rho - nu B + nu (L-1) w - (6 (1-rho) - nu - 1) u"""
    m = one_minus_rho(nu)
    return m - nu * B + nu * (L - 1.0) * w - (6.0 * m - nu - 1.0) * u


class Cfg:
    def __init__(self, gain=1.0, floor=0.6, dfac=0.999, boot=False, dL=0.005, eps=1e-6, N=90, cchild=0.1, nu_mode='q',
                 qmax=0.75, c6=6.0, K=8, shift=0.0, pl=(65, 33, 3), bmin_check=True, c0_override=None, qlow=0.5):
        self.gain, self.floor, self.dfac, self.boot, self.dL, self.eps, self.N = gain, floor, dfac, boot, dL, eps, N
        self.cchild, self.nu_mode, self.qmax, self.c6, self.K, self.shift = cchild, nu_mode, qmax, c6, K, shift
        self.pl = pl
        self.bmin_check = bmin_check
        self.c0_override = c0_override
        self.qlow = qlow

    def name(self):
        return 'g%g_f%.2f_b%d_d%.3f_dL%g_%s%s%s' % (self.gain, self.floor, int(self.boot), self.dfac, self.dL, self.nu_mode,
                                                    '' if self.K == 8 else '_K%d' % self.K,
                                                    '' if self.qlow == 0.5 else '_ql%g' % self.qlow)


def marked_gain(cfg, nu, B0, L0, c0, S, Q):
    if cfg.gain == 0.0:
        return np.zeros(np.broadcast(nu, S, Q).shape)
    ng, nr, lv = cfg.pl
    g = GC.gainK(nu, cfg.K, B0, L0, c0, np.maximum(S, 0.0), np.maximum(Q, 0.0), ngrid=ng, nref=nr, levels=lv)
    if cfg.bmin_check and B0 < GC.B_MIN:           # gainC = 0 outside ParentParams
        g = np.zeros_like(g)
    return cfg.gain * g + cfg.shift * np.maximum(Q, 0.0)


def gmin(cfg, B0, L0, c0, s0, A, D, N=None, full=False, nuf=None):
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
    if cfg.nu_mode == 'q':
        nu = qq[:, None]
    else:
        nf = NUF if nuf is None else nuf
        nu = qq[:, None] + (cfg.qmax - qq)[:, None] * nf[None, :]
    J = highJ(B, L, w[:, None], u[:, None], nu)
    gn = marked_gain(cfg, nu, B0, L0, c0, s_ret[:, None], H[:, None])
    Jm = J + gn
    g = dict(q_lower=q - cfg.qlow, q_upper=cfg.qmax - q, q_floor=q - cfg.floor, H_lower=H - 0.9,
             retained_cap=c0 * H - s_ret, retained_width=s_ret, low=(1 - cfg.dfac) * L0 * A / (1 + D * v),
             high=Jm.min(axis=1), high_deriv=25 / 24 * H - (B - (L - 1) * w - u),
             principal=1 - B + (L - 2) * w - 4.5 * u, second_ref=0.05 + 1.5 * (1 - B) + (1.5 * L - 2.5) * w - 4.5 * u,
             second_diag=1 - B + (L - 1) * w - 4 * u, ref_upper=1 / 3 - 2 * w - 3 * u, sel_deriv=A / (1 + D * v) ** 2)
    out = {k: float(val.min()) for k, val in g.items()}
    if full:
        out['_argmin_v_high'] = float(v[np.argmin(g['high'])])
        out['_q0'] = float(q[0])
        out['_Jun0'] = float(J[0, 0])
        out['_gain0'] = float(gn[0, 0])
    return out, vmax


def worst(cfg, B0, L0, c0, s0, A, D, **kw):
    m, vmax = gmin(cfg, B0, L0, c0, s0, A, D, **kw)
    if m is None:
        return -1.0, None, None
    best = None
    bk = None
    for k, x in m.items():
        if k.startswith('_'):
            continue
        if k == 'low' and cfg.dfac >= 1.0:       # 0.999 -> 1: the LOW identity gate is identically 0 (not required)
            continue
        val = (x if x <= 0 else 1.0) if k in SCALEFREE else x - cfg.eps
        if best is None or val < best:
            best, bk = val, k
    return best, bk, m


def s0_min(cfg, B0, L0, c0, A, D, lo=1e-5, hi=None, it=30, guess=None):
    hi = cfg.cchild - 1e-4 if hi is None else hi
    if guess is not None:                        # bracket around a previous solution
        g_lo, g_hi = max(lo, 0.85 * guess), min(hi, 1.25 * guess)
        if worst(cfg, B0, L0, c0, g_hi, A, D)[0] >= 0:
            hi = g_hi
            if worst(cfg, B0, L0, c0, g_lo, A, D)[0] < 0:
                lo = g_lo
                it = 24
    if hi == cfg.cchild - 1e-4 and worst(cfg, B0, L0, c0, hi, A, D)[0] < 0:
        return None
    if lo == 1e-5 and worst(cfg, B0, L0, c0, lo, A, D)[0] >= 0:
        return lo
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        if worst(cfg, B0, L0, c0, mid, A, D)[0] >= 0:
            hi = mid
        else:
            lo = mid
    return hi


def best_step(cfg, B0, L0, c0, guess, s_guess=None, maxeval=70):
    """pattern search over (log A, log D) minimising s0_min; returns (s0, A, D, nevals)"""
    cache = {}

    def f(a, d):
        key = (round(a, 6), round(d, 6))
        if key not in cache:
            s = s0_min(cfg, B0, L0, c0, float(np.exp(a)), float(np.exp(d)), guess=s_guess)
            cache[key] = 1.0 if s is None else s
        return cache[key]

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
    s_guess = None
    rows = []
    t0 = time.time()
    while L0 - cfg.dL >= Lend - 1e-12 and len(rows) < maxsteps:
        r = best_step(cfg, B0, L0, c0, guess, s_guess)
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
            print('L=%.4f B=%.6f s0=%.5f A=%.3f D=%.1f bind=%s [%d ev, %.0fs]' %
                  (L, B, s0, A, D, bk, nev, time.time() - t0), flush=True)
        B0, L0, c0 = B, L, cfg.cchild
        guess = (np.log(A), np.log(D))
        s_guess = s0
        if out:
            json.dump(rows, open(out, 'w'))
    return rows


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--gain', type=float, default=1.0)
    ap.add_argument('--floor', type=float, default=0.6)
    ap.add_argument('--dfac', type=float, default=0.999)
    ap.add_argument('--boot', type=int, default=0)
    ap.add_argument('--dL', type=float, default=0.005)
    ap.add_argument('--nu', default='q')
    ap.add_argument('--Lend', type=float, default=1.80)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    cfg = Cfg(gain=a.gain, floor=a.floor, dfac=a.dfac, boot=bool(a.boot), dL=a.dL, nu_mode=a.nu)
    run(cfg, Lend=a.Lend, out=a.out)
