"""dchain_cap.py -- like dchain_amp.py but with a CAPACITY-LIMITED doubled mass ud (absolute, in log_U units):
    u_total(v) = A v/(1+Dv) as in PR83;  the first ud of it is of doubled type (e=2), the rest simple (e=1);  c=6, r=1 for both.
    q(v) = min(3/4, f L0 (u+ud~)/(dL v + (6B0-L0) u)),  ud~ = min(ud, u);  highJ gets +ud~ (extra saving).
(original docstring follows)

dchain_amp.py -- discrete greedy density chain (DeltaL fixed) for a general amplifier (e, c, r)  (R2).

Replica of PR 83 `HybridGates` (B2/dchain.py, mode 'pr83', validated there against PR 86's 46 certified steps),
with the amplifier constants generalised exactly as in the report (section 4):

    dens  q(v) = f * e * L0 * A / ((L0-L)(1+Dv) + (c*B0 - r*L0) * A)            [PR83: f*L0*A/(... + (6B0-L0)A)]
    H = 1 - c*u
    highJ = 1 - rho(q) - q B + q (L-1) w - (c (1-rho(q)) - q r - e) u            [PR83: 6(1-rho) - q - 1]
    retained_cap  = c0 H - (w - r u),  retained_width = w - r u,  high_deriv = 25/24 H - (B - (L-1) w - r u)
    terminal gates (principal, second_ref, second_diag, ref_upper): UNCHANGED per-unit charges (4.5, 4.5, 4, 3)  [hyp]

usage: python3 dchain_amp.py e c r floor Lend out.json [dL]
"""
import sys, json, os
import numpy as np
from scipy.optimize import minimize


def rho(nu):
    return 1 - 10 * nu / (15 - 6 * nu)


GATES = ['q_lower', 'q_upper', 'q_floor', 'H_lower', 'retained_cap', 'retained_width', 'low', 'high_at_q', 'high_deriv',
         'principal', 'second_ref', 'second_diag', 'ref_upper', 'sel_deriv']
SCALEFREE = ('low', 'sel_deriv')
DFAC = float(os.environ.get("DFAC", "0.999"))


UD = float(os.environ.get('UD', '0'))


def gmin(B0, L0, c0, B, L, c, A, D, floor, E_, C_, R_, N=300, dfac=None, qmax=0.75):
    dfac = DFAC if dfac is None else dfac
    s0 = (B0 - B) / (L0 - L); vmax = c - s0
    if vmax <= 0:
        return None, s0, vmax
    t = np.linspace(0, 1, N) ** 3; v = vmax * t
    w = s0 + v; u = A * v / (1 + D * v)
    ud = np.minimum(UD, u)
    num = (L0 - L) * v + (C_ * B0 - R_ * L0) * u
    q = np.minimum(qmax - 2e-6, dfac * L0 * (E_ * u + ud) / np.maximum(num, 1e-300))
    q = np.where(v <= 0, np.minimum(qmax - 2e-6, dfac * L0 * ((E_ + (1.0 if UD > 0 else 0.0)) * A) / ((L0 - L) + (C_ * B0 - R_ * L0) * A)), q)   # LOW holds for every q <= formula; HIGH range [q, 3/4] needs q <= 3/4
    H = 1 - C_ * u
    J = 1 - rho(q) - q * B + q * (L - 1) * w - (C_ * (1 - rho(q)) - q * R_ - E_) * u + ud
    g = dict(q_lower=q - 0.5, q_upper=qmax - q, q_floor=q - floor, H_lower=H - 0.9,
             retained_cap=c0 * H - (w - R_ * u), retained_width=w - R_ * u,
             low=np.where(v > 0, (1 - dfac) * L0 * (E_ * u + ud) / np.maximum(v, 1e-300), (1 - dfac) * L0 * (E_ + (1.0 if UD > 0 else 0.0)) * A), high_at_q=J,
             high_deriv=25 / 24 * H - (B - (L - 1) * w - R_ * u),
             principal=1 - B + (L - 2) * w - 4.5 * u, second_ref=0.05 + 1.5 * (1 - B) + (1.5 * L - 2.5) * w - 4.5 * u,
             second_diag=1 - B + (L - 1) * w - 4 * u, ref_upper=1 / 3 - 2 * w - 3 * u, sel_deriv=A / (1 + D * v) ** 2)
    return {k: float(val.min()) for k, val in g.items()}, s0, vmax


def worst(B0, L0, c0, B, L, c, A, D, floor, eps, E_, C_, R_):
    m, s0, vmax = gmin(B0, L0, c0, B, L, c, A, D, floor, E_, C_, R_)
    if m is None:
        return -1.0, None, None
    best = None; bk = None
    for k, x in m.items():
        val = (x if x <= 0 else 1.0) if k in SCALEFREE else x - eps
        if best is None or val < best:
            best, bk = val, k
    return best, bk, m


def s0_min(B0, L0, c0, dL, c, A, D, floor, eps, E_, C_, R_):
    L = L0 - dL; hi = c - 1e-4
    xs = np.linspace(1e-5, hi, 60)
    ok = [worst(B0, L0, c0, B0 - s * dL, L, c, A, D, floor, eps, E_, C_, R_)[0] >= 0 for s in xs]
    if not any(ok):
        return None
    i = ok.index(True)
    if i == 0:
        return xs[0]
    a, b = xs[i - 1], xs[i]
    for _ in range(30):
        mid = 0.5 * (a + b)
        if worst(B0, L0, c0, B0 - mid * dL, L, c, A, D, floor, eps, E_, C_, R_)[0] >= 0:
            b = mid
        else:
            a = mid
    return b


def best_step(B0, L0, c0, dL, c, floor, eps, E_, C_, R_, guess):
    def f(x):
        A = np.exp(x[0]); D = np.exp(x[1])
        s = s0_min(B0, L0, c0, dL, c, A, D, floor, eps, E_, C_, R_)
        return 1.0 if s is None else s
    best = None
    starts = [guess] + [(np.log(a), np.log(d)) for a in (0.4, 0.6, 0.9) for d in (30, 150, 400)]
    for st in starts:
        r = minimize(f, np.array(st), method='Nelder-Mead', options=dict(xatol=2e-4, fatol=1e-9, maxiter=120))
        if best is None or r.fun < best.fun:
            best = r
        if st is guess and best.fun < 0.9:
            break
    return best.fun, float(np.exp(best.x[0])), float(np.exp(best.x[1]))


def run(E_, C_, R_, floor, dL, Lend, out, eps=1e-6):
    B0, L0, c0 = 0.99999, 2.5715, 0.1397
    guess = (np.log(0.6), np.log(400.0))
    rows = []
    while L0 - dL >= Lend - 1e-12:
        s, A, D = best_step(B0, L0, c0, dL, 0.1, floor, eps, E_, C_, R_, guess)
        if s >= 0.9:
            rows.append(dict(infeasible=True, B0=B0, L0=L0)); print('INFEASIBLE from', B0, L0, flush=True); break
        B = B0 - s * dL; L = L0 - dL
        w_, bk, m = worst(B0, L0, c0, B, L, 0.1, A, D, floor, eps, E_, C_, R_)
        rows.append(dict(B0=B0, L0=L0, B=B, L=L, s0=s, A=A, D=D, binding=bk,
                         gates={k: round(x, 6) for k, x in m.items()}))
        print('L=%.4f B=%.6f s0=%.5f A=%.3f D=%.1f bind=%s' % (L, B, s, A, D, bk), flush=True)
        B0, L0, c0 = B, L, 0.1; guess = (np.log(A), np.log(D))
        json.dump(rows, open(out, 'w'))
    return rows


if __name__ == '__main__':
    e, c, r = map(float, sys.argv[1:4]); floor = float(sys.argv[4]); Lend = float(sys.argv[5]); out = sys.argv[6]
    dL = float(sys.argv[7]) if len(sys.argv) > 7 else 0.005
    run(e, c, r, floor, dL, Lend, out)
