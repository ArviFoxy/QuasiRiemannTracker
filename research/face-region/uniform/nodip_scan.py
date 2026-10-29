"""Along the eta-curve (parametrised by the ray q = 0.999 L/(6B - L)): margins of the scalar conditions of the
generator lemma in the NO-DIP form, for a fixed selection (A, D), every step h in (0, h0] (checked at h0 and h0/50)
and slopes s0 at both ends of the window [sigma + mu, sigma + mu + ds].

No-dip form (HighCore.gamma_lower): Gamma(v, q(v)) >= q_min * m0 for all v when m0 >= 0 and A*C(q0) <= q_min*beta,
with m0 = (Lam0 - 1 [+ y])(s0 - sigma(q0)) and beta = the v-coefficient after the Lipschitz bound of sigma."""
import sys
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from conditions import cond, cond_1d, basics, sigma_w, y_of_w, R_of
d = 0.999
def q_of(B, L): return d*L/(6*B - L)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
def sigma(B, L): k = kappa(min(q_of(B, L), 0.75)); return (B - k)/(L - k)
eta, mu, h0, A, D, ds = (float(x) for x in sys.argv[1:7])
f = lambda L, y: [(y[0] - (kappa(min(q_of(y[0], L), 0.75)) - eta))/(L - (kappa(min(q_of(y[0], L), 0.75)) - eta))]
sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
Bc = lambda L: float(sol.sol(L)[0])

def nodip(B0, L0, h, s0, which):
    vmax, E0, q0, qmin, umax = basics(B0, L0, h, s0, A, D)
    Qs = np.linspace(qmin, q0, 201)
    sq = sigma_w(5 - 6*Qs, B0, L0)
    Ls = np.max(np.abs(np.gradient(sq, Qs)))
    if which == 12:
        m0 = (L0 - 1)*(s0 - sigma_w(5 - 6*q0, B0, L0))
        beta = (L0 - 1 - h) - (L0 - 1)*Ls*q0*h*D/E0
        C = 6*q0*R_of(5 - 6*q0, B0, L0) - q0 - 1
    else:
        y0 = y_of_w(5 - 6*q0); ymax = y_of_w(5 - 6*qmin)
        m0 = (L0 - 1 + y0)*(s0 - sigma_w(5 - 6*q0, B0, L0))
        beta = (L0 - 1 - h + y0) - (L0 - 1 + ymax)*Ls*q0*h*D/E0
        C = max(5*q*(1 - y_of_w(5 - 6*q)) - 1 for q in Qs)
    return m0, qmin*beta - A*C, qmin*m0

rows = []
qtop = q_of(Bc(2.5715), 2.5715) - 1e-7
for q in np.linspace(qtop, 0.5015, 40):
    L0 = brentq(lambda L: q_of(Bc(L), L) - q, 1.90, 2.5715); B0 = Bc(L0)
    for h in (h0, h0/50):
        for s0 in (sigma(B0, L0) + mu, sigma(B0, L0) + mu + ds):
            o = cond(B0, L0, h, s0, A, D); o.pop('V12'); o.pop('beta'); o.pop('m0')
            o.update(cond_1d(B0, L0, h, s0, A, D))
            for w in (12, 10):
                m0, cnd, r = nodip(B0, L0, h, s0, w)
                o['m0_%d' % w] = m0; o['nodip_%d' % w] = cnd; o['r_%d' % w] = r
            rows.append((q, L0, h, s0, o))
keys = list(rows[0][4].keys())
print('eta=%g mu=%g h0=%g A=%g D=%g ds=%g; %d rows' % (eta, mu, h0, A, D, ds, len(rows)))
for k in keys:
    vals = [(r[4][k], r[0], r[2]) for r in rows]
    m = min(vals)
    print('  %-12s min %+.3e at q=%.4f h=%.1e   (max %+.3e)' % (k, m[0], m[1], m[2], max(v[0] for v in vals)))
