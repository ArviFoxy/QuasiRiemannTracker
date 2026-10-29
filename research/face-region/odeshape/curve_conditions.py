"""All generator-lemma conditions along the explicit polynomial curve (curve_fit.py), worst case over the slope
window s0 in [beta'(L), beta'(L - h)] and the step h in (0, h0] (sampled), with fixed selection (A, D).
Conditions: one-variable gates (uniform/conditions.py cond_1d), facet conditions P/C and N (cond), and the no-dip
form of the HIGH gate (m0 > 0, A C12(q0) <= q_min beta) for Gamma12, plus the facet order S >= Q sigma(nu)."""
import sys, os, json
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'uniform'))
from conditions import cond, cond_1d, basics, sigma_w, R_of
d = 0.999
def q_of(B, L): return d*L/(6*B - L)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
eta, mu, q_stop, deg, shift, h0, A, D = (float(x) for x in sys.argv[1:9]); deg = int(deg)
Lb, Bb = 2.5715, 0.99999
f = lambda L, y: [(y[0] - (kappa(min(q_of(y[0], L), 0.75)) - eta))/(L - (kappa(min(q_of(y[0], L), 0.75)) - eta))]
sol = solve_ivp(f, [Lb, 1.90], [Bb], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
Bc = lambda L: float(sol.sol(L)[0])
La = brentq(lambda L: q_of(Bc(L), L) - q_stop, 1.90, 2.2)
if len(sys.argv) > 9: La = float(Fr(sys.argv[9]))
Lm, Lh = (La + Lb)/2, (Lb - La)/2
Lg = np.linspace(La, Lb, 4001); t = (Lg - Lm)/Lh
cheb = np.polynomial.chebyshev.Chebyshev.fit(t, sol.sol(Lg)[0] - shift, deg, domain=[-1, 1])
coef = [Fr(round(c*10**12), 10**12) for c in cheb.convert(kind=np.polynomial.Polynomial).coef]
P = np.polynomial.Polynomial([float(c) for c in coef]); dP = P.deriv()
beta = lambda L: P((L - Lm)/Lh); dbeta = lambda L: dP((L - Lm)/Lh)/Lh

def nodip12(B0, L0, h, s0):
    vmax, E0, q0, qmin, umax = basics(B0, L0, h, s0, A, D)
    Qs = np.linspace(qmin, q0, 101)
    Ls = np.max(np.abs(np.gradient(sigma_w(5 - 6*Qs, B0, L0), Qs)))
    m0 = (L0 - 1)*(s0 - sigma_w(5 - 6*q0, B0, L0))
    bet = (L0 - 1 - h) - (L0 - 1)*Ls*q0*h*D/E0
    C = 6*q0*R_of(5 - 6*q0, B0, L0) - q0 - 1
    # facet order S >= Q sigma(nu) for nu >= q(v): worst v small; S - Q sigma >= (s0 - sigma(q0)) + v(1 - A - Ls q0 h D/E0)
    order = 1 - A - Ls*q0*h*D/E0
    return dict(m0=m0, nodip=qmin*bet - A*C, r=qmin*m0, order=order)

worst = {}
where = {}
for L0 in np.linspace(La + 1e-9, Lb, 1501):
    B0 = beta(L0)
    for h in (h0, h0/10, h0/1000):
        if L0 - h < La: continue
        for s0 in (dbeta(L0), dbeta(L0 - h)):
            o = cond(B0, L0, h, s0, A, D); o.pop('V12'); o.pop('beta'); o.pop('m0')
            o.update(cond_1d(B0, L0, h, s0, A, D)); o.update(nodip12(B0, L0, h, s0))
            for k, v in o.items():
                if v < worst.get(k, np.inf): worst[k] = v; where[k] = (L0, h)
print('eta=%g mu=%g q_stop=%g deg=%d shift=%g h0=%g A=%g D=%g; L in [%.6f, %.6f]' % (eta, mu, q_stop, deg, shift, h0, A, D, La, Lb))
print('  beta(Lb) = %.10f ; end face (L, B) = (%.8f, %.8f)' % (beta(Lb), La, beta(La)))
for k in worst:
    print('  %-12s min %+.3e  at L=%.4f h=%.0e' % (k, worst[k], where[k][0], where[k][1]))
json.dump({'La': sys.argv[9] if len(sys.argv) > 9 else str(Fr(La).limit_denominator(10**9)), 'Lb': '5143/2000', 'Lm': str((Fr(sys.argv[9]) + Fr(5143, 2000))/2) if len(sys.argv) > 9 else str(Fr(Lm).limit_denominator(10**9)),
           'coef_t': [str(c) for c in coef], 'eta': eta, 'mu': mu, 'q_stop': q_stop, 'h0': h0, 'A': A, 'D': D},
          open('curve_%d.json' % deg, 'w'), indent=1)
