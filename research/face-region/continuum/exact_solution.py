import numpy as np
from scipy.integrate import solve_ivp, quad
def kap_r(r):
    q = min(0.999/(6*r - 1), 0.75); return 4*(5 - 3*q)/(25 - 18*q)
def G(r0, r1): return quad(lambda t: 1/((1 - t)**2*kap_r(t)), r0, r1, epsabs=1e-14, epsrel=1e-14)[0]
# closed antiderivative for q < 3/4 (d = 0.999):  kappa = 4(30r - a)/(150r - b), a = 5 + 3d, b = 25 + 18d
d = 0.999; a = 5 + 3*d; b = 25 + 18*d
def Gc(r):
    # 1/((1-r)^2 kappa) = (150r - b)/(4 (30r - a)(1-r)^2) ; partial fractions in u = 1-r
    # (150r - b)/((30r - a)(1-r)^2) = A1/(1-r)^2 + A2/(1-r) + A3/(30r - a)
    A1 = (150 - b)/(30 - a)                     # at r = 1
    A3 = (150*a/30 - b)/((1 - a/30)**2)         # at r = a/30
    # match the r -> infinity behaviour: numerator degree 1, denominator degree 3 -> coefficient of 1/r^2:
    # A2/(1-r) + A3/(30r) ~ (-A2 + A3/30)/r  must vanish  =>  A2 = A3/30
    A2 = A3/30
    return (A1/(1 - r) - A2*np.log(1 - r) + A3/30*np.log(30*r - a))/4
B0, L0 = 0.99999, 2.5715
r0 = B0/L0
def kap(B, L): return kap_r(B/L)
sol = solve_ivp(lambda L, y: [(y[0] - kap(y[0], L))/(L - kap(y[0], L))], [L0, 1.92], [B0], method='DOP853',
                rtol=1e-13, atol=1e-15, dense_output=True)
for L in [2.5, 2.3, 2.1, 1.95, 1.926072]:
    B = float(sol.sol(L)[0]); rr = B/L
    lhs = 1/(L - B)
    rhs_q = 1/(L0 - B0) + G(r0, rr)
    rhs_c = 1/(L0 - B0) + Gc(rr) - Gc(r0)
    print('Lam=%.6f B=%.10f 1/(Lam-B)=%.12f quad=%.12f closed=%.12f' % (L, B, lhs, rhs_q, rhs_c))
rf = (0.5 + d)/3
Zf = 1/(L0 - B0) + Gc(rf) - Gc(r0)
Lf = 1/((1 - rf)*Zf)
print('floor face from the formula: Lam_f = %.8f  B_f = %.8f' % (Lf, rf*Lf))
