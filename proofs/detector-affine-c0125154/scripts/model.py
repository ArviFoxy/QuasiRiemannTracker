from poly import *
theta = Q(437423, 500000); h = Q(15903, 20000)
ell = Q(11, 3) - 4*theta; x = 1 + ell - h; y = h - 2*ell; ks = 2*theta - 1
Lam = Q(19312, 4787); B = Q(14200, 14361) - Q(1, 100000)
dm, dp, d0 = h - Q(1, 1000), h + Q(1, 10**10), Q(1, 200)
m_lo = (B - Lam/25)/2; m_hi = Q(847, 2000); gam0 = Q(1, 10000)
REG = (Q(89, 200), Q(97, 200), Q(99, 200), Q(1, 2))
def capacity(d, new): return (2*y - (2 - B)*d)/Lam if new else min(d, 2*y - d)/(6*ks)
D = 3 - p - 2*p/(3*ks); P = 2*(1 - p)*(1 - p/(3*ks)); V = Q(5, 6) - delta
J = V*D + delta*P
def row_old(d, v, new):
    C = capacity(d, new)
    return J*(theta - v - (1+delta)/2 - 13*h/75 + y/2 + ell/2 - ell*delta*p - d*(Q(1,4) - Q(17,50)) + delta*p*C/2) - 3*d*((1 - delta)*J + delta*P*V/2)/4
DN = 3 - p - 4*p/Lam; aN = 2 - 4*p/Lam; cN = 1 - 2*p*B/Lam
JN = V*DN + delta*(1 - p)*aN
NumT = V*DN + delta*(1 - p)*(aN + cN)
def row_new(d, v, new):
    C = capacity(d, new)
    return JN*(theta - v - (1+delta)/2 - 13*h/75 + y/2 + ell/2 - ell*delta*p - d*(Q(1,4) - Q(17,50)) + delta*p*C/2) - 3*d*((1 - delta)*JN + V*delta*(1 - p)*cN)/4
rNnum = aN*NumT + (2*p*B/Lam - p)*JN          # rN * DN * JN
V1 = rNnum - Q(23, 37)*DN*JN                   # rN >= 23/37
V2 = DN*JN - rNnum                             # rN <= 1
V3 = (1 - p)*NumT + (p - 2*p*B/Lam)*JN - (m_lo + gam0)*DN*JN   # mN >= m_lo+gam0
V4 = JN*(-1 + 2*m_hi + 2*p*(1 - 2*m_hi)/(6*Q(3, 4))) + V*(1 - p)*cN   # shortNew(tN) >= Pold(m_hi; 3/4), divided by delta
V5 = Q(3, 2)*JN - NumT                         # tN <= 3/2
# V6: RNew <= countingR ks : c*JN - 2(1-p)cN(V+delta c) >= 0 , c = numc/denc
numc = 2*(1 - p)*(3*ks - p); denc = 3*ks*(3 - p) - 2*p
V6 = numc*JN - 2*(1 - p)*cN*(V*denc + delta*numc)
