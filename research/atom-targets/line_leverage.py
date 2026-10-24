"""Leverage of the three count lines (I, P, L) on the count R* at delta = 0.4546, p = 1/2,
using the closed-form crossing (FR4/NR2) on a C face. From the round-3 long-moment agent (2026-10-24)."""
from scipy.optimize import brentq
B=0.96226151753982; Lam=3.14813176381578
d=0.4546; p=0.5; V=5/6-d
def R_of(eI=0,eP=0,eL=0):
    def g(R):
        r=(1-d*p-R-eI)/(d*(1-p))
        m=(1-R-eP-2*d*p*B/Lam)/(2*d*(1-2*p/Lam))
        return 1/6+V*(r+m)-eL-R
    return brentq(g,0.3,0.9)
R0=R_of(); e=1e-6
print("R0",R0)
print("dR/d(I shift)",(R0-R_of(eI=e))/e)
print("dR/d(P shift)",(R0-R_of(eP=e))/e)
print("dR/d(L shift)",(R0-R_of(eL=e))/e)
