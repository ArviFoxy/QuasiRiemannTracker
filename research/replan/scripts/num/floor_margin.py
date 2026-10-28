import numpy as np
from scipy.optimize import brentq
def fm(c,h):
    theta=1-c; ell=4*c-1/3; x=1+ell-h; y=h-2*ell; dPlus=h+1e-10
    signal=theta-(5/6-x/3-ell/6)
    lhs=4/25*x-3/20-51/100*y+67/100*dPlus-3/20*ell
    return (signal-1/200)-lhs
def ss(c,h):
    ell=4*c-1/3; y=h-2*ell
    return y/2-h*(17/50-1/6)-1/50-7/100
print("at actual: floor_margin slack %.3e ; small_saving slack %.3e" % (fm(25201/200000,8053/10000), ss(25201/200000,8053/10000)))
# largest c (smallest theta) at which floor_margin>=0, per h
for h in [0.800,0.8030,0.8053,0.8060]:
    f=lambda c: fm(c,h)
    try:
        c0=brentq(f,0.10,0.14); print("h=%.4f: floor_margin >=0 iff c <= %.6f  (theta >= %.6f) ; ell<0.171 iff theta>=0.873917" % (h,c0,1-c0))
    except Exception as e: print(h,"no root",e)
