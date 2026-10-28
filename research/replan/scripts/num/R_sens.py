import numpy as np
from scipy.optimize import brentq
import return_replica as rr
from return_replica import Faces, Ret
from return_opt import worst_need

# Hypothetical improvement of the count: subtract dR from R=N/J for branch C and capP only on the whole domain
class RetShift(Ret):
    def __init__(self, c, h, F, dR):
        super().__init__(c,h,F); self.dR = dR
    def parts(self, b, dl, p):
        J,N,q = super().parts(b,dl,p)
        if b in ('C','capP'):
            N = N - self.dR*J
        return J,N,q

F = Faces()
def theta_min(dR, h=0.8053):
    def f(c):
        r = RetShift(c,h,F,dR)
        val,e,dl,p,b = worst_need(r,n=241,refine=False)
        return (r.theta-F.reserve)-val
    root = brentq(f, 0.118, 0.14, xtol=1e-9)
    return 1-root
base = theta_min(0.0)
print("baseline theta_min(h=.8053) = %.7f" % base)
for dR in [0.002,0.005,0.01,0.02]:
    th = theta_min(dR)
    print("lower count R on C/capP branches by %.3f -> theta_min = %.7f  (delta %.2e ; ratio %.3f)" % (dR, th, th-base, (th-base)/dR))
