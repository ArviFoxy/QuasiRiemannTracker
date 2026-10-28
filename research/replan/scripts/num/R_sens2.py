import numpy as np
from scipy.optimize import brentq
from return_replica import Faces, Ret
from return_opt import worst_need

class RetShift(Ret):
    """Hypothetical: count ratio R=N/J on branches C and capP lowered by dR *in the margin only*
    (admission guards untouched, so the natural-tail floor guard still uses the true N)."""
    def __init__(self, c, h, F, dR, floor_clip=True):
        super().__init__(c,h,F); self.dR = dR; self.floor_clip=floor_clip
    def needed(self, e, b, dl, p):
        d,C = self.edges()[e]
        J,N,_ = self.parts(b,dl,p)
        R = N/J
        if b in ('C','capP'):
            R = R - self.dR
            if self.floor_clip:
                # natural-tail floor (admission guard 10): R >= 1-2*dl*naturalM-2*dl*p*sMinus
                floor = 1-2*dl*self.naturalM-2*dl*p*self.F.sMinus
                R = np.maximum(R, floor)
        return self.Ebase(d,C,dl,p)+0.75*d*R

F = Faces()
def theta_min(dR, h=0.8053, clip=True):
    def f(c):
        r = RetShift(c,h,F,dR,clip)
        val,e,dl,p,b = worst_need(r,n=241,refine=False)
        return (r.theta-F.reserve)-val
    root = brentq(f, 0.115, 0.145, xtol=1e-9)
    return 1-root
base = theta_min(0.0)
print("baseline theta_min(h=.8053) = %.7f" % base)
for dR in [0.002,0.005,0.0075,0.01,0.02]:
    th = theta_min(dR)
    print("count ratio R lowered by %.4f on C/capP (clipped at natural-tail floor) -> theta_min=%.7f (delta %+.2e, ratio %.3f)" % (dR, th, th-base, (th-base)/dR))
# natural-tail floor at the binding point
nM = (1-4.5*0.03)/2
dl,p = 0.4406,0.5
print("natural-tail floor R at binding point = %.5f ; R_C there = 0.61521" % (1-2*dl*nM-2*dl*p*0.03))
