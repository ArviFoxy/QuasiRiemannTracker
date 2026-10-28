import numpy as np
from scipy.optimize import brentq
from return_replica import Faces, Ret
from return_opt import worst_need
F = Faces()
def margin(c,h,n=401):
    r = Ret(c,h,F); val,e,dl,p,b = worst_need(r,n=n,refine=True)
    return (r.theta-F.reserve)-val
for h in [0.8040,0.8045,0.8050,0.8053,0.8055,0.8058,0.8060,0.8063]:
    f = lambda c: margin(c,h)
    try:
        root = brentq(f, 0.1255, 0.1268, xtol=1e-10)
        print("h=%.4f  boundary c=%.8f -> theta_min=%.8f" % (h, root, 1-root))
    except Exception as ex:
        print("h=%.4f no root (%s)" % (h, ex))
