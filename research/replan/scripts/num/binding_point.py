import numpy as np
from return_replica import Faces, Ret
F = Faces()
r = Ret(25201/200000, 8053/10000, F)
dl, p = np.array(0.44058), np.array(0.5)
e = 'newTop'
d, C = r.edges()[e]
print("theta=%.6f h=%.4f ell=%.6f x=%.6f y=%.6f kappa=%.6f" % (r.theta, r.h, r.ell, r.x, r.y, r.kappa))
print("edge newTop: d=dp=%.10f, C=newCap(dp)=%.10f   (numeratorCap*dp=%.6f ; (2y-(2-PB)dp)/PL=%.6f)" % (d, C, F.numeratorCap*d, (2*r.y-(2-F.PB)*d)/F.PL))
print("Ebase = %.8f ; budget theta-reserve-Ebase = %.8f ; (3/4) d = %.6f" % (r.Ebase(d,C,dl,p), r.theta-F.reserve-r.Ebase(d,C,dl,p), 0.75*d))
for b in ['old','C','capP']:
    J,N,_ = r.parts(b, dl, p)
    R = N/J
    print("  branch %-4s : J=%.6f N=%.6f R=N/J=%.6f  admitted=%s  need=%.8f" % (b, J, N, R, ('n/a' if b=='old' else bool(r.admitted(b,dl,p))), r.needed(e,b,dl,p)))
Rmax = (r.theta-F.reserve-r.Ebase(d,C,dl,p))/(0.75*d)
print("max tolerated R at this point: %.8f" % Rmax)
# the other edges' worst-case slack for context
from return_replica import slack
worst,_ = slack(r, 401)
for ee,(val,dd,pp,bb) in worst.items():
    print("  edge %-9s worst need %.6f (slack %.2e) at delta=%.3f p=%.3f using %s" % (ee, val, r.theta-F.reserve-val, dd, pp, bb))
# dtheta/dR
print("dtheta/dR approx = (3 d/4)/(1+... ) -- numeric: shift R_C by -0.01 -> need drops by %.6f" % (0.75*d*0.01))
