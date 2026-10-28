import copy
from return_sens import theta_min
from return_replica import Faces
F0=Faces()
def mk(B,L):
    F=copy.deepcopy(F0); F.CB=B; F.CL=L; F.PB=B-1e-7; F.PL=L+0.001; return F
def th(B,L, hs=None):
    import numpy as np
    return theta_min(mk(B,L), hs=np.linspace(0.800,0.810,21), n=301)[0]
B0,L0=0.9934,2.45
t0=th(B0,L0)
dB=0.002; dL=0.02
tB=(th(B0+dB,L0)-th(B0-dB,L0))/(2*dB)
tL=(th(B0,L0+dL)-th(B0,L0-dL))/(2*dL)
print("theta_min(final face)=%.7f" % t0)
print("d theta/dB = %.4e per unit B ; d theta/dL = %.4e per unit L ; iso-theta slope dB/dL = %.4f" % (tB,tL,-tL/tB))
