import copy
from return_sens import theta_min, show
from return_replica import Faces
F0=Faces()
def mk(B,L,Ccap,Pcap,ncap):
    F=copy.deepcopy(F0); F.CB=B;F.CL=L;F.Ccap=Ccap;F.PB=B+0.00411 if False else B; F.PL=L+(0.0888 if False else 0.001);F.Pcap=Pcap;F.numeratorCap=ncap; return F
# decomposition with PR83-style P faces (P = C face with tiny offsets)
for (Ccap,Pcap,ncap,lab) in [(0.0549989,0.0549989,0.045,"PR76 caps (.055/.055, ncap .045)"),(0.09999,0.062,0.06,"PR83 caps (.09999/.062, ncap .06)")]:
    print("###",lab)
    for B in [0.96775,0.9999]:
        for L in [2.9112,2.58]:
            show("B=%.5f L=%.4f" % (B,L), mk(B,L,Ccap,Pcap,ncap))
