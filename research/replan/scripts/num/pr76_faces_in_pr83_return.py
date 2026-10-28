import copy
from return_sens import theta_min, show
from return_replica import Faces
F0=Faces()
def mk(CB,CL,Ccap,PB,PL,Pcap,ncap):
    F=copy.deepcopy(F0); F.CB=CB;F.CL=CL;F.Ccap=Ccap;F.PB=PB;F.PL=PL;F.Pcap=Pcap;F.numeratorCap=ncap; return F
print("Hypothetical: PR76's final faces fed to PR83's return replica (PR76's actual return differs: 6 edges, other literals)")
for ncap in [0.045, 0.054]:
    show("PR76 faces, numeratorCap=%.3f" % ncap, mk(0.9677508807835582,2.911203842943183,0.0549989,0.9718662931671764,3.000002018800438,0.0549989,ncap))
print("PR83 native-chain end face as final face (0.9999,2.58,cap .12), P cap .062, ncap .06")
show("bootstrapFace as final", mk(0.9999,2.58,0.12,0.9999-1e-7,2.581,0.062,0.06))
print("PR83 final")
show("final G(.9934,2.45,.1)", F0)
