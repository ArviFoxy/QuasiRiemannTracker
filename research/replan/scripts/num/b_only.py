import copy
from return_sens import show
from return_replica import Faces
F0=Faces()
for B in [0.996,0.998,0.9999]:
    F=copy.deepcopy(F0); F.CB=B; F.PB=B-1e-7
    show("B=%.4f, L=2.45 both faces" % B, F)
