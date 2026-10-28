import numpy as np, copy
from return_sens import theta_min, margin, show
from return_replica import Faces
F0 = Faces()
print("--- count face only (physical face fixed at P=(.9933999,2.451,.062))")
for L in [2.45,2.40,2.35,2.30]:
    F=copy.deepcopy(F0); F.CL=L; show("C: L=%.2f" % L, F)
for B in [0.9934,0.996,0.998]:
    F=copy.deepcopy(F0); F.CB=B; show("C: B=%.4f" % B, F)
print("--- physical face only (count face fixed at C=(.9934,2.45,.09999))")
for L in [2.451,2.40,2.35,2.30]:
    F=copy.deepcopy(F0); F.PL=L; show("P: L=%.3f" % L, F)
for B in [0.9933999,0.996,0.998]:
    F=copy.deepcopy(F0); F.PB=B; show("P: B=%.7f" % B, F)
