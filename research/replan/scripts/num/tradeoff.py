import copy
from return_sens import theta_min, margin, show
from return_replica import Faces
F0=Faces()
def mk(B,L,cap=9999/100000):
    F=copy.deepcopy(F0); F.CB=B; F.CL=L; F.Ccap=cap; F.PB=B-1e-7; F.PL=L+0.001; return F
print("--- trade-off along the density crossing (dB/dL ~ 0.05 .. 0.06)")
for (B,L) in [(0.9934,2.45),(0.9899,2.40),(0.9865,2.35),(0.9831,2.30),(0.9800,2.25),(0.9959,2.50),(0.9999,2.58)]:
    show("B=%.4f L=%.2f" % (B,L), mk(B,L))
