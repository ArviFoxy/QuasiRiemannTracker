import numpy as np, copy
from return_sens import theta_min, margin, show
from return_replica import Faces

F0 = Faces()
def mk(B, L, cap, pcap=None, ncap=None):
    F = copy.deepcopy(F0)
    F.CB=B; F.CL=L; F.Ccap=cap
    F.PB=B-1e-7; F.PL=L+0.001
    if pcap is not None: F.Pcap=pcap
    if ncap is not None: F.numeratorCap=ncap
    return F

print("--- face ceiling scan (count cap 0.1, P cap 0.062, numeratorCap 0.06)")
for (B,L) in [(0.9934,2.45),(0.9955,2.40),(0.997,2.35),(0.998,2.30),(0.999,2.25),(0.9995,2.2),(0.9999,2.1),(0.9999,2.0)]:
    show("B=%.4f L=%.2f" % (B,L), mk(B,L,0.1))
print("--- same, larger numeratorCap & physical cap")
for (B,L) in [(0.9934,2.45),(0.9999,2.2),(0.9999,2.0)]:
    show("B=%.4f L=%.2f ncap=.08 pcap=.1" % (B,L), mk(B,L,0.12,pcap=0.1,ncap=0.08))
