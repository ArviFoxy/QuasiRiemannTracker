import time
from fractions import Fraction as Fr
import pr86
base = pr86.Cfg()
def run(label, cfg, anchor=8739400):
    t0=time.time()
    t = pr86.theta_star(cfg, anchor=anchor, lo=8700000)
    print('%-86s theta* = %s  %s [%.1fs]' % (label, None if t is None else '%.7f' % (t/1e7), '' if t is None else pr86.report(cfg,t), time.time()-t0), flush=True)
    return t
BN = (Fr(873,1000),Fr(806,1000),Fr(467,1000),Fr(1725,10000))
allb = ['old','C','Ccap','C-7','P','Pcap']
for win in ('collet','lemmaW'):
    for h in (Fr(8051,10000), Fr(80525,100000)):
        run('%s, all six branches, h=%s' % (win, float(h)), base.copy(windows=win, branches=allb, h=h, bounds=BN))
# very rough: what is the floor of the C-branch return itself? use windows off (pointwise-optimistic) by giving huge freedom: lemmaW + wC=capC
