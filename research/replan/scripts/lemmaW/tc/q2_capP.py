import time
from fractions import Fraction as Fr
import pr86
base = pr86.Cfg()
def run(label, cfg, anchor=8739400):
    t0=time.time()
    t = pr86.theta_star(cfg, anchor=anchor, lo=8700000)
    print('%-76s theta* = %s  %s [%.1fs]' % (label, None if t is None else '%.7f' % (t/1e7), '' if t is None else pr86.report(cfg,t), time.time()-t0), flush=True)
    return t
BN = (Fr(873,1000),Fr(806,1000),Fr(467,1000),Fr(1725,10000))   # widen ell bound to avoid the box artefact (reported separately)
for win in ('collet','lemmaW'):
    for capP in (Fr(31,500), Fr(7,100), Fr(75,1000), Fr(8,100), Fr(85,1000), Fr(9,100), Fr(9999,100000)):
        run('%s windows, physical cap capP=%.4f (Pcap branch, numerator cap 0.06)' % (win, float(capP)), base.copy(windows=win, capP=capP, bounds=BN))
