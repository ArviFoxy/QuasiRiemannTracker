import time
from fractions import Fraction as Fr
import pr86
base = pr86.Cfg()
W = base.copy(windows='lemmaW')
def run(label, cfg, anchor=8739000):
    t0=time.time()
    t = pr86.theta_star(cfg, anchor=anchor, lo=8700000)
    print('%-70s theta* = %s  %s [%.1fs]' % (label, None if t is None else '%.7f' % (t/1e7), '' if t is None else pr86.report(cfg,t), time.time()-t0), flush=True)
    return t
print('declared PR86 theta passes with lemmaW windows?', pr86.certifiable(W, why=True))
for hnum in [8030, 8035, 8040, 8045, 8049, 8051]:
    run('Lemma W, PR86 faces (old,C,Pcap), h=%s' % (hnum/10000), W.copy(h=Fr(hnum,10000), bounds=(Fr(873,1000),Fr(806,1000),Fr(467,1000),Fr(172,1000))), anchor=8739000)
