import time
from fractions import Fraction as Fr
import pr86
base = pr86.Cfg()
def run(label, cfg, anchor=8739700):
    t0=time.time()
    t = pr86.theta_star(cfg, anchor=anchor)
    print('%-64s theta* = %s  %s [%.1fs]' % (label, None if t is None else '%.7f' % (t/1e7), '' if t is None else pr86.report(cfg,t), time.time()-t0), flush=True)
    return t
run('PR86 replica (pr86 edges, old/C/Pcap, BoundsN)', base)
run('  + our 6 edges (capacity-join ds, peak, kink), dMinus>3/4', base.copy(edges='ours'))
run('  + our 6 edges, dMinus>1/2', base.copy(edges='ours', dMinusLower=Fr(1,2)))
run('  + all six branches old,C,Ccap,C-7,P,Pcap', base.copy(branches=['old','C','Ccap','C-7','P','Pcap']))
run('  reserve 1e-9 (our rowFee)', base.copy(reserve=Fr(1,10**9)))
run('  BoundsR (874/1000<theta, h<807/1000, ell<171/1000)', base.copy(bounds=(Fr(874,1000),Fr(807,1000),Fr(467,1000),Fr(171,1000))), anchor=8740000)
run('  dm=0.74 (fixed switch moved)', base.copy(dm=Fr(74,100)))
run('  dm=0.80', base.copy(dm=Fr(80,100)))
