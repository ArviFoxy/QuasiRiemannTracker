import sys, time
from fractions import Fraction as Fr
import pr86
cfg = pr86.Cfg()
t0=time.time()
t = pr86.theta_star(cfg)
print('PR86 replica (Collet windows, 4 pr86 edges, branches old/C/Pcap, BoundsN, h=8051/10000): theta* = %d/1e7 = %.7f  [%.1fs]' % (t, t/1e7, time.time()-t0))
print('  theta*-1e-7 fails:', pr86.report(cfg, t))
print('  submitted 4369779/5000000 = 0.8739558; margin submitted - theta* = %.1e' % (0.8739558 - t/1e7))
