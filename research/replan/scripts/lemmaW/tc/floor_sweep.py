import json
from multiprocessing import Pool
from fractions import Fraction as Fr
from scipy.optimize import brentq
import pr86, best, ode_faces as OF
BAR = 0.8739358
six = ['old','C','Ccap','C-7','P','Pcap']
PH = (OF.frac(OF.B_ode(2.38)), OF.frac(2.38))
def wall_L(f):
    return brentq(lambda L: OF.q_of(OF.B_ode(L), L) - f, 2.02, 2.3415, xtol=1e-12)
def job(f):
    L = wall_L(f)
    fc = (OF.frac(OF.B_ode(L)), OF.frac(L))
    cfg = pr86.Cfg(windows='lemmaW', branches=six, BC=fc[0], LC=fc[1], BP=PH[0], LP=PH[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    cfg1 = cfg.copy(BP=fc[0], LP=fc[1])
    r1 = best.theta_best(cfg1, unit=10**9, anchor=873960000, lo=873900000, step=2000, maxstep=200)
    return f, L, OF.B_ode(L), r[0]/1e9, (r1[0]/1e9 if r1 else float('nan'))
if __name__ == '__main__':
    fl = [0.65, 0.64, 0.63, 0.62, 0.61, 0.60, 0.59, 0.58, 0.56]
    with Pool(4) as p: res = p.map(job, fl)
    print('floor  wall L   B_ode     theta*(split: C at wall, P at L=2.38)  gap     theta*(single face at wall)  gap')
    for f, L, B, t, t1 in res:
        print('%.2f  %.5f  %.7f   %.9f  %+.2e     %.9f  %+.2e' % (f, L, B, t, t-BAR, t1, t1-BAR))
