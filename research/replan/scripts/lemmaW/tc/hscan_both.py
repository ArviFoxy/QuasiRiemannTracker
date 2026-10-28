# h scan on PR 86's faces, Collet-structure vs Lemma W (six branches), 1e-9 resolution at fixed h
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best
base = pr86.Cfg()
six = ['old','C','Ccap','C-7','P','Pcap']
def job(a):
    h, win = a
    cfg = base.copy(windows=win, branches=six if win == 'lemmaW' else ['old','C','Pcap'])
    r = best.theta_best(cfg, unit=10**9, anchor=874100000, lo=873900000, step=1000, maxstep=200, hfix=h)
    return a, None if r is None else r[0]/1e9
if __name__ == '__main__':
    hs = [Fr(x, 10000) for x in (8030, 8035, 8040, 8045, 8050, 8051, 8052)]
    jobs = [(h, w) for h in hs for w in ('collet', 'lemmaW')]
    with Pool(4) as p: res = dict(p.map(job, jobs))
    for h in hs:
        print('h=%.4f  Collet-structure %.9f   Lemma W %.9f   diff %+.1e' % (float(h), res[(h,'collet')], res[(h,'lemmaW')], res[(h,'lemmaW')] - res[(h,'collet')]))
