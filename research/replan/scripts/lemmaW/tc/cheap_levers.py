import json
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
B46, L46, B38, L38 = Fr(chain[46]['B']), Fr(chain[46]['L']), Fr(chain[38]['B']), Fr(chain[38]['L'])
base = pr86.Cfg(BC=B46, LC=L46, BP=B38, LP=L38)
six = ['old','C','Ccap','C-7','P','Pcap']
CASES = [
 ('reference: role split 46/38, Collet structure', base),
 ('same, Lemma W six-branch', base.copy(windows='lemmaW', branches=six)),
 ('count cap 0.0857 (= width at the crossing)', base.copy(capC=Fr(857,10000))),
 ('count cap 0.0870', base.copy(capC=Fr(87,1000))),
 ('count cap 0.0900', base.copy(capC=Fr(9,100))),
 ('count cap 0.0800 (below crossing width)', base.copy(capC=Fr(8,100))),
 ('Lemma W + count cap 0.0800', base.copy(capC=Fr(8,100), windows='lemmaW', branches=six)),
 ('Lemma W + count cap 0.0700', base.copy(capC=Fr(7,100), windows='lemmaW', branches=six)),
 ('Lemma W + count cap 0.0600', base.copy(capC=Fr(6,100), windows='lemmaW', branches=six)),
 ('physical cap 0.0999 (numerator cap 0.06)', base.copy(capP=Fr(9999,100000))),
 ('numerator cap sP=0.0605/phys cap 0.062', base.copy(sP=Fr(605,10000))),
 ('numerator cap sP=0.07/phys cap 0.071', base.copy(sP=Fr(7,100), capP=Fr(71,1000))),
 ('numerator cap sP=0.05 (clip binds)', base.copy(sP=Fr(5,100))),
 ('switch dm=0.75005', base.copy(dm=Fr(75005,100000))),
 ('switch dm=0.78', base.copy(dm=Fr(78,100))),
 ('mMinus=0.30 (Collet structure)', base.copy(mMinus=Fr(3,10))),
 ('mMinus=0.40', base.copy(mMinus=Fr(2,5))),
 ('reserve 1e-9 instead of 1e-8', base.copy(reserve=Fr(1,10**9))),
]
def job(i):
    lab, cfg = CASES[i]
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    return i, None if r is None else r[0], None if r is None else best.why(cfg, r[0]-1, unit=10**9)
if __name__ == '__main__':
    with Pool(4) as p:
        res = {i: (t, w) for i, t, w in p.imap_unordered(job, range(len(CASES)))}
    t0 = res[0][0]
    for i, (lab, cfg) in enumerate(CASES):
        t, w = res[i]
        print('%-50s theta*=%s  shift vs ref %s  %s' % (lab, None if t is None else '%.9f' % (t/1e9), None if t is None else '%+.2e' % ((t-t0)/1e9), w))
