# count-face cap requirement: Collet-structure (PR 86 constants) vs Lemma W, role split 46/38
import json
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
B46, L46, B38, L38 = Fr(chain[46]['B']), Fr(chain[46]['L']), Fr(chain[38]['B']), Fr(chain[38]['L'])
base = pr86.Cfg(BC=B46, LC=L46, BP=B38, LP=L38)
six = ['old','C','Ccap','C-7','P','Pcap']
def th(a):
    cap, win = a
    br = six if win == 'lemmaW' else ['old','C','Pcap']
    cfg = base.copy(capC=cap, windows=win, branches=br)
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=2000, maxstep=80)
    return a, None if r is None else r[0]/1e9
if __name__ == '__main__':
    caps = [Fr(x,1000) for x in (180, 140, 120, 99, 98, 97, 96, 95, 94, 93, 92, 90, 88, 86, 84, 82, 80)] + [Fr(9999,100000)]
    jobs = [(c, w) for c in caps for w in ('collet','lemmaW')]
    with Pool(4) as p: res = dict(p.map(th, jobs))
    for c in sorted(caps, reverse=True):
        f = lambda t: 'none (> 0.87404)' if t is None else '%.9f (%+.2e)' % (t, t - 0.873954831)
        print('count cap %.5f   Collet-structure %-30s   Lemma W %s' % (float(c), f(res[(c,'collet')]), f(res[(c,'lemmaW')])))
