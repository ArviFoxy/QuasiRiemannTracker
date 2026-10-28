# lowered floor (0.60), PR 86-style greedy chain (dL=0.005) continued from the exact k=46 face: exact theta* for count face k_c, physical k_p=38 (exact PR 86 face)
import json, sys
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best, ode_faces as OF
BAR = 0.8739358
chain = json.load(open('chain86.json'))
ext = {}
for l in open('greedy_f060_dl005.jsonl'):
    r = json.loads(l)
    if not r.get('infeasible'): ext[r['k']] = (OF.frac(r['B']), OF.frac(r['L']), r['s0'])
def face(k):
    if k <= 46: return (Fr(chain[k]['B']), Fr(chain[k]['L']))
    return ext[k][:2]
base = pr86.Cfg()
six = ['old','C','Ccap','C-7','P','Pcap']
def job(a):
    kc, kp, win = a
    fc, fp = face(kc), face(kp)
    br = six if win == 'lemmaW' else ['old','C','Pcap']
    cfg = base.copy(windows=win, branches=br, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    return (a, None if r is None else r[0], None if r is None else float(r[1]), None if r is None else best.why(cfg, r[0]-1, unit=10**9))
if __name__ == '__main__':
    kcs = [46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 71, 72, 73, 74]
    jobs = [(kc, 38, w) for kc in kcs for w in ('collet', 'lemmaW')] + [(kc, kc, 'lemmaW') for kc in (46, 50, 55, 60, 64, 68, 72, 74)]
    res = {}
    with Pool(4) as pool:
        for a, t, h, why in pool.imap_unordered(job, jobs):
            res[a] = (t, h, why)
    print('count face k_c (L, B, s0) | role split (k_p=38) Collet-set | LemmaW six-branch | single face LemmaW')
    for kc in kcs:
        f = face(kc); s0 = ext[kc][2] if kc in ext else float(Fr(chain[kc]['s0']))
        c, w = res[(kc, 38, 'collet')], res[(kc, 38, 'lemmaW')]
        sg = res.get((kc, kc, 'lemmaW'))
        print('%2d (L=%.4f B=%.7f s0=%.4f) | %.9f (%+.2e) | %.9f (%+.2e) | %s' % (kc, float(f[1]), float(f[0]), s0, c[0]/1e9, c[0]/1e9-BAR, w[0]/1e9, w[0]/1e9-BAR, '' if sg is None else '%.9f (%+.2e)' % (sg[0]/1e9, sg[0]/1e9-BAR)))
    bk = min(kcs, key=lambda k: res[(k, 38, 'lemmaW')][0])
    print('best count face k_c =', bk, res[(bk, 38, 'lemmaW')])
