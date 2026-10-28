import json
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best, ode_faces as OF
from lowfloor_greedy import face, ext, chain, base, six, BAR
def qmin(r):
    B0,L0,B,L,A,D=r['B0'],r['L0'],r['B'],r['L'],r['A'],r['D']; s0=r['s0']; vmax=0.1-s0
    return 0.999*L0*A/((L0-L)*(1+D*vmax)+(6*B0-L0)*A)
rows = {}
for l in open('greedy_f060_dl005.jsonl'):
    r = json.loads(l)
    if not r.get('infeasible'): rows[r['k']] = r
def job(kc):
    fc, fp = face(kc), face(38)
    cfg = base.copy(windows='lemmaW', branches=six, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    return kc, r[0]
if __name__ == '__main__':
    ks = [47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69]
    with Pool(4) as p:
        res = dict(p.map(job, ks))
    for k in ks:
        print('k=%d L=%.4f B=%.7f minq(floor needed)=%.4f  split theta*=%.9f gap=%+.2e' % (k, rows[k]['L'], rows[k]['B'], qmin(rows[k]), res[k]/1e9, res[k]/1e9 - BAR))
