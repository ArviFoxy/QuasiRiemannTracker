import json, sys, time
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
base = pr86.Cfg()
def cfg_for(k, win, capC=Fr(9999,100000), capP=Fr(31,500), **kw):
    B, L = Fr(chain[k]['B']), Fr(chain[k]['L'])
    return base.copy(windows=win, BC=B, LC=L, BP=B, LP=L, capC=capC, capP=capP, **kw)
def job(args):
    k, win = args
    t0 = time.time()
    cfg = cfg_for(k, win)
    r = best.theta_best(cfg, unit=10**9, anchor=874030000, lo=873950000, step=1000)
    if r is None: return (k, win, None, None, None, time.time()-t0)
    return (k, win, r[0], float(r[1]), best.why(cfg, r[0]-1, unit=10**9), time.time()-t0)
if __name__ == '__main__':
    ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else list(range(0, 47))
    jobs = [(k, w) for k in ks for w in ('collet', 'lemmaW')]
    with Pool(4) as pool:
        for k, win, t, h, why, dt in pool.imap(job, jobs):
            print('k=%2d %-6s theta*=%s h=%s  %s  [%.0fs]' % (k, win, None if t is None else '%.9f' % (t/1e9), h, why, dt), flush=True)
