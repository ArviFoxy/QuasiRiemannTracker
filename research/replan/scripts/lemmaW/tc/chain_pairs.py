import json, sys, time
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
base = pr86.Cfg()
def cfg_for(kc, kp, win, **kw):
    return base.copy(windows=win, BC=Fr(chain[kc]['B']), LC=Fr(chain[kc]['L']), BP=Fr(chain[kp]['B']), LP=Fr(chain[kp]['L']), **kw)
def job(a):
    kc, kp, win = a
    cfg = cfg_for(kc, kp, win)
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873940000, step=1000)
    if r is None: return (kc, kp, win, None, None, None)
    return (kc, kp, win, r[0], float(r[1]), best.why(cfg, r[0]-1, unit=10**9))
if __name__ == '__main__':
    win = sys.argv[1]
    kcs = [int(x) for x in sys.argv[2].split(',')]
    kps = [int(x) for x in sys.argv[3].split(',')]
    jobs = [(kc, kp, win) for kc in kcs for kp in kps]
    res = {}
    with Pool(4) as pool:
        for kc, kp, w, t, h, why in pool.imap_unordered(job, jobs):
            res[(kc, kp)] = (t, h, why)
    print('# windows', win)
    print('count\\phys ' + ' '.join('%11d' % kp for kp in kps))
    for kc in kcs:
        print('%10d ' % kc + ' '.join(('%11.9f' % (res[(kc,kp)][0]/1e9)) if res[(kc,kp)][0] else '   none    ' for kp in kps))
    bestk = min(res, key=lambda k: res[k][0] if res[k][0] else 1e18)
    print('best:', bestk, res[bestk])
    json.dump({'%d,%d' % k: v for k, v in res.items()}, open('pairs_%s_%s_%s.json' % (win, sys.argv[2].replace(',','_'), sys.argv[3].replace(',','_')), 'w'))
