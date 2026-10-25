"""Return atlas at the mixed-step design point (faces from the mixed flow, Lemma D schedule with
dMinus > 1/2, physical window sP = 0.058, count window sC = 0.058, face caps 0.075).
usage: python3 atlas2.py EPS NPROC [filter]"""
import os, sys, json, time
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import atlas as A
import knobs as KB

A.CAP = Fr(75, 1000)
A.BASE = dict(BC=Fr('0.963421'), LC=Fr('2.08926'), BP=Fr('0.965778'), LP=Fr('2.12948'),
              h=Fr(401, 500), sC=Fr(58, 1000), sP=Fr(58, 1000), tf=Fr(1, 400))

def init():
    A.init()
    M = A.MOD
    M.GLOBAL_DROP = tuple(M.GLOBAL_DROP) + ('source_lambda_low',)
    rec0 = M.receipt
    def receipt(G, *a, **k):
        r = rec0(G, *a, **k)
        r['dMinus_lower_3_4'] = G['ds'] - Fr(1, 2)
        return r
    M.receipt = receipt

if __name__ == '__main__':
    eps = float(sys.argv[1]); nproc = int(sys.argv[2]); filt = sys.argv[3] if len(sys.argv) > 3 else ''
    init()
    KB.REL.clear()
    base = A.theta_star(dict(A.BASE), guess=8742864, span=400)
    print('base theta* =', base, flush=True)
    _, knobs = KB.instrumented()
    jobs = [('param', k, eps, base) for k in A.BASE if filt in k]
    jobs += [('knob', k, eps, base) for k in knobs if filt in k]
    out = []
    with Pool(nproc, initializer=init) as pool:
        for r in pool.imap_unordered(A.job, jobs):
            out.append(r)
            print(json.dumps(r), flush=True)
    out.sort(key=lambda r: -abs(r['delta'] or 0))
    json.dump(dict(base=base, eps=eps, results=out),
              open(os.path.join(HERE, f'atlas2_eps{eps:g}{"_"+filt if filt else ""}.json'), 'w'), indent=1)
