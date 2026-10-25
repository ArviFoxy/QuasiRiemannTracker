"""Sensitivity atlas of the exact final return: bump each literal knob (knobs.py) and each design
parameter by a relative eps, recompute theta* exactly, report the change.
usage: python3 atlas.py EPS NPROC [filter]"""
import os, sys, json, time
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import knobs as KB

CAP = Fr(549989, 10**7)
BASE = dict(BC=Fr(1272915379989926835893023, 1315333734400000000000000),
            LC=Fr(3063363697870470065773, 1052266987520000000000),
            BP=Fr(335106151738000623869543064163, 344806846470553600000000000000),
            LP=Fr(631360617375411063383, 210453397504000000000),
            h=Fr(401, 500), sC=Fr(13, 250), sP=Fr(9, 200), tf=Fr(1, 400))
MOD = None
def init():
    global MOD
    MOD, _ = KB.instrumented()

def ok(th, P):
    KB.apply_module_knobs(MOD)
    MOD.ADM_CACHE.clear()
    try:
        rec, cov, bad = MOD.run(Fr(th, 10**7), P['h'], (P['BC'], P['LC'], CAP), (P['BP'], P['LP'], CAP),
                                verbose=False, sP=P['sP'], sC=P['sC'], tf=P['tf'], mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False

def theta_star(P, guess=8746075, span=1200):
    lo, hi = guess - span, min(guess + span, 8747700)   # the incumbent receipt needs theta < theta_I = 0.8747759
    while not ok(hi, P):
        if hi >= 8747700: return None
        lo, hi = hi, min(hi + 4*span, 8747700)
    while ok(lo, P):
        hi, lo = lo, lo - 4*span
        if lo < 8700000: return lo
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, P) else (mid, hi)
    return hi

def job(args):
    kind, name, eps, base = args
    KB.REL.clear()
    P = dict(BASE)
    if kind == 'knob':
        KB.REL[name] = eps
    else:
        P[name] = P[name]*(1 + Fr(eps).limit_denominator(10**9))
    t = time.time()
    th = theta_star(P, guess=base)
    return dict(kind=kind, name=name, eps=eps, theta=th, delta=None if th is None else th - base,
                secs=round(time.time() - t, 1))

if __name__ == '__main__':
    eps = float(sys.argv[1]); nproc = int(sys.argv[2]); filt = sys.argv[3] if len(sys.argv) > 3 else ''
    init()
    KB.REL.clear()
    base = theta_star(dict(BASE))
    print('base theta* =', base, flush=True)
    _, knobs = KB.instrumented()
    jobs = [('param', k, eps, base) for k in BASE if filt in k]
    jobs += [('knob', k, eps, base) for k in knobs if filt in k]
    out = []
    with Pool(nproc, initializer=init) as pool:
        for r in pool.imap_unordered(job, jobs):
            out.append(r)
            print(json.dumps(r), flush=True)
    out.sort(key=lambda r: -abs(r['delta'] or 0))
    json.dump(dict(base=base, eps=eps, results=out),
              open(os.path.join(HERE, f'atlas_eps{eps:g}{"_"+filt if filt else ""}.json'), 'w'), indent=1)
