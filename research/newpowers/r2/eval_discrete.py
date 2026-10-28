"""eval_discrete.py -- exact-return price of a DISCRETE chain (dchain_amp.py output), floor 3/5, role split (R2).

count face: best of the last `nlast` steps; physical face: best step with L in [2.20, 2.60]; coordinate descent, exact thetas
(price_amp.theta = B2/tc exact-cover Lean return).   usage: python3 eval_discrete.py chain.json [nlast]
"""
import sys, json, os
from concurrent.futures import ProcessPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import price_amp as PA  # noqa: E402

BAR = PA.BAR


def _ev(a):
    return PA.theta(*a)


def evaluate(fn, nlast=12, workers=4):
    rows = [r for r in json.load(open(fn)) if not r.get('infeasible')]
    faces = [(r['B'], r['L'], r['s0']) for r in rows]
    phys = [f for f in faces if 2.20 <= f[1] <= 2.60]
    cnt = faces[-nlast:]
    pref = min(phys, key=lambda f: abs(f[1] - 2.38))
    with ProcessPoolExecutor(workers) as ex:
        tv = list(ex.map(_ev, [(c[0], c[1], pref[0], pref[1]) for c in cnt]))
    ok = [(t, c) for t, c in zip(tv, cnt) if t is not None]
    t0, cbest = min(ok)
    with ProcessPoolExecutor(workers) as ex:
        tv = list(ex.map(_ev, [(cbest[0], cbest[1], p[0], p[1]) for p in phys]))
    okp = [(t, p) for t, p in zip(tv, phys) if t is not None]
    t1, pbest = min(okp)
    # re-optimise the count face with the best physical face
    with ProcessPoolExecutor(workers) as ex:
        tv = list(ex.map(_ev, [(c[0], c[1], pbest[0], pbest[1]) for c in cnt]))
    ok = [(t, c) for t, c in zip(tv, cnt) if t is not None]
    t2, cbest = min(ok)
    print('%s: steps=%d end L=%.4f B=%.6f | count L=%.4f (s0=%.4f) phys L=%.4f (s0=%.4f) -> theta=%.9f gap=%+.2e' % (
        os.path.basename(fn), len(rows), faces[-1][1], faces[-1][0], cbest[1], cbest[2], pbest[1], pbest[2], t2, t2 - BAR), flush=True)
    return t2, cbest, pbest


if __name__ == '__main__':
    evaluate(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 12)
