"""scenarios.py -- price hypothetical amplifier mixtures with the continuum ODE + exact return (R2).

usage:  python3 scenarios.py <name> [<name> ...]        (names below)  -> appends JSON lines to results/<name>.jsonl
All numbers: floor q >= 3/5, role split (count face anywhere on the chain, physical face anywhere), continuum chain
(the discrete DeltaL=0.005 chain is +1.1..1.3e-6 above the continuum, lemmaW.md s4.2 / B2 s2).  bar = 0.8739358.
"""
import sys, os, json, time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import replace
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ledger import Amp, SIMPLE, DOUBLED, POOL, blend  # noqa: E402
from ode_amp import OdeAmp  # noqa: E402
import price_amp as PA  # noqa: E402

BAR = PA.BAR


def mk_type(e=1.0, c=6.0, r=1.0, name=None):
    return Amp(name or f"(e={e:g},c={c:g},r={r:g})", 1, 4, e, c, r, 1, "hypothetical")


def eval_pair(args):
    BC, LC, BP, LP = args
    return PA.theta(BC, LC, BP, LP)


def price_parallel(ode, floor=0.60, Lmin=2.0, nC=12, nP=9, workers=4):
    """role-split pricing with the line scans evaluated in parallel."""
    wall = ode.wall(floor)
    Lend = max(Lmin, wall if wall is not None else Lmin)
    Lc_grid = sorted(set([round(Lend + i * (2.46 - Lend) / (nC - 1), 4) for i in range(nC)]))
    Lp_grid = sorted(set([round(2.30 + i * 0.22 / (nP - 1), 4) for i in range(nP)]))
    ref_c = Lc_grid[len(Lc_grid) // 2]; ref_p = 2.38
    jobs = [(ode.B(Lc), Lc, ode.B(ref_p), ref_p) for Lc in Lc_grid] + \
           [(ode.B(ref_c), ref_c, ode.B(Lp), Lp) for Lp in Lp_grid]
    with ProcessPoolExecutor(workers) as ex:
        vals = list(ex.map(eval_pair, jobs))
    fC = dict(zip(Lc_grid, vals[:len(Lc_grid)])); gP = dict(zip(Lp_grid, vals[len(Lc_grid):]))
    okC = {k: v for k, v in fC.items() if v is not None}; okP = {k: v for k, v in gP.items() if v is not None}
    if not okC or not okP:
        return wall, None
    Lc = min(okC, key=okC.get); Lp = min(okP, key=okP.get)
    # refine both faces locally (golden-ish: 3 points each side)
    def refine(L0, step, other_fn, lo, hi):
        cand = [L0 - step / 2, L0 + step / 2, L0 - step / 4, L0 + step / 4]
        cand = [x for x in cand if lo <= x <= hi]
        with ProcessPoolExecutor(workers) as ex:
            tv = list(ex.map(eval_pair, [other_fn(x) for x in cand]))
        pairs = [(t, x) for t, x in zip(tv, cand) if t is not None]
        return min(pairs) if pairs else None
    stepc = Lc_grid[1] - Lc_grid[0]; stepp = Lp_grid[1] - Lp_grid[0]
    rc = refine(Lc, stepc, lambda x: (ode.B(x), x, ode.B(Lp), Lp), Lend, 2.5)
    t0 = PA.theta(ode.B(Lc), Lc, ode.B(Lp), Lp)
    if rc and rc[0] < t0:
        Lc = rc[1]; t0 = rc[0]
    rp = refine(Lp, stepp, lambda x: (ode.B(Lc), Lc, ode.B(x), x), 2.0, 2.6)
    if rp and rp[0] < t0:
        Lp = rp[1]; t0 = rp[0]
    return wall, dict(theta=t0, Lc=Lc, Lp=Lp, Bc=ode.B(Lc), Bp=ode.B(Lp), gap=t0 - BAR)


def run(tag, types, floor=0.60, f=0.999, qmax=0.75, **kw):
    t0 = time.time()
    ode = OdeAmp(types=types, f=f, qmax=qmax, **kw)
    wall, res = price_parallel(ode, floor)
    rec = dict(tag=tag, floor=floor, f=f, qmax=qmax, types=[(a.name, a.e, a.c, a.r) for a in types], wall=wall,
               s_at=[(L, round(ode.slope(L), 5), round(ode.qinf(L), 4)) for L in (2.34, 2.2, 2.0) if L >= ode.Lend],
               res=res, secs=round(time.time() - t0, 1))
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    with open(os.path.join(HERE, 'results', 'scen.jsonl'), 'a') as fh:
        fh.write(json.dumps(rec) + '\n')
    print(json.dumps(rec), flush=True)
    return rec


SCEN = {
    'base': lambda: run('PR83 gate (1,6,1)', [SIMPLE]),
    'f1': lambda: run('PR83 gate, f=1.0', [SIMPLE], f=1.0),
}
for eps in (0.01, 0.02, 0.03, 0.05, 0.10, 0.25, 0.5, 1.0):
    SCEN[f'e{eps}'] = (lambda eps=eps: run(f'e={1+eps:g} (frac {eps:g} doubled)', [mk_type(e=1 + eps)]))
for c in (5.95, 5.9, 5.8, 5.5, 5.0, 4.0):
    SCEN[f'c{c}'] = (lambda c=c: run(f'c={c:g}', [mk_type(c=c)]))
for r in (1.02, 1.05, 1.10):
    SCEN[f'r{r}'] = (lambda r=r: run(f'r={r:g}', [mk_type(r=r)]))
SCEN['doubled'] = lambda: run('full doubled (2,6,1)', [DOUBLED])
SCEN['simple+doubled'] = lambda: run('simple + doubled capacity>0', [SIMPLE, DOUBLED])

if __name__ == '__main__':
    for n in sys.argv[1:]:
        SCEN[n]()
