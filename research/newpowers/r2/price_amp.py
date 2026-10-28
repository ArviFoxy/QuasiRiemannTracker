"""price_amp.py -- exact return pricing of a (hypothetical) chain, floor 3/5, role split (R2).

Uses B2's exact-cover return toolchain (Lemma-W windows / identical to Collet structure on PR 86's constants), unchanged:
   $SCRATCH/analysis/B2/tc   (copy of lemmaW/tc, validated against PR 86's 32 rows / 240 admissions in lemmaW.md s1)
theta(BC,LC,BP,LP) = exact least theta (1e-9 resolution) for a count face G(BC,LC,.) and a physical face G(BP,LP,.).
Separable role split (lemmaW.md s3.3): theta(LC,LP) = f(LC)+g(LP), so only 2 line scans are needed.
"""
import sys, os, math, json, functools
TC = os.environ.get('R2_TC')          # directory of B2's exact-return toolchain (copy of lemmaW/tc); see README in the report
if not TC or not os.path.isdir(TC):
    raise SystemExit('set R2_TC to the directory holding pr86.py/best.py (analysis/B2/tc in the scratchpad)')
sys.path.insert(0, TC)
from fractions import Fraction as Fr
import pr86, best  # noqa: E402

BAR = 0.8739358
SIX = ['old', 'C', 'Ccap', 'C-7', 'P', 'Pcap']


def frac(x, den=10 ** 10):
    return Fr(round(x * den), den)


CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'theta_cache.jsonl')
_DISK = {}
if os.path.exists(CACHE_FILE):
    for _l in open(CACHE_FILE):
        try:
            _k, _v = json.loads(_l)
            _DISK[tuple(_k)] = _v
        except Exception:  # noqa: BLE001
            pass


@functools.lru_cache(maxsize=None)
def _theta(BC, LC, BP, LP):
    key = (BC, LC, BP, LP)
    if key in _DISK:
        return _DISK[key]
    fc = (frac(BC), frac(LC)); fp = (frac(BP), frac(LP))
    cfg = pr86.Cfg(windows='lemmaW', branches=SIX, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    try:
        r = best.theta_best(cfg, unit=10 ** 9, anchor=873960000, lo=873700000, step=1000, maxstep=80)
    except Exception as ex:  # noqa: BLE001
        r = None
    val = None if r is None else r[0] / 1e9
    try:
        with open(CACHE_FILE, 'a') as fh:
            fh.write(json.dumps([list(key), val]) + '\n')
    except Exception:  # noqa: BLE001
        pass
    return val


def theta(BC, LC, BP, LP):
    return _theta(round(BC, 9), round(LC, 9), round(BP, 9), round(LP, 9))


def split_price(Bfun, Lc_grid, Lp_grid, ref_c=None, ref_p=None, verbose=False):
    """role split on a chain B(L): scan the count face with the physical face at ref_p and conversely; return best."""
    ref_c = ref_c if ref_c is not None else Lc_grid[len(Lc_grid) // 2]
    ref_p = ref_p if ref_p is not None else Lp_grid[len(Lp_grid) // 2]
    base = theta(Bfun(ref_c), ref_c, Bfun(ref_p), ref_p)
    fC = {}
    for Lc in Lc_grid:
        t = theta(Bfun(Lc), Lc, Bfun(ref_p), ref_p)
        fC[Lc] = t
        if verbose:
            print('  count L=%.4f B=%.6f -> %s' % (Lc, Bfun(Lc), t), flush=True)
    gP = {}
    for Lp in Lp_grid:
        t = theta(Bfun(ref_c), ref_c, Bfun(Lp), Lp)
        gP[Lp] = t
        if verbose:
            print('  phys  L=%.4f B=%.6f -> %s' % (Lp, Bfun(Lp), t), flush=True)
    okC = {k: v for k, v in fC.items() if v is not None}
    okP = {k: v for k, v in gP.items() if v is not None}
    if not okC or not okP or base is None:
        return None
    Lc = min(okC, key=okC.get); Lp = min(okP, key=okP.get)
    t = theta(Bfun(Lc), Lc, Bfun(Lp), Lp)
    return dict(theta=t, Lc=Lc, Lp=Lp, Bc=Bfun(Lc), Bp=Bfun(Lp))


def price_ode(ode, floor=0.60, Lmin=2.0, nC=14, nP=10, verbose=False):
    """count face anywhere between the wall (or Lmin) and 2.5, physical face in [2.30,2.50] -> best role split."""
    wall = ode.wall(floor)
    Lend = max(Lmin, wall if wall is not None else Lmin)
    Lc_grid = sorted(set([round(Lend + i * (2.46 - Lend) / (nC - 1), 4) for i in range(nC)]))
    Lp_grid = sorted(set([round(2.30 + i * 0.20 / (nP - 1), 4) for i in range(nP)]))
    res = split_price(ode.B, Lc_grid, Lp_grid, verbose=verbose)
    if res is not None:
        # local refinement of the count face around the best grid point
        Lc0 = res['Lc']
        step = (Lc_grid[1] - Lc_grid[0])
        for Lc in (Lc0 - step / 2, Lc0 + step / 2):
            if Lc < Lend or Lc > 2.5:
                continue
            t = theta(ode.B(Lc), Lc, ode.B(res['Lp']), res['Lp'])
            if t is not None and t < res['theta']:
                res.update(theta=t, Lc=Lc, Bc=ode.B(Lc))
    return wall, res


if __name__ == '__main__':
    from ode_amp import OdeAmp
    o = OdeAmp()
    w, r = price_ode(o, 0.60)
    print('baseline PR83 gate, floor 0.60: wall', w, r, ' B2: 0.873945041 (continuum)')
