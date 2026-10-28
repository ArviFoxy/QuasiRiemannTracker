"""thresholds.py -- how much amplifier improvement is needed to reach the bar (R2).

For a one-parameter family of amplifier types, find the parameter value at which the exact-return continuum price
(floor 3/5, role split, pricing2.price_cd) equals the target:  BAR (0.8739358)  and  BAR - 1.2e-6  (the discrete
DeltaL = 0.005 chain is 1.1-1.3e-6 above its continuum, lemmaW.md s4.2 / B2 s2).
usage: python3 thresholds.py <knob> [floor]       knob in {e, c, r, f, qcap}
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ledger import Amp, SIMPLE  # noqa: E402
from ode_amp import OdeAmp  # noqa: E402
import pricing2 as P2  # noqa: E402

BAR = P2.BAR


def mk(e=1.0, c=6.0, r=1.0):
    return Amp(f"(e={e:.5f},c={c:.5f},r={r:.5f})", 1, 4, e, c, r, 1, "hyp")


def theta_of(knob, x, floor):
    if knob == 'e':
        ode = OdeAmp([mk(e=x)])
    elif knob == 'c':
        ode = OdeAmp([mk(c=x)])
    elif knob == 'r':
        ode = OdeAmp([mk(r=x)])
    elif knob == 'f':
        ode = OdeAmp([SIMPLE], f=x)
    elif knob == 'dthr':      # additive shift of the HIGH threshold T(q) = 10/(15-6q) + x
        ode = OdeAmp([SIMPLE], dthr=x)
    elif knob == 'eps':       # s0 scaled by (1-x)
        ode = OdeAmp([SIMPLE], eps=x)
    else:
        raise ValueError(knob)
    wall, res = P2.price_cd(ode, floor)
    return None if res is None else res['theta'], wall, res


def solve(knob, lo, hi, target, floor, tol=2e-8, maxit=14):
    """theta decreases with the knob (for e, r, dthr, eps) or increases (c): handle both by sign test."""
    flo = theta_of(knob, lo, floor)[0] - target
    fhi = theta_of(knob, hi, floor)[0] - target
    assert flo * fhi < 0, (knob, lo, hi, flo, fhi)
    a, b, fa, fb = lo, hi, flo, fhi
    for it in range(maxit):
        # regula falsi with Illinois damping
        x = b - fb * (b - a) / (fb - fa)
        fx = theta_of(knob, x, floor)[0] - target
        print('   %s it%d  x=%.6f  theta-target=%+.3e' % (knob, it, x, fx), flush=True)
        if abs(fx) < tol:
            return x
        if fx * fa < 0:
            b, fb = x, fx; fa *= 0.5
        else:
            a, fa = x, fx; fb *= 0.5
    return x


if __name__ == '__main__':
    knob = sys.argv[1]; floor = float(sys.argv[2]) if len(sys.argv) > 2 else 0.60
    brackets = dict(e=(1.0, 1.03), c=(5.9, 6.0), r=(1.0, 1.05), f=(0.999, 1.0), dthr=(0.0, 0.01), eps=(0.0, 0.10))
    lo, hi = brackets[knob]
    out = {}
    for tag, tgt in (('bar', BAR), ('bar-1.2e-6', BAR - 1.2e-6)):
        t0 = time.time()
        try:
            x = solve(knob, lo, hi, tgt, floor)
        except AssertionError as ex:
            x = None; print('bracket failed', ex)
        out[tag] = x
        print('RESULT knob=%s floor=%.2f target=%s -> %s  (%.0fs)' % (knob, floor, tag, x, time.time() - t0), flush=True)
    with open(os.path.join(HERE, 'results', 'thresholds.jsonl'), 'a') as fh:
        fh.write(json.dumps(dict(knob=knob, floor=floor, **out)) + '\n')
