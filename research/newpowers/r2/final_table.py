"""final_table.py -- consolidated prices (section 5.4 of R2_ledger.md): exact-return theta, floor 3/5, role split,
count/physical faces by coordinate descent (pricing2.price_cd).   usage: python3 final_table.py [tag ...]   (no tag = all)
Appends one JSON line per scenario to results/final.jsonl and prints a markdown table row.
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ledger import Amp, SIMPLE  # noqa: E402
from ode_amp import OdeAmp  # noqa: E402
import pricing2 as P2  # noqa: E402

BAR = P2.BAR


def mk(e=1.0, c=6.0, r=1.0):
    return Amp("(e=%.5f,c=%.5f,r=%.5f)" % (e, c, r), 1, 4, e, c, r, 1, "hyp")


SC = {
    'base':       lambda: OdeAmp([SIMPLE]),
    'f1':         lambda: OdeAmp([SIMPLE], f=1.0),
    'e1.0116':    lambda: OdeAmp([mk(e=1.0116095)]),
    'e1.02':      lambda: OdeAmp([mk(e=1.02)]),
    'e1.03':      lambda: OdeAmp([mk(e=1.03)]),
    'e1.05':      lambda: OdeAmp([mk(e=1.05)]),
    'e2':         lambda: OdeAmp([mk(e=2.0)]),
    'c5.9587':    lambda: OdeAmp([mk(c=5.9587499)]),
    'c5.9':       lambda: OdeAmp([mk(c=5.9)]),
    'r1.0171':    lambda: OdeAmp([mk(r=1.0170524)]),
    'r1.05':      lambda: OdeAmp([mk(r=1.05)]),
}

if __name__ == '__main__':
    tags = sys.argv[1:] or list(SC)
    for tag in tags:
        t0 = time.time()
        ode = SC[tag]()
        wall, res = P2.price_cd(ode, 0.60)
        row = dict(tag=tag, wall=wall, **(res or {}), secs=round(time.time() - t0))
        with open(os.path.join(HERE, 'results', 'final.jsonl'), 'a') as fh:
            fh.write(json.dumps(row) + '\n')
        print(json.dumps(row), flush=True)
