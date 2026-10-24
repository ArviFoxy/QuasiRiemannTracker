"""Collect envelope values and theta* for all runs into results.json (theta* via evalfaces.py logic)."""
import json, os, sys, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
runs = [('consolidated (0.0005, then 0.00025)', '../cap-induction/chain_h45.json'),
        ('uniform 0.002', 'result_step0.002.json'),
        ('uniform 0.001', 'result_step0.001.json'),
        ('uniform 0.0005', 'result_step0.0005.json'),
        ('consolidated pivots, fine fees', 'result_h45_finefees.json'),
        ('continuum, Collet fees', 'result_cont_q45.json'),
        ('continuum, fine fees', 'result_cont_q45_finefees.json')]
out = {}
for name, fn in runs:
    p = os.path.join(HERE, fn)
    if not os.path.exists(p): continue
    r = subprocess.run([sys.executable, os.path.join(HERE, 'evalfaces.py'), p], capture_output=True, text=True,
                       env=dict(os.environ, OMP_NUM_THREADS='1'))
    txt = r.stdout.strip().splitlines()
    print(name, '|', ' || '.join(txt), flush=True)
    out[name] = txt
json.dump(out, open(os.path.join(HERE, 'results.json'), 'w'), indent=1)
