"""Ratio actual/surrogate for further row subclasses, per run file: prime, composite without/with an inert factor,
inert smallest factor 5, rows containing a conjugate pair pi * pi-bar, composite rows by number of factors.
usage: python3 -I primerows_subclass.py logsP/run_1e5.npz logsP/run_2e5.npz ...
"""
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import primerows_core as PC

rng = np.random.default_rng(0)
for f in sys.argv[1:]:
    d = np.load(f)
    ms = list(d['ms']); K = int(d['K'])
    a2 = np.abs(d['S']) ** 2 / d['mass']; s6 = d['acc'][:, :, 2, :].sum(-1) / K
    nf = d['nf']; inert = d['has_inert']; pair = d['has_pair']; minn = d['minnorm']
    cl = PC.pair_clusters(d['conj'])
    print(f'== {f}  B={int(d["B"])}')
    cls = (('prime', nf == 1), ('comp_noinert', (nf >= 2) & ~inert), ('comp_inert', (nf >= 2) & inert),
           ('inert_q5', (nf >= 2) & inert & (minn == 25)), ('pair', pair), ('nf=2', nf == 2), ('nf>=3', nf >= 3))
    print('   m    ' + ' | '.join(f'{nm} (n={sel.sum()})' for nm, sel in cls))
    for im, m in enumerate(ms):
        row = []
        for nm, sel in cls:
            r, se, _ = PC.boot_ratio(a2[:, im] ** 3, s6[:, im], cl, nb=200, rng=rng, sel=sel)
            row.append(f'{r:.3f}({se:.3f})')
        print(f'   {m:.2f} ' + ' | '.join(row), flush=True)
