"""Normalisation check: class ratios with per-row renormalisation by the exact masked diagonal E|S_u|^2/mass (`diag`).
Prime rows have diag = 1 (no source is divisible by u), so only composite ratios can move.
usage: python3 -I primerows_normcheck.py 2e5 4e5 8e5 1.6e6
"""
import sys, os
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
for B in sys.argv[1:]:
    d = np.load(os.path.join(HERE, 'logsP', f'run_{B}.npz'))
    K = int(d['K']); a2 = np.abs(d['S']) ** 2 / d['mass']; s6 = d['acc'][:, :, 2, :].sum(-1) / K; s2 = d['acc'][:, :, 0, :].sum(-1) / K
    D = d['diag']; nf = d['nf']
    for im, m in enumerate(d['ms']):
        out = []
        for nm, sel in (('prime', nf == 1), ('comp', nf >= 2)):
            r_raw = (a2[sel, im] ** 3).mean() / s6[sel, im].mean()
            r_nrm = ((a2[sel, im] / D[sel, im]) ** 3).mean() / (s6[sel, im] / D[sel, im] ** 3).mean()
            out.append(f'{nm}: raw {r_raw:.3f} renormalised {r_nrm:.3f} (diag mean {D[sel, im].mean():.3f}, actual M2 {a2[sel, im].mean():.3f}, sur M2 {s2[sel, im].mean():.3f})')
        print(f'B={B} m={m:.2f} ' + ' | '.join(out))
