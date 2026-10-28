import json, os
from fractions import Fraction as Fr
import exact
HERE = os.path.dirname(os.path.abspath(__file__))
for nm in ('g1_f0.50_b1_d1.000', 'g1_f0.55_b1_d1.000', 'g1_f0.60_b1_d1.000'):
    r = json.load(open(os.path.join(HERE, 'results', 'e2_%s_dL0.005_q.json' % nm)))
    C, P = r['C'], r['P']
    out = []
    for cap in (Fr(9999, 100000), Fr(99, 1000), Fr(98, 1000), Fr(97, 1000), Fr(95, 1000), Fr(92, 1000), Fr(90, 1000)):
        for win in ('collet', 'lemmaW'):
            t = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], windows=win, capC=cap)
            out.append('%s cap %.5f: %s' % (win, float(cap), 'fails' if t is None else '%+.1e' % (t[0] - r['theta'])))
    print(nm, ' | '.join(out), flush=True)
