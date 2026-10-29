"""Physical numerator cap s_P (clip s_P*d at newTop) and physical cap: free lever at the new faces?"""
import sys, os, json
from fractions import Fraction as Fr
import exact
HERE = os.path.dirname(os.path.abspath(__file__))
for nm in sys.argv[1:]:
    r = json.load(open(os.path.join(HERE, 'results', 'e2_%s_dL0.005_q.json' % nm)))
    C, P = r['C'], r['P']
    out = []
    for sP, capP in ((Fr(3, 50), Fr(31, 500)), (Fr(31, 500), Fr(31, 500)), (Fr(31, 500), Fr(7, 100)), (Fr(65, 1000), Fr(7, 100)),
                     (Fr(7, 100), Fr(8, 100)), (Fr(8, 100), Fr(9, 100)), (Fr(9, 100), Fr(9999, 100000)), (Fr(1, 20), Fr(31, 500))):
        t = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], windows='collet', sP=sP, capP=capP)
        out.append('sP=%.4f capP=%.4f: %s' % (float(sP), float(capP), 'fails' if t is None else '%+.2e' % (t[0] - r['theta'])))
    print(nm, ' | '.join(out), flush=True)
