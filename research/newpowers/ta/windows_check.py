import json, os
import exact
HERE = os.path.dirname(os.path.abspath(__file__))
for nm in ('g1_f0.60_b1_d1.000', 'g1_f0.55_b1_d1.000', 'g1_f0.50_b1_d1.000', 'g1_f0.60_b0_d0.999', 'g1_f0.55_b0_d0.999', 'g1_f0.50_b0_d0.999'):
    r = json.load(open(os.path.join(HERE, 'results', 'e2_%s_dL0.005_q.json' % nm)))
    C, P = r['C'], r['P']
    t1 = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], windows='collet')
    t2 = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], windows='lemmaW')
    print(nm, 'collet/six %.9f   lemmaW/six %.9f   diff %+.1e' % (t1[0], t2[0], t2[0] - t1[0]), flush=True)
