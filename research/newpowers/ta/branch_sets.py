"""Which return branches are needed at the final faces of each marked scenario (Collet windows, box ell<0.18)."""
import sys, json, os
import exact
HERE = os.path.dirname(os.path.abspath(__file__))
sets = [('old,C,Pcap (PR 86)', ['old', 'C', 'Pcap']), ('+Ccap', ['old', 'C', 'Pcap', 'Ccap']), ('+C-7', ['old', 'C', 'Pcap', 'C-7']),
        ('+Ccap,C-7', ['old', 'C', 'Pcap', 'Ccap', 'C-7']), ('six', exact.SIX)]
for nm in ('g1_f0.60_b1_d1.000', 'g1_f0.55_b1_d1.000', 'g1_f0.50_b1_d1.000', 'g1_f0.60_b0_d0.999', 'g1_f0.55_b0_d0.999', 'g1_f0.50_b0_d0.999'):
    r = json.load(open(os.path.join(HERE, 'results', 'e2_%s_dL0.005_q.json' % nm)))
    C, P = r['C'], r['P']
    out = []
    for lab, br in sets:
        t = exact.theta_exact(C['B'], C['L'], P['B'], P['L'], guess=r['theta'], windows='collet', branches=br)
        out.append('%s: %s' % (lab, 'fails' if t is None else '%.9f' % t[0]))
    print(nm, ' | '.join(out), flush=True)
