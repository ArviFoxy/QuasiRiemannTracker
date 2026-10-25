"""Binding edge/box at a design point (dMinus > 1/2, Lemma D). usage: python3 diag2.py th 'BC=..,...'"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
import ret_scan as RS
P = dict(RS.DEF)
for kv in sys.argv[2].split(','):
    k, v = kv.split('='); P[k] = v
P = {k: Fr(v) for k, v in P.items()}
th = Fr(int(sys.argv[1]), 10**7)
G = CR.geometry(th, P['h'], P['BP'], P['LP'], P['sP'])
rec = CR.receipt(G, P['BP'], P['LP'], P['cap'], P['cap'], P['sC'], P['sPp'], CR.THETA_I)
rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
print('smallest receipts:', [(k, round(float(v), 6)) for k, v in sorted(rec.items(), key=lambda kv: kv[1])[:5]])
print('geometry:', {k: round(float(v), 6) for k, v in G.items()})
cands = CR.candidates({'C': (P['BC'], P['LC'], P['sC']), 'P': (P['BP'], P['LP'], P['sPp'])}, G['kap'])
for name, d, Ccap in CR.edges(G, P['BP'], P['LP']):
    try:
        cov = CR.cover_edge(G, d, Ccap, cands)
        from collections import Counter
        cnt = Counter(c[0] for c in cov)
        print(f"edge {name} d={float(d):.5f} C={float(Ccap):.5f}: {len(cov)} rects, min ret {float(min(c[2] for c in cov)):.3e}, branches {dict(cnt)}", flush=True)
    except ValueError as e:
        print(f"edge {name} d={float(d):.5f} C={float(Ccap):.5f}: FAIL {e}", flush=True)
