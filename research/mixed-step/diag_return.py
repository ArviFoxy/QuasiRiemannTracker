"""Which receipt or cover edge fails just below theta*? usage: python3 diag_return.py th BC,LC,BP,LP sP sC [h]"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
CAP = Fr(549989, 10**7)
th = Fr(int(sys.argv[1]), 10**7)
BC, LC, BP, LP = (Fr(x) for x in sys.argv[2].split(','))
sP, sC = Fr(sys.argv[3]), Fr(sys.argv[4])
h = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(401, 500)
G = CR.geometry(th, h, BP, LP, sP)
rec = CR.receipt(G, BP, LP, CAP, CAP, sC, Fr(43, 1000), CR.THETA_I)
rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
print('smallest receipts:', [(k, round(float(v), 6)) for k, v in sorted(rec.items(), key=lambda kv: kv[1])[:6]])
print('geometry:', {k: round(float(v), 6) for k, v in G.items()})
cands = CR.candidates({'C': (BC, LC, sC), 'P': (BP, LP, Fr(43, 1000))}, G['kap'])
for name, d, Ccap in CR.edges(G, BP, LP):
    try:
        cov = CR.cover_edge(G, d, Ccap, cands)
        print(f"edge {name} d={float(d):.5f} C={float(Ccap):.5f}: {len(cov)} rects, min ret {float(min(c[2] for c in cov)):.3e}", flush=True)
    except ValueError as e:
        print(f"edge {name} d={float(d):.5f} C={float(Ccap):.5f}: FAIL {e}", flush=True)
