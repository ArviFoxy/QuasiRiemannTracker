"""Slack of every scalar receipt and every conductor edge of the exact return at the best theta.
Usage: python3 receipts.py ../cap-induction/chain_h45.json [theta_num]   (theta = theta_num/1e7)"""
import sys, os, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
nodes = json.load(open(sys.argv[1]))
def face(n): return (Fr(n['B']), Fr(n['L']), Fr(n['cap']))
cands = [n for n in nodes if float(Fr(n['cap'])) >= 0.0521]
nC = max(cands, key=lambda n: float(Fr(n['B'])) - float(Fr(n['L']))*0.045)
nPs = [n for n in nodes if float(Fr(n['cap'])) >= 0.045]
zph = lambda n: (float(Fr(n['B'])) - 0.83666)/float(Fr(n['L']))
nP = max(nPs, key=zph)
C, P = face(nC), face(nP)
h = Fr(401, 500)
theta = Fr(int(sys.argv[2]), 10**7) if len(sys.argv) > 2 else Fr(8747257, 10**7)
CR.ADM_CACHE.clear()
G = CR.geometry(theta, h, P[0], P[1], Fr(9, 200))
rec = CR.receipt(G, P[0], P[1], C[2], P[2], Fr(13, 250), Fr(43, 1000), Fr(8747759, 10**7))
rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
print("theta", float(theta), "C", [float(v) for v in C], "P", [float(v) for v in P])
print("geometry:", {k: float(v) for k, v in G.items()})
for v, k in sorted((float(v), k) for k, v in rec.items()):
    print(f"  {k:40s} {v: .6e}")
cands_b = CR.candidates({'C': (C[0], C[1], Fr(13, 250)), 'P': (P[0], P[1], Fr(43, 1000))}, G['kap'])
for name, d, Ccap in CR.edges(G, P[0], P[1]):
    try:
        cov = CR.cover_edge(G, d, Ccap, cands_b)
        m = min(c[2] for c in cov)
        used = sorted(set(c[0] for c in cov))
        print(f"edge {name:10s} d={float(d):.5f} C={float(Ccap):.6f}: {len(cov)} rects, min coeff {float(m):.3e}, branches {used}")
    except ValueError as e:
        print(f"edge {name}: FAIL {e}")
