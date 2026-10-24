"""Envelope and exact-return theta* for a chain file or continuum rows.
usage: python3 evalfaces.py FILE.json   (nodes with B, L, cap[, pivot] or rows with s, E, B, L, cap)
Face selection and relaxations as in ../cap-induction/evalchain.py with relax22 relaxLP
(the consolidated value 0.8747257)."""
import sys, os, json
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
nodes = json.load(open(sys.argv[1]))
f = lambda x: float(Fr(x)) if isinstance(x, str) else float(x)
faces = [(f(n['B']), f(n['L']), f(n['cap'])) for n in nodes]
env = lambda z: max(B - L*z for (B, L, c) in faces if c >= z)
print(f"{sys.argv[1]}: {len(faces)} faces, envelope E(0.0412)={env(0.0412):.7f} E(0.045)={env(0.045):.7f}", flush=True)
cands = [x for x in faces if x[2] >= 0.0521]
C = max(cands, key=lambda x: x[0] - x[1]*0.045)
P = max([x for x in faces if x[2] >= 0.045], key=lambda x: (x[0] - 0.83666)/x[1])
toF = lambda x: (Fr(x[0]).limit_denominator(10**13), Fr(x[1]).limit_denominator(10**13), Fr(x[2]).limit_denominator(10**9))
Cq, Pq = toF(C), toF(P)
def ok(th):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), Cq, Pq, verbose=False, sP=Fr(9, 200), sC=Fr(13, 250), mode='global')
        return not bad
    except ValueError:
        return False
lo, hi = 8744000, 8747758
if not ok(hi): print("theta* above", hi); sys.exit()
while hi - lo > 1:
    mid = (lo+hi)//2
    if ok(mid): hi = mid
    else: lo = mid
print(f"  C=({C[0]:.8f},{C[1]:.6f}) P=({P[0]:.8f},{P[1]:.6f})  theta* = {hi/1e7:.7f}", flush=True)
