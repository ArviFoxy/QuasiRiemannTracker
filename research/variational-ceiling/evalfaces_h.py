"""evalfaces.py with the conductor top h (and the caps sP, sC) as parameters.
usage: python3 evalfaces_h.py FILE.json H_NUM H_DEN [SP_NUM SP_DEN SC_NUM SC_DEN]
Checks whether re-optimizing h moves the continuum ceiling (0.8747241 at h = 401/500)."""
import sys, os, json
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
nodes = json.load(open(sys.argv[1]))
h = Fr(int(sys.argv[2]), int(sys.argv[3]))
sP = Fr(int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else Fr(9, 200)
sC = Fr(int(sys.argv[6]), int(sys.argv[7])) if len(sys.argv) > 7 else Fr(13, 250)
f = lambda x: float(Fr(x)) if isinstance(x, str) else float(x)
faces = [(f(n['B']), f(n['L']), f(n['cap'])) for n in nodes]
cands = [x for x in faces if x[2] >= float(sC) + 1e-4]
C = max(cands, key=lambda x: x[0] - x[1]*0.045)
P = max([x for x in faces if x[2] >= 0.045], key=lambda x: (x[0] - 0.83666)/x[1])
toF = lambda x: (Fr(x[0]).limit_denominator(10**13), Fr(x[1]).limit_denominator(10**13), Fr(x[2]).limit_denominator(10**9))
Cq, Pq = toF(C), toF(P)
def ok(th):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), h, Cq, Pq, verbose=False, sP=sP, sC=sC, mode='global')
        return not bad
    except ValueError:
        return False
lo, hi = 8744000, 8747758
if not ok(hi): print(f"h={float(h):.6f}: theta* above", hi, flush=True); sys.exit()
while hi - lo > 1:
    mid = (lo+hi)//2
    if ok(mid): hi = mid
    else: lo = mid
print(f"h={float(h):.6f} sP={float(sP):.4f} sC={float(sC):.4f}: theta* = {hi/1e7:.7f}", flush=True)
