"""The fan: explicit faces from Sil's face through one point (s0, E0) down to the stall line
L/B = 6q/(1+q) at q = 7499/10000, each step checked exactly against the draft SourceValid3
(mixed_certs). Float bisection for the least slope, then a relative reserve, then exact check.
usage: python3 fan.py s0 [reserve] [ratio_stop]"""
import sys, os, json
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mixed_certs as M
import discrete_chain as DC

QF = Fr(7499, 10000)
CAP = Fr(os.environ.get("FANCAP", "549989/10000000"))
SIL = M.face(Fr(99999, 100000), Fr(93, 25), Fr(3, 50))

def least_slope_float(par, s0, cap):
    DC.QMAX = float(QF)
    DC.ok_child.__defaults__ = (float(cap), 5, None)
    return DC.min_L((float(par['B']), float(par['L']), float(par['cap'])), float(s0),
                    float(par['L'])*(1 - 1e-12), q=float(QF), it=50)

def build(s0, reserve=Fr(1, 10**6), ratio_stop=Fr(25713, 10000), maxsteps=90):
    E0 = SIL['B'] - SIL['L']*s0
    faces = [SIL]
    while True:
        par = faces[-1]
        # the weak cap needs the parent's cap to (nearly) cover the child's: grow caps gradually,
        # taking the largest cap in [parent cap, CAP] with a descending child
        lo, hi = min(par['cap'], CAP), CAP
        Lf = least_slope_float(par, s0, hi)
        if Lf is None or Fr(Lf) >= par['L']:
            Lf = least_slope_float(par, s0, lo)
            if Lf is None or Fr(Lf) >= par['L']: return faces, 'stuck'
            for _ in range(12):
                mid = (lo + hi)/2
                Lm = least_slope_float(par, s0, mid)
                if Lm is not None and Fr(Lm) < par['L']: lo, Lf = mid, Lm
                else: hi = mid
            hi = lo
        cap = Fr(hi).limit_denominator(10**6)
        if cap > hi: cap = Fr(int(hi*10**6), 10**6)
        Lf = least_slope_float(par, s0, cap)
        L = Fr(Lf).limit_denominator(10**9)*(1 + reserve)
        if L >= par['L']: return faces, 'no descent'
        n = M.face(E0 + L*s0, L, cap, QF)
        ok, msgs, _ = M.check_node(n, par, par, Fr(8))
        tries = 0
        while not (ok and M.cell_ok(n, par)) and tries < 20:
            L = L + (par['L'] - L)/4
            n = M.face(E0 + L*s0, L, cap, QF)
            ok, msgs, _ = M.check_node(n, par, par, Fr(8)); tries += 1
        if not ok: return faces, f'exact check failed: {msgs[:3]}'
        faces.append(n)
        print(f"fan {len(faces)-1}: cap={float(cap):.6f} L={float(L):.7f} B={float(n['B']):.7f} L/B={float(L/n['B']):.7f} "
              f"den3={float(M.den3(n, par)):.3e} d(cap)={float(M.dsel(n, par, cap)):.3e}", flush=True)
        if L/n['B'] <= ratio_stop or len(faces) > maxsteps: return faces, 'done'

if __name__ == '__main__':
    s0 = Fr(sys.argv[1])
    res = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(1, 10**6)
    rs = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(25713, 10000)
    faces, why = build(s0, res, rs)
    print(why, len(faces) - 1, 'steps')
    json.dump([{k: str(v) for k, v in f.items()} for f in faces], open(f'fan_{sys.argv[1].replace("/", "_")}_cap{float(CAP):g}.json', 'w'), indent=1)
