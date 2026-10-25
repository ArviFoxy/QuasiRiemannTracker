# Does an extra family face (between P and C) let the return close at a lower theta?
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/faceless-chain')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
import family2 as F2, polyq as P, cert_return as CR
fam, _ = F2.build2([0.0329365, 0.0376, 0.0423, 0.0472], m=16)
B, L, B0, L0, sv = fam.polys(2)
def face(y):
    return (P.ev(B, y), P.ev(L, y))
(jC, iC), (jP, iP) = F2.face_C(fam), F2.face_P(fam)
BC, LC = face(iC*fam.Dy); BP, LP = face(iP*fam.Dy)
extra = {f'X{k}': face(Fr(k, 100)) for k in (70, 80, 90, 95)}
for k, (b, l) in extra.items(): print(k, float(b), float(l), float(b/l))
def ok(th, faces_extra):
    CR.ADM_CACHE.clear()
    G = CR.geometry(Fr(th, 10**7), Fr(401, 500), BP, LP, Fr(9, 200))
    rec = CR.receipt(G, BP, LP, F2.CAPMAX, F2.CAPMAX, Fr(13, 250), Fr(43, 1000), CR.THETA_I)
    rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
    if any(v <= 0 for v in rec.values()): return False
    faces = {'C': (BC, LC, Fr(13, 250)), 'P': (BP, LP, Fr(43, 1000))}
    faces.update({k: (b, l, Fr(13, 250)) for k, (b, l) in faces_extra.items()})
    cands = CR.candidates(faces, G['kap'])
    try:
        for name, d, Ccap in CR.edges(G, BP, LP):
            CR.cover_edge(G, d, Ccap, cands)
        return True
    except (ValueError, AssertionError):
        return False
def star(fx, lo=8745800, hi=8746076):
    if not ok(hi, fx): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        if ok(mid, fx): hi = mid
        else: lo = mid
    return hi
print("C,P only:", star({}))
print("with extra faces:", star(extra))
