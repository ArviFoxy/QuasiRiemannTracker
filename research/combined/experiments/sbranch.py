# The return with the start face S (Sil's) as an extra affine branch.
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
import cert_return as CR
f = json.load(open(sys.argv[1]))
C = (Fr(f[0]['B']), Fr(f[0]['L']), Fr(f[0]['cap'])); P = (Fr(f[1]['B']), Fr(f[1]['L']), Fr(f[1]['cap']))
SF = (Fr(99999, 100000), Fr(93, 25), Fr(sys.argv[2]))   # (B, L, width cap s_plus)
def run(theta, h=Fr(401, 500), sP=Fr(9, 200), sC=Fr(13, 250), sPp=Fr(43, 1000), withS=True):
    (BC, LC, capC), (BP, LP, capP) = C, P
    G = CR.geometry(theta, h, BP, LP, sP)
    faces = {'C': (BC, LC, sC), 'P': (BP, LP, sPp)}
    if withS: faces['S'] = SF
    rec = CR.receipt(G, BP, LP, capC, capP, sC, sPp, CR.THETA_I)
    rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
    if any(v <= 0 for v in rec.values()): return False, None
    cands = CR.candidates(faces, G['kap'])
    used = {}
    for name, d, Ccap in CR.edges(G, BP, LP):
        cov = CR.cover_edge(G, d, Ccap, cands)
        for c in cov:
            used[c[0]] = used.get(c[0], 0) + 1
    return True, used
def ok(th, withS):
    CR.ADM_CACHE.clear()
    try:
        r, used = run(Fr(th, 10**7), withS=withS)
        return r, used
    except (ValueError, AssertionError) as e:
        return False, str(e)[:80]
def star(withS, lo=8744000, hi=8746100):
    if not ok(hi, withS)[0]: return None, ok(hi, withS)
    while hi - lo > 1:
        mid = (lo + hi)//2
        if ok(mid, withS)[0]: hi = mid
        else: lo = mid
    return hi, ok(hi, withS)[1]
print("with S:", star(True), flush=True)
