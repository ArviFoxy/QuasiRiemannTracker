"""Exact theta* of the Lean final return for a faces file, with exactly gen_return_lean.py's checks.

The test of a theta is what gen_return_lean.py checks before it emits the Lean certificate, plus
the transport layer's parameter bounds that FinalReturn/TransportInstances.lean proves:
  * the scalar receipts of cert_return.receipt (mode QRH_MODE, `lemmaD`: Collet's window receipts
    and `source_lambda_low` dropped; `dMinus_lower_3_4` is ds > QRH_DMINUS);
  * Geometry.BoundsR at (theta, h): 874/1000 < theta < 7/8, 793/1000 < h < H, 458/1000 < y < Y,
    1672/10000 < ell < E with QRH_RELAXED = 'H,Y,E', small_saving and floor_margin;
  * the edge order ds < dk < dp and the capacity join at ds (emit_constants);
  * a cover of [0,3/4]x[0,1/2] for each of the six conductor edges by the branches that the Lean
    formulas have (old, C, capC, weakC7, P, capP), with positive Bernstein rows and admissions.
    With QRH_WINDOWS=lemmaW the admissions are Lemma W's (cert_return.admission_polys_W) and the
    windows reach the window caps of gen_return_lean.window_caps (QRH_WCAP, or face cap - 1e-4).
Bisection in units of 1e-7.

usage: (source return_cut.env) python3 theta_star.py [--anchor A] [--h H1,H2,...]
  A: a theta (units 1e-7) to start from (default: the declared QRH_THETA rounded up); the search
     bisects below it, or steps up by 1e-6 first when it fails.
  --h: scan these h values (exact decimals or fractions) instead of QRH_H; prints theta*(h).
"""
import os, sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
import cert_return as CR
import gen_return_lean as GR

RELAXED = [Fr(v) for v in os.environ.get('QRH_RELAXED', '803/1000,467/1000,1678/10000').split(',')]


def face_list(path):
    """The faces [C, P] of a faces file: a list [C, P] (faces_exact.json) or a dict {C:…, P:…} (faces_k92.json)."""
    F = json.load(open(path))
    if isinstance(F, dict):
        F = [dict(F['C'], name='C'), dict(F['P'], name='P')]
    assert [f.get('name', n) for f, n in zip(F, 'CP')] == ['C', 'P'] and len(F) == 2
    return F


def faces():
    return tuple(tuple(Fr(n[k]) for k in ('B', 'L', 'cap')) for n in face_list(os.environ['QRH_FACES']))


def bounds_r(G):
    """Geometry.BoundsR (ReturnD/TransportGeometry.lean) at the final parameters: name -> slack."""
    th, h, x, y, ell, dP = (G[k] for k in ('theta', 'h', 'x', 'y', 'ell', 'dplus'))
    H, Y, E = RELAXED
    signal = x/2 + (y - x)/12
    return {'theta>874/1000': th - Fr(874, 1000), 'theta<7/8': Fr(7, 8) - th,
            'h>793/1000': h - Fr(793, 1000), 'h<H': H - h, 'y>458/1000': y - Fr(458, 1000), 'y<Y': Y - y,
            'ell>1672/10000': ell - Fr(1672, 10000), 'ell<E': E - ell,
            'small_saving': y/2 - h*(Fr(17, 50) - Fr(1, 6)) - Fr(1, 50) - Fr(7, 100),
            'floor_margin': signal - Fr(1, 200) - (Fr(4, 25)*x - Fr(3, 20) - Fr(51, 100)*y + Fr(67, 100)*dP
                                                   - Fr(3, 20)*ell) + Fr(1, 10**30)}


def certifiable(th, fc, h, sC, sP, mode, why=False):
    (BC, LC, capC), (BP, LP, capP) = fc
    G = CR.geometry(th, h, BP, LP, sP)
    rec = CR.receipt(G, BP, LP, capC, capP, sC, Fr(43, 1000), CR.THETA_I)
    drop = CR.GLOBAL_DROP + (('source_lambda_low',) if mode == 'lemmaD' else ()) if mode != 'pr69' else ()
    bad = {k: float(v) for k, v in rec.items() if k not in drop and v <= 0}
    bad.update({k: float(v) for k, v in bounds_r(G).items() if v <= 0})
    if bad:
        return (False, f'receipts {bad}') if why else False
    try:
        _, _, edges = GR.emit_constants(dict(theta=th, h=h, BP=BP, LP=LP, BC=BC, LC=LC, sP=sP))
    except AssertionError as e:
        return (False, f'constants: {e}') if why else False
    if CR.WINDOWS == 'lemmaW':
        wC, wP = GR.window_caps(capC, capP)
        GR.lemma_w_branches(BC, LC, BP, LP)
        fdict = {'C': (BC, LC, wC), 'P': (BP, LP, wP)}
    else:
        fdict = {'C': (BC, LC, sC), 'P': (BP, LP, Fr(43, 1000))}
    cands = [cd for cd in CR.candidates(fdict, G['kap']) if cd[0] in GR.ALLOWED]
    cands.sort(key=lambda cd: GR.ALLOWED.index(cd[0]))
    for nm, d, C in edges:
        try:
            GR.cover_tree(G, d, C, cands)
        except ValueError:
            return (False, f'cover of edge {nm}') if why else False
    return (True, 'ok') if why else True


def theta_star(fc, h, sC, sP, mode, anchor, lo=8700000):
    """least passing theta (units 1e-7) at h, searched from the anchor; None if none within 2e-5 above."""
    hi, step = anchor, 0
    while not certifiable(Fr(hi, 10**7), fc, h, sC, sP, mode):
        step += 1
        if step > 20:
            return None
        lo, hi = hi, hi + 10
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if certifiable(Fr(mid, 10**7), fc, h, sC, sP, mode) else (mid, hi)
    return hi


def main():
    fc = faces()
    sC, sP = (Fr(os.environ[k]) for k in ('QRH_SC', 'QRH_SP'))
    mode = os.environ.get('QRH_MODE', 'lemmaD')
    th = Fr(os.environ['QRH_THETA'])
    args = sys.argv[1:]
    anchor = -(-th.numerator * 10**7 // th.denominator)
    if '--anchor' in args:
        anchor = int(args[args.index('--anchor') + 1])
    hs = [Fr(os.environ['QRH_H'])]
    if '--h' in args:
        hs = [Fr(v) for v in args[args.index('--h') + 1].split(',')]
    print('faces C', [float(v) for v in fc[0]], 'P', [float(v) for v in fc[1]], ' windows', CR.WINDOWS,
          ' relaxed', [str(v) for v in RELAXED], flush=True)
    if CR.WINDOWS == 'lemmaW':
        print('window caps', [str(v) for v in GR.window_caps(fc[0][2], fc[1][2])], flush=True)
    best = None
    for h in hs:
        if len(hs) == 1:
            print('declared theta', th, float(th), 'at h', h, '->', certifiable(th, fc, h, sC, sP, mode, why=True))
        t = theta_star(fc, h, sC, sP, mode, anchor)
        if t is None:
            print(f'h = {h} ({float(h)}): no certifiable theta near the anchor', flush=True)
            continue
        why = certifiable(Fr(t - 1, 10**7), fc, h, sC, sP, mode, why=True)[1]
        print(f'h = {h} ({float(h)}): theta* = {t}/10^7 = {t / 1e7}  ({t - 1}/10^7 fails: {why})', flush=True)
        if best is None or t < best[0]:
            best = (t, h)
    if best and len(hs) > 1:
        print(f'best: theta* = {best[0]}/10^7 at h = {best[1]} ({float(best[1])})')


if __name__ == '__main__':
    main()
