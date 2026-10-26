"""Exact theta* of the Lean final return for a faces file, with exactly gen_return_lean.py's checks.

The test of a theta is what gen_return_lean.py checks before it emits the Lean certificate:
  * the scalar receipts of cert_return.receipt (mode QRH_MODE, `lemmaD`: Collet's window receipts
    and `source_lambda_low` dropped; `dMinus_lower_3_4` is ds > QRH_DMINUS);
  * the edge order ds < dk < dp and the capacity join at ds (emit_constants);
  * a cover of [0,3/4]x[0,1/2] for each of the six conductor edges by the branches that the Lean
    formulas have (old, C, capC, weakC7, P, capP), with positive Bernstein rows and admissions.
Bisection in units of 1e-7 (as research/mixed-step/ret_scan.py, which allows more branches).

usage: (source return_cut.env) python3 theta_star.py [LO]     (LO default 8730000, units of 1e-7)
Prints whether the declared QRH_THETA passes, and theta* = the least passing theta/1e7 (searched
below the declared theta, or above it in steps of 1e-6 when the declared theta fails).
"""
import os, sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
import cert_return as CR
import gen_return_lean as GR


def faces():
    F = json.load(open(os.environ['QRH_FACES']))
    C, P = F[0], F[1]
    assert C.get('name', 'C') == 'C' and P.get('name', 'P') == 'P'
    return tuple(tuple(Fr(n[k]) for k in ('B', 'L', 'cap')) for n in (C, P))


def certifiable(th, fc, h, sC, sP, mode, why=False):
    (BC, LC, capC), (BP, LP, capP) = fc
    G = CR.geometry(th, h, BP, LP, sP)
    rec = CR.receipt(G, BP, LP, capC, capP, sC, Fr(43, 1000), CR.THETA_I)
    drop = CR.GLOBAL_DROP + (('source_lambda_low',) if mode == 'lemmaD' else ()) if mode != 'pr69' else ()
    bad = {k: float(v) for k, v in rec.items() if k not in drop and v <= 0}
    if bad:
        return (False, f'receipts {bad}') if why else False
    try:
        _, _, edges = GR.emit_constants(dict(theta=th, h=h, BP=BP, LP=LP, BC=BC, LC=LC, sP=sP))
    except AssertionError as e:
        return (False, f'constants: {e}') if why else False
    cands = [cd for cd in CR.candidates({'C': (BC, LC, sC), 'P': (BP, LP, Fr(43, 1000))}, G['kap'])
             if cd[0] in GR.ALLOWED]
    cands.sort(key=lambda cd: GR.ALLOWED.index(cd[0]))
    for nm, d, C in edges:
        try:
            GR.cover_tree(G, d, C, cands)
        except ValueError:
            return (False, f'cover of edge {nm}') if why else False
    return (True, 'ok') if why else True


def main():
    fc = faces()
    h, sC, sP = (Fr(os.environ[k]) for k in ('QRH_H', 'QRH_SC', 'QRH_SP'))
    mode = os.environ.get('QRH_MODE', 'lemmaD')
    th = Fr(os.environ['QRH_THETA'])
    print('faces C', [float(v) for v in fc[0]], 'P', [float(v) for v in fc[1]])
    print('declared theta', th, float(th), '->', certifiable(th, fc, h, sC, sP, mode, why=True))
    # the search starts at the declared theta: far above it, dk > dp and the Lean layout (six edges,
    # the kink before the top) no longer applies, so certifiability is monotone only near theta*
    hi = -(-th.numerator * 10**7 // th.denominator)
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 8730000
    step = 0
    while not certifiable(Fr(hi, 10**7), fc, h, sC, sP, mode):
        step += 1
        if step > 200:
            print('no certifiable theta within 2e-5 above the declared one')
            return
        lo, hi = hi, hi + 10
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if certifiable(Fr(mid, 10**7), fc, h, sC, sP, mode) else (mid, hi)
    print(f'theta* = {hi}/10^7 = {hi / 1e7}  ({lo}/10^7 fails: '
          f'{certifiable(Fr(lo, 10**7), fc, h, sC, sP, mode, why=True)[1]})')


if __name__ == '__main__':
    main()
