"""Pricing pass for the face positions and extra count branches (pricing only; nothing is built).

Faces from the flow (price_faces.flow_face), theta* by theta_star (Lemma W, exactly the Lean branch
set plus optional extra count faces, each with its own affine and capped branch and its own
crossover m_X), best over h in HS.
usage: (source return_cut.env) python3 price_grid.py moveC|moveP|extra
"""
import os, sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_star as T
import price_faces as PF

HS = [Fr(403, 500), Fr(4031, 5000)]
W = Fr(29, 500)
EXACT = T.faces()                       # QRH_FACES: the exact faces of design (b)


def tstar(fc, extra=()):
    res = []
    for h in HS:
        t = T.theta_star(fc, h, W, W, 'lemmaD', 8740800, extra=tuple(extra))
        res.append((t if t is not None else 10**9, h))
    t, h = min(res)
    why = T.certifiable(Fr(t - 1, 10**7), fc, h, W, W, 'lemmaD', why=True, extra=tuple(extra))[1]
    return t, h, why


def face(s, cap):
    B, L = PF.flow_face(Fr(s))
    return (B, L, Fr(cap))


def main():
    what = sys.argv[1]
    if what == 'moveC':          # C along the flow (caps 0.085/0.090/0.095), P = the exact P of design (b)
        for cap in ('17/200', '9/100', '19/200'):
            for s in ('0.0595', '0.0600', '0.0610', '0.0615', '0.0620'):
                t, h, why = tstar((face(s, cap), EXACT[1]))
                print(f'C s={s} cap={float(Fr(cap)):.3f} | P exact: theta*={t/1e7:.7f} h={float(h)} [{why}]', flush=True)
    elif what == 'moveP':        # P along the flow (ramp caps, and 0.095), C at 0.062 with cap 0.095
        C = face('0.0620', '19/200')
        for pcap in ('ramp', '19/200'):
            for k in range(0, 15, 2):
                s = Fr(55, 1000) + Fr(5, 10000)*k
                P = (*PF.flow_face(s), PF.ramp_cap(s) if pcap == 'ramp' else Fr(pcap))
                t, h, why = tstar((C, P))
                print(f'C 0.062/0.095 | P s={float(s):.4f} cap={float(P[2]):.4f}: theta*={t/1e7:.7f} h={float(h)} [{why}]',
                      flush=True)
    elif what == 'extra':        # design (b) plus k extra count faces from the family (s <= 0.0595) or beyond
        base = EXACT
        print('design (b), no extra:', tstar(base), flush=True)
        pool = ['0.0300', '0.0400', '0.0450', '0.0500', '0.0520', '0.0540', '0.0560', '0.0570', '0.0580', '0.0590']
        best1 = None
        for s in pool:
            ex = [('X1', *face(s, '111411/1310720'))]
            t, h, why = tstar(base, ex)
            print(f'+1 face at s={s} (cap 0.0850): theta*={t/1e7:.7f} h={float(h)} [{why}]', flush=True)
            best1 = min(best1 or (t, s), (t, s))
        for s in ('0.0610', '0.0620'):
            for cap in ('17/200', '19/200'):
                ex = [('X1', *face(s, cap))]
                t, h, why = tstar(base, ex)
                print(f'+1 face beyond the family at s={s} (cap {float(Fr(cap)):.3f}): theta*={t/1e7:.7f} '
                      f'h={float(h)} [{why}]', flush=True)
        for ss in (('0.0610', '0.0620'), ('0.0600', '0.0610', '0.0615', '0.0620')):
            ex = [(f'X{i}', *face(s, '19/200')) for i, s in enumerate(ss)]
            t, h, why = tstar(base, ex)
            print(f'+{len(ss)} faces beyond the family at {ss} (cap 0.095): theta*={t/1e7:.7f} h={float(h)} [{why}]',
                  flush=True)


if __name__ == '__main__':
    main()
