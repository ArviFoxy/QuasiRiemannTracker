"""Price the face positions (pricing only; nothing is generated or built).

theta* of the Lean return (theta_star.certifiable: Lemma W, exactly the Lean branch set, the transport
bounds of return_cut.env) when the count face C and the physical face P sit at other positions s of
the mixed flow research/mixed-step/flow_k92.json (rows s, E, L, q with B = E + L s; linear
interpolation between rows). Caps: C at 17/200 (the ramp's end value); P on the piece-7 ramp
cap(y) = 3/40 + y/100 with y = (s - S7)/(0.0595 - S7), S7 fixed by P's node (y = 35747/65536 at
s = 0.057), clipped to [3/40, 3/40 + 1/100]; --cap X sets both caps to X instead.
usage: (source return_cut.env) python3 price_faces.py C|P|grid [--h H1,H2] [--cap X] [--exactP]
  C: C at s = 0.0595 .. 0.0620 with P fixed (exact P of QRH_FACES with --exactP, else flow P at 0.057)
  P: P at s = 0.055 .. 0.062 with C at --sC (default 0.0595)
"""
import os, sys, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_star as T

FLOW = json.load(open('/home/user/QuasiRiemannTracker/research/mixed-step/flow_k92.json'))
S7 = Fr(57, 1000) - (Fr(595, 10000) - Fr(57, 1000)) * Fr(35747, 65536) / (1 - Fr(35747, 65536))


def flow_face(s):
    s = Fr(s)
    rows = [(Fr(str(r['s'])), Fr(repr(r['E'])), Fr(repr(r['L']))) for r in FLOW]
    for (s0, E0, L0), (s1, E1, L1) in zip(rows, rows[1:]):
        if s0 <= s <= s1:
            t = (s - s0) / (s1 - s0)
            E, L = E0 + t*(E1 - E0), L0 + t*(L1 - L0)
            return E + L*s, L
    raise ValueError(f's = {float(s)} outside the flow')


def ramp_cap(s, const=None):
    if const is not None:
        return Fr(const)
    y = min(max((Fr(s) - S7) / (Fr(595, 10000) - S7), Fr(0)), Fr(1))
    return Fr(3, 40) + y/100


def best(fc, hs, sC, sP, anchor=8740800):
    out = []
    for h in hs:
        t = T.theta_star(fc, h, sC, sP, 'lemmaD', anchor)
        out.append((t if t is not None else 10**9, h))
    return min(out)


def why(fc, t, h, sC, sP):
    return T.certifiable(Fr(t - 1, 10**7), fc, h, sC, sP, 'lemmaD', why=True)[1]


def main():
    args = sys.argv[1:]
    what = args[0]
    hs = [Fr(v) for v in (args[args.index('--h') + 1].split(',') if '--h' in args else ['8055/10000', '403/500', '4031/5000'])]
    cap = args[args.index('--cap') + 1] if '--cap' in args else None
    sC0, sP0 = Fr(29, 500), Fr(29, 500)   # the windows SC, SP (not the face positions)
    exact = T.faces()
    if what == 'C':
        P = exact[1] if '--exactP' in args else (*flow_face(Fr(57, 1000)), ramp_cap(Fr(57, 1000), cap))
        print('P', 'exact' if '--exactP' in args else 'flow at 0.057', [float(v) for v in P], flush=True)
        for s in ('0.0595', '0.0600', '0.0605', '0.0610', '0.0615', '0.0620'):
            B, L = flow_face(Fr(s))
            fc = ((B, L, Fr(cap) if cap else Fr(17, 200)), P)     # the ramp's end value 0.085 (non-binding)
            t, h = best(fc, hs, sC0, sP0)
            print(f'C at s={s}: B={float(B):.7f} L={float(L):.7f} cap={float(fc[0][2]):.5f} -> theta*={t/1e7:.7f} '
                  f'at h={float(h)}  [{why(fc, t, h, sC0, sP0)}]', flush=True)
    elif what == 'P':
        sC = Fr(args[args.index('--sC') + 1]) if '--sC' in args else Fr('0.0595')
        B, L = flow_face(sC)
        C = (B, L, Fr(cap) if cap else Fr(17, 200))
        print('C flow at', float(sC), [float(v) for v in C], flush=True)
        for k in range(15):
            s = Fr(55, 1000) + Fr(5, 10000)*k
            Bp, Lp = flow_face(s)
            fc = (C, (Bp, Lp, ramp_cap(s, cap)))
            t, h = best(fc, hs, sC0, sP0)
            print(f'P at s={float(s):.4f}: B={float(Bp):.7f} L={float(Lp):.7f} cap={float(fc[1][2]):.5f} -> '
                  f'theta*={t/1e7:.7f} at h={float(h)}  [{why(fc, t, h, sC0, sP0)}]', flush=True)


if __name__ == '__main__':
    main()
