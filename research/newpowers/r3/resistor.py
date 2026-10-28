"""The count exponent as a 'resistor network' (own derivation), verified against the exact polynomials of the toolchain.

Lines (Lean: common_witness_count_bound hI0/hI/hA, Prop 19.2):   a = k_L - delta   (long slope),
   A_I = 1 - 2p/c_I (inverse slot factor),  A_P = 2 - 4p/Lam (plain slot factor),  D = A_I + A_P,  Z = 2 p B/Lam.
Closed form (affine branch):
        R - (1 - delta) = (1 - Z) / [ 1/delta + A_P ( 1/(delta A_I) + 1/a ) ]
equivalently  1/(R-(1-delta)) * (1-Z) = 1/delta + A_P/(delta A_I) + A_P/a.
The cutoff is t* = T/J, r* = (A_P t* + Z - p')/D, with the toolchain's J = a D + delta A_I A_P, T = J + delta A_I (1-Z).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tc'))
os.environ.setdefault('QRH_K', '9/2')
from fractions import Fraction as Fr
import cert_return as CR
from pm import scenario, face, Model

def R_closed(delta, p, B, Lam, kL=5/6, cI=2.0):
    a = kL - delta; AI = 1 - 2 * p / cI; AP = 2 - 4 * p / Lam; Z = 2 * p * B / Lam
    return 1 - delta + (1 - Z) / (1 / delta + AP * (1 / (delta * AI) + 1 / a))

def R_exact_poly(delta, p, B, Lam):
    """N/J from the exact polynomials of cert_return.branch_affine (Fractions)."""
    br = CR.branch_affine(Fr(B).limit_denominator(10**12), Fr(Lam).limit_denominator(10**12))
    ev = lambda P: sum(c * delta**i * p**j for (i, j), c in P.items())
    return ev(br['N']) / ev(br['J']), ev(br['T']) / ev(br['J'])

def elasticities(delta, p, B, Lam, kL=5/6, cI=2.0):
    """d R / d (parameter) and the series 'resistances' at the point."""
    a = kL - delta; AI = 1 - 2 * p / cI; AP = 2 - 4 * p / Lam; Z = 2 * p * B / Lam
    f = lambda **kw: R_closed(delta, p, kw.get('B', B), kw.get('Lam', Lam), kw.get('kL', kL), kw.get('cI', cI))
    R0 = f(); out = {}
    h = 1e-7
    out['R'] = R0
    out['resistances'] = dict(rho0=1 / delta, rhoI=AP / (delta * AI), rhoL=AP / a, norm=(1 - Z))
    tot = 1 / delta + AP / (delta * AI) + AP / a
    out['weights'] = dict(delta_term=(1 / delta) / tot, I=(AP / (delta * AI)) / tot, L=(AP / a) / tot)
    for nm, kw in (('kL', dict(kL=kL + h)), ('cI', dict(cI=cI + h)), ('Lam', dict(Lam=Lam + h)), ('B', dict(B=B + h))):
        out['dR/d' + nm] = (f(**kw) - R0) / h
    return out

if __name__ == '__main__':
    # (1) exact check at the binding point of the real chain: delta*, p = 1/2, faces of the two scenarios
    for s, (kc, kp) in (('A', (73, 38)), ('B', (46, 38))):
        m = scenario(s); b = m.binding()
        B, Lam = m.BC, m.LC
        d = float(b['delta'])
        Rc = R_closed(d, 0.5, B, Lam)
        Re, te = R_exact_poly(Fr(d).limit_denominator(10**9), Fr(1, 2), B, Lam)
        print('scenario %s: delta*=%.6f  R_closed=%.12f  R_exact(N/J)=%.12f  t*=%.6f   diff %.1e' % (s, d, Rc, float(Re), float(te), Rc - float(Re)))
        e = elasticities(d, 0.5, B, Lam)
        print('   weights of 1/(R-(1-delta))*(1-Z):', {k: round(v, 4) for k, v in e['weights'].items()})
        print('   dR/dkL=%.4f  dR/dcI=%.5f  dR/dLam=%.5f  dR/dB=%.4f' % (e['dR/dkL'], e['dR/dcI'], e['dR/dLam'], e['dR/dB']))
    # (2) a second, independent identity: R from the three LINES by brute-force maximisation over the cutoff t
    import numpy as np
    d, p, B, Lam = 0.4431, 0.5, *face(73)
    a = 5/6 - d
    best = 1e9
    for t in np.linspace(1.0, 1.5, 500001):
        # inverse witness r in [0, t]: for each r the adversary gets min(I(r), P(t-r), L if r>=1) ; take max over r
        r = np.linspace(0, t, 4001)
        I = 1 - d * r - 2 * d * p * (1 - r) / 2
        z = np.minimum(0.09999, np.maximum((B - 2 * (t - r)) / Lam, 0))
        P = 1 - 2 * d * (t - r) - 2 * d * p * z
        L = np.where(r >= 1, (1 + 5 * r) / 6 - d * r, 1e9)
        # I only valid for r<1 (with capacity), L for r>=1
        val = np.where(r < 1, np.minimum(I, P), np.minimum(L, P))
        v = val.max()
        best = min(best, v)
        if t > 1.2: break
    print('brute-force max_r min(lines) minimised over t:  %.6f   closed form %.6f' % (best, R_closed(d, p, B, Lam)))
