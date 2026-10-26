"""Independent check of Lemma W (opened count windows + crossover tail join) on the final cover.

For every rectangle of the exact cover that uses an improved branch, sample points (corners, edge
midpoints, centre) and check the witness argument directly from its definitions, not from the
admission polynomials:
  * R = N/J equals I(r*), P_b(m*), L(t*)                      (crossing algebra, FR4/FR5)
  * 23/37 <= r* <= 1 and 1 <= t* <= 12499/10000                (inverse and cutoff ranges)
  * the branch never uses more width than the face proves at m*:
        capped: z* <= min(cap_face, (B - 2m*)/L);  affine: (B - 2m*)/L <= cap_face
  * for every plain length m in [m*, 1/2) (fine grid) the TRUE plain count
        P_true(m) = 1 - 2 delta m - 2 delta p max(min(cap_face, (B-2m)/L), (1-2m)/K)
    is <= R  (face on [m*, m_X], natural face beyond; this is what the witness argument uses)
  * the returned exponent: J (theta - r0 - E_base) - (3/4) d N > 0 at the point.
usage: python3 verify_windows.py [theta_1e7] [spec]"""
import sys
from fractions import Fraction as Fr
import base as B
import windows as W
import scan_windows as SW
CR = B.CR

def ev(poly, d, p):
    return sum(c * d**i * p**j for (i, j), c in poly.items())

def main():
    th = int(sys.argv[1]) if len(sys.argv) > 1 else 8741364
    spec = sys.argv[2] if len(sys.argv) > 2 else ''
    _, P = SW.theta(spec + (',' if spec else '') + 'h=2011/2500') if False else (None, None)
    kv = dict(x.split('=') for x in spec.split(',') if x)
    W.JOIN = kv.pop('join', 'crossover')
    CR.M_MINUS = Fr(kv.pop('mminus', '0'))
    P = B.params(','.join(f'{k}={v}' for k, v in kv.items()))
    W.CONF = SW.conf(P)
    CR.ADM_CACHE.clear()
    rec, cov, bad = CR.run(Fr(th, 10**7), P['h'], (P['BC'], P['LC'], P['cap']), (P['BP'], P['LP'], P['cap']),
                           verbose=False, sP=P['sP'], sC=P['sC'], sPp=P['sPp'], mode='global')
    assert not bad, bad
    G = CR.geometry(Fr(th, 10**7), P['h'], P['BP'], P['LP'], P['sP'])
    cands = {n: (br, meta) for n, br, meta in
             CR.candidates({'C': (P['BC'], P['LC'], P['sC']), 'P': (P['BP'], P['LP'], P['sPp'])}, G['kap'])}
    E = {n: (d, C) for n, d, C in CR.edges(G, P['BP'], P['LP'])}
    K = CR.K_I; capF = P['cap']; ETA = CR.ETA
    nchk = 0; worst = {}
    def note(k, v):
        if k not in worst or v < worst[k]: worst[k] = v
    for edge, name, box, m, am in cov:
        d, C = E[edge]
        br, meta = cands[name]
        (d0, d1), (p0, p1) = box
        pts = [(a, b) for a in (d0, (d0+d1)/2, d1) for b in (p0, (p0+p1)/2, p1)]
        for dl, p in pts:
            J = ev(br['J'], dl, p); N = ev(br['N'], dl, p)
            Eb = Fr(1, 2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9, 100)*d + dl/2 + dl*p*(G['ell'] - C/2)
            note('return J(theta-r0-E)-3dN/4', J*(G['theta'] - CR.R0 - Eb) - Fr(3, 4)*d*N)
            if meta is None:
                note('old J', J); continue
            Bf, L, s_plus, capped = meta
            D = ev(br['D'], dl, p); T = ev(br['T'], dl, p); Rn = ev(br['Rn'], dl, p); Mn = ev(br['Mn'], dl, p)
            R = N/J; r = Rn/(D*J); mm = Mn/(D*J); t = T/J
            I_ = 1 - dl*(p + (1 - p)*r); L_ = Fr(1, 6) + (Fr(5, 6) - dl)*t
            zb = (s_plus - ETA) if capped else (Bf - 2*mm)/L
            P_ = 1 - 2*dl*mm - 2*dl*p*zb
            assert I_ == R and L_ == R and P_ == R and r + mm == t, (name, dl, p)
            note('r*-23/37', r - Fr(23, 37)); note('1-r*', 1 - r)
            note('t*-1', t - 1); note('1.2499-t*', Fr(12499, 10000) - t)
            note('m*', mm)
            face_w = min(capF, (Bf - 2*mm)/L)
            note('face width at m* - branch width', face_w - zb)
            # true plain count on [m*, 1/2)
            mX = (K*Bf - L)/(2*(K - L))
            grid = [mm + (Fr(1, 2) - mm)*Fr(k, 400) for k in range(400)] + [mX]
            for m_ in grid:
                if m_ < mm: continue
                w = max(min(capF, (Bf - 2*m_)/L), (1 - 2*m_)/K)
                note('R - P_true(m), m>=m*', R - (1 - 2*dl*m_ - 2*dl*p*w))
            nchk += 1
    print(f"theta={th}: {len(cov)} rectangles, {nchk} improved-branch sample points checked")
    for k, v in sorted(worst.items()):
        print(f"  min {k:40s} {float(v): .3e}  {'OK' if v >= 0 else 'VIOLATED'}")

if __name__ == '__main__':
    main()
