"""Anatomy of the binding after Lemma W (new_top, capped count branch at the face cap, p = 1/2).
Prints the binding (delta*, R, r*, m*, t*), the terms of E, the dual weights of the three count lines,
analytic sensitivities, and the Hoelder-tightness check (is Levy's (4/3, 4) step attained by an
adversary consistent with every input?).  usage: python3 anatomy.py [theta_1e7]"""
import sys
from fractions import Fraction as Fr
import base as B
import windows as W
import scan_windows as SW
CR = B.CR

def ev(poly, d, p):
    return sum(c * d**i * p**j for (i, j), c in poly.items())

th = int(sys.argv[1]) if len(sys.argv) > 1 else 8741364
P = B.params('')
W.JOIN = 'crossover'; CR.M_MINUS = Fr(0); W.CONF = SW.conf(P)
G = CR.geometry(Fr(th, 10**7), P['h'], P['BP'], P['LP'], P['sP'])
E = {n: (d, C) for n, d, C in CR.edges(G, P['BP'], P['LP'])}
d, C = E['new_top']
zs = P['cap'] - Fr(1, 10**4) - CR.ETA
br = CR.branch_affine(P['BC'], P['LC'], capped=True, zs=zs)
p = Fr(1, 2)
rp = CR.return_poly(br, G, d, C)
best = None
for k in range(3000, 5501):
    dl = Fr(k, 10000)
    v = ev(rp, dl, p) / ev(br['J'], dl, p)
    if best is None or v < best[0]: best = (v, dl)
v, dl = best
J = ev(br['J'], dl, p); N = ev(br['N'], dl, p); T = ev(br['T'], dl, p)
D = ev(br['D'], dl, p); Rn = ev(br['Rn'], dl, p); Mn = ev(br['Mn'], dl, p)
R = N/J; r = Rn/(D*J); m = Mn/(D*J); t = T/J
f = float
ell, y, h = G['ell'], G['y'], G['h']
q = dl*p
print(f"theta = {th/1e7}, h = {f(h)}, ell = {f(ell):.6f}, y = {f(y):.6f}, kappa = {f(G['kap']):.6f}")
print(f"new_top: d = {f(d):.6f}, C = {f(C):.6f} (face branch {(2*y-(2-P['BP'])*d)/P['LP']:.6f}, s_P d = {f(P['sP']*d):.6f})")
print(f"binding (min over delta of F/J, capped branch z* = {f(zs):.6f}): delta* = {f(dl):.4f}, F/J = {f(v):.2e}")
print(f"  count R = {f(R):.6f}, r* = {f(r):.6f}, m* = {f(m):.6f}, t* = {f(t):.6f}")
terms = {'1/2 + delta/2 (contour)': Fr(1, 2) + dl/2, '13h/75 - 9d/100': 13*h/75 - Fr(9, 100)*d,
         '-y/2': -y/2, '-ell/2': -ell/2, '+delta p ell (amplitudes)': q*ell,
         '-delta p C/2 (numerator slots)': -q*C/2, '(3d/4) R (Hoelder count)': Fr(3, 4)*d*R}
tot = sum(terms.values())
for k, val in terms.items():
    print(f"  E term {k:32s} {f(val): .6f}")
print(f"  E = {f(tot):.7f}  vs theta - r0 = {f(G['theta'] - CR.R0):.7f}")
# dual weights of the three lines at the crossing (p = 1/2: I' = -delta/2, P' = -2 delta, L' = 5/6 - delta)
Ip, Pp, Lp = -dl*(1 - p), -2*dl, Fr(5, 6) - dl
den = 1 - Lp/Ip - Lp/Pp
wI, wP, wL = (Lp/Ip)/(-den)*(-1), (Lp/Pp)/(-den)*(-1), 1/den
print(f"dual weights: inverse {f(wI):.3f}, plain {f(wP):.3f}, long {f(wL):.3f} (sum {f(wI+wP+wL):.3f})")
# sensitivities via the envelope theorem: dtheta = dG/(4 * (1/2 + q + 2q/L_P) + 1)
Gth = 4*(Fr(1, 2) + q + 2*q/P['LP']) + 1
print(f"dtheta*/dR = {f(Fr(3,4)*d/Gth):.4f}, dtheta*/dE = {f(1/Gth):.4f}, dtheta*/dC = {f(-q/2/Gth):.4f}, "
      f"dtheta*/dz*_count = {f(Fr(3,4)*d/Gth * (-wP*2*q)):.4f}")
# Hoelder tightness: worst case puts all U^R class rows at |N|^4 = U^{1 - R - 2 q z_A};
# it is consistent iff that level is below the pointwise bound |N|^2 <= U^{delta n0}
n0 = 1 - y/d; zA = C/d
lvl = 1 - R - 2*q*zA
print(f"Hoelder check: n0 = {f(n0):.4f}, z_A = C/d = {f(zA):.5f}; adversary level |N|^4 = U^{f(lvl):.4f} "
      f"<= pointwise U^(2 delta n0) = U^{f(2*dl*n0):.4f}: {'consistent -> (4/3,4) is attained' if lvl <= 2*dl*n0 else 'NOT consistent'}")
# pointwise alternative and C-S alternative (all in U-exponents, without the common slot factor)
hold = Fr(1, 4) + 3*R/4 - q*zA/2
pw = R + dl*n0/2
cs = R/2 + Fr(1, 2) - q*min(P['cap'], (P['BP'] - n0)/P['LP'])
print(f"numerator exponents (U units): Levy {f(hold):.5f}, pointwise {f(pw):.5f}, Cauchy-Schwarz with face at (n0,0) {f(cs):.5f}")
