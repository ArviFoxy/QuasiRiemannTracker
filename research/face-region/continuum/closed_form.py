"""Closed-form continuum slope of the marked density chain, checked against ode2.py and the 130 chain faces.

sigma(B, Lam) = (B - kappa)/(Lam - kappa),  kappa = 1 - y = 4(5 - 3q)/(25 - 18q),  q = min(0.999 Lam/(6B - Lam), 3/4).
Also: the two binding facets (1,0) and (1,2) at p = 1/2 give the same threshold (exact, Fractions)."""
import os, sys
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'newpowers', 'ta'))
from faces import load_faces
import ode2

def q_of(B, L): return min(0.999*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
def sigma(B, L):
    k = kappa(q_of(B, L)); return (B - k)/(L - k)

# 1. exact tie of the two binding facets at p = 1/2 (Fractions): gate_k/nu = (Lam-1)s - B + root_k
def roots_half(nu, s, B, L):
    w = 5 - 6*nu
    a = 5 + w
    r10 = (a + w*s/2)/(a + w/2)
    r12 = (a + w*B/(2*(L - 1)))/(a + w*L/(2*(L - 1)))
    return r10, r12
for (nu, B, L) in [(Fr(3, 4), Fr(99985, 100000), Fr(5133, 2000)), (Fr(1, 2), Fr(96232839, 10**8), Fr(3853, 2000)),
                   (Fr(5, 8), Fr(98, 100), Fr(22, 10))]:
    w = 5 - 6*nu; y = w/(10 + 3*w)
    s = (B - 1 + y)/(L - 1 + y)
    r10, r12 = roots_half(nu, s, B, L)
    print('nu=%s: gate(1,0) = %s, gate(1,2) = %s at s = sigma (exact)' % (nu, (L - 1)*s - B + r10, (L - 1)*s - B + r12))

# 2. pointwise against ode2.s0_inst (numerical inf over nu in [q,3/4], p and the six facets) along the chain
steps, faces = load_faces()
mx = 0.0
for k in range(0, 130, 4):
    B, L, c = (float(x) for x in faces[k])
    a, b = sigma(B, L), ode2.s0_inst(B, L, q_of(B, L))
    mx = max(mx, abs(a - b))
print('max |closed form - ode2.s0_inst| at 33 chain faces: %.2e' % mx)

# 3. trajectory from the boot face vs the chain
B0, L0 = 0.99999, 2.5715
sol = solve_ivp(lambda L, y: [sigma(y[0], L)], [L0, 1.85], [B0], method='DOP853', rtol=1e-12, atol=1e-14,
                dense_output=True)
print(' Lam      B_chain      B_continuum  diff')
for k in [0, 1, 32, 64, 96, 128, 129]:
    B, L, c = (float(x) for x in faces[k])
    Bc = float(sol.sol(L)[0])
    print('%.4f  %.8f  %.8f  %+.2e' % (L, B, Bc, Bc - B))
Lf = brentq(lambda L: q_of(float(sol.sol(L)[0]), L) - 0.5, 1.86, 2.2, xtol=1e-12)
print('continuum reaches the floor q = 1/2 at Lam = %.6f, B = %.8f' % (Lf, float(sol.sol(Lf)[0])))
# 4. envelope relation E(s) = kappa (1 - s) at the contact points of the chain faces
mx = 0.0
for k in range(1, 129):
    B0_, L0_, _ = (float(x) for x in faces[k - 1]); B, L, _ = (float(x) for x in faces[k])
    s = (B0_ - B)/(L0_ - L)
    mx = max(mx, abs((B - L*s) - kappa(q_of(B, L))*(1 - s)))
print('max |E(s_k) - kappa(q_k)(1 - s_k)| over the discrete chain: %.2e (discretisation)' % mx)
