"""Exact rational checks (Fractions) of the identities used to define the count variants."""
from fractions import Fraction as Fr
import random

def rho(nu): return 1 - 10 * nu / (15 - 6 * nu)
def counting_R(k, d, p):                       # Lean Cycle61 countingR (Feedback.lean:17)
    den = 3 * k * (3 - p) - 2 * p
    c = 2 * (1 - p) * (3 * k - p) / den
    rowden = (Fr(5, 6) - d) + d * c
    return 1 - d + d * c * (Fr(5, 6) - d) / (2 * rowden)
def R_old(d, p, k):                            # cert_return.branch_old: N/J
    V = Fr(5, 6) - d
    D = 3 - p - 2 * p / (3 * k)
    C = 2 * (1 - p) * (1 - p / (3 * k))
    J = V * D + d * C
    N = (1 - d) * J + d * C * V / 2
    return N / J
def R_affine(d, p, B, L):                      # cert_return.branch_affine: N/J
    V = Fr(5, 6) - d
    D = 3 - p - 4 * p / L; A = 2 - 4 * p / L; C0 = 1 - 2 * B * p / L
    U = (1 - p) * C0
    J = V * D + d * (1 - p) * A
    N = (1 - d) * J + V * d * U
    return N / J
def xi_K(nu, p, S, Q, K, BH, LH, hH):         # Gain.lean xiP (least branch root)
    w = 5 - 6 * nu
    inv = [(1 / (1 - p), p * Q / (1 - p))]
    if K:
        inv.append((Fr(1), 2 * p * K * S))
    d2 = 1 - 2 * p / LH
    pl = [(Fr(1), 2 * p * S), (Fr(1), 2 * p * hH * Q), (1 / d2, (2 * p * BH * Q / LH) / d2)]
    return min((5 * Q + w * (oi + oj / 2)) / (6 * nu + w * (si + sj / 2)) for (si, oi) in inv for (sj, oj) in pl)
def f_class(nu, p, S, Q, K, BH, LH, hH):
    return (1 - 2 * p) * nu * S + nu * (xi_K(nu, p, S, Q, K, BH, LH, hH) - Fr(10) / (15 - 6 * nu) * Q)

random.seed(7)
ok = True
for _ in range(2000):
    nu = Fr(random.randint(50, 75), 100); k = Fr(random.randint(70, 75), 100)
    B = Fr(random.randint(950, 1000), 1000); L = Fr(random.randint(190, 330), 100)
    S = Fr(random.randint(10, 100), 1000); Q = Fr(random.randint(900, 1000), 1000); h = Fr(random.randint(50, 150), 1000)
    ok &= counting_R(k, nu, Fr(0)) == rho(nu)
    ok &= R_old(nu, Fr(1, 3), k) == counting_R(k, nu, Fr(1, 3))
    ok &= R_affine(nu, Fr(0), B, L) == rho(nu)
    ok &= f_class(nu, Fr(0), S, Q, 2, B, L, h) == nu * S
    ok &= f_class(nu, Fr(1, 2), S, Q, 1, B, L, h) >= 0
print('all exact identities hold on 2000 random rational points:', ok)
print('countingR(k,d,0)=rho(d); old branch N/J == countingR; affine branch at p=0 == rho; f_0 = nu*S; f_{1/2} >= 0')
