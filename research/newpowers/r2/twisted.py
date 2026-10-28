"""twisted.py -- ledger of TWISTED amplifier types (R2, Q3) and the break-even conductor charge.

Parametrisation (derived in R2_ledger.md s4, identities from R1 and Lean `square_twist`/`normalized_fourth_power`):
  block D^m (m = 1,2,3) in the column, h = D^(m-1) H'  (support of g(D^m,.): v_D(h) = m-1),
  residual evaluated at the frequency  D^j H'   (j >= 0).
  twist-free  <=>  j = j_free = (4m mod 6) + m - 1  (m=1:4, m=2:3, m=3:2)           [R1; Lean for m=1,2]
  otherwise the residual carries chi_n(D)^(j_free - j) (order 6/gcd(6, j_free-j)), a character of conductor N(D) = U^d
  of the residual columns n  -- NOT a character of the fixed ray modulus of `ActualLow`.

Ledger per unit block volume d (x2' = 2 alpha' - mu',  alpha' = alpha - m d,  mu' = mu - (m-1) d + j d):
  c = m + 1 + j                                  (twist-free: 6 for m = 1,2,3)
  r = 1
  e = 1 (volume V -> V/W)  + [m >= 2] (divisor-bounded Cauchy-Schwarz over D || h)  - [twisted] (the W different twisted
      residuals are bounded one by one: the count W of the Cauchy-Schwarz is not absorbed by a common pushforward)
  pool p^k (outside the column): twist-free only for k = 6;  twisted: e = 0, c = k, r = 0.
unit payment  pi = e + q r - c q beta  (LOW);   break-even conductor charge kappa*  (extra scale cost per unit d that a
conductor-uniform source theorem may charge before pi < 0):  kappa* = (e + q r)/(q beta) - c.
"""
from math import gcd

Q_OP, BETA_OP = 0.6, 0.4442            # operating point of the floor wall (L = 2.2031, B = 0.97855)
Q_ST, BETA_ST = 0.75, 0.3889           # start of the chain (L = 2.5715, B = 0.99999)


def j_free(m):
    return (4 * m) % 6 + m - 1


def twist_order(m, j):
    d = (j_free(m) - j) % 6
    return 1 if d == 0 else 6 // gcd(d, 6)


def amp(m, j):
    tw = twist_order(m, j) != 1
    e = 1 + (1 if m >= 2 else 0) - (1 if tw else 0)
    return e, m + 1 + j, 1, twist_order(m, j)


def pay(e, c, r, q, b):
    return e + q * r - c * q * b


def kappa_star(e, c, r, q, b):
    return (e + q * r) / (q * b) - c


NAMES = {1: 'D^1 (simple)', 2: 'D^2 (squared)', 3: 'D^3 (cubed)'}
TW = {1: 'none', 2: 'quadratic', 3: 'cubic', 6: 'sextic'}


def rows():
    out = []
    for m in (1, 2, 3):
        for j in range(0, j_free(m) + 1):
            e, c, r, o = amp(m, j)
            out.append((m, j, o, e, c, r, pay(e, c, r, Q_OP, BETA_OP), pay(e, c, r, Q_ST, BETA_ST),
                        kappa_star(e, c, r, Q_OP, BETA_OP) if o != 1 else None))
    for k in range(1, 6):
        out.append((0, k, {1: 6, 2: 3, 3: 2, 4: 3, 5: 6}[k], 0, k, 0, pay(0, k, 0, Q_OP, BETA_OP), pay(0, k, 0, Q_ST, BETA_ST), None))
    return out


if __name__ == '__main__':
    print('| type | j (residual at D^j H\') | twist | e | c | r | pi @ q=.60,beta=.444 | pi @ start (q=.75,beta=.389) | kappa* |')
    print('|---|---|---|---|---|---|---|---|---|')
    for (m, j, o, e, c, r, p1, p2, ks) in rows():
        nm = ('pool p^%d' % j) if m == 0 else ('%s' % NAMES[m])
        jj = '-' if m == 0 else str(j)
        print('| %s | %s | %s | %g | %g | %g | %+.3f | %+.3f | %s |' % (nm, jj, TW[o], e, c, r, p1, p2,
                                                                       '-' if ks is None else '%.2f' % ks))
