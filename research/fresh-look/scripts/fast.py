"""Vectorised float model of Formulas.lean (branch values, 15 guards) for arrays of faces / points.
Mirrors model.py (checked against it in selftest())."""
import numpy as np

ETA = 1e-7
MMINUS, SMINUS, K = 0.377, 0.03, 4.5
NATM = (1 - K * SMINUS) / 2


def branch(d, p, B, L, cap, capped):
    """all arguments broadcastable numpy arrays (capped: bool array). returns dict of arrays"""
    d, p, B, L, cap = (np.asarray(v, dtype=float) for v in (d, p, B, L, cap))
    capped = np.asarray(capped, dtype=bool)
    V = 5 / 6 - d
    Zc = cap - ETA
    D = np.where(capped, 3 - p, 3 - p - 4 * p / L)
    A = np.where(capped, 2.0 + 0 * p, 2 - 4 * p / L)
    C0 = np.where(capped, 1 - 2 * Zc * p, 1 - 2 * B * p / L)
    Z = np.where(capped, 2 * Zc * p, 2 * B * p / L)
    dD = np.where(capped, -1.0, -1 - 4 / L)
    dA = np.where(capped, 0.0, -4 / L)
    dC = np.where(capped, -2 * Zc, -2 * B / L)
    U = (1 - p) * C0
    J = V * D + d * (1 - p) * A
    N = (1 - d) * J + V * d * U
    T = J + d * U
    RN = A * T + (Z - p) * J
    MN = D * T - RN
    DJ = D * J
    dU = -C0 + dC * (1 - p)
    dJ = dD * V + d * (-A + dA * (1 - p))
    return dict(D=D, A=A, C0=C0, Z=Z, U=U, J=J, N=N, T=T, RN=RN, MN=MN, DJ=DJ, dU=dU, dJ=dJ, Zc=Zc, V=V)


def guards(d, p, B, L, cap, capped, upper_t=1.2499, mMinus=MMINUS, sMinus=SMINUS, K_=K):
    b = branch(d, p, B, L, cap, capped)
    B, L, cap = (np.asarray(v, dtype=float) for v in (B, L, cap))
    capped = np.asarray(capped, dtype=bool)
    nm = (1 - K_ * sMinus) / 2
    Zc = b['Zc']
    lowerM = np.where(capped, mMinus + ETA, np.maximum(mMinus + ETA, (B - L * (cap - ETA)) / 2 + ETA))
    upperM = np.where(capped, np.minimum(np.minimum(11 / 25 - ETA, nm - ETA), (B - L * Zc) / 2 - ETA),
                      np.minimum(np.minimum(11 / 25 - ETA, nm - ETA), (B - L * (sMinus + ETA)) / 2 - ETA))
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (b[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    tail = 1 - 2 * nm * d - 2 * sMinus * d * p
    one = np.ones_like(J)
    g = [D, A, C0, J, T - J, upper_t * J - T, RN - 23 / 37 * DJ, DJ - RN, MN - lowerM * DJ, upperM * DJ - MN,
         N - tail * J, U * dJ - dU * J,
         (11 / 25 - nm - ETA) * one,
         (B - 2 * nm - L * (sMinus + ETA) - 2 * ETA) * one,
         np.where(capped, (Zc - sMinus - ETA) * DJ, 1.0)]
    return g, b


def count(d, p, B, L, cap, capped):
    b = branch(d, p, B, L, cap, capped)
    return b['N'] / b['J']


def old_count(d, p, kappa):
    k3 = 3 * kappa
    V = 5 / 6 - d
    oldD = 3 - p - 2 * p / k3
    oldC = 2 * (1 - p) * (1 - p / k3)
    J = V * oldD + d * oldC
    N = (1 - d) * J + d * oldC * V / 2
    return N / J


def admissible(d, p, B, L, cap, capped, **kw):
    g, b = guards(d, p, B, L, cap, capped, **kw)
    ok = np.ones(np.broadcast(*[np.asarray(x) for x in g]).shape, dtype=bool)
    for x in g:
        ok &= (x > 0)
    return ok, b['N'] / b['J']


def selftest():
    from fractions import Fraction as Fr
    from model import P, guard_vals, count as mcount
    Pm = P(theta=0.8737, h=0.8028, cB=0.99999, cL=2.1, cCap=0.12)
    for cand in ('C', 'capC', 'weakC7', 'capP'):
        for d, p in [(0.3, 0.2), (0.5, 0.5), (0.45, 0.4)]:
            g, _ = guard_vals(Pm, cand, d, p)
            B, L, cap = Pm.face(cand)
            g2, _ = guards(d, p, B, L, cap, cand in ('capC', 'capP'))
            assert np.allclose(g, [float(x) for x in g2], rtol=1e-9, atol=1e-12), (cand, d, p)
            assert abs(mcount(Pm, cand, d, p) - float(count(d, p, B, L, cap, cand in ('capC', 'capP')))) < 1e-12
    print('selftest ok')


if __name__ == '__main__':
    selftest()
