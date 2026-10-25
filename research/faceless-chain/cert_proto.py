"""Prototype of the uniform (all s in a piece) HIGH-gate certificate, exactly as the Lean kernel will
compute it. Local variable x = s - sig_j on piece j.

For branch k and width endpoint b (crossing b = s, or b = cap):
  Dn = 6 B0 den, a = Na/Dn, F = NF/Dn (F = sourceF - allowance), q = Nq/(6 B0)
  Dn gateG = Dn G0 + Ga Na + GF NF       (gateG is affine in (a, F))
  C_ij  : bicubic (nu, p) coefficients of Dn gateG, by interpolation at nu, p in {0, 1, -1, 2}
  U_aj  : (u, p) coefficients of (6 B0)^3 Dn gateG with nu = q + u (3/4 - q)
  leaves: bern33 of U on (u, p) boxes; each coefficient is a polynomial in x, positive by TM1.
"""
import sys, time
from fractions import Fraction as Fr
from math import comb
import polyq as P
import family as Fm

NU_PTS = [Fr(0), Fr(1), Fr(-1), Fr(2)]


def cubic4(f):
    f0, f1, fm, f2 = f[0], f[1], f[2], f[3]   # values at 0, 1, -1, 2 (as polys)
    c0 = f0
    c1 = P.smul(Fr(1, 6), P.add(P.add(P.smul(-1, f2), P.smul(6, f1)), P.add(P.smul(-3, f0), P.smul(-2, fm))))
    c2 = P.smul(Fr(1, 2), P.add(P.add(f1, fm), P.smul(-2, f0)))
    c3 = P.smul(Fr(1, 6), P.add(P.add(f2, P.smul(-3, f1)), P.add(P.smul(3, f0), P.smul(-1, fm))))
    return [c0, c1, c2, c3]


def gateG(a, T, S, F, fee, K, B, L, hc, nu, p, k):
    """Generic gateG over polys: a, T, S, F, B, L are polys; fee, K, hc, nu, p rationals."""
    i, j = k
    one = [Fr(1)]
    dI = one if i == 0 else [1 - p]
    eP = one if j < 2 else P.add(L, [-2*p])
    gP = one if j < 2 else L
    bI = P.smul(2*p*K, S) if i == 0 else P.smul(p, F)
    hP = [P.smul(2*p, S), P.smul(2*p*hc, F), P.mul(P.smul(2*p, B), F)][j]
    M = P.add(P.smul(12*nu, P.mul(dI, eP)), P.smul(5 - 6*nu, P.add(P.smul(2, eP), P.mul(dI, gP))))
    N = P.add(P.smul(10, P.mul(F, P.mul(dI, eP))),
              P.smul(5 - 6*nu, P.add(P.smul(2, P.mul(eP, bI)), P.mul(dI, hP))))
    tt = 15 - 6*nu
    base = P.add(P.add(P.smul(tt, P.sub(a, P.smul(nu, T))), P.smul(nu, P.sub([Fr(10)], P.smul(60, a)))),
                 P.add(P.smul(tt*(1 - 2*p)*nu, S), P.add(P.smul(-10*nu, F), [-fee*tt])))
    return P.add(P.mul(M, base), P.smul(nu*tt, N))


def piece_polys(fam, j):
    """B, L, B0, L0 as polys in x = s - sig_j for nodes inside piece j."""
    c = fam.Ecoef[j]; sig = fam.sig[j]; D = fam.Delta
    Et = list(c)
    EtD = P.shift(Et, D)
    L = P.smul(1/D, P.sub(Et, EtD))
    sv = [sig, Fr(1)]                          # s = sig + x
    B = P.add(Et, P.mul(sv, L))
    L0 = P.shift(L, -D); B0 = P.shift(B, -D)
    return B, L, B0, L0, sv


def high_polys(fam, j, b_kind, k, e, r, f, cap, den):
    B, L, B0, L0, sv = piece_polys(fam, j)
    b = sv if b_kind == 'cross' else [cap]
    t = P.sub(B, P.mul(L, P.sub(b, [e])))
    T = P.add(t, b); S = P.sub(b, [2*e])
    Dn = P.smul(6*den, B0)
    Na = P.add(P.smul(1 - den, P.add(P.mul(L0, b), P.sub(t, B0))), P.smul(6*r, B0))
    NF = P.sub(P.sub(Dn, P.smul(6, Na)), P.smul(e, Dn))
    vals = {}
    for nu in NU_PTS:
        for p in NU_PTS:
            G0 = gateG([], T, S, [], f, 8, B0, L0, cap, nu, p, k)
            Ga = P.sub(gateG([Fr(1)], T, S, [], f, 8, B0, L0, cap, nu, p, k), G0)
            GF = P.sub(gateG([], T, S, [Fr(1)], f, 8, B0, L0, cap, nu, p, k), G0)
            vals[(nu, p)] = P.add(P.add(P.mul(Dn, G0), P.mul(Ga, Na)), P.mul(GF, NF))
    # bicubic interpolation: C[i][jj]
    rowsp = {nu: cubic4([vals[(nu, p)] for p in NU_PTS]) for nu in NU_PTS}
    C = [[None]*4 for _ in range(4)]
    for jj in range(4):
        col = cubic4([rowsp[nu][jj] for nu in NU_PTS])
        for i in range(4):
            C[i][jj] = col[i]
    Nq = P.smul(1 - den, L0); D6 = P.smul(6, B0)
    al = Nq; be = P.sub(P.smul(Fr(9, 2), B0), Nq)
    pw = lambda p_, n: [Fr(1)] if n == 0 else P.mul(p_, pw(p_, n - 1))
    U = [[[] for _ in range(4)] for _ in range(4)]
    for a_ in range(4):
        for jj in range(4):
            acc = []
            for i in range(a_, 4):
                term = P.smul(comb(i, a_), P.mul(P.mul(C[i][jj], pw(al, i - a_)), P.mul(pw(be, a_), pw(D6, 3 - i))))
                acc = P.add(acc, term)
            U[a_][jj] = acc
    return U, (B, L, B0, L0)


def shift3(c, a, s):
    return [P.add(P.add(c[0], P.smul(a, c[1])), P.add(P.smul(a*a, c[2]), P.smul(a**3, c[3]))),
            P.smul(s, P.add(P.add(c[1], P.smul(2*a, c[2])), P.smul(3*a*a, c[3]))),
            P.smul(s*s, P.add(c[2], P.smul(3*a, c[3]))),
            P.smul(s**3, c[3])]


def bern3(e):
    return [e[0], P.add(e[0], P.smul(Fr(1, 3), e[1])),
            P.add(P.add(e[0], P.smul(Fr(2, 3), e[1])), P.smul(Fr(1, 3), e[2])),
            P.add(P.add(e[0], e[1]), P.add(e[2], e[3]))]


def bern33(U, a, s, b, t):
    """Bernstein coefficients on [a, a+s] x [b, b+t] of sum U[i][j] u^i p^j (polys in x)."""
    inner = [shift3(U[i], b, t) for i in range(4)]          # in p
    inner = [bern3(row) for row in inner]                   # inner[i][J]
    out = [[None]*4 for _ in range(4)]
    for J in range(4):
        col = shift3([inner[i][J] for i in range(4)], a, s)
        col = bern3(col)
        for I in range(4):
            out[I][J] = col[I]
    return out


if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    fam, _ = Fm.build(sig, 2e-5, 1e-4)
    e, r, f = Fm.FEES; cap = Fm.CAPMAX; den = fam.den
    j = int(sys.argv[2]); bk = sys.argv[3]; k = (int(sys.argv[4]), int(sys.argv[5]))
    t0 = time.time()
    U, _ = high_polys(fam, j, bk, k, e, r, f, cap, den)
    print("U built in %.1fs; degrees" % (time.time() - t0), [len(U[a][b]) - 1 for a in range(4) for b in range(4)][:6],
          "digits", max(P.digits(U[a][b]) for a in range(4) for b in range(4)), flush=True)
    h = fam.sig[j + 1] - fam.sig[j]
    D = fam.Delta
    # single leaf (u in [0,1], p in [0,1/2])
    t0 = time.time()
    BB = bern33(U, Fr(0), Fr(1), Fr(0), Fr(1, 2))
    print("bern33 in %.1fs" % (time.time() - t0), flush=True)
    worst = None; tot = 0
    for I in range(4):
        for J in range(4):
            br = P.tm1_split(BB[I][J], D, h - D)
            n = None if br is None else len(br) - 1
            tot += (n or 0)
            print(I, J, "intervals:", n, " value at mid %.3e" % float(P.ev(BB[I][J], h/2)), flush=True)
    print("total intervals", tot)
