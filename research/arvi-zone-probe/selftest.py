"""Self-tests of the toy model (faithfulness of the sextic symbol, ideal table, keep predicate).
Run:  python3 selftest.py   (writes logs/selftest.log)"""
import itertools
import math
import os
import sys

import numpy as np

import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "selftest.log"), "w")


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.write(s + "\n")
    LOG.flush()


def check(name, ok, extra=""):
    log(("PASS " if ok else "FAIL ") + name + (" " + extra if extra else ""))
    return ok


def direct_symbol(zx, zy, p, kind, r):
    """independent implementation of (z/P)_6 as an element of mu_6(C), via explicit arithmetic in O/P."""
    if kind == 0:
        t = (zx + zy * r) % p
        if t == 0:
            return 0
        u = pow(t, (p - 1) // 6, p)
        # find unit s*w^j with image s*r^j
        for s in (1, -1):
            for j in range(3):
                if (s * pow(r, j, p)) % p == u:
                    return s * np.exp(2j * np.pi * j / 3)
        raise AssertionError("not a sixth root of unity")
    else:
        # F_{p^2} = F_p[w]/(w^2+w+1); brute-force power
        def mul(a, b):
            return ((a[0] * b[0] - a[1] * b[1]) % p, (a[0] * b[1] + a[1] * b[0] - a[1] * b[1]) % p)
        base = (zx % p, zy % p)
        if base == (0, 0):
            return 0
        res = (1, 0)
        for _ in range((p * p - 1) // 6):
            res = mul(res, base)
        table = {(1, 0): 1, (0, 1): np.exp(2j * np.pi / 3), ((p - 1) % p, (p - 1) % p): np.exp(4j * np.pi / 3),
                 ((p - 1) % p, 0): -1, (0, (p - 1) % p): -np.exp(2j * np.pi / 3),
                 (1, 1): -np.exp(4j * np.pi / 3)}
        return table[res]


def main():
    ok_all = True
    Nmax = 3000
    PI = toy.build_prime_ideals(Nmax)
    rng = np.random.default_rng(7)
    zx = rng.integers(-300, 300, 200)
    zy = rng.integers(-300, 300, 200)
    E = toy.prime_symbols(PI, zx, zy)
    # 1. compare with independent direct implementation (subset of primes)
    bad = 0
    for i in range(0, PI.n, 7):
        for k in range(0, 200, 11):
            d = direct_symbol(int(zx[k]), int(zy[k]), int(PI.p[i]), int(PI.kind[i]), int(PI.r[i]))
            v = toy.ZETA6[E[i, k]]
            if abs(d - v) > 1e-9:
                bad += 1
    ok_all &= check("symbol table == independent direct computation", bad == 0, f"(mismatches={bad})")

    # 2. multiplicativity in z:  (z1 z2 / P) = (z1/P)(z2/P)
    z1 = (int(zx[0]), int(zy[0]))
    z2 = (int(zx[1]), int(zy[1]))
    z12 = toy.mul_eis(z1, z2)
    E1 = toy.prime_symbols(PI, [z1[0]], [z1[1]])[:, 0]
    E2 = toy.prime_symbols(PI, [z2[0]], [z2[1]])[:, 0]
    E12 = toy.prime_symbols(PI, [z12[0]], [z12[1]])[:, 0]
    prod = toy.MUL[E1, E2]
    ok_all &= check("multiplicative in the row element", bool(np.all(prod == E12)))

    # 3. sixth-power rows are principal off the support:  (w^6 / P) = 1 for P not dividing w
    w = (5, 7)
    w2 = toy.mul_eis(w, w)
    w3 = toy.mul_eis(w2, w)
    w6 = toy.mul_eis(w3, w3)
    E6 = toy.prime_symbols(PI, [w6[0]], [w6[1]])[:, 0]
    ok_all &= check("(w^6/P)_6 in {0,1}", bool(np.all((E6 == 0) | (E6 == 6))))

    # 4. cubic reciprocity as a check of the per-prime root assignment omega -> r_P:
    #    for primary primes pi, pi' (= 2 mod 3):  (pi/pi')_3 = (pi'/pi)_3 ,  cubic = sextic^2
    prim = []
    for p in toy.sieve_primes(400).tolist():
        if p % 3 == 1:
            for a in range(-60, 61):
                for b in range(-60, 61):
                    if toy.norm_eis(a, b) == p and a % 3 == 2 and b % 3 == 0:
                        prim.append((p, a, b))
        elif p % 3 == 2 and p > 2:
            prim.append((p * p, p, 0))  # inert prime p is primary (= 2 mod 3)
    # generators: need index of P=(pi) in PI:  split: root r = -a/b mod p ; inert: (p,p^2,kind 1)
    def idx_of(entry):
        nrm, a, b = entry
        if b == 0 and nrm != a:  # inert
            return int(np.nonzero((PI.kind == 1) & (PI.p == a))[0][0])
        p = nrm
        r = (-a * pow(b, -1, p)) % p if b % p else None
        return int(np.nonzero((PI.kind == 0) & (PI.p == p) & (PI.r == r))[0][0])
    bad = 0
    tested = 0
    sel = [e for e in prim if e[0] < 1500]
    for e1, e2 in itertools.combinations(sel[:40], 2):
        if e1[0] == e2[0]:
            continue
        i1, i2 = idx_of(e1), idx_of(e2)
        s12 = toy.prime_symbols(PI.__class__(PI.norm[[i2]], PI.p[[i2]], PI.kind[[i2]], PI.r[[i2]]), [e1[1]], [e1[2]])[0, 0]
        s21 = toy.prime_symbols(PI.__class__(PI.norm[[i1]], PI.p[[i1]], PI.kind[[i1]], PI.r[[i1]]), [e2[1]], [e2[2]])[0, 0]
        c12 = (2 * int(s12)) % 6
        c21 = (2 * int(s21)) % 6
        tested += 1
        if c12 != c21:
            bad += 1
    ok_all &= check("cubic reciprocity on primary primes", bad == 0, f"(pairs={tested}, violations={bad})")

    # 5. ideal table:  chi_z(I) via parent recursion  ==  product of prime symbols from factor list
    IL = toy.build_ideals(PI, 400)
    Eid = toy.ideal_exponents(IL, E[:, :50])
    # recompute one ideal by walking the parent chain explicitly
    bad = 0
    for i in range(1, IL.n, 13):
        acc = np.zeros(50, dtype=np.uint8)
        j = i
        while j > 0:
            acc = toy.MUL[acc, E[IL.last[j], :50]]
            j = IL.parent[j]
        if not np.all(acc == Eid[i]):
            bad += 1
    ok_all &= check("ideal exponent table consistent", bad == 0)
    # number of ideals coprime to 6 with norm <= x  ~ 0.3023 x
    x = 400
    cnt = int(np.sum(IL.norm <= x))
    ok_all &= check("ideal count ~ 0.302*x", abs(cnt / x - 0.3023) < 0.06, f"(count={cnt}, ratio={cnt/x:.3f})")

    # 5b. number of ideals of norm n (coprime to 6) = sum_{d | n} chi_{-3}(d)
    ILb = toy.build_ideals(toy.build_prime_ideals(600), 600)
    cnt = np.bincount(ILb.norm, minlength=601)
    bad = 0
    for n in range(1, 601):
        if n % 2 == 0 or n % 3 == 0:
            continue
        expect = sum((1 if d % 3 == 1 else -1) for d in range(1, n + 1) if n % d == 0 and d % 3 != 0)
        if cnt[n] != expect:
            bad += 1
    ok_all &= check("ideal counts by norm = sum_{d|n} chi_-3(d)", bad == 0, f"(mismatching norms={bad})")

    # 6. keep predicate
    ok_all &= check("w^6 removed", toy.is_removed(*toy.mul_eis(w3, w3)))
    ok_all &= check("2^3*lambda^2*w^6 removed", toy.is_removed(*toy.mul_eis(toy.mul_eis((8, 0), toy.mul_eis((1, -1), (1, -1))), w6)))
    ok_all &= check("random z kept", not toy.is_removed(37, 11))
    ok_all &= check("pi_7 * w^6 kept (cond 7 does not divide 72)", not toy.is_removed(*toy.mul_eis((3, 1), w6)))
    ok_all &= check("c0-twisted: z=c0^5*w^6 removed when eta=(c0/.)_6", toy.is_removed(*toy.mul_eis(toy.mul_eis(toy.mul_eis(toy.mul_eis((3, 1), (3, 1)), toy.mul_eis((3, 1), (3, 1))), (3, 1)), w6), c0=(3, 1)))

    # 7. lattice counting / sampling
    B = 2000.0
    cnt = toy.lattice_rows_count(B)
    ok_all &= check("lattice count ~ (2pi/sqrt3) B", abs(cnt / (toy.TWO_PI_OVER_SQRT3 * B) - 1) < 0.02, f"(count={cnt})")
    xs, ys = toy.sample_rows(B, 1000, np.random.default_rng(3))
    ok_all &= check("sampled rows inside the ball", bool(np.all(toy.norm_eis(xs, ys) <= B)) and bool(np.all(toy.norm_eis(xs, ys) > 0)))

    # 8. conductor of the row character (toy.cond_norm), against known number-field discriminants:
    #    z = 2 : K(sqrt2) has d = 8*3*24/3^2 = 64 = N(2^3);  K(cbrt2)=Q(w,cbrt2) has disc -2^4 3^7, so N(f)^2 = 2^4 3^7/3^3, N(f) = 36 = N(2 lambda^2);  sextic: N(2^3 lambda^2) = 576
    #    z = 3 : K(sqrt3)=Q(zeta12) has disc 144 = 3^2 * 16, N(f) = 16 = N(2^2);  K(cbrt3) has disc -3^11, N(f)^2 = 3^8, N(f) = 81 = N(lambda^4);  sextic: 16*81 = 1296
    #    z = -1: K(i) = Q(zeta12), N(f) = 16;   z = w: K(cbrt w) = Q(zeta9), disc -3^9, N(f)^2 = 3^6, N(f) = 27 = N(lambda^3)
    ok_all &= check("cond_norm(2) = 576", toy.cond_norm(2, 0) == 576.0)
    ok_all &= check("cond_norm(3) = 1296", toy.cond_norm(3, 0) == 1296.0)
    ok_all &= check("cond_norm(-1) = 16", toy.cond_norm(-1, 0) == 16.0)
    ok_all &= check("cond_norm(w) = 27", toy.cond_norm(0, 1) == 27.0)
    lam6 = (1, 0)
    for _ in range(6):
        lam6 = toy.mul_eis(lam6, (-1, 1))
    ok_all &= check("cond_norm(1) = cond_norm(2^6) = cond_norm(lambda^6) = 1", toy.cond_norm(1, 0) == toy.cond_norm(64, 0) == toy.cond_norm(*lam6) == 1.0)
    ok_all &= check("cond_norm(6) = N(72) = 5184 (the maximum 2,lambda-part)", toy.cond_norm(6, 0) == 5184.0)
    rng8 = np.random.default_rng(11)
    bad_inv, bad_rm, bad_bound, worst = 0, 0, 0, 1.0
    for _ in range(400):
        zz = (int(rng8.integers(-400, 400)), int(rng8.integers(-400, 400)))
        if zz == (0, 0):
            continue
        ex = toy.cond_exponents_2_lambda(*zz)
        if ex[0] > 3 or ex[1] > 4:
            bad_bound += 1
        # a sixth power w^6 (w prime to 6), 2^6, lambda^6 are sixth powers in K_2 and K_lambda: the 2,lambda-exponents cannot change
        for ww in ((5, 7), (4, 1), (2, 0), (-1, 1)):
            w6_ = (1, 0)
            for _ in range(6):
                w6_ = toy.mul_eis(w6_, ww)
            if toy.cond_exponents_2_lambda(*toy.mul_eis(zz, w6_)) != ex:
                bad_inv += 1
        removed = toy.is_removed(*zz)
        cn = toy.cond_norm(*zz)
        if removed != (toy.q6_norm(*zz) == 1.0):
            bad_rm += 1
        if removed and 5184.0 % cn != 0:
            bad_rm += 1
    ok_all &= check("2,lambda-exponents bounded by (3, 4) and invariant under z -> z*w^6", bad_bound == 0 and bad_inv == 0, f"(bad bound {bad_bound}, bad invariance {bad_inv})")
    ok_all &= check("removed rows <=> q6 = 1, and then N(f) divides N(72)", bad_rm == 0, f"(violations {bad_rm})")

    log("ALL PASS" if ok_all else "SOME FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
