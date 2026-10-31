"""Shared setup for the theta-span scripts: the sextic matrix E and the Gauss sums of its rows.

E[z, x] = chi_z(x) = prod_{pi | z} (x/pi)_6, with rows z = squarefree ideals with N(z) in [B, 2B] coprime to 6 (the
moduli) and columns x = primary elements with squarefree norm <= L, odd and coprime to 3 (the sources).
G(z,1) uses the Kubota character e(Tr(x/(sqrt(-3) z))) (ppcore 'canon'), extended to composite z by
G(c1 c2) = (c1/c2)_6 (c2/c1)_6 G(c1) G(c2).  unit_tw[z, k] = chi_z(u_k) for the six units u_k.

build(B, L) returns a namespace with E, R, S, rows, SA, SB, SN, spf, Grow, unit_tw and the helpers generator, sym,
sqfree_int; t0 is the build's start time.  build_tables(B, L) is the part of it that does not form the dense matrix
(rows, sources and the int8 symbol table T of row prime x source, 100 = "prime divides source"), for the matrix-free
scripts at sizes where E does not fit in memory; build() starts from it.
"""
import os, sys, time
from types import SimpleNamespace
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'prime_pool'))
sys.path.insert(0, os.path.join(HERE, '..'))
import ppcore as pc          # noqa: E402
import zomega as zo          # noqa: E402


def sym(prime, x):
    """(x/prime)_6 as a complex sixth root of unity, or None when prime divides x."""
    k = prime.sym((int(x[0]), int(x[1])))
    return None if k is None else np.exp(2j * np.pi * k / 6)


def build_tables(B, L, verbose=True):
    """Rows, sources and the symbol table, without the dense matrix.  Returns a namespace with ID, rows, R, S, SA, SB, SN,
    spf, uid (sorted ids of the row primes), T (len(uid) x S int8), LOC (R x J positions of z's primes in uid, -1
    padded), sqfree_int and t0."""
    t0 = time.time()
    ID = pc.Ideals(max(2 * B, L) + 16)
    rows = pc.enumerate_rows(B, ID)
    R = rows['R']
    SA, SB, SN = pc.primary_elements(L)
    spf = ID.spf

    def sqfree_int(n):
        while n > 1:
            p = int(spf[n]); n //= p
            if n % p == 0:
                return False
        return True

    keep = np.array([(1 < n) and (n % 2 == 1) and (n % 3 != 0) and sqfree_int(int(n)) for n in SN])
    SA, SB, SN = SA[keep], SB[keep], SN[keep]
    S = len(SA)
    uid = np.unique(rows['PID'][rows['PID'] >= 0])
    T = pc.symbol_table(ID, uid, SA, SB)
    LOC = pc.local_index(rows['PID'], uid)
    if verbose:
        print('B=%d L=%d  R=%d rows  S=%d sources  %d row primes   tables in %.0fs' % (B, L, R, S, len(uid), time.time() - t0),
              flush=True)
    return SimpleNamespace(ID=ID, rows=rows, R=R, S=S, SA=SA, SB=SB, SN=SN, spf=spf, uid=uid, T=T, LOC=LOC,
                           sqfree_int=sqfree_int, t0=t0)


def build(B, L):
    t0 = time.time()
    Tb = build_tables(B, L, verbose=False)
    ID, rows, R, SA, SB, SN, spf, S, T, LOC, sqfree_int = (Tb.ID, Tb.rows, Tb.R, Tb.SA, Tb.SB, Tb.SN, Tb.spf, Tb.S,
                                                           Tb.T, Tb.LOC, Tb.sqfree_int)
    E = pc.chi_chunk(LOC, T, 0, R).astype(np.complex128)
    del T, Tb
    print('B=%d L=%d  R=%d rows  S=%d sources   built in %.1fs' % (B, L, R, S, time.time() - t0), flush=True)

    gen_cache = {}

    def generator(i):
        """primary generator (a, b), Gauss sum and prime object for prime ideal id i."""
        if i in gen_cache:
            return gen_cache[i]
        if i < ID.ns:
            p, r = ID.split_pr(np.array([i]))
            p = int(p[0]); r = int(r[0])
            a, b = pc.primary_generator(p, r)
            gs, gc = pc.gauss_sums(dict(p=p, r=r, a=a, b=b))
            val = dict(a=a, b=b, G=gc, prime=zo.Prime(p, (a, b)))
        else:
            q = int(ID.inert_q[i - ID.ns])
            pr = zo.Prime(q)
            # inert Gauss sum over F_{q^2} with the Kubota character: Tr(x/(sqrt(-3) q)) = b_x / q
            tot = 0j
            for aa in range(q):
                for bb in range(q):
                    k = pr.sym((aa, bb))
                    if k is None:
                        continue
                    tot += np.exp(2j * np.pi * k / 6) * np.exp(2j * np.pi * bb / q)
            val = dict(a=q, b=0, G=tot / q, prime=pr)
        gen_cache[i] = val
        return val

    Grow = np.zeros(R, complex)
    unit_tw = np.zeros((R, 6), complex)          # chi_z(u) for the six units u (twist variants)
    for zi in range(R):
        ids = [int(i) for i in rows['PID'][zi] if i >= 0]
        gens = [generator(i) for i in ids]
        g = 1 + 0j
        for gi in gens:
            g *= gi['G']
        for a_ in range(len(gens)):
            for b_ in range(a_ + 1, len(gens)):
                s1 = sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b']))
                s2 = sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
                g *= s1 * s2
        Grow[zi] = g
        for k, u in enumerate(pc.UNITS):
            v = 1 + 0j
            for gi in gens:
                v *= sym(gi['prime'], u)
            unit_tw[zi, k] = v
    print('  |G(z,1)|: min %.3f max %.3f   (built %.1fs)' % (np.abs(Grow).min(), np.abs(Grow).max(), time.time() - t0),
          flush=True)
    return SimpleNamespace(E=E, R=R, S=S, rows=rows, SA=SA, SB=SB, SN=SN, spf=spf, ID=ID, Grow=Grow,
                           unit_tw=unit_tw, generator=generator, sym=sym, sqfree_int=sqfree_int, pc=pc, zo=zo, t0=t0)
