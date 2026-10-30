"""Is the excess at the top of the sextic spectrum arithmetic, or generic multiplicativity?

E[z, x] = chi_z(x) = prod_{pi | z} prod_{varpi | x} (varpi / pi)_6 is bi-multiplicative over the prime factors of the
row z and of the source x.  The comparison models keep E's zero pattern exactly (shared primes) and differ in what
they keep of the structure:
  * RSYM: an independent uniform sextic symbol e(pi, varpi) for every pair (row prime, source prime); still
    bi-multiplicative, but with no reciprocity and no character structure (varpi -> e(pi, varpi) is not a character
    mod pi);
  * RMM: every row an independent random completely multiplicative function of the source (uniform sixth roots at the
    source primes); only source-multiplicative, rows sharing primes are not correlated;
  * IID: independent uniform phases;
  * EXACT(P0): RMM with the true values chi_z(varpi) at the source primes of norm <= P0 (each row periodic in z
    modulo those primes, as the sextic rows are) and independent uniform sixth roots above P0;
  * RCHAR: the true symbols with each row prime's character replaced by its conjugate at random, (x/pi)_6^{e_pi},
    e_pi in {1, 5}.  Every row is still a character of the source mod z, but reciprocity between rows and sources
    (x/z)_6 ~ (z/x)_6 is broken.
The script prints the top singular values s^2/S of E and of each model (a few seeds).

usage: python3 -I theta_models.py B L [seeds] [P0,P0,...]
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
seeds = int(sys.argv[3]) if len(sys.argv) > 3 else 2
P0s = [int(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else []
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, spf, ID, pc = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.spf, F.ID, F.pc
mask = np.abs(E) > 0.5
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)

# ---- prime-ideal factorization of the sources (squarefree norm, so only split primes, each once)
src_ids = []
for a, b, n in zip(SA, SB, SN):
    n = int(n); ids = []
    while n > 1:
        p = int(spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (int(a) + int(b) * r0) % p == 0 else p - 1 - r0
        assert (int(a) + int(b) * r) % p == 0
        ids.append(ID.ideal_id(p, r))
    src_ids.append(ids)
Us = np.unique(np.concatenate([np.array(i, np.int64) for i in src_ids if i]))
col = {int(u): j for j, u in enumerate(Us)}
Fsrc = np.zeros((S, len(Us)), np.int16)                 # source x source-prime incidence
for j, ids in enumerate(src_ids):
    for i in ids:
        Fsrc[j, col[i]] = 1
uid = np.unique(rows['PID'][rows['PID'] >= 0])
LOC = pc.local_index(rows['PID'], uid)
print('sources factored: %d source primes, %d row primes' % (len(Us), len(uid)), flush=True)


def top(M, k=5):
    s = svds(M, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


print('sextic E : %s' % np.round(top(E), 3), flush=True)
rng = np.random.default_rng(17)
for t in range(seeds):
    e = rng.integers(0, 6, (len(uid), len(Us))).astype(np.int16)
    T = ((e @ Fsrc.T.astype(np.int16)) % 6).astype(np.int8)     # (row prime, source) codes
    Ms = pc.chi_chunk(LOC, T, 0, R).astype(np.complex128) * mask
    print('RSYM %d   : %s' % (t, np.round(top(Ms), 3)), flush=True)
    del Ms, T
    V = rng.integers(0, 6, (R, len(Us))).astype(np.int16)
    Mm = ZETA6[(V @ Fsrc.T.astype(np.int16)) % 6] * mask
    print('RMM %d    : %s' % (t, np.round(top(Mm), 3)), flush=True)
    del Mm, V
    Mi = np.exp(2j * np.pi * rng.random(E.shape)) * mask
    print('IID %d    : %s' % (t, np.round(top(Mi), 3)), flush=True)
    del Mi
    for P0 in P0s:
        V = rng.integers(0, 6, (R, len(Us))).astype(np.int16)
        for j, u in enumerate(Us):                       # exact values at the small source primes
            p_, r_ = ID.split_pr(np.array([u]))
            if int(p_[0]) > P0:
                continue
            a_, b_ = pc.primary_generator(int(p_[0]), int(r_[0]))
            jj = np.nonzero((SA == a_) & (SB == b_))[0]
            assert len(jj) == 1
            col_ = E[:, jj[0]]
            V[:, j] = np.where(np.abs(col_) > 0.5, np.round(np.angle(col_) / (np.pi / 3)) % 6, 0).astype(np.int16)
        Mx = ZETA6[(V @ Fsrc.T.astype(np.int16)) % 6] * mask
        print('EXACT(%d) %d: %s' % (P0, t, np.round(top(Mx), 3)), flush=True)
        del Mx, V
    Tt = pc.symbol_table(ID, uid, SA, SB).astype(np.int16)
    ec = rng.choice([1, 5], size=len(uid))
    Tc = np.where(Tt < 6, (Tt * ec[:, None]) % 6, Tt).astype(np.int8)
    Mc = pc.chi_chunk(LOC, Tc, 0, R).astype(np.complex128)
    print('RCHAR %d  : %s' % (t, np.round(top(Mc), 3)), flush=True)
    del Mc, Tt, Tc
