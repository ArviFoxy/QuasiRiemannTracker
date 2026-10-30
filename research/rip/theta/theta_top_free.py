"""Top of the sextic spectrum at sizes where E does not fit in memory as complex numbers.

E is stored as int8 codes (k for zeta6^k, 6 for a zero entry), R x S bytes, and E^H E is applied chunk by chunk
(Lanczos via eigsh).  Compared models, each with E's exact zero pattern:
  * random phases (stored as int8 codes of 2 pi k / 256);
  * RCHAR: each row prime's character conjugated at random (reciprocity broken, rows still characters).
Prints the top eigenvalues of E^H E divided by S (= top singular values squared over S).

usage: python3 -I theta_top_free.py B L [k]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import eigsh, LinearOperator

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'prime_pool'))
sys.path.insert(0, os.path.join(HERE, '..'))
import ppcore as pc          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
k = int(sys.argv[3]) if len(sys.argv) > 3 else 4
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
print('B=%d L=%d  R=%d rows  S=%d sources  %d row primes   tables in %.0fs' % (B, L, R, S, len(uid), time.time() - t0),
      flush=True)
CH = max(1, 40_000_000 // S)


def codes_from(Tab):
    out = np.empty((R, S), np.int8)
    for r0 in range(0, R, CH):
        r1 = min(R, r0 + CH)
        acc = np.zeros((r1 - r0, S), np.int16)
        for j in range(LOC.shape[1]):
            li = LOC[r0:r1, j]; sel = li >= 0
            if sel.any():
                acc[sel] += Tab[li[sel]]
        out[r0:r1] = np.where(acc >= pc.ZCODE, 6, acc % 6).astype(np.int8)
    return out


LUT6 = np.concatenate([np.exp(2j * np.pi * np.arange(6) / 6), [0]]).astype(np.complex64)


def top(codes, lut):
    def mv(v):
        v = v.astype(np.complex64)
        w = np.zeros(S, np.complex64)
        for r0 in range(0, R, CH):
            C = lut[codes[r0:r0 + CH]]
            w += C.conj().T @ (C @ v)
        return w
    op = LinearOperator((S, S), matvec=mv, dtype=np.complex64)
    ev = eigsh(op, k=k, which='LA', return_eigenvectors=False, tol=1e-4)
    return np.sort(ev)[::-1] / S


codes = codes_from(T)
print('sextic E      : %s   (%.0fs)' % (np.round(top(codes, LUT6), 3), time.time() - t0), flush=True)
rng = np.random.default_rng(31)
LUT256 = np.concatenate([np.exp(2j * np.pi * np.arange(255) / 255), [0]]).astype(np.complex64)
for s in range(2):
    rc = np.where(codes == 6, 255, rng.integers(0, 255, size=codes.shape, dtype=np.int16)).astype(np.uint8)
    print('masked random : %s   (%.0fs)' % (np.round(top(rc, LUT256), 3), time.time() - t0), flush=True)
    del rc
ec = rng.choice([1, 5], size=len(uid))
Tc = np.where(T < 6, (T.astype(np.int16) * ec[:, None]) % 6, T).astype(np.int8)
del codes
cc = codes_from(Tc)
print('RCHAR         : %s   (%.0fs)' % (np.round(top(cc, LUT6), 3), time.time() - t0), flush=True)
print('MP edge (no mask) %.3f' % ((math.sqrt(R) + math.sqrt(S)) ** 2 / S))
