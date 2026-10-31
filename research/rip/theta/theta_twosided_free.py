"""theta_twosided.py without the dense matrix (B up to 10^5 and beyond): the sextic family with both thetas removed.

Row family V and source family P as in theta_twosided.py.  The normal operators are applied matrix-free:
  one-sided   E^H P_V^perp E = E^H E - M M^H,                M = E^H Q_V (one chunked pass over the rows of E);
  two-sided   P_P^perp (E^H E - M M^H) P_P^perp;
with E^H E v from the compiled kernel (theta_ckernel, single precision) and the twist columns E e_j from Kernel.forward.
Random spans of the same dimensions are the control.  Row Gauss sums use theta_core's generator, including inert primes.

usage: python3 -I theta_twosided_free.py B L [M] [J] [beta,...] [threads]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
import numpy as np
from scipy.sparse.linalg import eigsh, LinearOperator

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
Mtw = int(sys.argv[3]) if len(sys.argv) > 3 else 30
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
betas = [float(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else [1.0 / 3]
nth = int(sys.argv[6]) if len(sys.argv) > 6 else 3
t0 = time.time()
Tb = tc.build_tables(B, L)
R, S, ID, pc, zo, rows = Tb.R, Tb.S, Tb.ID, tc.pc, tc.zo, Tb.rows
Ff = tu.free_namespace(Tb)
sd = tu.source_data(Ff)
print('  source Gauss sums (%.0fs)' % (time.time() - t0), flush=True)
cache = {}


def generator(i):
    """theta_core.build's generator: split primes through ppcore, inert primes by brute force over F_{q^2}."""
    if i in cache:
        return cache[i]
    if i < ID.ns:
        val = Ff.generator(i)
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                k = pr.sym((aa, bb))
                if k is not None:
                    tot += np.exp(2j * np.pi * k / 6) * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


sym = tc.sym
Grow = np.zeros(R, complex); gen = np.zeros((R, 2), np.int64); ut = np.zeros((R, 6), complex)
for zi in range(R):
    gens = [generator(int(i)) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j; x = (1, 0)
    for gi in gens:
        g *= gi['G']; x = zo.mul(x, (gi['a'], gi['b']))
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    Grow[zi] = g; gen[zi] = x
    for k, u in enumerate(pc.UNITS):
        v = 1 + 0j
        for gi in gens:
            v *= sym(gi['prime'], u)
        ut[zi, k] = v
print('  row Gauss sums: |G| in [%.3f, %.3f]   (%.0fs)' % (np.abs(Grow).min(), np.abs(Grow).max(), time.time() - t0),
      flush=True)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
chim1 = np.rint(ut[:, 3].real).astype(int)
chiw = np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3
unit = (chim1 > 0) * 3 + chiw
prof = [(rows['N'].astype(float) / B) ** (-j / 2) for j in range(J)]


def orth(X):
    Q, Rr = np.linalg.qr(X)
    d = np.abs(np.diag(Rr))
    return Q[:, d > 1e-8 * d.max()]


SN = Tb.SN.astype(float)
twist = [int(j) for j in np.argsort(SN, kind='stable') if SN[j] <= Mtw]
Ecol = K.forward(np.eye(S, len(twist), dtype=complex)[:, :0] if not twist else
                 np.stack([np.eye(1, S, j, dtype=complex)[0] for j in twist], axis=1)).astype(complex)
cols = [tu.class_span(c36, Grow * p) for p in prof] + [tu.class_span(c36, p.astype(complex)) for p in prof]
for t in range(len(twist)):
    e = Ecol[:, t]
    for p in prof:
        cols += [tu.class_span(unit, Grow * np.conj(e) * p), tu.class_span(unit, e * p), tu.class_span(unit, np.conj(e) * p)]
QV = orth(np.concatenate(cols, axis=1)); dV = QV.shape[1]
cell = (((Tb.SA % 4) * 4 + Tb.SB % 4) * 81 + (Tb.SA % 9) * 9 + Tb.SB % 9) * 2 + sd['nprime'] % 2
pcols = []
for be in betas:
    pcols += [tu.class_span(cell, np.conj(sd['Gsrc']) * SN ** (-be)), tu.class_span(cell, sd['Gsrc'] * SN ** (-be))]
QP = orth(np.concatenate(pcols, axis=1)); dP = QP.shape[1]
rng = np.random.default_rng(97)
QVr = orth(rng.standard_normal((R, dV)) + 1j * rng.standard_normal((R, dV)))
QPr = orth(rng.standard_normal((S, dP)) + 1j * rng.standard_normal((S, dP)))
print('B=%d: R=%d S=%d; V (M=%d, J=%d) dim %d (%.3f R); P (betas %s) dim %d (%.3f S); twists %d   (%.0fs)'
      % (B, R, S, Mtw, J, dV, dV / R, betas, dP, dP / S, len(twist), time.time() - t0), flush=True)


def adjoint_block(Q, chunk=600):
    """E^H Q for a block Q of row vectors, by a chunked pass over the dense rows of E."""
    out = np.zeros((S, Q.shape[1]), complex)
    for st in range(0, R, chunk):
        en = min(R, st + chunk)
        Ec = pc.chi_chunk(Tb.LOC, Tb.T, st, en).astype(np.complex64)
        out += (Ec.conj().T @ Q[st:en].astype(np.complex64)).astype(complex)
    return out


MV = adjoint_block(QV)
MVr = adjoint_block(QVr)
print('  E^H Q_V and E^H Q_V(random) done   (%.0fs)' % (time.time() - t0), flush=True)


def top(MV_=None, QP_=None, k=4):
    def mv(v):
        v = np.asarray(v).ravel().astype(complex)
        if QP_ is not None:
            v = v - QP_ @ (QP_.conj().T @ v)
        w = K.matvec(v)
        if MV_ is not None:
            w = w - MV_ @ (MV_.conj().T @ v)
        if QP_ is not None:
            w = w - QP_ @ (QP_.conj().T @ w)
        return w
    op = LinearOperator((S, S), dtype=complex, matvec=mv)
    w = eigsh(op, k=k, which='LA', return_eigenvectors=False, tol=1e-5)
    return np.sort(w)[::-1] / S


def edge(dr, ds):
    return (math.sqrt((R - dr) / S) + math.sqrt((S - ds) / S)) ** 2


print('full top                        %s   MP edge %.3f' % (np.round(top(), 3), edge(0, 0)), flush=True)
print('one-sided, off V                %s   MP edge %.3f' % (np.round(top(MV), 3), edge(dV, 0)), flush=True)
print('two-sided, off V and P          %s   MP edge %.3f' % (np.round(top(MV, QP), 3), edge(dV, dP)), flush=True)
print('off V, random source span       %s' % np.round(top(MV, QPr), 3), flush=True)
print('random spans, same dims         %s' % np.round(top(MVr, QPr), 3), flush=True)
print('done in %.0fs' % (time.time() - t0))
