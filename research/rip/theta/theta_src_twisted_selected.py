"""Twisted source spikes on slot-selected rows: do their row images concentrate there?  (Lambda_src, K-wall)

The source spike is the top right singular vector v0 of E (the class-signed source theta).  Its twists
v0(x)(x/m)_6, for sources m with N(m) <= M, have row images Phi_m = E (v0 (./m)_6); in the residue picture
Phi_m(z) ~ Phi_1(zm) ~ L^{1/3} tau6(zm) (journal, "The block outlier is a residue").  The K-wall needs their Bessel
constant on slot-selected row sets W: Lambda_src(W) = top eigenvalue of the Gram [<Phi_m 1_W, Phi_m' 1_W>].

W = the top rho*R rows by |T(z)|, T(z) = sum over the split primes pi with N(pi) in [P0, 2 P0] of chi_z(pi) (as in
theta_selected_free.py).  For each P0 and rho the script prints
  * the mean concentration of the images on W, (sum_W |Phi_m|^2 / sum |Phi_m|^2) / rho (flat images give 1);
  * Lambda_src(W) against random row sets of the same size (mean of ndraw draws), both divided by the flat value
    rho * Lambda_src(all rows);
and the same for the masked random matrix (kernel mode 1, its own v0 and slot sums) as the calibration.

usage: python3 -I theta_src_twisted_selected.py B L M P0[,P0..] rho[,rho..] [ndraw] [threads]
"""
import os, sys, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); M = int(sys.argv[3])
P0s = [int(t) for t in sys.argv[4].split(',')]
rhos = [float(t) for t in sys.argv[5].split(',')]
ndraw = int(sys.argv[6]) if len(sys.argv) > 6 else 8
nth = int(sys.argv[7]) if len(sys.argv) > 7 else 3
t0 = time.time()
Tb = tc.build_tables(B, L)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
R, S, SN = Tb.R, Tb.S, Tb.SN
ID, uid = Tb.ID, Tb.uid
order = np.argsort(SN, kind='stable')
twists = [int(j) for j in order if SN[j] <= M]


def src_char(j):
    """x -> (x/m)_6 for the source m = SA[j] + SB[j] w, from the symbol-table rows of m's prime ideals."""
    a, b, n = int(Tb.SA[j]), int(Tb.SB[j]), int(SN[j])
    ids = []
    while n > 1:
        p = int(Tb.spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (a + b * r0) % p == 0 else p - 1 - r0
        ids.append(ID.ideal_id(p, r))
    pos = np.searchsorted(uid, ids)
    assert np.all(pos < len(uid)) and np.all(uid[pos] == ids)
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        row = Tb.T[p_].astype(np.int64)
        zero |= (row & 0x40) != 0
        codes += row & 7
    return np.where(zero, 0, np.exp(2j * np.pi * (codes % 6) / 6))


chars = np.stack([src_char(j) for j in twists], axis=1)          # S x nt
slot_cols = {}
for P0 in P0s:
    # split primes with norm in [P0, 2 P0] among the sources: prime norms p = 1 mod 3
    isprime = np.array([int(Tb.spf[int(n)]) == int(n) for n in SN])
    slot_cols[P0] = ((SN >= P0) & (SN <= 2 * P0) & isprime).astype(complex)
print('B=%d L=%d: R=%d S=%d; %d twists with N(m) <= %d; slot primes %s   (%.0fs)'
      % (B, L, R, S, len(twists), M, {P0: int(slot_cols[P0].real.sum()) for P0 in P0s}, time.time() - t0), flush=True)
rng = np.random.default_rng(23)


def run(mode, seed):
    lam, vec = K.top(k=1, mode=mode, seed=seed, vectors=True, tol=1e-6)
    v0 = vec[:, 0]
    V = v0[:, None] * chars
    Phi = np.zeros((R, V.shape[1]), complex)
    for st in range(0, V.shape[1], 8):
        Phi[:, st:st + 8] = K.forward(V[:, st:st + 8], mode=mode, seed=seed)
    tot = np.sum(np.abs(Phi) ** 2, axis=0)
    G_all = Phi.conj().T @ Phi
    lam_all = np.linalg.eigvalsh((G_all + G_all.conj().T) / 2)[-1]
    out = []
    for P0 in P0s:
        T = K.forward(slot_cols[P0][:, None], mode=mode, seed=seed)[:, 0]
        rank = np.argsort(-np.abs(T))
        for rho in rhos:
            nW = max(1, int(rho * R))
            W = rank[:nW]
            conc = float(np.mean(np.sum(np.abs(Phi[W]) ** 2, axis=0) / tot) / rho)
            GW = Phi[W].conj().T @ Phi[W]
            lW = np.linalg.eigvalsh((GW + GW.conj().T) / 2)[-1]
            lr = []
            for _ in range(ndraw):
                Wr = rng.choice(R, nW, replace=False)
                Gr = Phi[Wr].conj().T @ Phi[Wr]
                lr.append(np.linalg.eigvalsh((Gr + Gr.conj().T) / 2)[-1])
            flat = rho * lam_all
            out.append((P0, rho, conc, lW / flat, np.mean(lr) / flat, np.std(lr) / flat))
    return float(lam[0]), out


for name, mode in (('sextic', 0), ('masked null', 1)):
    top0, out = run(mode, 4)
    print('%s: top s^2/S %.3f' % (name, top0), flush=True)
    for P0, rho, conc, lw, lr, sr in out:
        print('  P0=%d rho=%.3f: concentration on W %.3f (flat 1); Lambda_src(W)/flat %.3f, random sets %.3f +- %.3f'
              % (P0, rho, conc, lw, lr, sr), flush=True)
print('done in %.0fs' % (time.time() - t0))
