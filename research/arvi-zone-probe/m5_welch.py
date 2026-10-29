"""Mechanism 5: frame / Welch-bound lower bounds for the family's moments  vs  what the admissible (rigid) data can reach.

Setting: V[z, c] = (z/c)_6 for the kept rows z (weights phi_z = Phi(N(z)/K)) and the columns c (ideals with N(c) in [X/4, 9X/4], or primes with N(P) in [D, 2D]).
G = V^* Phi V,  tr G = K_eff * n_c (unimodular entries)  =>  lambda_max(G) >= tr G / rank >= max(K_eff, n_c)   (Welch / large-sieve sharpness for FREE coefficients).
The Lean energy only sees coefficient vectors a = (W(N c / X) N(c)^{it}): smooth in the norm.  We compute
   lambda_max (power iteration),  r_rigid = a^* G a / a^* a  for the baseline smooth vector,  r_best = best Rayleigh quotient over admissible smooth data
   (|t| <= 3 resp. |t| <= 300, X-scale rho, profile flatness), and r_rigid with the principal rows (which initialKeep removes) put back.

   python3 m5_welch.py     (writes logs/m5_welch.log)
"""
import math
import os
import time

import numpy as np

import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m5_welch.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def all_rows(B):
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    X, Y = [], []
    for x in range(-xmax, xmax + 1):
        disc = 4.0 * B - 3.0 * x * x
        if disc < 0:
            continue
        sq = math.sqrt(disc)
        for y in range(math.ceil((x - sq) / 2 - 1e-9), math.floor((x + sq) / 2 + 1e-9) + 1):
            if x * x - x * y + y * y > 0:
                X.append(x)
                Y.append(y)
    return np.array(X, dtype=np.int64), np.array(Y, dtype=np.int64)


class Frame:
    """matrix V (rows x columns) given through the exponent table E_cols[c, z]; products are done in column chunks."""

    def __init__(self, E_cols, phi, rowmask, chunk=1000):
        self.E = E_cols
        self.idx = np.nonzero(rowmask)[0]
        self.phi = phi[self.idx]
        self.chunk = chunk
        self.n_c = E_cols.shape[0]

    def V_times(self, A):
        """A: (n_c, P) -> (rows, P)"""
        out_ = np.zeros((len(self.idx), A.shape[1]), dtype=np.complex128)
        for s in range(0, self.n_c, self.chunk):
            blk = toy.ZETA6[self.E[s : s + self.chunk][:, self.idx]]  # (c, rows)
            out_ += blk.T @ A[s : s + self.chunk]
        return out_

    def Vh_times(self, U):
        """U: (rows, P) -> (n_c, P)"""
        out_ = np.empty((self.n_c, U.shape[1]), dtype=np.complex128)
        for s in range(0, self.n_c, self.chunk):
            blk = toy.ZETA6[self.E[s : s + self.chunk][:, self.idx]]
            out_[s : s + self.chunk] = blk.conj() @ U
        return out_

    def rayleigh(self, A):
        VA = self.V_times(A)
        num = np.sum(self.phi[:, None] * np.abs(VA) ** 2, axis=0)
        den = np.sum(np.abs(A) ** 2, axis=0)
        return num / den

    def lambda_max(self, iters=30, seed=0):
        rng = np.random.default_rng(seed)
        v = (rng.standard_normal((self.n_c, 1)) + 1j * rng.standard_normal((self.n_c, 1)))
        lam = 0.0
        for _ in range(iters):
            w = self.Vh_times(self.phi[:, None] * self.V_times(v))
            lam = float(np.linalg.norm(w) / np.linalg.norm(v))
            v = w / np.linalg.norm(w)
        return lam


def admissible_vectors(nrm, X, kind, rng, n, tmax):
    cols = []
    for _ in range(n):
        t = rng.uniform(-tmax, tmax) if tmax > 0 else 0.0
        rho = rng.uniform(0.7, 1.4)
        fl = rng.uniform(0.1, 0.5)
        if kind == "plain":
            W = toy.make_profile(0.25, 2.25, fl)
            cols.append(W(nrm / (rho * X)) * np.exp(1j * t * np.log(nrm)))
        else:
            W = toy.make_profile(1.0, 2.0, fl)
            cols.append(W(nrm / (rho * X)) * (nrm / X) ** (-0.66 + 1j * t))
    A = np.array(cols).T.astype(np.complex128)
    ok = np.sum(np.abs(A) ** 2, axis=0) > 0
    return A[:, ok]


def run_Z(Z, ms, ws, rng, nbest=80):
    B = 2.0 * Z
    x, y = all_rows(B)
    Xmax = Z ** max(ms)
    Nmax = int(max(2.25 * Xmax, 2.0 * Z ** max(ws) if ws else 10)) + 10
    PI = toy.build_prime_ideals(Nmax)
    IL = toy.build_ideals(PI, Nmax)
    ctx = toy.build_context(Z, Nmax, x, y, K=Z, PI=PI, IL=IL)
    keep, phi = ctx.keep, ctx.phi
    Keff = float(np.sum(phi * keep))
    out(f"-- Z = {Z:.0f}: rows {len(x)}, kept K_eff = {Keff:.0f}, removed rows = {int((~keep).sum())}")
    out(f"   ideal columns (plain polynomial of length X = Z^m):")
    out(f"   {'m':>5s} {'n_cols':>7s} | {'Welch bound':>11s} {'lambda_max':>10s} | {'r_rigid':>8s} {'r_best(|t|<=3)':>14s} {'r_best(|t|<=300)':>16s} | {'r_rigid +principal rows':>23s}")
    nrm = IL.norm.astype(float)
    for m in ms:
        X = Z ** m
        sel = np.nonzero((nrm >= 0.25 * X) & (nrm <= 2.25 * X))[0]
        n_c = len(sel)
        if n_c < 3:
            continue
        E_cols = ctx.E[sel]
        fr = Frame(E_cols, phi, keep)
        lam = fr.lambda_max()
        W1 = toy.make_profile(0.25, 2.25, 0.25)
        a0 = W1(nrm[sel] / X).astype(np.complex128)[:, None]
        r_rigid = float(fr.rayleigh(a0)[0])
        r3 = float(np.max(fr.rayleigh(admissible_vectors(nrm[sel], X, "plain", rng, nbest, 3.0))))
        r300 = float(np.max(fr.rayleigh(admissible_vectors(nrm[sel], X, "plain", rng, nbest, 300.0))))
        fr2 = Frame(E_cols, phi, np.ones_like(keep))
        r_pr = float(fr2.rayleigh(a0)[0])
        out(f"   {m:5.2f} {n_c:7d} | {max(Keff, n_c):11.0f} {lam:10.0f} | {r_rigid:8.1f} {r3:14.1f} {r300:16.1f} | {r_pr:23.1f}")
    if ws:
        out("   prime columns (slot polynomial, W(N P/D) (N P/D)^(-sigma+iv)):")
        out(f"   {'w':>5s} {'n_P':>6s} | {'Welch bound':>11s} {'lambda_max':>10s} | {'r_rigid':>8s} {'r_best(|v|<=3)':>14s} {'r_best(|v|<=300)':>16s} | {'r_rigid +principal rows':>23s}")
        for w in ws:
            D = Z ** w
            sel = np.nonzero((PI.norm >= D) & (PI.norm <= 2 * D))[0]
            n_c = len(sel)
            if n_c < 3:
                continue
            fr = Frame(ctx.Ep[sel], phi, keep)
            lam = fr.lambda_max()
            Ws = toy.make_profile(1.0, 2.0, 0.25)
            u = PI.norm[sel] / D
            a0 = (Ws(u) * u ** (-0.66)).astype(np.complex128)[:, None]
            r_rigid = float(fr.rayleigh(a0)[0])
            nn = PI.norm[sel].astype(float)
            r3 = float(np.max(fr.rayleigh(admissible_vectors(nn, D, "slot", rng, nbest, 3.0))))
            r300 = float(np.max(fr.rayleigh(admissible_vectors(nn, D, "slot", rng, nbest, 300.0))))
            fr2 = Frame(ctx.Ep[sel], phi, np.ones_like(keep))
            r_pr = float(fr2.rayleigh(a0)[0])
            out(f"   {w:5.2f} {n_c:6d} | {max(Keff, n_c):11.0f} {lam:10.0f} | {r_rigid:8.1f} {r3:14.1f} {r300:16.1f} | {r_pr:23.1f}")
    out("")


def main():
    t0 = time.time()
    out(f"# m5_welch  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    out("lambda_max(G) >= max(K_eff, n_cols)  is the (rigorous) Welch / large-sieve sharpness for FREE coefficients.")
    out("r_rigid / r_best: Rayleigh quotients a^* G a / a^* a of the coefficient vectors the Lean statement allows (smooth in N(.), twist t).")
    rng = np.random.default_rng(2)
    run_Z(1000.0, [0.3, 0.5, 0.7, 1.0, 1.3, 1.5], [0.3, 0.5, 0.7, 0.9], rng)
    run_Z(3000.0, [0.5, 0.8, 1.0, 1.2], [0.3, 0.5, 0.8], rng, nbest=40)
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
