#!/usr/bin/env python3
"""
Numerics on the actual sextic family psi_u(n) = (u/n)_6 over Z[w], w^2+w+1=0.

Rows: primary (u = 1 mod 3) squarefree u with N(u) in [U, 2U].
Columns: ideals n coprime to 6 with N(n) in [Y, 2Y], smooth weight w(N(n)/Y).
Gram G(u,v) = sum_n w(N n/Y)^2 psi_u(n) conj psi_v(n).

Checks:
 (a) E_{u != v} |G(u,v)|^2 / Neff   (Neff = typical diagonal)  -> ~1 means off-diagonal ~ Neff^{1/2}
 (b) Halasz row sums vs R * Neff^delta, for random R and for actual large-value sets
 (c) cubic trace decomposition tr(G_R^3) = D3 + 3 tr(D O^2) + tr(O^3), with Schatten bound E2^{3/2}
"""
import numpy as np, math, sys, time

def primes_upto(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def rep_norm(p):
    # find (a,b) with a^2 - a b + b^2 = p
    for b in range(1, int(2*math.sqrt(p/3))+2):
        # a^2 - a b + b^2 - p = 0 -> a = (b +- sqrt(4p - 3b^2))/2
        disc = 4*p - 3*b*b
        if disc < 0: break
        s = int(math.isqrt(disc))
        if s*s == disc and (b + s) % 2 == 0:
            return ((b + s)//2, b)
    raise ValueError(p)

def vec_powmod(x, e, p):
    r = np.ones_like(x); b = x % p
    while e:
        if e & 1: r = (r*b) % p
        b = (b*b) % p; e >>= 1
    return r

def build(U, Ycols_list, seed=0):
    t0 = time.time()
    Ymax = max(Ycols_list)
    # ---- rows
    rows = []
    A = int(math.sqrt(4*2*U/3)) + 3
    for a in range(-A, A+1):
        for b in range(-A, A+1):
            N = a*a - a*b + b*b
            if U <= N < 2*U and (a - 1) % 3 == 0 and b % 3 == 0:
                rows.append((a, b, N))
    rows = np.array(rows, dtype=np.int64)
    # ---- prime ideals up to 2*Ymax (norm)
    P = primes_upto(2*Ymax + 10)
    pid = []        # list of (p, w0 or -1 for inert)
    pindex = {}     # (p, which) -> index
    for p in P:
        p = int(p)
        if p == 3 or p == 2: continue
        if p % 3 == 1:
            a, b = rep_norm(p)
            binv = pow(b, -1, p)
            w0a = (-a*binv) % p
            w0b = ((a - b)*binv) % p
            pindex[(p, 0)] = len(pid); pid.append((p, w0a, (a, b)))
            pindex[(p, 1)] = len(pid); pid.append((p, w0b, (a - b, -b)))
        else:
            if p*p <= 2*Ymax:
                pindex[(p, 2)] = len(pid); pid.append((p, -1, None))
    nP = len(pid)
    # ---- symbol exponents K[u, P] in {0..5}, -1 if P | u
    a_u = rows[:, 0]; b_u = rows[:, 1]
    K = np.full((len(rows), nP), -1, dtype=np.int8)
    for j, (p, w0, gen) in enumerate(pid):
        if w0 >= 0:
            x = (a_u + b_u*w0) % p
            r = vec_powmod(x, (p - 1)//6, p)
            k = np.full(len(rows), -1, dtype=np.int8)
            w2 = (w0*w0) % p
            k[r == 1] = 0
            k[r == (p - w2) % p] = 1   # -w^2 = e^{i pi/3}
            k[r == w0] = 2             # w = e^{2 pi i/3}
            k[r == p - 1] = 3
            k[r == w2] = 4             # w^2 = e^{4 pi i/3}
            k[r == (p - w0) % p] = 5   # -w = e^{5 pi i /3}
            k[x == 0] = -1
            K[:, j] = k
        else:
            # inert p: F_{p^2} = F_p[w]/(w^2+w+1); exponent (p^2-1)/6
            e = (p*p - 1)//6
            def fmul(x, y):
                (c, d), (c2, d2) = x, y
                return ((c*c2 - d*d2) % p, (c*d2 + d*c2 - d*d2) % p)
            kk = np.full(len(rows), -1, dtype=np.int8)
            for i in range(len(rows)):
                c, d = int(a_u[i]) % p, int(b_u[i]) % p
                if c == 0 and d == 0: continue
                res = (1, 0); base = (c, d); ee = e
                while ee:
                    if ee & 1: res = fmul(res, base)
                    base = fmul(base, base); ee >>= 1
                mp = {(1, 0): 0, (1, 1): 1, (0, 1): 2, (p-1, 0): 3, (p-1, p-1): 4, (0, p-1): 5}
                kk[i] = mp[res]
            K[:, j] = kk
    # squarefree rows: exclude rows with p^2 | u  (check via norms quickly: exclude if any split prime appears squared)
    # simple test: N(u) squarefree up to the factor structure of split primes -> use norm test on rational primes
    keep = np.ones(len(rows), dtype=bool)
    for i, (a, b, N) in enumerate(rows):
        n = int(N)
        for p in P:
            p = int(p)
            if p*p > n: break
            if n % (p*p) == 0:
                # p^2 | N(u): if p split, u might be pi*pibar (fine) or pi^2 (not squarefree);
                # conservative: drop all such rows
                keep[i] = False; break
    rows = rows[keep]; K = K[keep]
    print(f"[build] rows={len(rows)} primeideals={nP} time {time.time()-t0:.1f}s", flush=True)
    return rows, K, pid, pindex, P

def column_ideals(Y, pid, pindex, P):
    """list of (norm, [(prime_index, exp), ...]) for ideals coprime to 6 with norm in [Y,2Y)"""
    cols = []
    smallP = [int(p) for p in P if p*p <= 2*Y + 10]
    for N in range(int(Y), int(2*Y)):
        if N % 2 == 0 or N % 3 == 0: continue
        n = N; fac = []
        for p in smallP:
            if p*p > n: break
            if n % p == 0:
                e = 0
                while n % p == 0: n //= p; e += 1
                fac.append((p, e))
        if n > 1: fac.append((n, 1))
        # build ideals
        choices = [[]]
        ok = True
        for (p, e) in fac:
            if p % 3 == 1:
                new = []
                for c in choices:
                    for i in range(e + 1):
                        lst = list(c)
                        if i: lst.append((pindex[(p, 0)], i))
                        if e - i: lst.append((pindex[(p, 1)], e - i))
                        new.append(lst)
                choices = new
            else:
                if e % 2: ok = False; break
                choices = [c + [(pindex[(p, 2)], e//2)] for c in choices]
        if ok:
            for c in choices: cols.append((N, c))
    return cols

def psi_matrix(K, cols):
    nR = K.shape[0]; nC = len(cols)
    E = np.zeros((nR, nC), dtype=np.int16); Z = np.zeros((nR, nC), dtype=bool)
    for j, (N, fac) in enumerate(cols):
        for (i, e) in fac:
            k = K[:, i].astype(np.int16)
            Z[:, j] |= (k < 0)
            E[:, j] += e*np.where(k < 0, 0, k)
    Psi = np.exp(1j*np.pi/3*(E % 6))
    Psi[Z] = 0
    return Psi

def bump(x):
    y = np.zeros_like(x, dtype=float)
    m = (x > 1) & (x < 2)
    s = 2*x[m] - 3
    y[m] = np.exp(1 - 1/(1 - s*s))
    return y

if __name__ == "__main__":
    U = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    delta = 0.4546
    expo = [float(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [0.414, 0.6, 0.7435, 0.8717, 1.0, 1.1539]
    Ys = [int(round(U**e)) for e in expo]
    rows, K, pid, pindex, P = build(U, Ys)
    rng = np.random.default_rng(1)
    nR = len(rows)
    for e, Y in zip(expo, Ys):
        cols = column_ideals(Y, pid, pindex, P)
        Psi = psi_matrix(K, cols)
        wts = bump(np.array([c[0] for c in cols], dtype=float)/Y)
        Pw = Psi*wts[None, :]
        G = Pw @ Pw.conj().T
        Neff = np.real(np.mean(np.diag(G)))
        off = G[~np.eye(nR, dtype=bool)]
        m2 = np.mean(np.abs(off)**2)/Neff
        w4 = np.sum(wts**4); m2r = np.mean(np.abs(off)**2)/w4
        frac = np.mean(np.abs(off) > Neff**delta)
        # full-family operator norm vs rows and Neff
        lam = np.linalg.eigvalsh(G)[-1]
        print(f"\n== y={e:.4f} Y={Y} cols={len(cols)} Neff={Neff:.1f} rows={nR}")
        print(f"  E|G(u,v)|^2/sum w^4 = {m2r:.3f} (random-phase prediction 1);")
        print(f"  E|G(u,v)|^2/Neff = {m2:.3f};  P(|G|>Neff^delta) = {frac:.3f};  "
              f"Neff^(1/2-delta) = {Neff**(0.5-delta):.3f}; median|G|/Neff^delta = {np.median(np.abs(off))/Neff**delta:.3f}")
        print(f"  ||G_full|| = {lam:.1f}  (rows {nR}, Neff {Neff:.1f}, rows*Neff/min(rows,cols) = {nR*Neff/min(nR,len(cols)):.1f})")
        # random subsets of size R ~ rows^0.6 and R ~ cols/2
        for Rsz in sorted(set([max(8, int(nR**0.6)), max(8, min(nR//2, len(cols)//2))])):
            res = []
            for trial in range(3):
                idx = rng.choice(nR, Rsz, replace=False)
                GR = G[np.ix_(idx, idx)]
                D = np.real(np.diag(GR)); O = GR - np.diag(np.diag(GR))
                rowsum = np.max(np.sum(np.abs(O), axis=1))
                E2 = np.sum(np.abs(O)**2)
                S3 = np.real(np.trace(O @ O @ O))
                trDO2 = np.real(np.sum(D[:, None]*np.abs(O)**2))
                lamR = np.linalg.eigvalsh(GR)[-1]
                res.append((rowsum/(Rsz*Neff**delta), E2/(Rsz**2*Neff), S3/E2**1.5, S3/(Rsz**3*Neff), S3/(3*trDO2), lamR/(Rsz + Neff)))
            res = np.array(res).mean(axis=0)
            print(f"  random R={Rsz}: Halasz rowsum/(R Neff^d)={res[0]:.2f}  E2/(R^2 Neff)={res[1]:.3f}  "
                  f"S3/E2^1.5={res[2]:.4f}  S3/(R^3 Neff)={res[3]:.3f}  S3/(3trDO^2)={res[4]:.3f}  ||G_R||/(R+Neff)={res[5]:.2f}")
        # large-value set of an actual polynomial: Moebius block and plain block (coefficient-blind check)
        mu_col = np.array([(-1)**len(f) if all(e_ == 1 for (_, e_) in f) else 0 for (_, f) in cols], dtype=float)
        for lab, xi in [("mu", mu_col), ("one", np.ones(len(cols)))]:
            Dv = Pw @ xi
            Rsz = max(8, int(nR**0.6))
            idx = np.argsort(-np.abs(Dv))[:Rsz]
            GR = G[np.ix_(idx, idx)]
            D = np.real(np.diag(GR)); O = GR - np.diag(D)
            E2 = np.sum(np.abs(O)**2); S3 = np.real(np.trace(O @ O @ O))
            trDO2 = np.real(np.sum(D[:, None]*np.abs(O)**2))
            thr = np.abs(Dv[idx[-1]])**2/np.sum(np.abs(xi*wts)**2)
            print(f"  top-{Rsz} rows of |{lab}-poly|: level |D|^2/||xi||^2 = Neff^{math.log(max(thr,1e-9))/math.log(Neff):.3f}; "
                  f"E2/(R^2 Neff)={E2/(Rsz**2*Neff):.3f}  S3/E2^1.5={S3/E2**1.5:.4f}  S3/(R^3 Neff)={S3/(Rsz**3*Neff):.3f}  "
                  f"S3/(3trDO^2)={S3/(3*trDO2):.3f}")
