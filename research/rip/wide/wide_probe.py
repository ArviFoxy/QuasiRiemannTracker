"""RIP program (4): wide random features on the actual sextic atoms.

Data: rows z (squarefree ideals of norm in [B, 2B] coprime to 6) as unit vectors x_z = chi_z|_sources / norm.
Dictionary of different atoms: degree-l Rademacher (Maclaurin) features feat_w(x) = prod_{i<l} <w_i, x>, whose exact
kernel is rho^l entrywise (Lean: WideFeatures.sum_feat_mul_conj), and ReLU features (arc-cosine kernel of Re rho).

Measures, on slot-selected row sets W (top |T| rows) and on the plain-sum large-value sets:
  * coherence over all pairs vs within W;
  * RIP constants (lambda_min, lambda_max) of the raw Gram rho_W and of the wide kernels rho_W^l, l = 2, 3, 4;
  * the same for m sampled features (the existence theorem's random operator);
  * the large-value count certificate of each degree, |W| <= lambda_max(rho_W^l) / min_W v^(2l)
    (Lean: count_le_of_rip, mixture_ge_min), against the true |W|.

usage: python3 wide_probe.py B L [P0] [m]
"""
import sys, os, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from zomega import norm, primes_list  # noqa: E402

rng = np.random.default_rng(11)
B = int(sys.argv[1]); L = int(sys.argv[2])
P0 = int(sys.argv[3]) if len(sys.argv) > 3 else 30
M_FEAT = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
zeta6 = np.exp(2j * np.pi * np.arange(6) / 6)

# ---------------------------------------------------------------- the sextic family (as in ../zfamily.py)
PR = primes_list(max(2 * B, L))
PR.sort(key=lambda x: x.N)
rows = []


def build(start, N, facs):
    if B <= N <= 2 * B:
        rows.append(tuple(facs))
    for j in range(start, len(PR)):
        pr = PR[j]
        if N * pr.N > 2 * B:
            break
        build(j + 1, N * pr.N, facs + [j])


build(0, 1, [])


def sqfree(n):
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


src = []
mm = int(math.isqrt(4 * L)) + 3
for a in range(-mm, mm + 1):
    if a % 3 != 2:
        continue
    for b in range(-mm, mm + 1):
        if b % 3:
            continue
        n = norm(a, b)
        if 1 < n <= L and n % 2 and n % 3 and sqfree(n):
            src.append((a, b))
R, S = len(rows), len(src)
used = sorted({j for r in rows for j in r})
symtab = {}
for j in used:
    pr = PR[j]
    arr = np.empty(S, int)
    for s, x in enumerate(src):
        k = pr.sym(x)
        arr[s] = -1 if k is None else k
    symtab[j] = arr
E = np.zeros((R, S), complex)
for r, facs in enumerate(rows):
    tot = np.zeros(S, int)
    zero = np.zeros(S, bool)
    for j in facs:
        a = symtab[j]
        zero |= a < 0
        tot = (tot + np.maximum(a, 0)) % 6
    E[r] = np.where(zero, 0, zeta6[tot])

# slot polynomial over split primes of norm in [P0, 2 P0]
slot = [x for x in primes_list(2 * P0 + 2) if x.split and P0 <= x.N <= 2 * P0]


def gen_of(pr):
    p = pr.p
    m2 = int(math.isqrt(4 * p)) + 3
    for a in range(-m2, m2 + 1):
        for b in range(-m2, m2 + 1):
            if norm(a, b) == p and a % 3 == 2 and b % 3 == 0 and (a + b * pr.r) % p == 0:
                return (a, b)


gens = [gen_of(pr) for pr in slot]
Tz = np.zeros(R, complex)
for r, facs in enumerate(rows):
    for g in gens:
        tot = 0
        z = False
        for j in facs:
            k = PR[j].sym(g)
            if k is None:
                z = True
                break
            tot += k
        if not z:
            Tz[r] += zeta6[tot % 6]
absT = np.abs(Tz)

# ---------------------------------------------------------------- unit data and the Gram
X = E / np.linalg.norm(E, axis=1, keepdims=True)
rho = X @ X.conj().T
off = np.abs(rho - np.diag(np.diag(rho)))
mu_all = off.max()
print('B=%d L=%d rows R=%d sources S=%d; slot primes %d (norm in [%d,%d]); 1/sqrt(S)=%.4f' %
      (B, L, R, S, len(gens), P0, 2 * P0, 1 / math.sqrt(S)))
print('coherence over all pairs: max %.4f  rms %.4f  (sqrt(S)*max = %.2f)' %
      (mu_all, math.sqrt((off ** 2).sum() / (R * (R - 1))), math.sqrt(S) * mu_all))


def eig_ends(Mat):
    ev = np.linalg.eigvalsh(Mat)
    return ev[0], ev[-1]


def relu_kernel(t):
    t = np.clip(t, -1.0, 1.0)
    return (np.sqrt(1 - t * t) + (np.pi - np.arccos(t)) * t) / (2 * np.pi)


B0, B1 = 1 / (2 * np.pi), 0.25      # constant and linear Maclaurin coefficients of the ReLU kernel
HP1 = 0.5 - B0 - B1                  # diagonal of the high-pass ReLU kernel


def report(label, W):
    W = np.asarray(W)
    k = len(W)
    sub = rho[np.ix_(W, W)]
    offW = np.abs(sub - np.diag(np.diag(sub)))
    muW = offW.max()
    line = '%-22s |W|=%5d  mu_W=%.4f (x sqrt S %.2f)  sqrt-barrier 1/mu_W=%.0f' % (label, k, muW, muW * math.sqrt(S), 1 / muW)
    print(line)
    for ell in (1, 2, 3, 4):
        lo, hi = eig_ends(sub ** ell)
        gers = (k - 1) * muW ** ell
        print('    degree %d kernel rho^%d: lambda in [%.3f, %.3f]   Gershgorin bound %.3f' % (ell, ell, lo, hi, gers))
    Kr = relu_kernel(np.real(sub))
    lo, hi = eig_ends(Kr)
    Khp = (Kr - B0 - B1 * np.real(sub)) / HP1
    lo2, hi2 = eig_ends(Khp)
    print('    ReLU kernel: lambda in [%.3f, %.3f] (diag 0.5);  high-pass (degree>=2, normalized): [%.3f, %.3f]' %
          (lo, hi, lo2, hi2))
    return sub


def sampled_features(W, ell, m):
    """m degree-ell Rademacher features on the rows W; returns the empirical Gram (Lean: fvec)."""
    XW = X[np.asarray(W)]
    F = np.ones((len(W), m), complex)
    for _ in range(ell):
        Wsign = rng.choice([-1.0, 1.0], size=(S, m))
        F *= XW @ Wsign
    return (F.conj() @ F.T).T / m      # entry (z, z') = (1/m) sum_j conj(f_j(z)) f_j(z')


def sampled_relu(W, m):
    XW = X[np.asarray(W)]
    Xr = np.hstack([XW.real, XW.imag])
    G = rng.standard_normal((2 * S, m))
    F = np.maximum(Xr @ G, 0.0)
    return F @ F.T / m


print('\n== random row sets (baseline) and slot-selected row sets W = top |T| ==')
for dens in (0.25, 0.1, 0.05):
    k = max(4, int(dens * R))
    report('random  dens=%.2f' % dens, rng.choice(R, k, replace=False))
    Wslot = np.argsort(-absT)[:k]
    sub = report('slot    dens=%.2f' % dens, Wslot)
    if dens == 0.1:
        for ell in (2, 3):
            Ghat = sampled_features(Wslot, ell, M_FEAT)
            dev = np.abs(Ghat - sub ** ell).max()
            lo, hi = eig_ends((Ghat + Ghat.conj().T) / 2)
            print('    sampled degree-%d features (m=%d): max entry error %.3f, lambda in [%.3f, %.3f]' %
                  (ell, M_FEAT, dev, lo, hi))
        Kh = sampled_relu(Wslot, M_FEAT)
        Khp = (Kh - B0 - B1 * np.real(sub)) / HP1
        lo, hi = eig_ends(Khp)
        print('    sampled ReLU features (m=%d): high-pass lambda in [%.3f, %.3f]' % (M_FEAT, lo, hi))

# ---------------------------------------------------------------- detection: large values of a plain sum
print('\n== transfer: count certificates for the large-value sets of the plain sum a = 1 (normalized) ==')
a = np.ones(S) / math.sqrt(S)
v = np.abs(X.conj() @ a)          # |<a, x_z>|, typical size 1/sqrt(S)
print('  |<a,x_z>|: rms %.4f  max %.4f   (1/sqrt(S) = %.4f)' % (math.sqrt((v ** 2).mean()), v.max(), 1 / math.sqrt(S)))
for k in (5, 20, 80, 320):
    W = np.argsort(-v)[:k]
    vmin = v[W].min()
    sub = rho[np.ix_(W, W)]
    certs = []
    for ell in (1, 2, 3):
        hi = eig_ends(sub ** ell)[1]
        certs.append(hi / vmin ** (2 * ell))
    print('  top %4d rows (min |<a,x>| = %.4f = %.2f/sqrt S): certificates by degree 1,2,3 = %s   [true |W| = %d]' %
          (k, vmin, vmin * math.sqrt(S), ', '.join('%.3g' % c for c in certs), k))
