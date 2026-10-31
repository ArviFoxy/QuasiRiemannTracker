"""Dual-frame (Q-metric) certificates for the sextic matrix on slot-selected row sets, exact dense linear algebra.

For a positive definite Q on row space and a row set W,
    sum_{z in W} |(E a)(z)|^2 = |P_W Q^{-1/2} Q^{1/2} E a|^2 <= lambda_max((Q^{-1})_WW) * lambda_max(E^H Q E) * |a|^2.
The product is >= |E_W|^2 (the truth) for every Q, with equality approached as Q -> P_W, and equals |E|^2 (the trivial
bound) for Q = I.  The question: does some Q chosen without knowing W bring the product below |E|^2, i.e. can a
non-tight frame with a dual frame certify the thin-set bound better than the trivial bound?

All quantities are in units of S (= 'top singular value squared / S'), so the trivial bound is about 4.3 at B = L = 10^4.
Row sets: the slot-selected W (top rho*R rows by |T(z)|, T = sum of chi_z over the split primes of norm in [P0, 2*P0])
and, as a control, random row sets of the same size.  Q families:
  (1) Q = I;
  (2) Q = P_W + eps I                         (oracle: depends on W; the product -> truth as eps -> 0);
  (3) Q = I - (1 - eps) P_V                   V = twisted-theta span {conj G(z) chi_z(m) chi_z(u)}, block span
                                              {chi_z(m) chi_z(u)}, or both, N(m) <= M, six units u (the FlatDilution route),
                                              in the conjugation conventions listed below;
  (4) Q = K/sum(b) + eps I, K = sum_l b_l Ghat^{o l}   wide kernel: Ghat the unit-diagonal row Gram, o the Hadamard power,
                                              b_l the Maclaurin coefficients of the ReLU arc-cosine kernel (checked below),
                                              degrees 0..4, 1..4 and 2..4;
  (5) Q = P_low + eps I                       P_low = projection onto the block span (coarse / low-pass metric);
  and two reference families, which depend on E but not on W:
  (4b) Q^-1 = K/sum(b) + eps I                the same kernel as the dual-frame GRAM instead of the metric (not asked for; the
                                              kernel is the Gram of the wide features, and Q^-1 is what the W-block of the
                                              bound sees): f1 = lambda_max(K_WW + eps), f2 = lambda_max(E^H (K + eps)^-1 E)/S;
  (6) Q = I - (1 - eps) P_k                   P_k = projection onto the top k left singular vectors of E (the best
                                              possible V of dimension k), eps optimised on a grid;
  (7) Q = (Ghat + tau I)^-1                   Tikhonov inverse of the unit-diagonal row Gram: f1 = lambda_max((Ghat + tau)_WW)
                                              is the Gram on W again (circular), f2 <= 1 + ...; tau -> 0 gives the truth;
  (8) Q = U min(1, c/s^2) U^H + inf * P_perp  the best Q that is a function of E's singular values s (U = left singular vectors)
                                              with f2 = c: product(c) = lambda_max(U_W max(c, s^2) U_W^H), which is the truth
                                              at c = 0 and the trivial bound at c = s_1^2.  Also printed: the Haar (Jacobi
                                              edge) prediction of lambda_max((P_k)_WW) for the families (6).
For each Q: f1 = lambda_max((Q^-1)_WW), f2 = lambda_max(E^H Q E)/S, product f1*f2, its ratio to the truth and to the trivial
bound.  The kernel Q is normalised to unit diagonal (the product is invariant under scaling Q).

Conjugation conventions.  f2 is the quadratic form |Q^(1/2) E a|^2 and the row Gram is G = E E^H, so the theta row vectors
that carry the excess in this form are G(z) conj chi_z(m) conj chi_z(u) (the Lean convention, theta_offspan.py); the span
{conj G chi chi} named in the task is the conjugate span, which carries the excess in |E^T c|^2 instead.  Both are run:
  asspec : theta = conj G chi(m) chi(u); block = chi(m) chi(u); both = block + theta;
  lean   : theta = G conj chi(m) conj chi(u) ('theta-lean'); block-conj = conj chi(m) conj chi(u); both-lean = block + theta-lean.

usage: python3 -I theta_dualframe.py B L [P0=40] [rho,rho=0.1,0.03] [M,M,M=30,100,300] [ndraw=3] [convs=asspec,lean]
                                        [families=1,2,3,4,4b,5,6,7]
"""
import os, sys, math, time
os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
sys.dont_write_bytecode = True
import numpy as np
import scipy.linalg as sla
from scipy.sparse.linalg import eigsh

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
P0 = int(sys.argv[3]) if len(sys.argv) > 3 else 40
rhos = [float(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [0.1, 0.03]
Ms = [int(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else [30, 100, 300]
ndraw = int(sys.argv[6]) if len(sys.argv) > 6 else 3
convs = (sys.argv[7] if len(sys.argv) > 7 else 'asspec,lean').split(',')
fams = (sys.argv[8] if len(sys.argv) > 8 else '1,2,3,4,4b,5,6,7').split(',')
EPS = [0.1, 0.01]
t0 = time.time()
F = tc.build(B, L)
E, R, S, SN, spf, Grow, unit_tw = F.E, F.R, F.S, F.SN, F.spf, F.Grow, F.unit_tw
rng = np.random.default_rng(7)


def top_eig(Mh):
    """largest eigenvalue of a Hermitian matrix (dense solver when small, Lanczos when large)."""
    n = Mh.shape[0]
    if n <= 400:
        return float(np.linalg.eigvalsh(Mh)[-1])
    ev = eigsh(Mh, k=2, which='LA', tol=1e-9, ncv=60, v0=np.random.default_rng(5).standard_normal(n) + 0j,
               return_eigenvectors=False)
    return float(np.max(ev))


def stamp():
    return '%.0fs' % (time.time() - t0)


# ---- ReLU arc-cosine Maclaurin coefficients: E[relu(u) relu(v)] = (1/2pi)(sqrt(1-x^2) + (pi - arccos x) x), corr x
xs = np.linspace(-0.5, 0.5, 4001)
kfun = (np.sqrt(1 - xs ** 2) + (np.pi - np.arccos(xs)) * xs) / (2 * np.pi)
coef = np.polynomial.polynomial.polyfit(xs, kfun, 8)
bl = [1 / (2 * math.pi), 0.25, 1 / (4 * math.pi), 0.0, 1 / (48 * math.pi)]
print('ReLU kernel Maclaurin coefficients b_0..b_4: fitted %s, claimed %s (max dev %.1e); b_5 %.1e, b_6 %.4f (1/(160 pi) = %.4f)' %
      (np.round(coef[:5], 5), np.round(bl, 5), np.abs(coef[:5] - bl).max(), coef[5], coef[6], 1 / (160 * math.pi)), flush=True)

# ---- the matrices
A = E.conj().T @ E                                      # S x S
G = E @ E.conj().T                                      # R x R
d = np.real(np.diag(G))
Gh = G / np.sqrt(np.outer(d, d))
trivial = top_eig(A) / S
print('B=%d L=%d R=%d S=%d: trivial bound |E|^2/S = %.4f   (%s)' % (B, L, R, S, trivial, stamp()), flush=True)

# ---- row sets
isprime = np.array([int(spf[int(n)]) == int(n) for n in SN])
slot = np.nonzero((SN >= P0) & (SN <= 2 * P0) & isprime)[0]
Tz = np.abs(E[:, slot].sum(1))
order = np.argsort(-Tz)
sets = []                                               # (label, W index array)
for rho in rhos:
    n = max(2, int(rho * R))
    sets.append(('slot P0=%d rho=%.2f (|W|=%d)' % (P0, rho, n), np.sort(order[:n])))
    for t in range(ndraw):
        sets.append(('random rho=%.2f #%d' % (rho, t + 1), np.sort(rng.choice(R, n, replace=False))))
truth = {lab: top_eig(G[np.ix_(W, W)]) / S for lab, W in sets}
print('row sets and truths |E_W|^2/S: ' + '; '.join('%s: %.4f' % (lab, truth[lab]) for lab, _ in sets), flush=True)

# ---- spans
order_src = np.argsort(SN)


def orth(X):
    U, s, _ = np.linalg.svd(X, full_matrices=False)
    return U[:, s > 1e-9 * s[0]]


spans = {}                                              # (name, M) -> orthonormal basis (R x k)
for M in Ms:
    idx = order_src[SN[order_src] <= M]
    blocks = (E[:, idx][:, :, None] * unit_tw[:, None, :]).reshape(R, -1)
    thetas = np.conj(Grow)[:, None] * blocks            # conj G chi(m) chi(u)
    thetas_lean = Grow[:, None] * np.conj(blocks)       # G conj chi(m) conj chi(u)
    if 'asspec' in convs:
        spans[('block', M)] = orth(blocks)
        spans[('theta', M)] = orth(thetas)
        spans[('both', M)] = orth(np.concatenate([blocks, thetas], axis=1))
    if 'lean' in convs:
        spans[('block-conj', M)] = orth(np.conj(blocks))
        spans[('theta-lean', M)] = orth(thetas_lean)
        spans[('both-lean', M)] = orth(np.concatenate([blocks, thetas_lean], axis=1))
print('spans (dimension): ' + ', '.join('%s N(m)<=%d: %d' % (nm, M, v.shape[1]) for (nm, M), v in spans.items()), flush=True)

rows_out = []                                           # (family, label, f2, {set label: f1})
show = [lab for lab, _ in sets if lab.startswith('slot') or lab.endswith('#1')]


def report(family, name, f2, f1s):
    rows_out.append((family, name, f2, f1s))
    cells = ['%s: f1 %.3g prod %.3f (%.2f x truth, %.2f x triv)' % (lab.split('(')[0].strip(), f1s[lab], f1s[lab] * f2,
                                                                  f1s[lab] * f2 / truth[lab], f1s[lab] * f2 / trivial)
             for lab in show if lab in f1s and np.isfinite(f1s[lab])]
    print('(%s) %-40s f2 %.4f | %s' % (family, name, f2, ' | '.join(cells)), flush=True)


# (1) Q = I
report('1', 'Q = I', trivial, {lab: 1.0 for lab, _ in sets})

# (2) Q = P_W + eps I   (oracle)
for eps in (EPS if '2' in fams else []):
    for lab, W in sets:
        if lab not in show:
            continue
        f2 = top_eig(E[W].conj().T @ E[W] + eps * A) / S
        report('2', 'P_W + %g I   [%s]' % (eps, lab.split('(')[0].strip()), f2, {lab: 1.0 / (1 + eps)})

# (3) Q = I - (1 - eps) P_V, (5) Q = P_low + eps I
for (nm, M), QV in (spans.items() if ('3' in fams or '5' in fams) else []):
    C = QV.conj().T @ E                                 # k x S
    CC = C.conj().T @ C
    PW = {lab: QV[W] @ QV[W].conj().T for lab, W in sets}
    lamP = {lab: top_eig(PW[lab]) for lab, _ in sets}
    lamPmin = {lab: float(np.linalg.eigvalsh(PW[lab])[0]) for lab, _ in sets}
    for eps in (EPS + [0.3, 0.03] if '3' in fams else []):
        f2 = top_eig(A - (1 - eps) * CC) / S
        f1s = {lab: 1 + (1 / eps - 1) * lamP[lab] for lab, _ in sets}
        report('3', 'I-(1-%g)P_V %s N(m)<=%d dim %d' % (eps, nm, M, QV.shape[1]), f2, f1s)
    if nm in ('block', 'block-conj') and '5' in fams:
        for eps in EPS:
            f2 = top_eig(eps * A + CC) / S
            f1s = {lab: 1 / eps - (1 / eps - 1 / (1 + eps)) * lamPmin[lab] for lab, _ in sets}
            report('5', 'P_low + %g I, low = block N(m)<=%d dim %d' % (eps, M, QV.shape[1]), f2, f1s)
    print('    lambda_max((P_V)_WW) per set: ' + ', '.join('%s %.3f' % (lab.split('(')[0].strip(), lamP[lab]) for lab, _ in sets),
          '(%s)' % stamp(), flush=True)

# (4) wide kernel
Gp = [np.ones_like(Gh), Gh]
for l in range(2, 5):
    Gp.append(Gp[-1] * Gh)
Nl = []
for l in (range(5) if '4' in fams else []):
    Z = Gp[l] @ E
    Nl.append(E.conj().T @ Z)
    print('  kernel term l=%d done (%s)' % (l, stamp()), flush=True)
for degs, name in ((((0, 1, 2, 3, 4), 'degrees 0-4'), ((1, 2, 3, 4), 'degrees 1-4'), ((2, 3, 4), 'degrees 2-4')) if '4' in fams else ()):
    sb = sum(bl[l] for l in degs)
    Kn = sum(bl[l] * Gp[l] for l in degs) / sb
    Mk = sum(bl[l] * Nl[l] for l in degs) / sb
    for eps in EPS + [1.0]:
        Q = Kn + eps * np.eye(R)
        f2 = top_eig(Mk + eps * A) / S
        cf = sla.cho_factor(Q)
        f1s = {}
        for lab, W in sets:
            Ie = np.zeros((R, len(W)), complex)
            Ie[W, np.arange(len(W))] = 1.0
            X = sla.cho_solve(cf, Ie)
            f1s[lab] = float(np.linalg.eigvalsh(X[W])[-1])
        report('4', 'kernel %s + %g I' % (name, eps), f2, f1s)

# (4b) the kernel as Q^-1
for degs, name in ((((0, 1, 2, 3, 4), 'degrees 0-4'), ((1, 2, 3, 4), 'degrees 1-4'), ((2, 3, 4), 'degrees 2-4')) if '4b' in fams else ()):
    sb = sum(bl[l] for l in degs)
    Kn = sum(bl[l] * Gp[l] for l in degs) / sb
    for eps in EPS + [1.0]:
        Qinv = Kn + eps * np.eye(R)
        cf = sla.cho_factor(Qinv)
        f2 = top_eig(E.conj().T @ sla.cho_solve(cf, E)) / S
        f1s = {lab: top_eig(Qinv[np.ix_(W, W)]) for lab, W in sets}
        report('4b', 'inverse kernel %s: Q^-1 = K + %g I' % (name, eps), f2, f1s)

# (6) top-k singular subspace (E-dependent, W-independent)
if '6' in fams:
    U, sv, _ = np.linalg.svd(E, full_matrices=False)
    s2 = sv ** 2 / S
    print('  singular values^2/S: top %s ; k=%d..: %s   (%s)' % (np.round(s2[:6], 4), 32, np.round(s2[31:34], 4), stamp()), flush=True)
epsgrid = np.concatenate([np.linspace(0.99, 0.5, 50), np.geomspace(0.5, 0.01, 40)])
for k in ((1, 2, 4, 8, 16, 32, 64, 128, 256, 384, 512, 768, 1024, 1536, 2048) if '6' in fams else ()):
    Uk = U[:, :k]
    lamP = {lab: np.linalg.norm(Uk[W], 2) ** 2 for lab, W in sets}
    for lab, _ in sets:
        best = None
        for eps in epsgrid:
            f2 = max(eps * s2[0], s2[k])
            f1 = 1 + (1 / eps - 1) * lamP[lab]
            if best is None or f1 * f2 < best[0]:
                best = (f1 * f2, eps, f1, f2)
        pr, eps, f1, f2 = best
        rows_out.append(('6', 'I-(1-eps)P_k, k=%d (eps*=%.3f)' % (k, eps), f2, {lab: f1}))
        if lab in show:
            a_, b_ = len(dict(sets)[lab]) / R, k / R
            haar = (math.sqrt(a_ * (1 - b_)) + math.sqrt(b_ * (1 - a_))) ** 2
            print('(6) top-%d singular subspace, best eps %.3f   f2 %.4f | %s: f1 %.4g prod %.3f (%.2f x truth, %.2f x triv)   lam_max((P_k)_WW) %.3f (Haar %.3f)' %
                  (k, eps, f2, lab.split('(')[0].strip(), f1, pr, pr / truth[lab], pr / trivial, lamP[lab], haar), flush=True)

# (8) best Q that is a function of the singular values, at f2 = c
for c in ((3.5, 3.0, 2.5, 2.0, 1.5, 1.0, 0.7, 0.5, 0.3, 0.1) if '6' in fams else ()):
    D = np.maximum(c, s2)
    f1s = {}
    for lab, W in sets:
        UW = U[W]
        f1s[lab] = top_eig((UW * D) @ UW.conj().T) / c
    report('8', 'spectral Q with f2 = c = %.1f' % c, c, f1s)

# (7) Tikhonov inverse Gram
for tau in ((1.0, 0.3, 0.1, 0.03) if '7' in fams else ()):
    Qinv = Gh + tau * np.eye(R)
    cf = sla.cho_factor(Qinv)
    f2 = top_eig(E.conj().T @ sla.cho_solve(cf, E)) / S
    f1s = {lab: top_eig(Qinv[np.ix_(W, W)]) for lab, W in sets}
    report('7', '(Ghat + %g I)^-1' % tau, f2, f1s)

print('\nsummary (product / truth ; product / trivial) per row set; trivial bound %.3f' % trivial)
for lab, _ in sets:
    if lab.startswith('random') and not lab.endswith('#1'):
        continue
    print('== %s: truth %.4f, trivial %.4f (trivial/truth = %.2f)' % (lab, truth[lab], trivial, trivial / truth[lab]))
    best = {}
    for fam, nm, f2, f1s in rows_out:
        f1 = f1s.get(lab)
        if f1 is None or not np.isfinite(f1):
            continue
        pr = f1 * f2
        if fam not in best or pr < best[fam][0]:
            best[fam] = (pr, nm, f1, f2)
    for fam in sorted(best):
        pr, nm, f1, f2 = best[fam]
        print('   family (%s) best: %-44s f1 %.4g f2 %.4f product %.4f = %.3f x truth = %.3f x trivial' %
              (fam, nm, f1, f2, pr, pr / truth[lab], pr / trivial))
