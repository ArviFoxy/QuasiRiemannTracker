"""Task B3: candidate 'corner' vectors from Poisson in both variables, and the class-signed source theta.

The source Gram H = E^* E has a coherent part from the Poisson dual of the ROW sum (Gauss sums of the sources, repeated dual
atoms j^6).  Its candidate eigenvector is a conjugate source theta with class phases:

   f(x) = A(x mod 4) * lam3(x) * parsign(x) * conj g~(x) * N(x)^(-alpha),   lam3(x) = omega^(-b/3)   (cubic character mod 9),

12 free class coefficients A, parsign = -1 on sources with chi_x(-1) = -1 and an odd number of prime factors.  Its row image
is E f.  The script measures (all against random-phase controls with the same classes and profile):

  1. literal candidates  a(z) = sum_m conj g~(m) N(m)^(-1/2) chi_z(m) (= E c) and the source thetas g~, conj g~ with unit twists
     only (no class phases): Rayleigh quotients, overlaps with the top singular pair;
  2. the 12-dim class-signed span: compressed top eigenvalue of H/R, overlap |<f, v0>| with the top right vector and |<Ef,u0>|
     with the top left vector, as a function of alpha and of the truncation N(x) <= M;
  3. the 9 cubic characters of the 3-adic class group (only omega^(-b/3) works) and G versus conj G;
  4. the 216-dim (mod 36, parity) span: its top compressed eigenvalues against the singular values of E and the overlaps of
     v_0..v_4 with them (the outliers are a CLUSTER);
  5. the coherent kernel itself: with the class phases Theta fitted on one half of the sources, the phase-aligned average of
     H(x,x') g~(x) conj g~(x') conj Theta(x) Theta(x')/R over pairs of the other half, binned by y = N(x)N(x')/B;
     the dual-atom picture predicts (N N')^(-1/2) mu(y) with mu(y) ~ y^(1/6) (sixth powers j^6 all give the trivial character).

usage: python3 -I theta_mech_corner.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '2')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
t0 = time.time()
A_ = tu.load_all(B, L, 8)
F, sd, sc, s, U, Vh, R, S = A_.F, A_.sd, A_.sc, A_.s, A_.U, A_.Vh, A_.R, A_.S
E = F.E
SN = F.SN.astype(float); Gs = sd['Gsrc']
rng = np.random.default_rng(7)
u0 = U[:, 0]; v0 = Vh[0].conj()
print('top s^2/S: %s ; s^2/R: %s' % (np.round(s[:6] ** 2 / S, 3), np.round(s[:3] ** 2 / R, 3)), flush=True)


def lam3(j, k):
    """cubic character omega^(j*m + k*n) of the 3-adic class of a primary x = (3m - 1) + 3n*omega."""
    m = ((F.SA + 1) // 3) % 3
    n = ((F.SB % 9) // 3)
    return np.exp(2j * np.pi * (j * m + k * n) / 3)


def span_stats(base, cl, tag, nrand=6, show=True):
    """compressed top eigenvalue (s^2/R units) of the class span of `base`, overlap of the best vector with v0, image with u0."""
    X = tu.class_span(cl, base)
    nrm = np.linalg.norm(X, axis=0)
    X = X[:, nrm > 1e-12]
    Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
    M = tu.compressed(F, Xn, 'src')
    w, V = tu.top_eig(M, 3)
    f = Xn @ V[:, 0]
    Ef = E @ f
    ovv = abs(np.vdot(v0, f)); ovu = abs(np.vdot(u0, Ef)) / np.linalg.norm(Ef)
    # random-phase control with the same classes and the same profile
    prof = np.abs(base)
    top_r = []
    for _ in range(nrand):
        Xr = tu.class_span(cl, np.exp(2j * np.pi * rng.random(S)) * prof)
        Xr = Xr[:, np.linalg.norm(Xr, axis=0) > 1e-12]
        Xrn = Xr / np.linalg.norm(Xr, axis=0, keepdims=True)
        top_r.append(tu.top_eig(tu.compressed(F, Xrn, 'src'), 1)[0][0])
    if show:
        print('  %-44s dim %3d  top s^2/R %s  (random phases %.3f +- %.3f)  |<f,v0>| %.3f  |<Ef,u0>| %.3f' %
              (tag, X.shape[1], np.round(w, 3), np.mean(top_r), np.std(top_r), ovv, ovu))
    return w, V, f, np.mean(top_r)


# ---------------------------------------------------------------- 1. literal candidates (no class phases)
print('\n1. literal candidates')
print('   random level of overlaps: 1/sqrt(S) = %.3f, 1/sqrt(R) = %.3f' % (1 / math.sqrt(S), 1 / math.sqrt(R)))
prof_all = SN ** -0.5
for name, c in (('conj g~ N^-1/2', np.conj(Gs) * prof_all), ('g~ N^-1/2', Gs * prof_all)):
    for Mcut in (100, 1000, 10 ** 9):
        cc = c * (SN <= Mcut)
        for k in (0,):
            a = E @ (cc * sd['utw'][:, k])
            r_row = np.linalg.norm(E.conj().T @ a) ** 2 / (S * np.linalg.norm(a) ** 2)
            ov = abs(np.vdot(u0, a)) / np.linalg.norm(a)
            r_src = np.linalg.norm(E @ cc) ** 2 / (R * np.linalg.norm(cc) ** 2)
            ovs = abs(np.vdot(v0, cc)) / np.linalg.norm(cc)
            ccr = np.exp(2j * np.pi * rng.random(S)) * np.abs(cc)
            rr = np.linalg.norm(E @ ccr) ** 2 / (R * np.linalg.norm(ccr) ** 2)
            print('   x <= %-10s %-16s : source Rayleigh |Ec|^2/(R|c|^2) %.3f (random phases %.3f), overlap with v0 %.3f ; row image a = Ec: |<a,u0>| %.3f, |E^*a|^2/(S|a|^2) %.3f' %
                  ('all' if Mcut > 1e8 else Mcut, name, r_src, rr, ovs, ov, r_row))

# ---------------------------------------------------------------- 2. class-signed span: alpha and truncation scans
print('\n2. class-signed conj source theta: base = conj g~ * N^-alpha * lam3 * parsign on the 12 classes mod 4')
alphas = [0.0, 0.1, 0.2, 0.25, 0.3, 1 / 3, 0.4, 0.5, 0.6, 0.75, 1.0]
best = None
for al in alphas:
    base = np.conj(Gs) * SN ** (-al) * lam3(0, -1) * sc['parsign']
    w, V, f, tr = span_stats(base, sc['c4'], 'alpha = %.3f' % al, nrand=3)
    if best is None or w[0] > best[0]:
        best = (w[0], al)
al_best = best[1]
print('   best alpha (largest compressed top eigenvalue): %.3f' % al_best)
al_use = 1 / 3 if abs(al_best - 1 / 3) < 0.11 else al_best
print('   using alpha = %.3f below' % al_use, flush=True)
prof = SN ** (-al_use)
print('   truncated at N(x) <= M (rest of f set to zero):')
for Mcut in (30, 100, 300, 1000, 3000, 10 ** 9):
    base = np.conj(Gs) * prof * lam3(0, -1) * sc['parsign'] * (SN <= Mcut)
    span_stats(base, sc['c4'], 'M = %s' % ('all' if Mcut > 1e8 else Mcut), nrand=2)
print('   truncated at N(x) > M (small sources removed):')
for Mcut in (10, 30, 100, 300, 1000):
    base = np.conj(Gs) * prof * lam3(0, -1) * sc['parsign'] * (SN > Mcut)
    span_stats(base, sc['c4'], 'N(x) > %d' % Mcut, nrand=2)

# fitted class phases A(c) of the best vector at alpha_use and the BBP consistency of the Rayleigh excess
base = np.conj(Gs) * prof * lam3(0, -1) * sc['parsign']
w, V, f, tr = span_stats(base, sc['c4'], 'alpha = %.3f (reference)' % al_use, nrand=4)
top12_ref = w[0]
keys4 = sorted(set(sc['c4'].tolist()))
Xtmp = tu.class_span(sc['c4'], base)
nrm_ = np.linalg.norm(Xtmp, axis=0)
coef = V[:, 0] / nrm_ * np.exp(-1j * np.angle(V[0, 0]))
print('   fitted class coefficients A(c) of the top vector (class = (a mod 4, b mod 4); phase in degrees relative to class %s, in units of 30 degrees):' % (str(divmod(keys4[0], 4))))
print('     ' + '  '.join('(%d,%d): |A|=%.2f ph=%+6.1f (%+5.2f)' % (k // 4, k % 4, abs(coef[i]) * nrm_.mean(), np.angle(coef[i]) * 180 / np.pi, np.angle(coef[i]) * 6 / np.pi) for i, k in enumerate(keys4)))
v0n = float(np.mean(np.abs(E) > 0.5))                # noise variance per entry = fraction of nonzero entries (the coprimality mask)
sig2 = (w[0] - tr) * R / v0n                         # spike sigma^2 in units of the noise variance: compressed top minus random-phase span
bbp = v0n * (sig2 + R) * (sig2 + S) / sig2 / S if sig2 > math.sqrt(R * S) else float('nan')
edge_m = v0n * (math.sqrt(R) + math.sqrt(S)) ** 2 / S
print('   BBP check (mask-corrected, v0 = %.3f): compressed top %.3f - random-phase span %.3f -> sigma^2/R = %.3f ; threshold sqrt(S/R) = %.3f ; masked edge %.3f ; predicted outlier s^2/S = %.3f ; observed %.3f' %
      (v0n, w[0], tr, sig2 / R, math.sqrt(S / R), edge_m, bbp, s[0] ** 2 / S))

# ---------------------------------------------------------------- 3. which 3-adic character, which conjugation
print('\n3. 3-adic twist: omega^(j m + k n) for the 9 cubic characters (m = (a+1)/3, n = b/3 mod 3), alpha = %.3f' % al_use)
for conj in (True, False):
    for j in range(3):
        for k in range(3):
            g = np.conj(Gs) if conj else Gs
            base = g * prof * lam3(j, k) * sc['parsign']
            span_stats(base, sc['c4'], '%s lam3 = w^(%dm+%dn)' % ('conj g~' if conj else 'g~    ', j, k), nrand=2)
print('   without parsign / without any 3-adic twist (class phases only):')
span_stats(np.conj(Gs) * prof * lam3(0, -1), sc['c4'], 'conj g~, lam3 = w^-n, no parsign', nrand=2)
span_stats(np.conj(Gs) * prof * sc['parsign'], sc['c4'], 'conj g~, parsign, no 3-adic twist', nrand=2)
span_stats(np.conj(Gs) * prof, sc['c4'], 'conj g~ only, 12 class phases', nrand=2)

# ---------------------------------------------------------------- 4. the 216-dim span and the cluster of outliers
print('\n4. free coefficients on the 216 classes (mod 36, parity), base conj g~ N^-alpha: compressed spectrum vs singular values')
base = np.conj(Gs) * prof
cl216 = sc['c36'] * 2 + sc['par']
X = tu.class_span(cl216, base)
Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
M = tu.compressed(F, Xn, 'src')
w, V = np.linalg.eigh(M)
o = np.argsort(-w); w = w[o]; V = V[:, o]
Xr = tu.class_span(cl216, np.exp(2j * np.pi * rng.random(S)) * prof)
Xrn = Xr / np.linalg.norm(Xr, axis=0, keepdims=True)
wr = np.sort(np.linalg.eigvalsh(tu.compressed(F, Xrn, 'src')))[::-1]
print('   dim %d ; top-12 compressed eigenvalues (s^2/R): %s' % (Xn.shape[1], np.round(w[:12], 3)))
print('   random-phase span, same classes          : %s' % np.round(wr[:12], 3))
print('   singular values s_k^2/R of E (k = 0..7)  : %s' % np.round(s ** 2 / R, 3))
Vk = np.array([Vh[k].conj() for k in range(8)])
ov = np.abs(Vk.conj() @ (Xn @ V[:, :12]))
print('   |<v_k, w_j>| for k = 0..5 (rows), j = 0..11 (columns):')
for k in range(6):
    print('     v%d: %s' % (k, np.round(ov[k], 2)))
en = np.array([np.linalg.norm(Xn.conj().T @ Vk[k]) ** 2 for k in range(8)])
print('   energy of v_k in the whole 216-dim span (random %.3f): %s' % (Xn.shape[1] / S, np.round(en, 3)))
Xs = tu.class_span(sc['c4'], np.conj(Gs) * prof * lam3(0, -1) * sc['parsign'])
Xsn = Xs / np.linalg.norm(Xs, axis=0, keepdims=True)
en12 = np.array([np.linalg.norm(Xsn.conj().T @ Vk[k]) ** 2 for k in range(8)])
print('   energy of v_k in the 12-dim class-signed span (random %.3f)    : %s' % (Xsn.shape[1] / S, np.round(en12, 3)))
w12, V12 = tu.top_eig(tu.compressed(F, Xsn, 'src'), 12)
print('   12-dim compressed eigenvalues (all 12): %s' % np.round(np.sort(np.linalg.eigvalsh(tu.compressed(F, Xsn, 'src')))[::-1], 3))

# ---------------------------------------------------------------- 5. coherent kernel with split-sample class phases
print("\n5. coherent kernel of H = E^*E: phase-aligned mean of H(x,x') g~(x) conj g~(x') conj Theta(x) Theta(x') / R over pairs, binned by y = N N'/B")
idx = np.arange(S)
half = (idx % 2 == 0)
base = np.conj(Gs) * prof * lam3(0, -1) * sc['parsign'] * half
Xh = tu.class_span(sc['c4'], base)
Xhn = Xh / np.linalg.norm(Xh, axis=0, keepdims=True)
wh, Vh_ = tu.top_eig(tu.compressed(F, Xhn, 'src'), 1)
keys = sorted(set(sc['c4'].tolist()))
Acoef = {k: Vh_[i, 0] / abs(Vh_[i, 0]) for i, k in enumerate(keys)}          # class phase of the fitted vector
Theta = np.array([Acoef[c] for c in sc['c4']]) * lam3(0, -1) * sc['parsign']
other = ~half
io = np.nonzero(other)[0]
ybins = np.array([0.0, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0, 100.0, 300.0, 1000.0, 3000.0, 1e9])
acc = np.zeros(len(ybins) - 1); cnt = np.zeros(len(ybins) - 1); acc2 = np.zeros(len(ybins) - 1); accy = np.zeros(len(ybins) - 1)
Eo = E[:, io]
CHK = 600
for c0 in range(0, len(io), CHK):
    ii = io[c0:c0 + CHK]
    Hb = E[:, ii].conj().T @ Eo                                  # (chunk, |io|) = sum_z conj chi_z(x) chi_z(x')
    Psi = np.real(Hb * (Gs[ii][:, None] * np.conj(Gs[io])[None, :]) * (np.conj(Theta[ii])[:, None] * Theta[io][None, :])) / R
    Y = SN[ii][:, None] * SN[io][None, :] / B
    msk = ii[:, None] != io[None, :]
    bi = np.searchsorted(ybins, Y, side='right') - 1
    for b in range(len(ybins) - 1):
        m = (bi == b) & msk
        if m.any():
            v = Psi[m]
            acc[b] += v.sum(); acc2[b] += (v ** 2).sum(); cnt[b] += m.sum(); accy[b] += np.log(Y[m]).sum()
print('   fitted on even-indexed sources (compressed top %.3f), evaluated on odd-indexed pairs; random-pair sd of the entries ~ 1/sqrt(R) = %.4f' % (wh[0], 1 / math.sqrt(R)))
print("   y = N N'/B bin          pairs     mean Psi/R      s.e.    K = mean*sqrt(N N')   K/y^(1/6)   K/y^(1/3)   (geometric mean y)")
ymid = []
vals = []
for b in range(len(ybins) - 1):
    if cnt[b] < 50:
        continue
    mean = acc[b] / cnt[b]
    se = math.sqrt(max(acc2[b] / cnt[b] - mean ** 2, 0) / cnt[b])
    lo, hi = ybins[b], ybins[b + 1]
    ym = math.exp(accy[b] / cnt[b])
    ymid.append(ym); vals.append(mean)
    K = mean * math.sqrt(ym * B)
    print('   [%7g,%8g) %10d   %+.5f   %.5f   %+.4f         %+.4f      %+.4f     y=%.2f' % (lo, hi, cnt[b], mean, se, K, K / ym ** (1 / 6), K / ym ** (1 / 3), ym))
ymid = np.array(ymid); vals = np.array(vals)
for lo_ in (1.0, 3.0, 10.0):
    sel = (ymid >= lo_) & (vals > 0)
    if sel.sum() >= 3:
        p = np.polyfit(np.log(ymid[sel]), np.log(vals[sel]), 1)
        print('   power-law fit of the mean over bins with y >= %g: Psi ~ y^%.2f   (no multiplicity: y^-0.5 ; sixth-power multiplicity: y^-1/3)' % (lo_, p[0]))

# ---------------------------------------------------------------- 6. control: the same spans on RCHAR (row-prime characters conjugated at random)
print('\n6. control RCHAR: each row prime\'s character conjugated at random (rows still characters, reciprocity broken); same spans, true Gauss sums')
pc = F.pc
uid = np.unique(F.rows['PID'][F.rows['PID'] >= 0])
LOC = pc.local_index(F.rows['PID'], uid)
Tt = pc.symbol_table(F.ID, uid, F.SA, F.SB).astype(np.int16)
Xc = tu.class_span(sc['c4'], base)
Xcn = Xc / np.linalg.norm(Xc, axis=0, keepdims=True)
for draw in range(2):
    ec = rng.choice([1, 5], size=len(uid))
    Tc = np.where(Tt < 6, (Tt * ec[:, None]) % 6, Tt).astype(np.int8)
    Er = pc.chi_chunk(LOC, Tc, 0, R).astype(np.complex128)
    EQ = Er @ Xcn
    Mr = EQ.conj().T @ EQ / R
    wr_, Vr_ = tu.top_eig((Mr + Mr.conj().T) / 2, 3)
    sr = np.linalg.svd(Er, compute_uv=False)[:3] if R * S < 2e7 else None
    print('   RCHAR draw %d: 12-dim class-signed span top s^2/R %s ; sextic %.3f ; random-phase span %.3f%s' %
          (draw, np.round(wr_, 3), top12_ref, tr, '' if sr is None else ' ; top singular s^2/S of RCHAR %s' % np.round(sr ** 2 / S, 3)))
    del Er, EQ
print('\ndone in %.0fs' % (time.time() - t0))
