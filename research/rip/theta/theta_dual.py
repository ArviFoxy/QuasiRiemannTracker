"""Task A, matrix level: how exactly is the Gaussian-weighted sextic Gram G_off self-dual at the balanced point?

Rows: the squarefree ideals z with N(z) in [B, wf*B] coprime to 6 (a narrow window); sources: ALL primary n with the weight
w(n) = exp(-pi N(n)/L), L = (3 sqrt3/2) N0 the self-dual length at the window's mean norm N0 (then the common dual length Lt0 =
27 N0^2/(4L) equals L).  G = sum_n w chi_z(n) conj chi_z'(n) and G_off = G minus its diagonal.

Predicted dual images of G_off (all built from the exact Poisson formula of theta_dualcore.py / theta_poisson.py):
  P0  exact formula with the COMMON dual length Lt0 in place of Lt(z,z') = 27 N(z) N(z')/(4L)   [window-width error only];
  P1  = P0 rewritten through PRIMARY-h Grams (unit-character types a, b, c; lengths Lt0, Lt0/3, Lt0/9, ...)  [algebraically equal];
  P0' = P0 plus the first-order dilation correction (weights exp(-pi N(h)/Lt(z,z')) expanded to first order in
        1/Lt0 - 1/Lt(z,z'), which is a sum a(z) + a(z'));
  P3  the single-length family image: every pair gets sqrt(L/Lt0) eps_t g~ conj g~ conj G_{Lt0}(z,z') with its type's eps
      (type c: leading term) -- i.e. 'the dual is the SAME family at ONE length';
  P4  the naive image of the fresh look: eps replaced by s(z,z') chi_z'(-1) only.
Non-coprime pairs get prediction 0 in every P (the formula has Pair = 0 there); their share of ||G_off||_F^2 is reported.
It reports ||G_off - P||_F/||G_off||_F, ||G_off - P||_op/||G_off||_op, the error split by pair type, and the top/bottom
eigenvalues of G_off and of each P (units of the mean diagonal), plus a ladder showing what the sieve's own restrictions
(sharp cutoff N <= Lc, odd norm, squarefree norm) do to G_off: cosine of the off-diagonal parts with the Gaussian one.

usage: python3 -I theta_dual.py B [wf=1.1] [Lmul=1.0] [dil=1]
       (Lmul scales L away from the self-dual length; dil=0 skips the first-order dilation correction P0' to save time)
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '2')
from collections import defaultdict
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_dualcore as dc      # noqa: E402

B = int(sys.argv[1])
wf = float(sys.argv[2]) if len(sys.argv) > 2 else 1.1
Lmul = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
DIL = int(sys.argv[4]) if len(sys.argv) > 4 else 1
CUT = 7.0
t0 = time.time()
F = tc.build(B, 100)
S = dc.Symbols(F)
zsall = dc.row_generators(F)
Nall = F.rows['N'].astype(float)
W = np.nonzero((Nall >= B) & (Nall <= wf * B))[0]
Rw = len(W)
N = Nall[W]; zs = zsall[W]; Gz = F.Grow[W]; ut = F.unit_tw[W]
N0 = N.mean()
L = Lmul * (3 * math.sqrt(3) / 2) * N0
Lt0 = 27 * N0 ** 2 / (4 * L)
Ltmax = 27 * N.max() ** 2 / (4 * L)
print('window [B, %.2fB]: %d rows ; N0 = %.0f ; L = %.0f (x%.2f of self-dual) ; common dual length Lt0 = %.0f ; Lt(z,z\') in [%.0f, %.0f]' %
      (wf, Rw, N0, L, Lmul, Lt0, 27 * N.min() ** 2 / (4 * L), Ltmax), flush=True)

# ---------------------------------------------------------------- Gram on the primary sources (Gaussian) and the sieve ladder
pa, pb, pN = dc.elements_primary(CUT * L)
print('primary sources to %.0f: %d' % (CUT * L, len(pa)), flush=True)
codesP = np.zeros((Rw, len(pa)), np.int8)
for k, zi in enumerate(W):
    codesP[k] = S.row_codes(int(zi), pa, pb)
print('  symbols (%.0fs)' % (time.time() - t0), flush=True)
LUT = np.concatenate([dc.ZETA6, [0]])
sqfree = np.ones(len(pN), bool)                                   # squarefree norm, by sieving with p^2 for p <= sqrt(max)
for p_ in range(2, int(math.isqrt(int(pN.max()))) + 1):
    if all(p_ % q for q in range(2, int(math.isqrt(p_)) + 1)):
        sqfree &= (pN % (p_ * p_) != 0)
odd = pN % 2 == 1
ladder = {}
Lc_list = [0.5 * L, 1.0 * L, 2.0 * L]
weights = {'gauss': np.exp(-math.pi * pN / L)}
for lc in Lc_list:
    weights['sharp %.1fL' % (lc / L)] = (pN <= lc).astype(float)
    weights['sharp %.1fL odd' % (lc / L)] = ((pN <= lc) & odd).astype(float)
    weights['sharp %.1fL odd sqfree' % (lc / L)] = ((pN <= lc) & odd & sqfree & (pN > 1)).astype(float)
Gs = {k: np.zeros((Rw, Rw), complex) for k in weights}
CH = 20000
for c0 in range(0, len(pa), CH):
    C = LUT[codesP[:, c0:c0 + CH]]
    for k, w in weights.items():
        ww = w[c0:c0 + CH]
        if ww.any():
            Cw = C * np.sqrt(ww)[None, :]
            Gs[k] += Cw @ Cw.conj().T
G = Gs['gauss']
diag = np.real(np.diag(G)).copy()
print('Gram done (%.0fs); mean diagonal %.1f (= sum_n w ~ L/(9) (2/sqrt3) * coprime density = %.1f)' % (time.time() - t0, diag.mean(), L * 2 / (9 * math.sqrt(3))), flush=True)
Goff = G - np.diag(np.diag(G))

# ---------------------------------------------------------------- the dual side: symbols at all h (and primary h)
ha, hb, hN = dc.elements_all(CUT * Ltmax)
hprim = (ha % 3 == 2) & (hb % 3 == 0)
print('dual elements to %.0f: %d (primary: %d)' % (CUT * Ltmax, len(ha), hprim.sum()), flush=True)
codesH = np.zeros((Rw, len(ha)), np.int8)
for k, zi in enumerate(W):
    codesH[k] = S.row_codes(int(zi), ha, hb)
print('  dual symbols (%.0fs)' % (time.time() - t0), flush=True)
phi1 = np.exp(2j * np.pi * ((2 * hb) % 3) / 3)                 # phi_{A=+1}(h)
T0 = {+1: np.zeros((Rw, Rw), complex), -1: np.zeros((Rw, Rw), complex)}
T1 = {+1: np.zeros((Rw, Rw), complex), -1: np.zeros((Rw, Rw), complex)}      # N(h)-weighted (first order dilation)
Mset = [Lt0 / 3 ** k for k in range(0, 14)]
Gp = {k: np.zeros((Rw, Rw), complex) for k in range(len(Mset))}               # conj G^fam_M over primary h
wt0 = np.exp(-math.pi * hN / Lt0) * (hN <= CUT * Lt0)
for c0 in range(0, len(ha), CH):
    sl = slice(c0, c0 + CH)
    Vc = np.conj(LUT[codesH[:, sl]])                                          # conj chi_z(h)
    ww = np.sqrt(wt0[sl])
    Vw = Vc * ww[None, :]
    ph = phi1[sl]
    for A in (+1, -1):
        phA = ph if A == 1 else np.conj(ph)
        T0[A] += (Vw * phA[None, :]) @ Vw.conj().T
        if DIL:
            T1[A] += (Vw * (phA * math.pi * hN[sl] / Lt0)[None, :]) @ Vw.conj().T
    pm = hprim[sl]
    if pm.any():
        Vp = Vc[:, pm]; Np = hN[sl][pm]
        for k, M in enumerate(Mset):
            wk = np.exp(-math.pi * Np / M) * (Np <= CUT * M)
            if wk.any():
                Vk = Vp * np.sqrt(wk)[None, :]
                Gp[k] += Vk @ Vk.conj().T
print('dual Grams done (%.0fs)' % (time.time() - t0), flush=True)

# ---------------------------------------------------------------- pair data (window rows)
A_par = (zs[:, 0] % 3).astype(int)
chi_z_zp = np.zeros((Rw, Rw), np.int8)
for k, zi in enumerate(W):
    chi_z_zp[k] = S.row_codes(int(zi), zs[:, 0], zs[:, 1])
c_m1 = np.array([S.row_codes(int(zi), np.array([-1]), np.array([0]))[0] for zi in W]).astype(int)
c_3 = np.array([S.row_codes(int(zi), np.array([3]), np.array([0]))[0] for zi in W]).astype(int)
c_pi3 = np.array([S.row_codes(int(zi), np.array([dc.PI3[0]]), np.array([dc.PI3[1]]))[0] for zi in W]).astype(int)
cop = (chi_z_zp != dc.ZERO)
cop &= cop.T
np.fill_diagonal(cop, False)
cz = chi_z_zp.astype(int)
pair_e = (cz - cz.T + c_m1[None, :] + c_3[:, None] - c_3[None, :]) % 6          # exponent of Pair (units 1/6), [i, j]
Pair = np.where(cop, LUT[pair_e % 6], 0)
cw = np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3
cm = (ut[:, 3].real < 0).astype(int)
dw = (cw[:, None] - cw[None, :]) % 3
dm = (cm[:, None] + cm[None, :]) % 2
Aij = np.where((A_par[:, None] * A_par[None, :]) % 3 == 1, 1, -1)
typ = np.where(dw != 0, 0, np.where(dm == 1, 1, 2))
psi_pi3_e = (c_pi3[:, None] - c_pi3[None, :]) % 6
psi_3_e = (c_3[:, None] - c_3[None, :]) % 6
ua = (dw == (Aij % 3))
UB = np.array([u[1] for u in F.pc.UNITS])
kap_a = np.where(ua, 1.0, np.where(dm == 1, -1.0, 1.0))                          # U/3
kap_b = -1j * Aij * np.conj(LUT[psi_pi3_e])                                      # -i A conj psi(pi3)
Pfac = 2 * L / (9 * math.sqrt(3)) / np.sqrt(N[:, None] * N[None, :])
gg = Gz[:, None] * np.conj(Gz)[None, :]
print('pair types among coprime pairs: a %.3f b %.3f c %.3f ; non-coprime pairs %.3f' %
      (((typ == 0) & cop).sum() / cop.sum(), ((typ == 1) & cop).sum() / cop.sum(), ((typ == 2) & cop).sum() / cop.sum(), 1 - cop.sum() / (Rw * (Rw - 1))), flush=True)


def select(Mp, Mm):
    return np.where(Aij == 1, Mp, Mm)


# P0: exact formula, common length
P0 = np.where(cop, Pfac * gg * Pair * select(T0[1], T0[-1]), 0)
# P0': first order dilation  exp(-pi N(h)/Lt) ~ exp(-pi N(h)/Lt0) (1 + pi N(h) (1/Lt0 - 1/Lt))  with 1/Lt = 4 L N(z)N(z')... : 1/Lt = 4L/(27 N N')
inv_Lt = 4 * L / (27 * N[:, None] * N[None, :])
dl = (1 / Lt0 - inv_Lt)                                            # (1/Lt0 - 1/Lt)(z,z'), multiplies pi N(h)/Lt0-weighted Gram / (1/Lt0)
P0p = np.where(cop, Pfac * gg * Pair * (select(T0[1], T0[-1]) + dl * Lt0 * select(T1[1], T1[-1]) / 1.0 * 1.0), 0)
# (T1 contains pi N(h)/Lt0 * w0 ; the first-order term is pi N(h) (1/Lt0 - 1/Lt) w0 = (1 - Lt0/Lt) * [pi N(h)/Lt0 w0]  -> use dl*Lt0)
# P1: through primary-h Grams
Gp0, Gp1 = Gp[0], Gp[1]
Ta = np.zeros((Rw, Rw), complex)
# U = +-3 (type a)
Ta = 3 * kap_a * Gp0
Tb = -3 * math.sqrt(3) * 1j * Aij * np.conj(LUT[psi_pi3_e]) * Gp1
cc = np.conj(LUT[psi_pi3_e])
c3 = np.conj(LUT[psi_3_e])
ser = np.zeros((Rw, Rw), complex)
for j in range(12):
    ser += cc ** j * Gp[j + 2]
Tc = -3 * cc * Gp1 + 6 * c3 * ser
T1fam = np.where(typ == 0, Ta, np.where(typ == 1, Tb, Tc))
P1 = np.where(cop, Pfac * gg * Pair * T1fam, 0)
# P3: single length family image   sqrt(L/Lt0) eps g conj g conj G_{Lt0};  type c: leading term eps = Pair * (-conj psi(pi3))
base3 = math.sqrt(L / Lt0) * gg * Gp0
eps3 = np.where(typ == 0, Pair * kap_a, np.where(typ == 1, Pair * kap_b, Pair * (-cc)))
P3 = np.where(cop, eps3 * base3, 0)
# P4: naive sign s(z,z') chi_z'(-1) only
s_e = (cz - cz.T) % 6
eps4 = np.where(cop, LUT[(s_e + 3 * 0 + c_m1[None, :]) % 6], 0)
P4 = eps4 * base3


def rel(P, mask=None):
    D = Goff - P
    if mask is not None:
        D = np.where(mask, D, 0); Gm = np.where(mask, Goff, 0)
    else:
        Gm = Goff
    fro = np.linalg.norm(D) / np.linalg.norm(Gm)
    op = np.linalg.norm(D, 2) / np.linalg.norm(Gm, 2)
    return fro, op


nc = ~cop & ~np.eye(Rw, dtype=bool)
print('\nshare of ||G_off||_F^2 on non-coprime pairs: %.3f ; on type a / b / c coprime pairs: %.3f / %.3f / %.3f' %
      (np.sum(np.abs(Goff[nc]) ** 2) / np.sum(np.abs(Goff) ** 2), *[np.sum(np.abs(Goff[cop & (typ == t)]) ** 2) / np.sum(np.abs(Goff) ** 2) for t in range(3)]))
print('\nrelative error of the predicted dual image    Frobenius  operator  | Frobenius on coprime pairs of type a  b  c')
for name, P in (('P0  exact formula, common Lt0', P0), ("P0' + first-order dilation correction", P0p), ('P1  primary-h Grams, 3 types (= P0)', P1),
                ('P3  single-length family image', P3), ('P4  naive sign s*chi(-1) only', P4), ('zero prediction', np.zeros_like(P0))):
    fr, op = rel(P)
    byt = [rel(P, cop & (typ == t))[0] for t in range(3)]
    print('  %-42s %.4f    %.4f   |  %.4f %.4f %.4f' % (name, fr, op, *byt))
print('  (P1 - P0 relative size: %.1e)' % (np.linalg.norm(P1 - P0) / np.linalg.norm(P0)))
print('\nsame comparison on COPRIME pairs only (G_off and P both restricted to coprime pairs): Frobenius  operator')
Gc = np.where(cop, Goff, 0)
for name, P in (('P0  exact formula, common Lt0', P0), ("P0' + first-order dilation correction", P0p), ('P3  single-length family image', P3), ('P4  naive sign', P4)):
    fr, op = rel(P, cop)
    print('  %-42s %.4f    %.4f' % (name, fr, op))
# entries correlation
for name, P in (('P0', P0), ("P0'", P0p), ('P3', P3)):
    m = cop
    c = np.vdot(P[m], Goff[m]) / (np.linalg.norm(P[m]) * np.linalg.norm(Goff[m]))
    sc = np.vdot(P[m], Goff[m]).real / np.vdot(P[m], P[m]).real
    print('  %s: complex cosine with G_off on coprime pairs %.4f %+.4fi ; least-squares scale %.4f' % (name, c.real, c.imag, sc))

# ---------------------------------------------------------------- spectra
dm_ = diag.mean()
def eigs(M):
    M = (M + M.conj().T) / 2
    return np.linalg.eigvalsh(M) / dm_
eg = eigs(Goff)
print('\neigenvalues of G_off / mean diagonal: top5 %s ; bottom5 %s ; Frobenius^2/R %.3f' % (np.round(eg[-5:][::-1], 3), np.round(eg[:5], 3), np.linalg.norm(Goff) ** 2 / Rw / dm_ ** 2))
Keff = (np.sum(weights['gauss'])) ** 2 / np.sum(weights['gauss'] ** 2)
cMP = Rw / Keff
print('  Marchenko-Pastur reference for a random Gram with K_eff = (sum w)^2/sum w^2 = %.0f sources (c = R/K_eff = %.4f): edges %.3f, %.3f ; ||G_off||_F^2/(R diag^2) would be %.4f' %
      (Keff, cMP, (1 + math.sqrt(cMP)) ** 2 - 1, (1 - math.sqrt(cMP)) ** 2 - 1, cMP))
Pm = np.where(cop, 1.0, 0) * Goff
ec = eigs(Pm)
print('  G_off with the non-coprime pairs removed: top5 %s ; bottom5 %s' % (np.round(ec[-5:][::-1], 3), np.round(ec[:5], 3)))
for name, P in (('P0', P0), ("P0'", P0p)):
    ep = eigs(P)
    print('  vs %-3s: max |sorted eigenvalue difference| / ||.||_op = %.4f' % (name, np.max(np.abs(ep - ec)) / max(abs(ec[0]), abs(ec[-1]))))
for name, P in (('P0', P0), ("P0'", P0p), ('P3', P3), ('P4', P4)):
    ep = eigs(P)
    print('  %-3s: top5 %s ; bottom5 %s ; max |sorted eigenvalue difference| / ||G_off||_op %.4f' % (name, np.round(ep[-5:][::-1], 3), np.round(ep[:5], 3), np.max(np.abs(ep - eg)) / max(abs(eg[0]), abs(eg[-1]))))
# top eigenvector overlap
def topvec(M):
    w, v = np.linalg.eigh((M + M.conj().T) / 2)
    return v[:, -1], v[:, 0]
vg, vgl = topvec(Goff)
for name, P in (('P0', P0), ("P0'", P0p), ('P3', P3)):
    vp, vpl = topvec(P)
    print('  %-3s: |<top eigvec of G_off, of P>| = %.3f ; |<bottom, bottom>| = %.3f' % (name, abs(np.vdot(vg, vp)), abs(np.vdot(vgl, vpl))))

# ---------------------------------------------------------------- ladder: sieve restrictions
print('\nwhat the sieve\'s own source restrictions do to the off-diagonal Gram (cosine with the Gaussian G_off, mean diagonal in units of the Gaussian one):')
gref = Goff
for k, M in Gs.items():
    if k == 'gauss':
        continue
    Mo = M - np.diag(np.diag(M))
    m = np.ones((Rw, Rw), bool); np.fill_diagonal(m, False)
    c = np.vdot(gref[m], Mo[m]) / (np.linalg.norm(gref[m]) * np.linalg.norm(Mo[m]))
    print('  %-26s cosine %.3f %+.3fi ; mean diag %.1f ; ||G_off||_F/R %.2f' % (k, c.real, c.imag, np.real(np.diag(M)).mean(), np.linalg.norm(Mo) / Rw))
print('\ndone in %.0fs' % (time.time() - t0))
