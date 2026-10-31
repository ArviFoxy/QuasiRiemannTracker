"""Task A, entrywise: exact Poisson duality for the sextic Gram G(z,z') = sum_{n primary} w(N n/L) chi_z(n) conj chi_z'(n).

Weight: the 2D Gaussian w(t) = exp(-pi t) (its Fourier transform is again Gaussian).  Sum: ALL primary n (n = 2 mod 3), no
squarefree / parity restriction, so that the Poisson identity is exact (see theta_dualcore.py for the formula):

  G = P * g~(z) conj g~(z') * Pair * T,   P = 2L/(9 sqrt(3) sqrt(N z N z')),
  Pair = chi_z(z') conj chi_z'(z) chi_z'(-1) chi_z(3) conj chi_z'(3),
  T = sum_{h in Z[w]} exp(-pi N(h)/Lt) phi_A(h) conj chi_z(h) chi_z'(h),   Lt = 27 N(z) N(z')/(4L).

What it prints:
  1. relative error |G_direct - G_formula|/|G_direct| for the coprime pairs of a row sample (quantiles);
  2. the reduction of T to sums over PRIMARY h by the unit character of psi = chi_z conj chi_z' (types a, b, c), with the
     errors of each reduced form, and the self-duality identity   G = sqrt(L/M) eps g~ conj g~ conj G_M(z,z')   with
     |eps| = 1 and G_M the SAME family at the dual length M (L~ for type a, L~/3 for type b);
  3. the phase eps over ALL coprime pairs of the full row set (cheap: no sums): the values it takes, and whether it is constant
     on the classes of (z_* mod 4, z_* mod 9) (the 'O(1) classes' of the fresh look);
  4. the reciprocity sign s(z,z') = chi_z(z') conj chi_z'(z) on classes mod 4.

usage: python3 -I theta_poisson.py B [nrows=30] [seed=5]       (B = 10000 gives the log theta_poisson_B10000.log)
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
nrows = int(sys.argv[2]) if len(sys.argv) > 2 else 30
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 5
CUT = 7.0                                  # Gaussian tails cut at N > CUT * length (e^{-7 pi} = 2.8e-10)
t0 = time.time()
F = tc.build(B, 100)                       # only the rows and their Gauss sums are used
S = dc.Symbols(F)
zs = dc.row_generators(F)
Nrow = F.rows['N'].astype(float)
R = F.R
rng = np.random.default_rng(seed)
win = np.nonzero((Nrow >= B) & (Nrow <= 1.5 * B))[0]
sel = rng.choice(win, min(nrows, len(win)), replace=False)
L = (3 * math.sqrt(3) / 2) * math.sqrt(np.mean(Nrow[sel]) ** 2)         # self-dual length at the mean norm
Lt_max = 27 * (Nrow[sel].max()) ** 2 / (4 * L)
print('rows in window [B, 1.5B]: %d ; sample %d ; L = %.0f (self-dual length (3 sqrt3/2) N0, N0 = %.0f) ; Lt in [%.0f, %.0f]' %
      (len(win), len(sel), L, np.mean(Nrow[sel]), 27 * Nrow[sel].min() ** 2 / (4 * L), Lt_max), flush=True)
pa, pb, pN = dc.elements_primary(CUT * L)
ha, hb, hN = dc.elements_all(CUT * Lt_max)
hprim = (ha % 3 == 2) & (hb % 3 == 0)
print('primary elements to %.0f: %d ; dual elements (all h) to %.0f: %d   (%.0fs)' % (CUT * L, len(pa), CUT * Lt_max, len(ha), time.time() - t0), flush=True)
codesP = {int(zi): S.row_codes(int(zi), pa, pb) for zi in sel}
codesH = {int(zi): S.row_codes(int(zi), ha, hb) for zi in sel}
print('symbol tables done (%.0fs)' % (time.time() - t0), flush=True)
UB = np.array([u[1] for u in F.pc.UNITS])                  # omega-coordinate of the six units
ut = F.unit_tw

errs, typ_err = [], defaultdict(list)
ident_err = defaultdict(list)
eps_vals = defaultdict(list)
kcheck = []
n_pairs = 0
for ii in range(len(sel)):
    for jj in range(ii + 1, len(sel)):
        zi, zj = int(sel[ii]), int(sel[jj])
        if (set(F.rows['PID'][zi].tolist()) & set(F.rows['PID'][zj].tolist())) - {-1}:
            continue
        n_pairs += 1
        Ni, Nj = Nrow[zi], Nrow[zj]
        Lt = 27 * Ni * Nj / (4 * L)
        cp, cq = codesP[zi], codesP[zj]
        mk = (cp != dc.ZERO) & (cq != dc.ZERO)
        direct = np.sum(np.exp(-math.pi * pN[mk] / L) * dc.ZETA6[(cp[mk].astype(int) - cq[mk].astype(int)) % 6])
        ch, cj = codesH[zi], codesH[zj]
        mk0 = (ch != dc.ZERO) & (cj != dc.ZERO)
        v2 = (cj.astype(int) - ch.astype(int)) % 6             # conj chi_z(h) chi_z'(h) = zeta^v2
        prod = F.zo.mul(tuple(map(int, zs[zi])), tuple(map(int, zs[zj])))
        A = 1 if prod[0] % 3 == 1 else -1
        phi = np.exp(2j * np.pi * ((2 * A * hb) % 3) / 3)
        m = mk0 & (hN <= CUT * Lt)
        T = np.sum((np.exp(-math.pi * hN / Lt) * phi * dc.ZETA6[v2])[m])
        pair = dc.pair_factor(S, zi, zj, zs)
        P = 2 * L / (9 * math.sqrt(3) * math.sqrt(Ni * Nj))
        gg = F.Grow[zi] * np.conj(F.Grow[zj])
        formula = P * gg * pair * T
        errs.append(abs(direct - formula) / abs(direct))

        def Gp(M):                                              # sum over primary h:  conj G_M(z,z')
            mm = mk0 & hprim & (hN <= CUT * M)
            return np.sum((np.exp(-math.pi * hN / M) * dc.ZETA6[v2])[mm])
        psi_u = ut[zi] * np.conj(ut[zj])
        psi_pi3 = S.row_value(zi, *dc.PI3) * np.conj(S.row_value(zj, *dc.PI3))
        psi_3 = S.row_value(zi, 3, 0) * np.conj(S.row_value(zj, 3, 0))
        if abs(psi_u[1] - 1) > 1e-9:
            typ = 'a'; U = np.sum(np.conj(psi_u) * np.exp(2j * np.pi * ((A * UB) % 3) / 3))
            Tpred = U * Gp(Lt); kap = U / 3; M = Lt
            tw = int(round(np.angle(psi_u[1]) / (2 * np.pi / 3))) % 3          # psi(w) = w^tw
            kcl = 1.0 if tw == A % 3 else psi_u[3].real                          # closed form: U/3 = 1 if psi(w) = w^A, else psi(-1)
            kcheck.append(abs(kap - kcl))
        elif abs(psi_u[3] + 1) < 1e-9:
            typ = 'b'; Tpred = -3 * math.sqrt(3) * 1j * A * np.conj(psi_pi3) * Gp(Lt / 3); kap = -1j * A * np.conj(psi_pi3); M = Lt / 3
        else:
            typ = 'c'; c = np.conj(psi_pi3)
            Tpred = -3 * c * Gp(Lt / 3) + 6 * np.conj(psi_3) * sum(c ** j * Gp(Lt / 3 ** (j + 2)) for j in range(16)); kap = None; M = None
        typ_err[typ].append(abs(T - Tpred) / abs(T))
        if typ != 'c':
            # G = sqrt(L/M) eps g~ conj g~ conj(G_M),   G_M(z,z') = sum_{h prim} w chi_z conj chi_z'  ->  Gp(M) = conj G_M
            eps = pair * kap
            pred = math.sqrt(L / M) * eps * gg * Gp(M)
            ident_err[typ].append(abs(direct - pred) / abs(direct))
            eps_vals[typ].append(eps)
        else:
            eps_vals[typ].append(pair)       # type c: Pair only (the coefficient is a series)
qs = lambda v: ' '.join('%.1e' % x for x in np.quantile(v, [0.5, 0.9, 1.0]))
print('\n1. exact Poisson formula, %d coprime pairs: relative error of G_direct vs G_formula (median, 90%%, max): %s' % (n_pairs, qs(errs)))
print('   (Gaussian tails cut at N > %.0f * length; the residual 1e-10..1e-8 is that truncation)' % CUT)
fr = {t: len(v) for t, v in typ_err.items()}
print('\n2. reduction of T to primary-h sums, by the unit character of psi = chi_z conj chi_z\': pair counts %s' % fr)
for t in 'abc':
    if t in typ_err:
        print('   type %s: |T - T_reduced|/|T| (median, 90%%, max): %s' % (t, qs(typ_err[t])), end='')
        if t in ident_err:
            print('   ;  |G - sqrt(L/M) eps g conj g conj G_M|/|G|: %s' % qs(ident_err[t]), end='')
        print()
print('   closed form U/3 = 1 if psi(w) = w^A else psi(-1): max deviation from the numerical unit sum over type-a pairs: %.1e' % max(kcheck))
print('   type a: psi(w) != 1, T = U conj G_L~,  U = +-3 real;  type b: psi(w) = 1, psi(-1) = -1, T = -3 sqrt3 i A conj psi(pi3) conj G_{L~/3};')
print('   type c: psi trivial on units, T = -3 conj psi(pi3) G~(L~/3) + 6 conj psi(3) sum_j conj psi(pi3)^j G~(L~/3^(j+2))  (Euler factor at pi3)')

# ---- 3. phase structure over all coprime pairs of the full row set (no sums needed)
if R > 6000:
    print('\n3. skipped for R = %d > 6000 (the python class-constancy loops are too slow); see the B = 10000 log' % R)
    sys.exit(0)
print('\n3. phase eps over ALL coprime pairs of the %d rows (B,2B]  [%.0fs]' % (R, time.time() - t0), flush=True)
allr = np.arange(R)
A_par = (zs[:, 0] % 3).astype(int)           # z_* mod 3 in {1, 2}
cls4 = (zs[:, 0] % 4) * 4 + (zs[:, 1] % 4)
cls9 = (zs[:, 0] % 9) * 9 + (zs[:, 1] % 9)
chi_z_zp = np.zeros((R, R), np.int8)          # code of chi_z(z'_*) (6 = zero)
for zi in range(R):
    chi_z_zp[zi] = S.row_codes(zi, zs[:, 0], zs[:, 1])
c_m1 = np.array([S.row_codes(zi, np.array([-1]), np.array([0]))[0] for zi in range(R)])
c_3 = np.array([S.row_codes(zi, np.array([3]), np.array([0]))[0] for zi in range(R)])
c_pi3 = np.array([S.row_codes(zi, np.array([dc.PI3[0]]), np.array([dc.PI3[1]]))[0] for zi in range(R)])
cw = np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3          # chi_z(w) = w^cw
cm = (ut[:, 3].real < 0).astype(int)                                         # chi_z(-1) = (-1)^cm
ok = chi_z_zp != dc.ZERO
np.fill_diagonal(ok, False)
ok &= ok.T
I, J = np.nonzero(np.triu(ok, 1))
print('   coprime pairs: %d of %d' % (len(I), R * (R - 1) // 2))
# s(z,z') = chi_z(z') conj chi_z'(z), exponent in Z/6
sexp = (chi_z_zp[I, J].astype(int) - chi_z_zp[J, I].astype(int)) % 6
print('   s(z,z\') exponent values (0 = +1, 3 = -1):', dict(zip(*np.unique(sexp, return_counts=True))))
# constancy of s on classes mod 4
grp = defaultdict(set)
for i, j, e in zip(I, J, sexp):
    grp[(cls4[i], cls4[j])].add(int(e))
print('   s constant on every (class mod 4, class mod 4) block: %s' % all(len(v) == 1 for v in grp.values()))
# eps exponent in Z/12 (units of 2 pi/12) ; ingredients
dm = (cm[I] + cm[J]) % 2                      # psi(-1) = (-1)^dm
dw = (cw[I] - cw[J]) % 3                      # psi(w) = w^dw
Ai = np.where((A_par[I] * A_par[J]) % 3 == 1, 1, -1)       # A = (z z')^{-1} = z z' mod 3 in {+-1}
typ = np.where(dw != 0, 0, np.where(dm == 1, 1, 2))
print('   pair types: a %.3f  b %.3f  c %.3f' % ((typ == 0).mean(), (typ == 1).mean(), (typ == 2).mean()))
# Pair exponent (units of 1/6): chi_z(z') - chi_z'(z) + chi_z'(-1) + chi_z(3) - chi_z'(3)
pair_e = (chi_z_zp[I, J].astype(int) - chi_z_zp[J, I].astype(int) + c_m1[J].astype(int) + c_3[I].astype(int) - c_3[J].astype(int)) % 6
# kappa: type a: U/3 = 1 if psi(w) = w^A else psi(-1) ; type b: -i A conj psi(pi3)
psi_pi3_e = (c_pi3[I].astype(int) - c_pi3[J].astype(int)) % 6
kap12 = np.zeros(len(I), int)                  # exponent in units of 1/12
ua = (dw == (Ai % 3))                          # psi(w) = w^A  <=> dw == A mod 3
kap12 = np.where(typ == 0, np.where(ua, 0, 6 * dm), (-3 * Ai - 2 * psi_pi3_e) % 12)
eps12 = (2 * pair_e + kap12) % 12
print('   eps = Pair * kappa in 12th roots of unity: exponent counts (units 2pi/12): by type')
for t, nm in enumerate('abc'):
    mm = typ == t
    if t < 2:
        print('     type %s: %s' % (nm, dict(zip(*[x.tolist() for x in np.unique(eps12[mm], return_counts=True)]))))
    else:
        print('     type %s (Pair only, exponent in 1/6): %s' % (nm, dict(zip(*[x.tolist() for x in np.unique(pair_e[mm], return_counts=True)]))))
# class constancy of eps (types a, b) on (cls4, cls9) x (cls4, cls9)
for name, cl in (('z_* mod 4', cls4), ('z_* mod 4 and mod 9', cls4 * 100 + cls9), ('z_* mod 4, mod 9, unit class', (cls4 * 100 + cls9) * 6 + cw * 2 + cm)):
    for t, nm in enumerate('ab'):
        mm = typ == t
        g = defaultdict(set)
        for i, j, e in zip(I[mm], J[mm], eps12[mm]):
            g[(cl[i], cl[j])].add(int(e))
        pure = sum(1 for v in g.values() if len(v) == 1)
        print('   type %s: eps constant on class pairs (%s): %d of %d blocks pure (%d class pairs seen)' % (nm, name, pure, len(g), len(g)))
# type c: the coefficients are (Pair, psi(pi3), psi(3)); constant on classes mod 36?
mm = typ == 2
psi3_e = (c_3[I] - c_3[J]) % 6
g = defaultdict(set)
cl36 = cls4 * 100 + cls9
for i, j, a_, b_, c_ in zip(I[mm], J[mm], pair_e[mm], psi_pi3_e[mm], psi3_e[mm]):
    g[(cl36[i], cl36[j])].add((int(a_), int(b_), int(c_)))
print('   type c: (Pair, psi(pi3), psi(3)) constant on class pairs (z_* mod 4 and mod 9): %d of %d blocks pure' % (sum(1 for v in g.values() if len(v) == 1), len(g)))
print('\ndone in %.0fs' % (time.time() - t0))
