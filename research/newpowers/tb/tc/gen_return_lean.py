"""Emit the Lean final-return certificate of the repeated-mark submission.

Mirrors the layout of Collet's generated final stage (Record1252270103Finite/ReturnConstants,
ReturnNNN, AdmissionNN; Record1252270103Return/CountWindows, FinalEdgeCertificates), with the
constants of our final source faces.  All arithmetic is exact (Fractions); every Bernstein
certificate is `m + sum g_ij bterm_ij` with `m = min beta > 0`, `g_ij >= 0`.

usage: python3 gen_return_lean.py CHAIN THETA H iC iP OUTDIR [SC [SP [global]]]
SC is the constant-width cap of the count face C (default 11/250, Collet's value); the face is
proved up to its own cap, so any SC below it is admissible. SP is the numerator cap of the
physical face (default 1/25, Collet's value). With `global`, the physical face is applied through
its global source theorem (Lemma D) and the window receipts of Collet's schedule are not checked.
With `lemmaD`, as `global`, and the receipt `source_lambda_low` (lambda_P > 3, PR 69's FR21) is not
checked either: the forked schedule (ReturnD/Schedule.lean) needs only 2 <= lambda_P <= 9/2.
The receipt `dMinus_lower_3_4` checks ds > 3/4, or ds > QRH_DMINUS when that is set (cert_return.py).
With QRH_WINDOWS=lemmaW the count windows are Lemma W's (research/return-transfer/REPORT.md §2; run
fork_return.py with the same flag): lowerM without 2/5, upperM and the natural tail at the crossover
crossM b, guards 12-14 = 1/2 - m_X - eta, w_X - eta, (z_* - eta) DJ, and branchCap = the window caps
(window_caps: QRH_WCAP, by default the face caps of the faces file).
"""
import sys, json, os
from fractions import Fraction as Fr
from math import comb
import cert_return as CR

NS = 'QRH.RepeatedMarks.Return'
PKG = os.environ.get('QRH_PKG', 'Submissions.repeated_marks_20261024')
HDR = '/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).\nLayout and definitions follow Collet\'s final stage (Record1252270103Finite, Apache-2.0). -/\n'

LEAN_BRANCH = {'old': '.old', 'C': '.C', 'Ccap': '.capC', 'C-7': '.weakC7', 'P': '.P', 'Pcap': '.capP'}
ALLOWED = ['old', 'C', 'Ccap', 'C-7', 'P', 'Pcap']


def q(v):
    v = Fr(v)
    return f'({v.numerator}/{v.denominator}:ℝ)' if v.denominator != 1 else f'({v.numerator}:ℝ)'


def qs(v):
    """bare rational literal, for interval endpoints"""
    v = Fr(v)
    return f'{v.numerator}/{v.denominator}' if v.denominator != 1 else f'{v.numerator}/1'


# ---------------------------------------------------------------- Bernstein form
def bern_coeffs(a, box):
    (d0, d1), (p0, p1) = box
    n, m = CR.degs(a)
    w1, w2 = d1 - d0, p1 - p0
    sc = {}
    for (i, j), c in a.items():
        for s in range(i + 1):
            ci = c * comb(i, s) * d0 ** (i - s) * w1 ** s
            for t in range(j + 1):
                sc[(s, t)] = sc.get((s, t), 0) + ci * comb(j, t) * p0 ** (j - t) * w2 ** t
    beta = [[Fr(0)] * (m + 1) for _ in range(n + 1)]
    for I in range(n + 1):
        for J in range(m + 1):
            b = Fr(0)
            for s in range(I + 1):
                for t in range(J + 1):
                    c = sc.get((s, t), 0)
                    if c:
                        b += c * Fr(comb(I, s) * comb(J, t), comb(n, s) * comb(m, t))
            beta[I][J] = b
    return n, m, beta


def certificate(a, box):
    """(n1,n2,m,g) with a = m + sum g_ij bterm_ij on box, m>0, g>=0."""
    (d0, d1), (p0, p1) = box
    n, m, beta = bern_coeffs(a, box)
    mn = min(min(r) for r in beta)
    if mn <= 0:
        raise ValueError('non-positive Bernstein coefficient')
    sc = (d1 - d0) ** n * (p1 - p0) ** m
    g = [[(beta[i][j] - mn) * comb(n, i) * comb(m, j) / sc for j in range(m + 1)] for i in range(n + 1)]
    # self-check at a few points
    for (u, v) in ((Fr(1, 3), Fr(2, 7)), (Fr(0), Fr(1)), (Fr(5, 9), Fr(0))):
        dd = d0 + (d1 - d0) * u
        pp = p0 + (p1 - p0) * v
        lhs = sum(c * dd ** i * pp ** j for (i, j), c in a.items())
        rhs = mn + sum(g[i][j] * (dd - d0) ** i * (d1 - dd) ** (n - i) * (pp - p0) ** j * (p1 - pp) ** (m - j)
                       for i in range(n + 1) for j in range(m + 1))
        assert lhs == rhs, 'certificate identity'
    return n, m, mn, g


def lean_matrix(g):
    rows = []
    for r in g:
        rows.append('![' + ', '.join(q(v) for v in r) + ']')
    return '![' + ',\n'.join(rows) + ']'


# ---------------------------------------------------------------- cover tree
class Leaf:
    def __init__(self, cand, box):
        self.cand, self.box = cand, box


class Split:
    def __init__(self, axis, mid, lo, hi, box):
        self.axis, self.mid, self.lo, self.hi, self.box = axis, mid, lo, hi, box


def cover_tree(G, d, C, cands, box=((Fr(0), Fr(3, 4)), (Fr(0), Fr(1, 2))), depth=0, maxdepth=34):
    (d0, d1), (p0, p1) = box
    for name, br, meta in cands:
        rp = CR.return_poly(br, G, d, C)
        if CR.bernstein_min(rp, box) <= 0:
            continue
        if meta is not None:
            ok, _ = CR.admitted(name, br, meta, ((d0, d1), (p0, Fr(1, 2))))
            if not ok:
                continue
        return Leaf((name, br, meta), box)
    if depth >= maxdepth:
        raise ValueError('cover failed')
    if (d1 - d0) / Fr(3, 4) >= (p1 - p0) / Fr(1, 2):
        mid = (d0 + d1) / 2
        lo = cover_tree(G, d, C, cands, ((d0, mid), (p0, p1)), depth + 1, maxdepth)
        hi = cover_tree(G, d, C, cands, ((mid, d1), (p0, p1)), depth + 1, maxdepth)
        return Split('d', mid, lo, hi, box)
    mid = (p0 + p1) / 2
    lo = cover_tree(G, d, C, cands, ((d0, d1), (p0, mid)), depth + 1, maxdepth)
    hi = cover_tree(G, d, C, cands, ((d0, d1), (mid, p1)), depth + 1, maxdepth)
    return Split('p', mid, lo, hi, box)


def leaves(t):
    if isinstance(t, Leaf):
        return [t]
    return leaves(t.lo) + leaves(t.hi)


# ---------------------------------------------------------------- guards (Lean admissionGuard order)
def guards(br, meta):
    B, L, s_plus, capped = meta
    polys, scal = CR.admission_polys(br, B, L, s_plus, capped)
    order = ['D', 'A', 'C0', 'J', 'T-J', '1.2499J-T', 'Rn-23/37DJ', 'DJ-Rn', 'Mn-mLDJ', 'mUDJ-Mn', 'N-tail',
             'UJp-UpJ']
    out = [polys[k] for k in order]
    k12, k13 = ('1/2-mX-eta', 'wX-eta') if CR.WINDOWS == 'lemmaW' else ('mplus-mH', 'B-2mH-L(s-+eta)')
    out.append(CR.const(scal[k12]))
    out.append(CR.const(scal[k13]))
    out.append(polys['cap'] if capped else CR.const(1))
    return out


# ---------------------------------------------------------------- Lean emitters
CONST_SIMP = 'c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap'
ROW_SIMP = ('rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,'
            'branchZ,isCap,' + CONST_SIMP)
GUARD_SIMP = 'admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,' + ROW_SIMP
if CR.WINDOWS == 'lemmaW':
    GUARD_SIMP = 'crossM,crossW,' + GUARD_SIMP


def emit_constants(P):
    th, h, BP, LP, BC, LC = P['theta'], P['h'], P['BP'], P['LP'], P['BC'], P['LC']
    sP = P['sP']
    K = CR.K_I
    c = 1 - th
    ell = 4 * c - Fr(1, 3)
    x = 1 + ell - h
    y = h - 2 * ell
    kap = 1 - 2 * c
    ds = 2 * y / (1 + 6 * kap * sP)
    dk = 2 * y / (2 - BP + LP * sP)
    dp = h + Fr(1, 10 ** 10)
    d0 = Fr(1, 200)
    oldCap = lambda d: min(d, 2 * y - d) / (6 * kap)
    newCap = lambda d: min(sP * d, (2 * y - (2 - BP) * d) / LP)
    assert ds < dk < dp, 'edge order'
    V = dict(c=c, theta=th, h=h, ell=ell, x=x, y=y, kappa=kap, ds=ds, dk=dk, dp=dp, d0=d0)
    edges = [('oldSmall', d0, oldCap(d0)), ('oldPeak', y, oldCap(y)), ('oldSwitch', ds, oldCap(ds)),
             ('newSwitch', ds, newCap(ds)), ('newTop', dp, newCap(dp)), ('newKink', dk, newCap(dk))]
    assert oldCap(ds) == newCap(ds) == sP * ds
    L = [HDR, 'import Submissions.hailey_collet_1252270103.Record12518109.Bernstein',
         'set_option autoImplicit false', f'namespace {NS}', 'noncomputable section']
    L += [f'def c : ℝ := {q(c)}', f'def h : ℝ := {q(h)}', f'def physicalB : ℝ := {q(BP)}',
          f'def physicalLambda : ℝ := {q(LP)}', f'def countCB : ℝ := {q(BC)}', f'def countCL : ℝ := {q(LC)}',
          f'def naturalK : ℝ := {q(K)}',
          'def theta : ℝ := 1-c', 'def ell : ℝ := 4*c-1/3', 'def x : ℝ := 1+ell-h', 'def y : ℝ := h-2*ell',
          'def kappa : ℝ := 1-2*c', f'def numeratorCap : ℝ := {q(sP)}',
          'def ds : ℝ := 2*y/(1+6*kappa*numeratorCap)',
          'def dk : ℝ := 2*y/(2-physicalB+physicalLambda*numeratorCap)', 'def dp : ℝ := h+1/10000000000',
          'def d0 : ℝ := 1/200', 'def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)',
          'def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)',
          'def rowFee : ℝ := 1/1000000000',
          'inductive Edge | oldSmall | oldPeak | oldSwitch | newSwitch | newTop | newKink',
          ' deriving DecidableEq',
          'def edgeD : Edge → ℝ', ' | .oldSmall => d0', ' | .oldPeak => y', ' | .oldSwitch | .newSwitch => ds',
          ' | .newTop => dp', ' | .newKink => dk',
          'def edgeC (e : Edge) : ℝ := match e with',
          ' | .oldSmall | .oldPeak | .oldSwitch => oldCapacity (edgeD e)',
          ' | .newSwitch | .newTop | .newKink => newCapacity (edgeD e)']
    for k in ('c', 'theta', 'h', 'ell', 'x', 'y', 'kappa', 'ds', 'dk', 'dp', 'd0'):
        L.append(f'theorem {k}_value : {k} = {q(V[k])} := by norm_num [{CONST_SIMP}]')
    for nm, d, C in edges:
        L.append(f'theorem edgeD_{nm} : edgeD .{nm} = {q(d)} := by norm_num [edgeD,{CONST_SIMP}]')
        L.append(f'theorem edgeC_{nm} : edgeC .{nm} = {q(C)} := by norm_num '
                 f'[edgeC,edgeD,oldCapacity,newCapacity,{CONST_SIMP}]')
    L.append('theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = numeratorCap*ds := by')
    L.append(' norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h,numeratorCap]')
    L.append('theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by')
    L.append(' norm_num [theta,x,y,ell,h,c]')
    L += ['end', f'end {NS}', '']
    return '\n'.join(L), V, edges


FORMULAS = r'''
inductive CountBranch | old | C | P | capC | capP | weakC7
 deriving DecidableEq
def branchB : CountBranch → ℝ
 | .C | .capC => countCB
 | .P | .capP => physicalB
 | .weakC7 => countCB-7/4000
 | .old => 0
def branchL : CountBranch → ℝ
 | .C | .capC | .weakC7 => countCL
 | .P | .capP => physicalLambda
 | .old => 1
def branchCap : CountBranch → ℝ
 | .C | .capC | .weakC7 => 11/250
 | .P | .capP => 43/1000
 | .old => 1/25
def isCap : CountBranch → Bool
 | .capC | .capP => true
 | _ => false
def branchZ (b : CountBranch) : ℝ := branchCap b-1/10000000
def V (δ : ℝ) : ℝ := 5/6-δ
def D (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 3-p else 3-p-4*p/branchL b
def A (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 2 else 2-4*p/branchL b
def C0 (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 1-2*p*branchZ b else 1-2*p*branchB b/branchL b
def Z (b : CountBranch) (p : ℝ) : ℝ :=
 if isCap b then 2*p*branchZ b else 2*p*branchB b/branchL b
def U (b : CountBranch) (p : ℝ) : ℝ := (1-p)*C0 b p
def oldD (p : ℝ) : ℝ := 3-p-2*p/(3*kappa)
def oldC (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappa))
def countJ (b : CountBranch) (δ p : ℝ) : ℝ :=
 match b with
 | .old => V δ*oldD p+δ*oldC p
 | b => V δ*D b p+δ*(1-p)*A b p
def countN (b : CountBranch) (δ p : ℝ) : ℝ :=
 match b with
 | .old => (1-δ)*countJ .old δ p+δ*oldC p*V δ/2
 | b => (1-δ)*countJ b δ p+V δ*δ*U b p
def countT (b : CountBranch) (δ p : ℝ) : ℝ := countJ b δ p+δ*U b p
def RN (b : CountBranch) (δ p : ℝ) : ℝ :=
 A b p*countT b δ p+(Z b p-p)*countJ b δ p
def MN (b : CountBranch) (δ p : ℝ) : ℝ :=
 D b p*countT b δ p-RN b δ p
def DJ (b : CountBranch) (δ p : ℝ) : ℝ := D b p*countJ b δ p
def naturalM : ℝ := (1-naturalK*(17/500))/2
def lowerM (b : CountBranch) : ℝ :=
 if isCap b then 2/5+1/10000000 else
 max (2/5+1/10000000) ((branchB b-branchL b*(branchCap b-1/10000000))/2+1/10000000)
def upperM (b : CountBranch) : ℝ :=
 if isCap b then min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*branchZ b)/2-1/10000000)
 else min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*(17/500+1/10000000))/2-1/10000000)
def derivativeD (b : CountBranch) : ℝ := if isCap b then -1 else -1-4/branchL b
def derivativeA (b : CountBranch) : ℝ := if isCap b then 0 else -4/branchL b
def derivativeC (b : CountBranch) : ℝ := if isCap b then -2*branchZ b else -2*branchB b/branchL b
def derivativeU (b : CountBranch) (p : ℝ) : ℝ := -C0 b p+(1-p)*derivativeC b
def derivativeJ (b : CountBranch) (δ p : ℝ) : ℝ :=
 V δ*derivativeD b+δ*(-A b p+(1-p)*derivativeA b)
def admissionGuard (b : CountBranch) (δ p : ℝ) (j : Fin 15) : ℝ :=
 match b with
 | .old => countJ .old δ p
 | b => ![D b p,A b p,C0 b p,countJ b δ p,countT b δ p-countJ b δ p,
 (12499/10000)*countJ b δ p-countT b δ p,
 RN b δ p-(23/37)*DJ b δ p,DJ b δ p-RN b δ p,
 MN b δ p-lowerM b*DJ b δ p,upperM b*DJ b δ p-MN b δ p,
 countN b δ p-(1-2*δ*naturalM-2*δ*p*(17/500))*countJ b δ p,
 U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p,
 11/25-naturalM-1/10000000,
 branchB b-2*naturalM-branchL b*(17/500+1/10000000)-2/10000000,
 if isCap b then (branchZ b-17/500-1/10000000)*DJ b δ p else 1] j

def Ebase (d C δ p : ℝ) : ℝ :=
 1/2+13*h/75-y/2-ell/2-9*d/100+δ/2+δ*p*(ell-C/2)
def rowMargin (e : Edge) (b : CountBranch) (δ p : ℝ) : ℝ :=
 countJ b δ p*(theta-rowFee-Ebase (edgeD e) (edgeC e) δ p)-3/4*edgeD e*countN b δ p
'''

FACTS = r'''
theorem countJ_pos (b : CountBranch) {δ p : ℝ}
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0<countJ b δ p := by
 have hv : 0<V δ := by dsimp [V]; linarith [hδ.2]
 have hdp : 0≤δ*(1-p) := mul_nonneg hδ.1 (by linarith [hp.2])
 have hd : 0<oldD p := by norm_num [oldD,kappa,c]; nlinarith [hp.2]
 have hc : 0≤oldC p := by
  unfold oldC
  apply mul_nonneg
  · nlinarith [hp.2]
  · norm_num [kappa,c]; nlinarith [hp.2]
 have had (b : CountBranch) : 0<D b p := by
  cases b <;> norm_num [D,isCap,branchL,countCL,physicalLambda] <;> nlinarith [hp.2]
 have haa (b : CountBranch) : 0≤A b p := by
  cases b <;> norm_num [A,isCap,branchL,countCL,physicalLambda] <;> nlinarith [hp.2]
 cases b with
 | old => exact add_pos_of_pos_of_nonneg (mul_pos hv hd) (mul_nonneg hδ.1 hc)
 | C => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .C)) (mul_nonneg hdp (haa .C))
 | P => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .P)) (mul_nonneg hdp (haa .P))
 | capC => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capC)) (mul_nonneg hdp (haa .capC))
 | capP => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capP)) (mul_nonneg hdp (haa .capP))
 | weakC7 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC7)) (mul_nonneg hdp (haa .weakC7))

theorem edgeD_nonneg (e : Edge) : 0≤edgeD e := by
 cases e <;> norm_num [edgeD,ds,dk,dp,d0,y,h,ell,c,kappa,physicalB,physicalLambda,numeratorCap]

/-- Requires the actual admitted count at the same witness. -/
theorem exponent_lt_of_margin {e : Edge} {b : CountBranch} {δ p R : ℝ}
 (hJ : 0<countJ b δ p) (hF : 0<rowMargin e b δ p)
 (hR : R≤countN b δ p/countJ b δ p) :
 Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R < theta-rowFee := by
 have hd : 0≤3/4*edgeD e := by positivity [edgeD_nonneg e]
 have hRN := mul_le_mul_of_nonneg_left ((le_div_iff₀ hJ).mp hR) hd
 have hlt : countJ b δ p*(Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R) <
  countJ b δ p*(theta-rowFee) := by
  dsimp [rowMargin] at hF
  nlinarith only [hF,hRN]
 exact (mul_lt_mul_iff_right₀ hJ).mp hlt
'''


# Lemma W (QRH_WINDOWS=lemmaW; research/return-transfer/REPORT.md §2): the count windows opened to the
# faces' proved domain. Each edit is (old, new) on FORMULAS and must apply exactly once.
LEMMA_W_EDITS = [
    (""" | .P | .capP => 43/1000
""", """ | .P | .capP => @@WCAPP@@
"""),
    (""" | .C | .capC | .weakC7 => 11/250
""", """ | .C | .capC | .weakC7 => @@WCAPC@@
"""),
    ("""def lowerM (b : CountBranch) : ℝ :=
 if isCap b then 2/5+1/10000000 else
 max (2/5+1/10000000) ((branchB b-branchL b*(branchCap b-1/10000000))/2+1/10000000)
def upperM (b : CountBranch) : ℝ :=
 if isCap b then min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*branchZ b)/2-1/10000000)
 else min (min (11/25-1/10000000) (naturalM-1/10000000))
 ((branchB b-branchL b*(17/500+1/10000000))/2-1/10000000)
""", """/-- Lemma W: the crossover plain length, where the face width `(B-2m)/Λ` equals the natural width
`(1-2m)/K`; the plain line joins the natural one there. -/
def crossM (b : CountBranch) : ℝ := (naturalK*branchB b-branchL b)/(2*(naturalK-branchL b))
def crossW (b : CountBranch) : ℝ := (1-2*crossM b)/naturalK
def lowerM (b : CountBranch) : ℝ :=
 if isCap b then 1/10000000 else
 max (1/10000000) ((branchB b-branchL b*(branchCap b-1/10000000))/2+1/10000000)
def upperM (b : CountBranch) : ℝ :=
 if isCap b then min (min (1/2-1/10000000) (crossM b-1/10000000))
 ((branchB b-branchL b*branchZ b)/2-1/10000000)
 else min (1/2-1/10000000) (crossM b-1/10000000)
"""),
    (""" countN b δ p-(1-2*δ*naturalM-2*δ*p*(17/500))*countJ b δ p,
 U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p,
 11/25-naturalM-1/10000000,
 branchB b-2*naturalM-branchL b*(17/500+1/10000000)-2/10000000,
 if isCap b then (branchZ b-17/500-1/10000000)*DJ b δ p else 1] j
""", """ countN b δ p-(1-2*δ*crossM b-2*δ*p*crossW b)*countJ b δ p,
 U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p,
 1/2-crossM b-1/10000000,
 crossW b-1/10000000,
 if isCap b then (branchZ b-1/10000000)*DJ b δ p else 1] j
"""),
]


def lemma_w_formulas(wcapC, wcapP):
    text = FORMULAS
    for old, new in LEMMA_W_EDITS:
        assert text.count(old) == 1, old
        text = text.replace(old, new)
    return text.replace('@@WCAPC@@', qs(wcapC)).replace('@@WCAPP@@', qs(wcapP))


def window_caps(capC, capP):
    """Lemma W: the source caps s_+ of the count windows (branchCap), at most the face caps (the count
    moment is the face restricted to broadFace B L s_+; Restricts allows s_+ = cap). QRH_WCAP='sC,sP'
    sets them; by default the face caps themselves (the report used cap - 1/10000 = 749/10000)."""
    w = os.environ.get('QRH_WCAP')
    wC, wP = (Fr(v) for v in w.split(',')) if w else (capC, capP)
    assert 0 < wC <= capC and 0 < wP <= capP, 'window caps must lie in (0, face cap]'
    return wC, wP


def lemma_w_branches(BC, LC, BP, LP):
    """the five improved Lean branches (C, capC, weakC7, P, capP) need K > L and 2/5 <= m_X < 1/2."""
    for B, L in ((BC, LC), (BC - Fr(7, 4000), LC), (BP, LP)):
        mX, wX = CR.crossover(B, L)
        assert CR.K_I > L and Fr(2, 5) <= mX < Fr(1, 2) and wX > CR.ETA, (float(B), float(L), float(mX))


def module_file(mod, imports, body):
    L = [HDR] + [f'import {i}' for i in imports] + ['set_option autoImplicit false', 'set_option linter.unnecessarySeqFocus false', f'namespace {NS}',
                                                    'noncomputable section', body, 'end', f'end {NS}', '']
    return '\n'.join(L)


def emit_row(idx, edge, cand, box, cert):
    n1, n2, m, g = cert
    (d0, d1), (p0, p1) = box
    nm = f'row{idx:03d}'
    br = LEAN_BRANCH[cand]
    s = [f'def {nm}_coefficients : Fin {n1+1} → Fin {n2+1} → ℝ := {lean_matrix(g)}',
         f'theorem {nm}_identity (δ p : ℝ) : rowMargin .{edge} {br} δ p =',
         f' Record12518109.Bernstein.bsum {n1} {n2} {q(m)} {nm}_coefficients {q(d0)} {q(d1)} {q(p0)} {q(p1)} δ p := by',
         f' norm_num [{ROW_SIMP},edgeD_{edge},edgeC_{edge},Record12518109.Bernstein.bsum,'
         f'Record12518109.Bernstein.bterm,{nm}_coefficients,Fin.sum_univ_succ] <;> ring',
         f'theorem {nm}_pos {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
         f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) : 0 < rowMargin .{edge} {br} δ p := by',
         f' rw [{nm}_identity]',
         ' apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp',
         ' intro i j',
         f' fin_cases i <;> fin_cases j <;> norm_num [{nm}_coefficients]']
    return '\n'.join(s)


def emit_admission(widx, cand, window, certs):
    (d0, d1), (p0, p1) = window
    br = LEAN_BRANCH[cand]
    out = []
    for j, cert in enumerate(certs):
        n1, n2, m, g = cert
        nm = f'admission{widx:02d}_{j:02d}'
        out += [f'def {nm}_coefficients : Fin {n1+1} → Fin {n2+1} → ℝ := {lean_matrix(g)}',
                f'theorem {nm}_identity (δ p : ℝ) : admissionGuard {br} δ p {j} =',
                f' Record12518109.Bernstein.bsum {n1} {n2} {q(m)} {nm}_coefficients {q(d0)} {q(d1)} {q(p0)} {q(p1)} δ p := by',
                f' norm_num [{GUARD_SIMP},Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,'
                f'{nm}_coefficients,Fin.sum_univ_succ] <;> ring',
                f'theorem {nm}_pos {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
                f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) : 0 < admissionGuard {br} δ p {j} := by',
                f' rw [{nm}_identity]',
                ' apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp',
                ' intro i j',
                f' fin_cases i <;> fin_cases j <;> norm_num [{nm}_coefficients]']
    out += [f'theorem admission{widx:02d}_all {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
            f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) (j : Fin 15) : 0<admissionGuard {br} δ p j := by',
            ' fin_cases j']
    out += [f' · exact admission{widx:02d}_{j:02d}_pos hδ hp' for j in range(15)]
    return '\n'.join(out)


def main():
    chain = json.load(open(sys.argv[1]))
    th, h = Fr(sys.argv[2]), Fr(sys.argv[3])
    nC, nP = chain[int(sys.argv[4])], chain[int(sys.argv[5])]
    out = sys.argv[6]
    sC = Fr(sys.argv[7]) if len(sys.argv) > 7 else Fr(11, 250)
    sP = Fr(sys.argv[8]) if len(sys.argv) > 8 else Fr(1, 25)
    mode = sys.argv[9] if len(sys.argv) > 9 else 'pr69'
    BC, LC, capC = Fr(nC['B']), Fr(nC['L']), Fr(nC['cap'])
    BP, LP, capP = Fr(nP['B']), Fr(nP['L']), Fr(nP['cap'])
    P = dict(theta=th, h=h, BP=BP, LP=LP, BC=BC, LC=LC, sP=sP)
    G = CR.geometry(th, h, BP, LP, sP)
    rec = CR.receipt(G, BP, LP, capC, capP, sC, Fr(43, 1000), CR.THETA_I)
    if mode == 'global':
        rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP}
    if mode == 'lemmaD':   # as cert_return.run(mode='lemmaD'): the forked schedule needs only 2 <= lambda_P <= 9/2
        rec = {k: v for k, v in rec.items() if k not in CR.GLOBAL_DROP + ('source_lambda_low',)}
    bad = {k: v for k, v in rec.items() if v <= 0}
    assert not bad, bad
    if CR.WINDOWS == 'lemmaW':
        wcapC, wcapP = window_caps(capC, capP)
        lemma_w_branches(BC, LC, BP, LP)
        faces = {'C': (BC, LC, wcapC), 'P': (BP, LP, wcapP)}
        formulas = lemma_w_formulas(wcapC, wcapP)
        print('Lemma W windows: s_+ =', wcapC, wcapP)
    else:
        faces = {'C': (BC, LC, sC), 'P': (BP, LP, Fr(43, 1000))}
        formulas = FORMULAS.replace(' | .C | .capC | .weakC7 => 11/250', f' | .C | .capC | .weakC7 => {qs(sC)}')
    cands = [cd for cd in CR.candidates(faces, G['kap']) if cd[0] in ALLOWED]
    cands.sort(key=lambda cd: ALLOWED.index(cd[0]))
    const_src, V, edges = emit_constants(P)
    os.makedirs(os.path.join(out, 'FinalReturn', 'Rows'), exist_ok=True)
    fr = os.path.join(out, 'FinalReturn')
    open(os.path.join(fr, 'ReturnConstants.lean'), 'w').write(const_src)
    open(os.path.join(fr, 'ReturnFormulas.lean'), 'w').write(
        module_file('ReturnFormulas', [f'{PKG}.FinalReturn.ReturnConstants'], formulas))
    open(os.path.join(fr, 'ReturnFacts.lean'), 'w').write(
        module_file('ReturnFacts', [f'{PKG}.FinalReturn.ReturnFormulas'], FACTS))
    # covers
    trees = {}
    rows = []          # (idx, edge, cand, box)
    windows = {}       # (cand, d0, d1, p0) -> widx
    for nm, d, C in edges:
        t = cover_tree(G, d, C, cands)
        trees[nm] = t
        for lf in leaves(t):
            rows.append((len(rows) + 1, nm, lf.cand[0], lf.box, lf.cand))
            lf.row = len(rows)
            if lf.cand[2] is not None:
                (a0, a1), (b0, _) = lf.box
                key = (lf.cand[0], a0, a1, b0)
                if key not in windows:
                    windows[key] = len(windows) + 1
                lf.window = windows[key]
    print('rows', len(rows), 'windows', len(windows))
    # row files: one module per edge
    edge_of = {}
    for nm, _, _ in edges:
        body = []
        for (idx, e, cand, box, cd) in rows:
            if e != nm:
                continue
            br, d, C = cd[1], dict((a, b) for a, b, _ in edges)[e], dict((a, c) for a, _, c in edges)[e]
            rp = CR.return_poly(br, G, d, C)
            body.append(emit_row(idx, e, cand, box, certificate(rp, box)))
        open(os.path.join(fr, 'Rows', f'Edge_{nm}.lean'), 'w').write(
            module_file(nm, [f'{PKG}.FinalReturn.ReturnFormulas'], '\n'.join(body)))
    # admission files: one module per window
    wl = sorted(windows.items(), key=lambda kv: kv[1])
    candmap = {cd[0]: cd for cd in cands}
    for (cand, a0, a1, b0), widx in wl:
        _, br, meta = candmap[cand]
        win = ((a0, a1), (b0, Fr(1, 2)))
        certs = [certificate(gp, win) for gp in guards(br, meta)]
        open(os.path.join(fr, 'Rows', f'Admission{widx:02d}.lean'), 'w').write(
            module_file(f'Admission{widx:02d}', [f'{PKG}.FinalReturn.ReturnFormulas'],
                        emit_admission(widx, cand, win, certs)))
    json.dump(dict(rows=[(i, e, c, [[str(v) for v in b[0]], [str(v) for v in b[1]]]) for i, e, c, b, _ in rows],
                   windows=[(w, c, str(a0), str(a1), str(b0)) for (c, a0, a1, b0), w in wl]),
              open(os.path.join(fr, 'cover.json'), 'w'), indent=0)
    emit_windows_and_edges(fr, edges, trees, rows, wl)


def emit_windows_and_edges(fr, edges, trees, rows, wl):
    # CountWindows-style window definitions (appended by the fork of CountWindows)
    W = []
    for (cand, a0, a1, b0), widx in wl:
        W += [f'def returnWindow{widx:02d} : ReturnCountWindow where', f' branch := {LEAN_BRANCH[cand]}',
              ' nonold := by decide', f' deltaLo := {q(a0)}', f' deltaHi := {q(a1)}', f' pLo := {q(b0)}',
              ' deltaBounds := by norm_num', ' pBounds := by norm_num', f' certificate := admission{widx:02d}_all']
    W.append('def returnWindows : List ReturnCountWindow := [' +
             ','.join(f'returnWindow{w:02d}' for _, w in wl) + ']')
    open(os.path.join(fr, 'windows.lean.part'), 'w').write('\n'.join(W) + '\n')
    # FinalEdgeCertificates body
    E = []
    for _, w in wl:
        E.append(f'theorem window{w:02d}_mem : returnWindow{w:02d}∈returnWindows := by simp [returnWindows]')
    concl = lambda e: (f'Ebase (edgeD .{e}) (edgeC .{e}) δ p+3/4*edgeD .{e}*'
                       f'(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee')
    for (idx, e, cand, box, cd) in rows:
        (d0, d1), (p0, p1) = box
        br = LEAN_BRANCH[cand]
        E += [f'theorem envelope_row{idx:03d} {{δ p:ℝ}} (hδ:δ∈Set.Icc {q(d0)} {q(d1)}) '
              f'(hp:p∈Set.Icc {q(p0)} {q(p1)}) : {concl(e)} := by',
              ' have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]',
              ' have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]']
        if cd[2] is None:
            E += [' have hR := finiteEnvelope_le_old hd0 hp0',
                  f' exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row{idx:03d}_pos hδ hp) hR']
        else:
            w = dict(((c, a0, a1, b0), ww) for (c, a0, a1, b0), ww in wl)[(cand, d0, d1, p0)]
            E += [f' have ha : returnWindow{w:02d}.Available δ p := by',
                  f'  change δ∈Set.Icc {q(d0)} {q(d1)} ∧ p∈Set.Icc {q(p0)} (1/2:ℝ)',
                  '  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]',
                  f' have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN {br} δ p/countJ {br} δ p := '
                  f'finiteEnvelope_le_window returnWindow{w:02d} window{w:02d}_mem ha',
                  f' exact exponent_lt_of_margin (countJ_pos {br} hd0 hp0) (row{idx:03d}_pos hδ hp) hR']
    counter = [0]

    def node(t, e):
        if isinstance(t, Leaf):
            k = counter[0]; counter[0] += 1
            (d0, d1), (p0, p1) = t.box
            E.extend([f'theorem cover_node_{k:03d} {{δ p:ℝ}} (hδ:δ∈Set.Icc {q(d0)} {q(d1)})',
                      f' (hp:p∈Set.Icc {q(p0)} {q(p1)}) : {concl(e)} := by',
                      f' exact envelope_row{t.row:03d} (by constructor <;> linarith [hδ.1,hδ.2]) '
                      f'(by constructor <;> linarith [hp.1,hp.2])'])
            return k
        a = node(t.lo, e)
        b = node(t.hi, e)
        k = counter[0]; counter[0] += 1
        (d0, d1), (p0, p1) = t.box
        E.extend([f'theorem cover_node_{k:03d} {{δ p:ℝ}} (hδ:δ∈Set.Icc {q(d0)} {q(d1)})',
                  f' (hp:p∈Set.Icc {q(p0)} {q(p1)}) : {concl(e)} := by'])
        if t.axis == 'd':
            E.extend([f' rcases le_total δ {q(t.mid)} with hsplit | hsplit',
                      f' · exact cover_node_{a:03d} ⟨hδ.1,hsplit⟩ hp',
                      f' · exact cover_node_{b:03d} ⟨hsplit,hδ.2⟩ hp'])
        else:
            E.extend([f' rcases le_total p {q(t.mid)} with hsplit | hsplit',
                      f' · exact cover_node_{a:03d} hδ ⟨hp.1,hsplit⟩',
                      f' · exact cover_node_{b:03d} hδ ⟨hsplit,hp.2⟩'])
        return k

    for e, _, _ in edges:
        root = node(trees[e], e)
        E += [f'theorem edge_{e}_certificate {{δ p:ℝ}} (hδ:δ∈Set.Icc 0 (3/4))',
              f' (hp:p∈Set.Icc 0 (1/2)) : {concl(e)} := by',
              f' exact cover_node_{root:03d} (by simpa using hδ) (by simpa using hp)']
    E += ['theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))',
          ' (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*'
          '(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by',
          ' cases e with']
    for e, _, _ in edges:
        E.append(f' | {e} => exact edge_{e}_certificate hδ hp')
    open(os.path.join(fr, 'edges.lean.part'), 'w').write('\n'.join(E) + '\n')


if __name__ == '__main__':
    main()
