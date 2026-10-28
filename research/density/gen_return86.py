#!/usr/bin/env python3
"""Generator of the final-return layer `Return/` of the density-split line, in PR 86's layout.

PR 86 (`Submissions.density_split_fine_chain.Return`, 44 modules) is Sil's PR 83 return with retuned constants and
regenerated Bernstein certificates.  This script emits the same 44 modules (or the two-source variant of the endpoint)
for ANY return constants, in any package/namespace, on top of a `ReturnD/` fork (research/density/fork_returnd.py).

  generated here (depend on the constants)             copied from return86_tpl/ (PR 86's text, tokens renamed)
  -------------------------------------------          ----------------------------------------------------------
  Constants.lean                                       Formulas, Facts, Geometry, Conductor, CountAdmission,
  Windows.lean                                         CountDecode, CountMonotonicity, CountWidth, CountWindow,
  Rows/Admission01..NN.lean  (15 guards per window)    FinalEnvelopeBounds, FinalRows (reserve literal patched),
  Rows/Edge_<edge>[_k].lean  (Bernstein rows)          FinalSchedule, FinalScheme, FinalWindows, SourceInlet,
  EdgeCertificates.lean      (cover trees)             TransportInstances, WindowSources, EndpointFromNumerator,
  Endpoint.lean              (two-source / single)     EndpointFromSources

Everything is exact rational arithmetic (fractions).  The Bernstein certificates are `m + sum g_ij bterm_ij` with
`m` the minimal tensor-Bernstein coefficient (> 0) and `g_ij >= 0`; rows use the fixed degrees (2,3), admission guards
their own degrees (as Sil's generator did).  Validated by regenerating PR 86's own `Return/` (see --preset pr86).

Constants (all exact rationals `a/b`)
  --theta T          final boundary theta = 1 - c            --h H            row cutoff h  (`--h auto[:D]`: floor ceiling, D digits)
  --count-face B,L,CAP   countCB, countCL, countCap          --phys-face B,L,CAP    physicalB, physicalLambda, physicalCap
  --numerator-cap S  numeratorCap (physical slot cap s_P)    --dm D           fixed switch d_m         --reserve R
  --m-minus M --s-minus S --natural-k K                      (window floors and natural cost: PR 86 = 377/1000, 3/100, 9/2)
  --count-src B,L,C  --phys-src B,L,C   the faces of the two GlobalSource hypotheses of the endpoint
                     (default: B,L of the return faces and chain cap C = 1/10; must dominate the return faces)
  --preset pr86      all of the above at PR 86's values (the default of every unset constant)
Layout
  --pkg P            module prefix (e.g. Submissions.arvi_density) of the generated `P.Return.*`
  --returnd-pkg P    prefix of the `ReturnD` fork (default: --pkg)         --ns N      Lean namespace prefix (QRH.ArviDensity)
  --cover auto|pr86|FILE.json   cover trees of the four conductor edges: `auto` = greedy dyadic bisection (candidates
                     old, C, capP in this order), `pr86` = PR 86's trees (return86_tpl/cover_pr86.json), FILE = a spec made by
                     --extract-cover; with --repair, a spec leaf that fails is re-covered greedily
  --endpoint two-source|single   two-source: dirichlet_of_sources (count source, physical source); single: PR 86's text
  --box arvi|pr83    transport box assumed by the side-condition check (arvi = ReturnD fork: ell<175/1000, y>440/1000,
                     small_saving 6/100)
  --no-notice        do not append our modification notice; with --preset pr86 --pkg Submissions.density_split_fine_chain
                     --returnd-pkg Submissions.sil_density_split_20261026 --ns QRH.SilDensitySplit --endpoint single --cover pr86
                     --box pr83 the output is byte-identical to PR 86's `Return/` (validate_return86.py)
  --emit-cover FILE  write the cover spec that was used;   --clean   delete stale .lean files of OUTDIR
Other modes
  --receipts         only print the side-condition margins of the constants (no files)
  --find-theta LO HI [--h auto[:D]] least theta (multiples of 1e-7 in [LO,HI], bisection) whose four edges are covered
  --extract-cover EdgeCertificates.lean Windows.lean OUT.json   cover spec of an existing Lean return in this layout

Example (the baseline of Submissions.arvi_density, PR 86's constants, both sources = PR 86's final face):
  python3 gen_return86.py /home/user/lean-env/qrh/Submissions/arvi_density/Return --preset pr86 \\
      --pkg Submissions.arvi_density --ns QRH.ArviDensity --cover pr86
"""
import argparse, json, math, os, re, sys
from fractions import Fraction as Fr
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
TPL = os.path.join(HERE, 'return86_tpl')
ETA = Fr(1, 10 ** 7)                      # the `1/10000000` of Formulas.lean
LEAN_BRANCH = {'old': '.old', 'C': '.C', 'capP': '.capP'}
CANDS = ['old', 'C', 'capP']              # greedy order = PR 86's CountBranch order
ROW_DEGS = (2, 3)                         # Sil's rows are all certified in degrees (2,3)
EDGES = ['oldSmall', 'oldSwitch', 'newSwitch', 'newTop']
MAX_ROWS_PER_FILE = 16                    # an edge with more rows is spread over Edge_<edge>_1, _2, ...
ROOT_BOX = ((Fr(0), Fr(3, 4)), (Fr(0), Fr(1, 2)))

# --------------------------------------------------------------------------------------------------
# header blocks (PR 86's files; kept verbatim as inherited notices)
SIL_GEN = ("/- Copyright (c) 2026 Sil. Apache-2.0.\n"
           "Generated by work/formalization-0873995/return-gen/gen_return_lean.py from\n"
           "hybrid-0873995-certificate.json (sha256 15e19d29cb3e6932...). Do not edit by hand.\n"
           "Layout follows PR76 FinalReturn/Rows (Repeated marks, Apache-2.0) and Collet's final stage\n"
           "(Record1252270103Finite, Apache-2.0); Bernstein checker from PR69 Record12518109.Bernstein. -/")
PR86_ROWS = ("/- Modified for the 46-step density-split chain (27 Oct 2026): coefficients and reserves regenerated by "
             "q83/lean/tools/recoef.py for the retuned constants of Return/Constants.lean; boxes, degrees and proofs are Sil's. -/")
CONST_HDR = [
    "/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).\n"
    "Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/",
    "/- Modified by Sil (2026-10-26): constants of the return at theta = 174799/200000 (h = 8053/10000,\n"
    "count face C = (4967/5000, 49/20, 9999/100000), physical face P = (9933999/10^7, 2451/1000, 31/500),\n"
    "physical slot cap 3/50, fixed switch dm = 19/25, natural tail s_minus = 3/100, m_minus = 19/50,\n"
    "certificate reserve 1/10^8); only the four conductor edges used by the Lean return are kept. -/",
    "/- Modified for the 46-step density-split chain (27 Oct 2026): constants of the return at theta = 4369779/5000000 "
    "(h = 8051/10000, count face C = (9888151/10000000, 4683001/2000000, 9999/100000), physical face P = "
    "(9888151/10000000, 4683001/2000000, 31/500), m_minus = 377/1000); every other constant, the windows and the "
    "layout are Sil's. -/"]
EDGECERT_PR86 = ("/- Modified for the 46-step density-split chain (27 Oct 2026): the cover node of row023 (new top edge, "
                 "delta in [225/512, 453/1024]) is split at delta = 1809/4096 into row023a and row023b "
                 "(q83/lean/tools/split_row.py); everything else is Sil's. -/")
ENDPOINT_HDR = [
    "/- Copyright (c) 2026 Sil. Apache-2.0.\n"
    "The return at theta = 174799/200000 from the global source G(4967/5000, 49/20, 1/10).\n"
    "Adapted from PR76 `FinalReturn/EndpointFromGlobalSources.lean` and `Graph/Endpoint.lean`\n"
    "(Repeated marks, Apache-2.0; forks of Collet's Record1252270103Graph, Apache-2.0).\n"
    "The count face C = (4967/5000, 49/20, 9999/100000) and the physical face\n"
    "P = (9933999/10^7, 2451/1000, 31/500) are literal subfaces of G. The natural cap\n"
    "`2β − 1 ≤ naturalK/6 = 3/4` is the baseline's `β ≤ 7/8` (PR76 `Graph/NaturalCap.lean`).\n"
    "The source G is a hypothesis here, under `51/100 ≤ β`; the complementary case is trivial. -/",
    "/- Modified for the 46-step density-split chain (27 Oct 2026): source face G(9888151/10000000, 4683001/2000000, 1/10), "
    "count face C = (9888151/10000000, 4683001/2000000, 9999/100000), physical face P = (9888151/10000000, "
    "4683001/2000000, 31/500), theta = 4369779/5000000 = 0.8739558. Proofs unchanged. -/"]


# --------------------------------------------------------------------------------------------------
# rational / Lean literals
def q(v):
    v = Fr(v)
    return f'({v.numerator}/{v.denominator}:ℝ)' if v.denominator != 1 else f'({v.numerator}:ℝ)'


def qs(v):
    v = Fr(v)
    return f'{v.numerator}/{v.denominator}' if v.denominator != 1 else f'{v.numerator}'


def fr(s):
    return Fr(s.strip())


def frs(s, n):
    parts = [fr(t) for t in s.split(',')]
    assert len(parts) == n, f'expected {n} comma-separated rationals: {s}'
    return tuple(parts)


# --------------------------------------------------------------------------------------------------
# bivariate polynomials in (δ, p): dict {(i,j): Fraction}
def const(a):
    return {(0, 0): Fr(a)}


DEL = {(1, 0): Fr(1)}
PP = {(0, 1): Fr(1)}


def add(*ps):
    out = {}
    for p_ in ps:
        for k, v in p_.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def smul(s, a):
    return {k: Fr(s) * v for k, v in a.items() if Fr(s) * v != 0}


def sub(a, b):
    return add(a, smul(-1, b))


def mul(a, b):
    out = {}
    for (i, j), u in a.items():
        for (k, l), v in b.items():
            out[(i + k, j + l)] = out.get((i + k, j + l), 0) + u * v
    return {k: v for k, v in out.items() if v != 0}


def dpoly(a):
    """derivative in p"""
    return {(i, j - 1): j * v for (i, j), v in a.items() if j > 0}


def degs(a):
    if not a:
        return (0, 0)
    return (max(i for i, _ in a), max(j for _, j in a))


# --------------------------------------------------------------------------------------------------
# Bernstein certificates  a = m + sum g_ij (d-d0)^i (d1-d)^(n-i) (p-p0)^j (p1-p)^(m-j)
def bern_coeffs(a, box, dg=None):
    (d0, d1), (p0, p1) = box
    n, m = dg if dg is not None else degs(a)
    ad = degs(a)
    assert ad[0] <= n and ad[1] <= m, f'polynomial of degrees {ad} does not fit {(n, m)}'
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


def bmin(a, box, dg=None):
    _, _, beta = bern_coeffs(a, box, dg)
    return min(min(r) for r in beta)


def certificate(a, box, dg=None):
    """(n1, n2, m, g) with a = m + sum g_ij bterm_ij on box, m = min Bernstein coefficient > 0, g >= 0."""
    (d0, d1), (p0, p1) = box
    n, m, beta = bern_coeffs(a, box, dg)
    mn = min(min(r) for r in beta)
    if mn <= 0:
        raise ValueError('non-positive Bernstein coefficient')
    sc = (d1 - d0) ** n * (p1 - p0) ** m
    g = [[(beta[i][j] - mn) * comb(n, i) * comb(m, j) / sc for j in range(m + 1)] for i in range(n + 1)]
    # exact identity self-check on an (n+1) x (m+1) grid of distinct nodes: a polynomial of degrees <= (n, m)
    # that vanishes there is zero, so this proves the identity (Lean re-checks it anyway)
    for u in (Fr(i, n + 2) for i in range(n + 1)):
        for v in (Fr(j, m + 2) for j in range(m + 1)):
            dd = d0 + (d1 - d0) * u
            pp = p0 + (p1 - p0) * v
            lhs = sum(c * dd ** i * pp ** j for (i, j), c in a.items())
            rhs = mn + sum(g[i][j] * (dd - d0) ** i * (d1 - dd) ** (n - i) * (pp - p0) ** j * (p1 - pp) ** (m - j)
                           for i in range(n + 1) for j in range(m + 1))
            assert lhs == rhs, 'certificate identity'
    return n, m, mn, g


def lean_matrix(g):
    return '![' + ',\n'.join('![' + ', '.join(q(v) for v in r) + ']' for r in g) + ']'


# --------------------------------------------------------------------------------------------------
# the return constants (Return/Constants.lean) and the formulas of Return/Formulas.lean
class Params:
    FIELDS = ('theta', 'h', 'cB', 'cL', 'cCap', 'pB', 'pL', 'pCap', 'numCap', 'dm', 'reserve', 'mMinus', 'sMinus', 'K',
              'srcC', 'srcP')

    def __init__(self, **kw):
        for k in self.FIELDS:
            setattr(self, k, kw.get(k))

    @staticmethod
    def pr86():
        return Params(theta=Fr(4369779, 5000000), h=Fr(8051, 10000),
                      cB=Fr(9888151, 10 ** 7), cL=Fr(4683001, 2 * 10 ** 6), cCap=Fr(9999, 100000),
                      pB=Fr(9888151, 10 ** 7), pL=Fr(4683001, 2 * 10 ** 6), pCap=Fr(31, 500),
                      numCap=Fr(3, 50), dm=Fr(19, 25), reserve=Fr(1, 10 ** 8), mMinus=Fr(377, 1000),
                      sMinus=Fr(3, 100), K=Fr(9, 2), srcC=None, srcP=None)

    def finish(self):
        """derived constants and default source faces"""
        self.c = 1 - self.theta
        self.ell = 4 * self.c - Fr(1, 3)
        self.x = 1 + self.ell - self.h
        self.y = self.h - 2 * self.ell
        self.kappa = 1 - 2 * self.c
        self.dp = self.h + Fr(1, 10 ** 10)
        self.d0 = Fr(1, 200)
        self.naturalM = (1 - self.K * self.sMinus) / 2
        if self.srcC is None:
            self.srcC = (self.cB, self.cL, Fr(1, 10))
        if self.srcP is None:
            self.srcP = (self.pB, self.pL, Fr(1, 10))
        return self

    # capacities of Constants.lean
    def old_capacity(self, d):
        return min(d, 2 * self.y - d) / (6 * self.kappa)

    def new_capacity(self, d):
        return min(self.numCap * d, (2 * self.y - (2 - self.pB) * d) / self.pL)

    def edges(self):
        return [('oldSmall', self.d0, self.old_capacity(self.d0)), ('oldSwitch', self.dm, self.old_capacity(self.dm)),
                ('newSwitch', self.dm, self.new_capacity(self.dm)), ('newTop', self.dp, self.new_capacity(self.dp))]

    def face(self, cand):
        return (self.cB, self.cL, self.cCap) if cand == 'C' else (self.pB, self.pL, self.pCap)


def branch_polys(P, cand):
    """polynomials of Formulas.lean for the branch `cand` ('old' | 'C' | 'capP'), as dicts in (δ, p)"""
    V = sub(const(Fr(5, 6)), DEL)
    if cand == 'old':
        k3 = 3 * P.kappa
        oldD = sub(sub(const(3), PP), smul(Fr(2) / k3, PP))
        oldC = mul(smul(2, sub(const(1), PP)), sub(const(1), smul(1 / k3, PP)))
        J = add(mul(V, oldD), mul(DEL, oldC))
        N = add(mul(sub(const(1), DEL), J), smul(Fr(1, 2), mul(mul(DEL, oldC), V)))
        return dict(J=J, N=N)
    B, L, cap = P.face(cand)
    capped = cand == 'capP'
    Zc = cap - ETA
    if capped:
        D = sub(const(3), PP)
        A = const(2)
        C0 = sub(const(1), smul(2 * Zc, PP))
        Z = smul(2 * Zc, PP)
        dD, dA, dC = Fr(-1), Fr(0), -2 * Zc
    else:
        D = sub(sub(const(3), PP), smul(4 / L, PP))
        A = sub(const(2), smul(4 / L, PP))
        C0 = sub(const(1), smul(2 * B / L, PP))
        Z = smul(2 * B / L, PP)
        dD, dA, dC = -1 - 4 / L, -4 / L, -2 * B / L
    U = mul(sub(const(1), PP), C0)
    J = add(mul(V, D), mul(mul(DEL, sub(const(1), PP)), A))
    N = add(mul(sub(const(1), DEL), J), mul(mul(V, DEL), U))
    T = add(J, mul(DEL, U))
    RN = add(mul(A, T), mul(sub(Z, PP), J))
    MN = sub(mul(D, T), RN)
    DJ = mul(D, J)
    dU = add(smul(-1, C0), smul(dC, sub(const(1), PP)))                      # derivativeU
    dJ = add(smul(dD, V), mul(DEL, add(smul(-1, A), smul(dA, sub(const(1), PP)))))   # derivativeJ
    return dict(D=D, A=A, C0=C0, Z=Z, U=U, J=J, N=N, T=T, RN=RN, MN=MN, DJ=DJ, dU=dU, dJ=dJ, Zc=Zc, capped=capped, B=B, L=L, cap=cap)


def guards(P, cand):
    """the 15 polynomials of `admissionGuard` (Formulas.lean) for the branch cand, in Lean's order"""
    br = branch_polys(P, cand)
    B, L, cap, Zc, capped = br['B'], br['L'], br['cap'], br['Zc'], br['capped']
    nm = P.naturalM
    if capped:
        lowerM = P.mMinus + ETA
        upperM = min(min(Fr(11, 25) - ETA, nm - ETA), (B - L * Zc) / 2 - ETA)
    else:
        lowerM = max(P.mMinus + ETA, (B - L * (cap - ETA)) / 2 + ETA)
        upperM = min(min(Fr(11, 25) - ETA, nm - ETA), (B - L * (P.sMinus + ETA)) / 2 - ETA)
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (br[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    tail = sub(const(1), add(smul(2 * nm, DEL), smul(2 * P.sMinus, mul(DEL, PP))))
    return [D, A, C0, J, sub(T, J), sub(smul(Fr(12499, 10000), J), T),
            sub(RN, smul(Fr(23, 37), DJ)), sub(DJ, RN),
            sub(MN, smul(lowerM, DJ)), sub(smul(upperM, DJ), MN),
            sub(N, mul(tail, J)),
            sub(mul(U, dJ), mul(dU, J)),
            const(Fr(11, 25) - nm - ETA),
            const(B - 2 * nm - L * (P.sMinus + ETA) - 2 * ETA),
            smul(Zc - P.sMinus - ETA, DJ) if capped else const(1)]


def row_poly(P, cand, d, C):
    """rowMargin e b δ p = J (θ - reserve - Ebase) - 3/4 d N"""
    br = branch_polys(P, cand)
    Eb = add(const(Fr(1, 2) + 13 * P.h / 75 - P.y / 2 - P.ell / 2 - Fr(9, 100) * d), smul(Fr(1, 2), DEL),
             smul(P.ell - C / 2, mul(DEL, PP)))
    return sub(mul(br['J'], sub(const(P.theta - P.reserve), Eb)), smul(Fr(3, 4) * d, br['N']))


# --------------------------------------------------------------------------------------------------
# side conditions (everything the Lean modules prove by norm_num/linarith from the constants)
BOXES = {   # (name, lo, hi) of BoundsN
    'arvi': dict(theta=(Fr(873, 1000), Fr(7, 8)), h=(Fr(793, 1000), Fr(806, 1000)), y=(Fr(440, 1000), Fr(467, 1000)),
                 ell=(Fr(1672, 10000), Fr(175, 1000)), ss=Fr(6, 100)),
    'pr83': dict(theta=(Fr(873, 1000), Fr(7, 8)), h=(Fr(793, 1000), Fr(806, 1000)), y=(Fr(458, 1000), Fr(467, 1000)),
                 ell=(Fr(1672, 10000), Fr(171, 1000)), ss=Fr(7, 100)),
}


def side_conditions(P, box='arvi'):
    """name -> margin; strict conditions need margin > 0, `ok_nonneg` ones margin >= 0"""
    bx = BOXES[box]
    th, h, ell, x, y, kap, dp = P.theta, P.h, P.ell, P.x, P.y, P.kappa, P.dp
    signal = x / 2 + (y - x) / 12
    r = {
        # Geometry.Parameters (Return/Geometry.lean)
        'ell_pos': ell, 'sixth_lt_ell': ell - Fr(1, 6), 'ell_lt_fifth': Fr(1, 5) - ell, 'ell_lt_x': x - ell,
        'x_lt_y': y - x, 'y_lt_half': Fr(1, 2) - y, 'dilation_gap': 2 * x - y - ell,
        'tuple_margin_neg': -(1 + 3 * ell - 2 * (x + y)),
        # BoundsN (ReturnD/TransportGeometry.lean)
        'box.theta_lo': th - bx['theta'][0], 'box.theta_hi': bx['theta'][1] - th,
        'box.h_lo': h - bx['h'][0], 'box.h_hi': bx['h'][1] - h,
        'box.y_lo': y - bx['y'][0], 'box.y_hi': bx['y'][1] - y,
        'box.ell_lo': ell - bx['ell'][0], 'box.ell_hi': bx['ell'][1] - ell,
        'box.small_saving': y / 2 - h * (Fr(17, 50) - Fr(1, 6)) - Fr(1, 50) - bx['ss'],
        'box.floor_margin (>=0)': signal - Fr(1, 200) - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y
                                                         + Fr(67, 100) * dp - Fr(3, 20) * ell),
        # PhysicalSchedule (ReturnD/Schedule.lean, Return/FinalSchedule.lean)
        'sched.cap_lt_fifth': Fr(1, 5) - P.numCap, 'sched.cap_nonneg (>=0)': P.numCap,
        'sched.dMinus_lower': P.dm - Fr(3, 4), 'sched.dMinus_before_top (>=0)': dp - P.dm,
        'sched.y_before_switch': P.dm - y, 'sched.switch_before_twoy': 2 * y - P.dm,
        'sched.lambda_low (>=0)': P.pL - 2, 'sched.lambda_high (>=0)': Fr(9, 2) - P.pL,
        'sched.B_pos': P.pB, 'sched.B_le_one (>=0)': 1 - P.pB,
        'sched.small_plain_global (>=0)': 1 - P.pB / 2 - (Fr(9, 2) - P.pL / 2) * P.numCap,
        'sched.prime_supply': ell / dp - Fr(1, 5), 'sched.incumbent (>=0)': P.K / 6 - kap,
        # Formulas / CountWidth / CountDecode / FinalRows / EndpointFromSources
        'natural_lo (>=0)': P.naturalM - Fr(2, 5), 'natural_hi': Fr(1, 2) - P.naturalM,
        'natural_kappa_lo (>=0)': P.K / 6 - Fr(7, 10), 'natural_kappa_hi (>=0)': Fr(3, 4) - P.K / 6,
        'natural_cap_return: K/6>=3/4 (>=0)': P.K / 6 - Fr(3, 4),      # Endpoint.natural_cap_return (beta <= 7/8)
        'C.cap<=7/37+eta (>=0)': Fr(7, 37) + ETA - P.cCap, 'C.cap>2eta': P.cCap - 2 * ETA,
        'P.cap<=7/37+eta (>=0)': Fr(7, 37) + ETA - P.pCap, 'P.cap>2eta': P.pCap - 2 * ETA,
        'C.lambda>1': P.cL - 1, 'P.lambda>1': P.pL - 1, 'mMinus (>=0)': P.mMinus,
        'reserve>=rowFee (>=0)': P.reserve - Fr(1, 10 ** 9), 'numeratorCap<=physicalCap (>=0)': P.pCap - P.numCap,
        'physicalB>=1/2 (>=0)': P.pB - Fr(1, 2), 'theta>=51/100 (>=0)': th - Fr(51, 100), 'theta<=7/8 (>=0)': Fr(7, 8) - th,
    }
    for nm_, (sB, sL, sC), (rB, rL, rC) in (('count', P.srcC, (P.cB, P.cL, P.cCap)), ('phys', P.srcP, (P.pB, P.pL, P.pCap))):
        r[f'{nm_}_src.B>=ret.B (>=0)'] = sB - rB
        r[f'{nm_}_src.lambda<=ret.lambda (>=0)'] = rL - sL
        r[f'{nm_}_src.cap>=ret.cap (>=0)'] = sC - rC
    return r


def failing(rec):
    return {k: v for k, v in rec.items() if (v < 0 if '(>=0)' in k else v <= 0)}


# --------------------------------------------------------------------------------------------------
# cover trees
class Leaf:
    def __init__(self, box, cand, name=None, parts=None, window=None):
        self.box, self.cand, self.name, self.parts, self.window = box, cand, name, parts, window


class Split:
    def __init__(self, box, axis, mid, lo, hi):
        self.box, self.axis, self.mid, self.lo, self.hi = box, axis, mid, lo, hi


def sub_boxes(box, axis, mid):
    (d0, d1), (p0, p1) = box
    if axis == 'd':
        return ((d0, mid), (p0, p1)), ((mid, d1), (p0, p1))
    return ((d0, d1), (p0, mid)), ((d0, d1), (mid, p1))


def window_of(box):
    (d0, d1), (p0, _) = box
    return ((d0, d1), (p0, Fr(1, 2)))


class Ctx:
    """exact certification oracle for one set of constants"""

    def __init__(self, P):
        self.P = P
        self.rowp = {}
        self.guardp = {}
        self.win_cache = {}
        self.edges = {nm: (d, C) for nm, d, C in P.edges()}

    def row(self, edge, cand):
        k = (edge, cand)
        if k not in self.rowp:
            d, C = self.edges[edge]
            self.rowp[k] = row_poly(self.P, cand, d, C)
        return self.rowp[k]

    def row_ok(self, edge, cand, box):
        return bmin(self.row(edge, cand), box, ROW_DEGS) > 0

    def window_ok(self, cand, win):
        k = (cand, win)
        if k not in self.win_cache:
            if cand not in self.guardp:
                self.guardp[cand] = guards(self.P, cand)
            self.win_cache[k] = all(bmin(g, win) > 0 for g in self.guardp[cand])
        return self.win_cache[k]

    def leaf_ok(self, edge, cand, box, window=None):
        if not self.row_ok(edge, cand, box):
            return False
        return cand == 'old' or self.window_ok(cand, window or window_of(box))


def cover_auto(ctx, edge, box=ROOT_BOX, depth=0, maxdepth=34):
    """greedy dyadic bisection: certify the box by the first candidate that works, else split the longer side"""
    for cand in CANDS:
        if ctx.leaf_ok(edge, cand, box):
            return Leaf(box, cand)
    if depth >= maxdepth:
        raise ValueError(f'cover of edge {edge} failed at depth {depth}, box {[(float(a), float(b)) for a, b in box]}')
    (d0, d1), (p0, p1) = box
    if (d1 - d0) / Fr(3, 4) >= (p1 - p0) / Fr(1, 2):
        axis, mid = 'd', (d0 + d1) / 2
    else:
        axis, mid = 'p', (p0 + p1) / 2
    bl, bh = sub_boxes(box, axis, mid)
    return Split(box, axis, mid, cover_auto(ctx, edge, bl, depth + 1, maxdepth), cover_auto(ctx, edge, bh, depth + 1, maxdepth))


def cover_from_spec(ctx, edge, spec, box=ROOT_BOX, repair=False):
    if 'axis' in spec:
        mid = Fr(spec['mid'])
        bl, bh = sub_boxes(box, spec['axis'], mid)
        return Split(box, spec['axis'], mid, cover_from_spec(ctx, edge, spec['lo'], bl, repair),
                     cover_from_spec(ctx, edge, spec['hi'], bh, repair))
    cand = spec['cand']
    win = None
    if 'window' in spec:
        win = tuple(tuple(Fr(v) for v in pr) for pr in spec['window'])
    parts = None
    boxes = [box]
    if 'parts' in spec:
        pa = spec['parts']
        parts = (pa['axis'], Fr(pa['mid']), tuple(pa['names']))
        boxes = list(sub_boxes(box, pa['axis'], parts[1]))
    if win is not None:
        (wd0, wd1), (wp0, wp1) = win
        (d0, d1), (p0, p1) = box
        assert wd0 <= d0 and d1 <= wd1 and wp0 <= p0 and p1 <= wp1 == Fr(1, 2), f'window does not contain the leaf {spec.get("name")}'
    ok = all(ctx.row_ok(edge, cand, b) for b in boxes) and (cand == 'old' or ctx.window_ok(cand, win or window_of(box)))
    if ok:
        return Leaf(box, cand, spec.get('name'), parts, win)
    if not repair:
        raise ValueError(f'spec leaf {spec.get("name")} of edge {edge} ({cand}, box {[(str(a), str(b)) for a, b in box]}) is not certified')
    return cover_auto(ctx, edge, box)


def leaves_of(t):
    return [t] if isinstance(t, Leaf) else leaves_of(t.lo) + leaves_of(t.hi)


def spec_of(t):
    """JSON-able spec of a tree"""
    if isinstance(t, Split):
        return dict(axis=t.axis, mid=str(t.mid), lo=spec_of(t.lo), hi=spec_of(t.hi))
    s = dict(cand=t.cand)
    if t.name:
        s['name'] = t.name
    if t.parts:
        s['parts'] = dict(axis=t.parts[0], mid=str(t.parts[1]), names=list(t.parts[2]))
    if t.window:
        s['window'] = [[str(a), str(b)] for a, b in t.window]
    return s


# --------------------------------------------------------------------------------------------------
# extraction of a cover spec from a Lean return (EdgeCertificates.lean + Windows.lean) in this layout
def extract_cover(edge_path, win_path):
    def pq(s):
        s = s.strip()
        s = s[:-2] if s.endswith(':ℝ') else s
        return Fr(s.strip('()'))

    txt = open(edge_path, encoding='utf-8').read()
    rows = {}
    for m in re.finditer(r'theorem envelope_(row\w+) \{δ p:ℝ\} \(hδ:δ∈Set\.Icc \(([^)]*)\) \(([^)]*)\)\) \(hp:p∈Set\.Icc \(([^)]*)\) \(([^)]*)\)\) : Ebase \(edgeD \.(\w+)\)', txt):
        name, d0, d1, p0, p1, edge = m.groups()
        end = txt.find('\ntheorem ', m.end())
        body = txt[m.end():end]
        w = re.search(r'have ha : returnWindow(\d+)\.Available δ p := by\n  change δ∈Set\.Icc \(([^)]*)\) \(([^)]*)\) ∧ p∈Set\.Icc \(([^)]*)\) \(([^)]*)\)', body)
        br = re.search(r'countN \.(\w+) δ p/countJ', body)
        rows[name] = dict(edge=edge, box=((pq(d0), pq(d1)), (pq(p0), pq(p1))), cand=(br.group(1) if br else 'old'),
                          wbox=(((pq(w.group(2)), pq(w.group(3))), (pq(w.group(4)), pq(w.group(5)))) if w else None))
    nodes = {}
    for m in re.finditer(r'theorem cover_node_(\d+) \{δ p:ℝ\} \(hδ:δ∈Set\.Icc \(([^)]*)\) \(([^)]*)\)\)\n \(hp:p∈Set\.Icc \(([^)]*)\) \(([^)]*)\)\) : Ebase \(edgeD \.(\w+)\)', txt):
        k, d0, d1, p0, p1, edge = m.groups()
        end = txt.find('\ntheorem ', m.end())
        body = txt[m.end():end]
        box = ((pq(d0), pq(d1)), (pq(p0), pq(p1)))
        if 'rcases' in body:
            r = re.search(r'rcases le_total (δ|p) \(([^)]*)\) with hsplit \| hsplit\n · exact (cover_node_\d+|envelope_\w+)\b[^\n]*\n · exact (cover_node_\d+|envelope_\w+)\b', body)
            nodes[int(k)] = dict(edge=edge, box=box, kind='split', axis='d' if r.group(1) == 'δ' else 'p',
                                 mid=pq(r.group(2)), lo=r.group(3), hi=r.group(4))
        else:
            nodes[int(k)] = dict(edge=edge, box=box, kind='leaf', row=re.search(r'exact envelope_(\w+)', body).group(1))
    wins = {}
    for m in re.finditer(r'def returnWindow(\d+) : ReturnCountWindow where\n branch := \.(\w+)\n nonold := by decide\n deltaLo := \(([^)]*):ℝ\)\n deltaHi := \(([^)]*):ℝ\)\n pLo := \(([^)]*):ℝ\)',
                         open(win_path, encoding='utf-8').read()):
        wins[int(m.group(1))] = (m.group(2), Fr(m.group(3)), Fr(m.group(4)), Fr(m.group(5)))

    def build(k):
        n = nodes[k]
        if n['kind'] == 'leaf':
            return leaf_of_row(n['row'], n['box'])
        sub_ = {}
        for side in ('lo', 'hi'):
            ref = n[side]
            sub_[side] = build(int(ref.split('_')[-1])) if ref.startswith('cover_node_') else ('row', ref.replace('envelope_', ''))
        if isinstance(sub_['lo'], tuple):                        # a leaf split into two rows (PR 86: row023a/b)
            ra, rb = rows[sub_['lo'][1]], rows[sub_['hi'][1]]
            base = re.sub(r'[a-z]$', '', sub_['lo'][1])
            return dict(cand=ra['cand'], name=base, parts=dict(axis=n['axis'], mid=str(n['mid']),
                        names=[sub_['lo'][1], sub_['hi'][1]]), **({'window': wbox_spec(ra['wbox'])} if ra['wbox'] else {}))
        return dict(axis=n['axis'], mid=str(n['mid']), lo=sub_['lo'], hi=sub_['hi'])

    def wbox_spec(wb):
        return [[str(a), str(b)] for a, b in wb]

    def leaf_of_row(rname, box):
        r = rows[rname]
        s = dict(cand=r['cand'], name=rname)
        if r['wbox'] and r['wbox'] != window_of(box):
            s['window'] = wbox_spec(r['wbox'])
        return s

    roots = {}
    for k in sorted(nodes):
        roots[nodes[k]['edge']] = k                              # the root of an edge is its last node
    out = {e: build(roots[e]) for e in EDGES if e in roots}
    # cand names: Lean branch names -> generator names
    def fix(s):
        if 'axis' in s:
            fix(s['lo']); fix(s['hi'])
        else:
            s['cand'] = {'old': 'old', 'C': 'C', 'capP': 'capP'}[s['cand']]
    for s in out.values():
        fix(s)
    return dict(edges=out)


# --------------------------------------------------------------------------------------------------
# text emission
ROW_SIMP = ('rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,'
            'c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,'
            'sMinus,mMinus,reserve,numeratorCap')
GUARD_SIMP = ('admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,'
              'V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,'
              'c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,'
              'sMinus,mMinus,reserve,numeratorCap')
BSUM = 'Record12518109.Bernstein.bsum'
BTERM = 'Record12518109.Bernstein.bterm'


def emit_row(name, edge, cand, box, cert):
    n1, n2, m, g = cert
    (d0, d1), (p0, p1) = box
    br = LEAN_BRANCH[cand]
    return '\n'.join([
        f'def {name}_coefficients : Fin {n1 + 1} → Fin {n2 + 1} → ℝ := {lean_matrix(g)}',
        f'theorem {name}_identity (δ p : ℝ) : rowMargin .{edge} {br} δ p =',
        f' {BSUM} {n1} {n2} {q(m)} {name}_coefficients {q(d0)} {q(d1)} {q(p0)} {q(p1)} δ p := by',
        f' norm_num [{ROW_SIMP},edgeD_{edge},edgeC_{edge},{BSUM},{BTERM},{name}_coefficients,Fin.sum_univ_succ] <;> ring',
        f'theorem {name}_pos {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
        f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) : 0 < rowMargin .{edge} {br} δ p := by',
        f' rw [{name}_identity]',
        f' apply {BSUM}_pos (by norm_num) _ hδ hp',
        ' intro i j',
        f' fin_cases i <;> fin_cases j <;> norm_num [{name}_coefficients]'])


def emit_admission(widx, cand, win, certs):
    (d0, d1), (p0, p1) = win
    br = LEAN_BRANCH[cand]
    out = []
    for j, cert in enumerate(certs):
        n1, n2, m, g = cert
        nm = f'admission{widx:02d}_{j:02d}'
        out += [f'def {nm}_coefficients : Fin {n1 + 1} → Fin {n2 + 1} → ℝ := {lean_matrix(g)}',
                f'theorem {nm}_identity (δ p : ℝ) : admissionGuard {br} δ p {j} =',
                f' {BSUM} {n1} {n2} {q(m)} {nm}_coefficients {q(d0)} {q(d1)} {q(p0)} {q(p1)} δ p := by',
                f' norm_num [{GUARD_SIMP},{BSUM},{BTERM},{nm}_coefficients,Fin.sum_univ_succ] <;> ring',
                f'theorem {nm}_pos {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
                f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) : 0 < admissionGuard {br} δ p {j} := by',
                f' rw [{nm}_identity]',
                f' apply {BSUM}_pos (by norm_num) _ hδ hp',
                ' intro i j',
                f' fin_cases i <;> fin_cases j <;> norm_num [{nm}_coefficients]']
    out += [f'theorem admission{widx:02d}_all {{δ p : ℝ}} (hδ : δ ∈ Set.Icc {q(d0)} {q(d1)})',
            f' (hp : p ∈ Set.Icc {q(p0)} {q(p1)}) (j : Fin 15) : 0<admissionGuard {br} δ p j := by',
            ' fin_cases j']
    out += [f' · exact admission{widx:02d}_{j:02d}_pos hδ hp' for j in range(15)]
    return '\n'.join(out)


class Out:
    """collects the generated files; applies the notice policy"""

    def __init__(self, outdir, pkg, rpkg, ns, notice=True, today='2026-10-28'):
        self.outdir, self.pkg, self.rpkg, self.ns, self.notice, self.today = outdir, pkg, rpkg, ns, notice, today
        self.files = {}
        self.cover_note = "boxes, degrees and proofs are PR 86's"   # set by main() according to --cover

    def write(self, rel, header_blocks, body, own_notice):
        blocks = list(header_blocks)
        if self.notice:
            blocks.append(f'/- Modified by ArviFoxy ({self.today}): {own_notice} -/')
        self.files[rel] = '\n'.join(blocks) + '\n' + body

    def flush(self):
        """write the files; a file whose content is unchanged is not touched (keeps its .olean fresh for lake/build_roots)"""
        self.rewritten = 0
        for rel, text in self.files.items():
            path = os.path.join(self.outdir, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            self.rewritten += 1


def split_header(text):
    """(header, body): header = leading run of `/- ... -/` notice blocks (not `/--` doc comments)"""
    pos = 0
    blocks = []
    while text.startswith('/-', pos) and not text.startswith('/--', pos):
        end = text.index('-/', pos) + 2
        blocks.append(text[pos:end])
        pos = end + 1 if text[end:end + 1] == '\n' else end
    return blocks, text[pos:]


def retoken(s, out):
    s = s.replace('Submissions.density_split_fine_chain', out.pkg)
    s = s.replace('Submissions.sil_density_split_20261026', out.rpkg)
    s = s.replace('QRH.SilDensitySplit', out.ns)
    return s


STATIC = ['Formulas', 'Facts', 'Geometry', 'Conductor', 'CountAdmission', 'CountDecode', 'CountMonotonicity', 'CountWidth',
          'CountWindow', 'FinalEnvelopeBounds', 'FinalRows', 'FinalSchedule', 'FinalScheme', 'FinalWindows', 'SourceInlet',
          'TransportInstances', 'WindowSources', 'EndpointFromNumerator', 'EndpointFromSources']


def emit_static(out, P):
    for nm in STATIC:
        text = open(os.path.join(TPL, nm + '.lean'), encoding='utf-8').read()
        blocks, body = split_header(text)
        if nm == 'FinalRows':      # the only constant inside a copied module
            old = ' have h2 : reserve = (1/100000000:ℝ) := rfl\n'
            assert body.count(old) == 1
            lit = f'1/{P.reserve.denominator}' if P.reserve.numerator == 1 else q(P.reserve)
            body = body.replace(old, f' have h2 : reserve = ({lit}:ℝ) := rfl\n')
        body = retoken(body, out)
        out.write(f'{nm}.lean', blocks, body,
                  f'module prefix and namespaces renamed to {out.pkg}.Return and {out.ns}.Return'
                  + (f'; the reserve literal of `FinalRows.reserve_le` follows Constants.lean' if nm == 'FinalRows' else '')
                  + ' (no other change).')


def lit_or_frac(v):
    return f'1/{v.denominator}' if v.numerator == 1 else q(v)


def emit_constants(out, P):
    NS = out.ns + '.Return'
    th, ell = P.theta, P.ell
    L = ['import Mathlib.Data.Real.Basic', 'import Mathlib.Tactic.NormNum', 'set_option autoImplicit false',
         f'namespace {NS}', 'noncomputable section',
         f'def c : ℝ := {q(P.c)}', f'def h : ℝ := {q(P.h)}', f'def physicalB : ℝ := {q(P.pB)}',
         f'def physicalLambda : ℝ := {q(P.pL)}', f'def physicalCap : ℝ := {q(P.pCap)}',
         f'def countCB : ℝ := {q(P.cB)}', f'def countCL : ℝ := {q(P.cL)}', f'def countCap : ℝ := {q(P.cCap)}',
         f'def naturalK : ℝ := {q(P.K)}',
         '/-- The natural tail slope floor `s_minus` and the plain floor `m_minus` of the count windows. -/',
         f'def sMinus : ℝ := {q(P.sMinus)}', f'def mMinus : ℝ := {q(P.mMinus)}',
         'def theta : ℝ := 1-c', 'def ell : ℝ := 4*c-1/3', 'def x : ℝ := 1+ell-h', 'def y : ℝ := h-2*ell',
         'def kappa : ℝ := 1-2*c',
         f'/-- The physical marked cap actually used, `s_P = {qs(P.numCap)}`. -/',
         f'def numeratorCap : ℝ := {q(P.numCap)}',
         f'/-- The fixed switch `d_m = {qs(P.dm)}` (not the capacity join). -/',
         f'def dm : ℝ := {q(P.dm)}',
         'def dp : ℝ := h+1/10000000000', 'def d0 : ℝ := 1/200',
         'def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)',
         'def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)',
         '/-- The certificate reserve (`reserve` in hybrid-0873995-certificate.json). -/',
         f'def reserve : ℝ := {lit_or_frac(P.reserve)}',
         'inductive Edge | oldSmall | oldSwitch | newSwitch | newTop', ' deriving DecidableEq',
         'def edgeD : Edge → ℝ', ' | .oldSmall => d0', ' | .oldSwitch | .newSwitch => dm', ' | .newTop => dp',
         'def edgeC (e : Edge) : ℝ := match e with',
         ' | .oldSmall | .oldSwitch => oldCapacity (edgeD e)', ' | .newSwitch | .newTop => newCapacity (edgeD e)',
         f'theorem c_value : c = {q(P.c)} := rfl',
         f'theorem theta_value : theta = {q(th)} := by norm_num [theta,c]',
         f'theorem h_value : h = {q(P.h)} := rfl',
         f'theorem ell_value : ell = {q(ell)} := by norm_num [ell,c]',
         f'theorem x_value : x = {q(P.x)} := by norm_num [x,ell,c,h]',
         f'theorem y_value : y = {q(P.y)} := by norm_num [y,ell,c,h]',
         f'theorem kappa_value : kappa = {q(P.kappa)} := by norm_num [kappa,c]',
         f'theorem dp_value : dp = {q(P.dp)} := by norm_num [dp,h]']
    edges = {nm: (d, C) for nm, d, C in P.edges()}
    spec = {'oldSmall': ('d0', 'oldCapacity', 'd0', 'kappa'), 'oldSwitch': ('dm', 'oldCapacity', 'dm', 'kappa'),
            'newSwitch': ('dm', 'newCapacity', 'dm', None), 'newTop': ('dp', 'newCapacity', 'dp', None)}
    for nm in EDGES:
        d, C = edges[nm]
        dname, cap, dsimp, kap = spec[nm]
        base = {'oldSmall': 'd0', 'oldSwitch': 'dm', 'newSwitch': 'dm', 'newTop': 'dp,h'}[nm]
        L.append(f'theorem edgeD_{nm} : edgeD .{nm} = {q(d)} := by norm_num [edgeD,{base}]')
        simp = f'edgeC,edgeD,{cap},{dsimp},y,ell,c,h' + (',kappa' if kap else ',numeratorCap,physicalB,physicalLambda')
        L.append(f'theorem edgeC_{nm} : edgeC .{nm} = {q(C)} := by')
        L.append(f' norm_num [{simp}]')
    L += ['theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by', ' norm_num [theta,x,y,ell,h,c]',
          'end', f'end {NS}', '']
    out.write('Constants.lean', CONST_HDR, '\n'.join(L),
              f'regenerated by research/density/gen_return86.py for theta = {qs(th)}, h = {qs(P.h)}, count face C = '
              f'({qs(P.cB)}, {qs(P.cL)}, {qs(P.cCap)}), physical face P = ({qs(P.pB)}, {qs(P.pL)}, {qs(P.pCap)}), '
              f'numeratorCap = {qs(P.numCap)}, dm = {qs(P.dm)}, m_minus = {qs(P.mMinus)}, s_minus = {qs(P.sMinus)}, '
              f'reserve = {qs(P.reserve)}; every other constant, the windows and the layout are PR 86\'s.')


def edge_file_names(edge, n):
    if n <= MAX_ROWS_PER_FILE:
        return [f'Edge_{edge}']
    parts = -(-n // MAX_ROWS_PER_FILE)
    return [f'Edge_{edge}_{i + 1}' for i in range(parts)]


def chunks(items, parts):
    n = len(items)
    sizes = [n // parts + (1 if i >= parts - n % parts else 0) for i in range(parts)]
    out, k = [], 0
    for s in sizes:
        out.append(items[k:k + s])
        k += s
    return out


def emit_cover(out, P, ctx, trees):
    """rows, windows, admission files, Windows.lean, EdgeCertificates.lean"""
    NS = out.ns + '.Return'
    rows, windows = [], {}          # rows: dict(name, edge, cand, box, wkey); windows: key -> index
    counter = [0]
    used = set()
    for e in EDGES:                 # explicit names of the cover spec must stay unique
        for lf in leaves_of(trees[e]):
            for nm in ([lf.name] if lf.name else []) + (list(lf.parts[2]) if lf.parts else []):
                assert nm not in used, f'duplicate row name {nm}'
                used.add(nm)

    def walk(t, edge):
        if isinstance(t, Split):
            walk(t.lo, edge)
            walk(t.hi, edge)
            return
        if not t.name:
            while True:
                counter[0] += 1
                nm = f'row{counter[0]:03d}'
                if nm not in used:
                    break
            t.name = nm
            used.add(nm)
        t.wkey = None
        if t.cand != 'old':
            (d0, d1), (p0, _) = t.window or window_of(t.box)
            t.wkey = (t.cand, d0, d1, p0)
            if t.wkey not in windows:
                windows[t.wkey] = len(windows) + 1
        for nm, b in ([(t.name, t.box)] if not t.parts else
                      list(zip(t.parts[2], sub_boxes(t.box, t.parts[0], t.parts[1])))):
            rows.append(dict(name=nm, edge=edge, cand=t.cand, box=b, wkey=t.wkey))

    for e in EDGES:
        walk(trees[e], e)
    # ---- Rows/Edge_*.lean
    for e in EDGES:
        er = [r for r in rows if r['edge'] == e]
        names = edge_file_names(e, len(er))
        for fn, grp in zip(names, chunks(er, len(names))):
            body = [f'import {out.pkg}.Return.Formulas', 'set_option autoImplicit false',
                    'set_option linter.unnecessarySeqFocus false', f'namespace {NS}', 'noncomputable section']
            for r in grp:
                body.append(emit_row(r['name'], e, r['cand'], r['box'], certificate(ctx.row(e, r['cand']), r['box'], ROW_DEGS)))
            body += ['end', f'end {NS}', '']
            out.write(f'Rows/{fn}.lean', [SIL_GEN, PR86_ROWS], '\n'.join(body),
                      'Bernstein coefficients regenerated by research/density/gen_return86.py for the constants of '
                      f'Return/Constants.lean; {out.cover_note}.')
    # ---- Rows/AdmissionNN.lean and Windows.lean
    wl = sorted(windows.items(), key=lambda kv: kv[1])
    for (cand, d0, d1, p0), widx in wl:
        win = ((d0, d1), (p0, Fr(1, 2)))
        certs = [certificate(g, win) for g in guards(P, cand)]
        body = [f'import {out.pkg}.Return.Formulas', 'set_option autoImplicit false',
                'set_option linter.unnecessarySeqFocus false', f'namespace {NS}', 'noncomputable section',
                emit_admission(widx, cand, win, certs), 'end', f'end {NS}', '']
        out.write(f'Rows/Admission{widx:02d}.lean', [SIL_GEN, PR86_ROWS], '\n'.join(body),
                  'Bernstein coefficients regenerated by research/density/gen_return86.py for the constants of '
                  f'Return/Constants.lean; {out.cover_note}.')
    W = [f'import {out.pkg}.Return.CountWindow'] + [f'import {out.pkg}.Return.Rows.Admission{w:02d}' for _, w in wl]
    W += ['set_option autoImplicit false', 'set_option linter.unnecessarySeqFocus false', f'namespace {NS}', 'noncomputable section']
    for (cand, d0, d1, p0), widx in wl:
        W += [f'def returnWindow{widx:02d} : ReturnCountWindow where', f' branch := {LEAN_BRANCH[cand]}', ' nonold := by decide',
              f' deltaLo := {q(d0)}', f' deltaHi := {q(d1)}', f' pLo := {q(p0)}', ' deltaBounds := by norm_num',
              ' pBounds := by norm_num', f' certificate := admission{widx:02d}_all']
    W.append('def returnWindows : List ReturnCountWindow := [' + ','.join(f'returnWindow{w:02d}' for _, w in wl) + ']')
    W += ['end', f'end {NS}', '']
    out.write('Windows.lean', [SIL_GEN], '\n'.join(W),
              'windows and admission certificates regenerated by research/density/gen_return86.py for the constants of '
              'Return/Constants.lean.')
    # ---- EdgeCertificates.lean
    concl = lambda e: (f'Ebase (edgeD .{e}) (edgeC .{e}) δ p+3/4*edgeD .{e}*'
                       f'(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve')
    E = [f'import {out.pkg}.Return.FinalEnvelopeBounds']
    for e in EDGES:
        er = [r for r in rows if r['edge'] == e]
        for fn in edge_file_names(e, len(er)):
            E.append(f'import {out.pkg}.Return.Rows.{fn}')
    E += ['set_option autoImplicit false', 'set_option maxHeartbeats 200000', f'namespace {NS}.FinalEdges',
          'open QRH.Record1252270103Return', 'noncomputable section']
    for _, w in wl:
        E.append(f'theorem window{w:02d}_mem : returnWindow{w:02d}∈returnWindows := by simp [returnWindows]')
    for r in rows:
        (d0, d1), (p0, p1) = r['box']
        E += [f'theorem envelope_{r["name"]} {{δ p:ℝ}} (hδ:δ∈Set.Icc {q(d0)} {q(d1)}) '
              f'(hp:p∈Set.Icc {q(p0)} {q(p1)}) : {concl(r["edge"])} := by',
              ' have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]',
              ' have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]']
        br = LEAN_BRANCH[r['cand']]
        if r['cand'] == 'old':
            E += [' have hR := finiteEnvelope_le_old hd0 hp0',
                  f' exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) ({r["name"]}_pos hδ hp) hR']
        else:
            w = windows[r['wkey']]
            _, wd0, wd1, wp0 = r['wkey']
            E += [f' have ha : returnWindow{w:02d}.Available δ p := by',
                  f'  change δ∈Set.Icc {q(wd0)} {q(wd1)} ∧ p∈Set.Icc {q(wp0)} (1/2:ℝ)',
                  '  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]',
                  f' have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN {br} δ p/countJ {br} δ p := '
                  f'finiteEnvelope_le_window returnWindow{w:02d} window{w:02d}_mem ha',
                  f' exact exponent_lt_of_margin (countJ_pos {br} hd0 hp0) ({r["name"]}_pos hδ hp) hR']
    cnt = [0]

    def node(t, e):
        (d0, d1), (p0, p1) = t.box
        head = [f'theorem cover_node_{{k:03d}} {{{{δ p:ℝ}}}} (hδ:δ∈Set.Icc {q(d0)} {q(d1)})',
                f' (hp:p∈Set.Icc {q(p0)} {q(p1)}) : {concl(e)} := by']
        if isinstance(t, Leaf):
            if t.parts:
                axis, mid, (na, nb) = t.parts
                k = cnt[0]; cnt[0] += 1
                E.extend([head[0].format(k=k), head[1], f' rcases le_total {"δ" if axis == "d" else "p"} {q(mid)} with hsplit | hsplit'])
                if axis == 'd':
                    E.extend([f' · exact envelope_{na} ⟨hδ.1,hsplit⟩ hp', f' · exact envelope_{nb} ⟨hsplit,hδ.2⟩ hp'])
                else:
                    E.extend([f' · exact envelope_{na} hδ ⟨hp.1,hsplit⟩', f' · exact envelope_{nb} hδ ⟨hsplit,hp.2⟩'])
                return k
            k = cnt[0]; cnt[0] += 1
            E.extend([head[0].format(k=k), head[1],
                      f' exact envelope_{t.name} hδ hp'])
            return k
        a = node(t.lo, e)
        b = node(t.hi, e)
        k = cnt[0]; cnt[0] += 1
        E.extend([head[0].format(k=k), head[1]])
        if t.axis == 'd':
            E.extend([f' rcases le_total δ {q(t.mid)} with hsplit | hsplit',
                      f' · exact cover_node_{a:03d} ⟨hδ.1,hsplit⟩ hp', f' · exact cover_node_{b:03d} ⟨hsplit,hδ.2⟩ hp'])
        else:
            E.extend([f' rcases le_total p {q(t.mid)} with hsplit | hsplit',
                      f' · exact cover_node_{a:03d} hδ ⟨hp.1,hsplit⟩', f' · exact cover_node_{b:03d} hδ ⟨hsplit,hp.2⟩'])
        return k

    for e in EDGES:
        root = node(trees[e], e)
        E += [f'theorem edge_{e}_certificate {{δ p:ℝ}} (hδ:δ∈Set.Icc 0 (3/4))',
              f' (hp:p∈Set.Icc 0 (1/2)) : {concl(e)} := by',
              f' exact cover_node_{root:03d} (by simpa using hδ) (by simpa using hp)']
    E += ['theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))',
          ' (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*'
          '(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by',
          ' cases e with']
    E += [f' | {e} => exact edge_{e}_certificate hδ hp' for e in EDGES]
    E += ['end', f'end {NS}.FinalEdges', '']
    own = ('cover trees, rows and windows regenerated by research/density/gen_return86.py for the constants of '
           'Return/Constants.lean (statements and proofs as in PR 86; ' + out.cover_note + ').')
    out.write('EdgeCertificates.lean', [SIL_GEN, EDGECERT_PR86], '\n'.join(E), own)
    return rows, windows


# ---------------------------------------------------------------- endpoints
def emit_endpoint_single(out, P):
    """PR 86's Endpoint.lean (one source G for both faces), literals substituted (validation / compatibility)"""
    text = open(os.path.join(TPL, 'Endpoint_single.lean'), encoding='utf-8').read()
    blocks, body = split_header(text)
    sB, sL, sC = P.srcC
    assert (sB, sL, sC) == P.srcP, 'single-source endpoint needs one source face'
    body = body.replace('(9888151/10000000) (4683001/2000000) (1/10)', f'({qs(sB)}) ({qs(sL)}) ({qs(sC)})')
    body = body.replace('(4369779/5000000 : ℝ)', f'({qs(P.theta)} : ℝ)').replace('(4369779 / 5000000 : ℝ)', f'({P.theta.numerator} / {P.theta.denominator} : ℝ)')
    body = retoken(body, out)
    out.write('Endpoint.lean', blocks, body, 'single-source endpoint (PR 86\'s text, literals of the constants substituted).')


TWO_SOURCE = r'''import @PKG@.Return.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace @NS@.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

/-- The global face of the count source `G(@CB@, @CL@, @CC@)`. -/
abbrev countSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (@CB@) (@CL@) (@CC@)
/-- The global face of the physical source `G(@PB@, @PL@, @PC@)`. -/
abbrev physicalSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (@PB@) (@PL@) (@PC@)

theorem source_restricts_count : countSourceFace.Restricts countGlobal := by
 constructor <;> norm_num [countSourceFace,QRH.Record1252270103Source.globalFace,countGlobal,
  QRH.Record1252270103Return.globalFace,countCB,countCL,countCap]

theorem source_restricts_physical : physicalSourceFace.Restricts physicalGlobal := by
 constructor <;> norm_num [physicalSourceFace,QRH.Record1252270103Source.globalFace,physicalGlobal,
  QRH.Record1252270103Return.globalFace,physicalB,physicalLambda,physicalCap]

theorem uniform_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
 (hs : UniformUnitFaceSource strong) : UniformUnitFaceSource weak := by
 intro ε hε
 obtain ⟨mesh,hm,hsrc⟩ := hs ε hε
 exact ⟨mesh,hm,unit_source_restrict h hsrc⟩

lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [naturalK]
 linarith

theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤theta :=
 Final.beta_of_global_sources hC hP natural_cap_return

/-- **The two-source return.** The count face `C` and the physical face `P` of the return are supplied by two
(possibly different) global sources: `G(@CB@, @CL@, @CC@)` for the count windows and
`G(@PB@, @PL@, @PC@)` for the capped physical windows and the physical numerator. Each is
given under `51/100 ≤ β`; the complementary case is trivial. -/
theorem beta_le_theta_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (@CB@) (@CL@) (@CC@))
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (@PB@) (@PL@) (@PC@)) :
    HeckeZeroSupremum.beta ≤ (@TH@ : ℝ) := by
  rw [← theta_value]
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · exact beta_of_two_global_sources (uniform_restrict source_restricts_count (hC hbeta))
      (uniform_restrict source_restricts_physical (hP hbeta))
  · have ht : (51/100:ℝ) ≤ theta := by norm_num [theta,c]
    exact (not_le.mp hbeta).le.trans ht

/-- The Dirichlet transfer of `beta_le_theta_of_sources` (as PR76 `Graph.dirichlet_of_step`). -/
theorem dirichlet_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (@CB@) (@CL@) (@CC@))
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (@PB@) (@PL@) (@PC@))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (@THS@ : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num)
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      ((beta_le_theta_of_sources hC hP).trans_lt hs) hpole) χ s hs hpole

end
end @NS@.Return
'''


def emit_endpoint_two(out, P):
    (cB, cL, cC), (pB, pL, pC) = P.srcC, P.srcP
    body = TWO_SOURCE
    for k, v in {'@PKG@': out.pkg, '@NS@': out.ns, '@CB@': qs(cB), '@CL@': qs(cL), '@CC@': qs(cC),
                 '@PB@': qs(pB), '@PL@': qs(pL), '@PC@': qs(pC), '@TH@': qs(P.theta),
                 '@THS@': f'{P.theta.numerator} / {P.theta.denominator}'}.items():
        body = body.replace(k, v)
    out.write('Endpoint.lean', ENDPOINT_HDR, body,
              f'two-source endpoint after PR 85 `Return/Endpoint.lean`: the count face and the physical face are supplied by two '
              f'global sources G({qs(cB)}, {qs(cL)}, {qs(cC)}) and G({qs(pB)}, {qs(pL)}, {qs(pC)}) (theta = {qs(P.theta)}); proofs as in PR 86.')


# --------------------------------------------------------------------------------------------------
def stale_files(outdir, files):
    out = []
    for dp, _, fs in os.walk(outdir):
        for f in fs:
            rel = os.path.relpath(os.path.join(dp, f), outdir)
            if f.endswith('.lean') and rel not in files:
                out.append(rel)
    return sorted(out)


def hceiling(theta, digits=None, hu=Fr(806, 1000)):
    """largest h (rounded down to `digits` decimals) allowed by BoundsN.floor_margin (and h < hu)"""
    ell = Fr(11, 3) - 4 * theta

    def fm(h):
        x = 1 + ell - h; y = h - 2 * ell; dP = h + Fr(1, 10 ** 10)
        sig = x / 2 + (y - x) / 12
        return sig - Fr(1, 200) - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * dP - Fr(3, 20) * ell)
    f0, f1 = fm(Fr(0)), fm(Fr(1))
    hm = min(-f0 / (f1 - f0), hu - Fr(1, 10 ** 6))
    if digits:
        s = 10 ** digits
        return Fr(math.floor(hm * s), s)
    return hm


def certifiable(P, box='arvi'):
    P.finish()
    if failing(side_conditions(P, box)):
        return False
    ctx = Ctx(P)
    try:
        for e in EDGES:
            cover_auto(ctx, e)
    except ValueError:
        return False
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('outdir', nargs='?')
    ap.add_argument('--preset', choices=['pr86'])
    ap.add_argument('--theta'); ap.add_argument('--h')
    ap.add_argument('--count-face'); ap.add_argument('--phys-face')
    ap.add_argument('--numerator-cap'); ap.add_argument('--dm'); ap.add_argument('--reserve')
    ap.add_argument('--m-minus'); ap.add_argument('--s-minus'); ap.add_argument('--natural-k')
    ap.add_argument('--count-src'); ap.add_argument('--phys-src')
    ap.add_argument('--pkg', default='Submissions.arvi_density'); ap.add_argument('--returnd-pkg'); ap.add_argument('--ns', default='QRH.ArviDensity')
    ap.add_argument('--cover', default='auto'); ap.add_argument('--repair', action='store_true')
    ap.add_argument('--endpoint', choices=['two-source', 'single'], default='two-source')
    ap.add_argument('--box', choices=list(BOXES), default='arvi')
    ap.add_argument('--no-notice', action='store_true')
    ap.add_argument('--clean', action='store_true', help='delete .lean files of OUTDIR that this run did not generate')
    ap.add_argument('--emit-cover', metavar='FILE', help='also write the cover spec that was used (re-usable with --cover FILE)')
    ap.add_argument('--receipts', action='store_true')
    ap.add_argument('--find-theta', nargs=2, metavar=('LO', 'HI'))
    ap.add_argument('--extract-cover', nargs=3, metavar=('EDGECERT', 'WINDOWS', 'OUT'))
    a = ap.parse_args()

    if a.extract_cover:
        spec = extract_cover(a.extract_cover[0], a.extract_cover[1])
        json.dump(spec, open(a.extract_cover[2], 'w'), indent=1)
        print('cover spec written to', a.extract_cover[2])
        return

    P = Params.pr86() if a.preset == 'pr86' else Params()
    if a.theta: P.theta = fr(a.theta)
    if a.count_face: P.cB, P.cL, P.cCap = frs(a.count_face, 3)
    if a.phys_face: P.pB, P.pL, P.pCap = frs(a.phys_face, 3)
    if a.numerator_cap: P.numCap = fr(a.numerator_cap)
    if a.dm: P.dm = fr(a.dm)
    if a.reserve: P.reserve = fr(a.reserve)
    if a.m_minus: P.mMinus = fr(a.m_minus)
    if a.s_minus: P.sMinus = fr(a.s_minus)
    if a.natural_k: P.K = fr(a.natural_k)
    if a.count_src: P.srcC = frs(a.count_src, 3)
    if a.phys_src: P.srcP = frs(a.phys_src, 3)
    if a.h and not a.h.startswith('auto'):
        P.h = fr(a.h)
    missing = [k for k in ('theta', 'cB', 'pB', 'numCap', 'dm', 'reserve', 'mMinus', 'sMinus', 'K') if getattr(P, k) is None]
    assert not missing, f'missing constants {missing} (use --preset pr86 or pass them)'

    def set_h(P):
        if a.h and a.h.startswith('auto'):
            dig = int(a.h.split(':')[1]) if ':' in a.h else 4
            P.h = hceiling(P.theta, dig)
        assert P.h is not None, 'h missing'

    if a.find_theta:
        lo, hi = (int(Fr(v) * 10 ** 7) for v in a.find_theta)

        def ok(units):
            P2 = Params(**{k: getattr(P, k) for k in Params.FIELDS})
            P2.theta = Fr(units, 10 ** 7)
            set_h(P2)
            return certifiable(P2, a.box)
        assert ok(hi), 'hi is not certifiable'
        assert not ok(lo), 'lo is already certifiable'
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ok(mid):
                hi = mid
            else:
                lo = mid
        P2 = Params(**{k: getattr(P, k) for k in Params.FIELDS})
        P2.theta = Fr(hi, 10 ** 7)
        set_h(P2)
        print('least certifiable theta:', Fr(hi, 10 ** 7), f'= {hi}/10^7 = {hi / 1e7:.7f}', f'with h = {P2.h} (= {float(P2.h):.6f}; floor ceiling'
              f' {float(hceiling(P2.theta)):.7f})')
        print(f'regenerate with: --theta {Fr(hi, 10 ** 7)} --h {P2.h}')
        return

    set_h(P)
    P.finish()
    rec = side_conditions(P, a.box)
    if a.receipts:
        for k, v in sorted(rec.items(), key=lambda kv: float(kv[1])):
            print(f'{float(v):+.4e}  {k}')
        print('failing:', failing(rec))
        return
    bad = failing(rec)
    assert not bad, f'side conditions fail: { {k: float(v) for k, v in bad.items()} }'
    assert a.outdir, 'outdir missing'

    out = Out(a.outdir, a.pkg, a.returnd_pkg or a.pkg, a.ns, notice=not a.no_notice)
    if a.cover == 'auto':
        out.cover_note = ("the boxes are the greedy dyadic cover of gen_return86.py (candidates old, C, capP), "
                          "degrees and proofs are PR 86's")
    elif a.cover != 'pr86':
        out.cover_note = (f"the boxes follow the cover spec {os.path.basename(a.cover)}"
                          + (" (failing leaves re-covered greedily)" if a.repair else "") + ", degrees and proofs are PR 86's")
    ctx = Ctx(P)
    if a.cover == 'auto':
        trees = {e: cover_auto(ctx, e) for e in EDGES}
    else:
        path = os.path.join(TPL, 'cover_pr86.json') if a.cover == 'pr86' else a.cover
        spec = json.load(open(path))['edges']
        trees = {e: cover_from_spec(ctx, e, spec[e], ROOT_BOX, a.repair) for e in EDGES}
    emit_static(out, P)
    emit_constants(out, P)
    rows, windows = emit_cover(out, P, ctx, trees)
    if a.endpoint == 'single':
        emit_endpoint_single(out, P)
    else:
        emit_endpoint_two(out, P)
    out.flush()
    smallest = min(((k, v) for k, v in rec.items() if k.startswith('box.')), key=lambda kv: kv[1])
    stale = stale_files(a.outdir, out.files)
    if stale:
        if a.clean:
            for rel in stale:
                os.remove(os.path.join(a.outdir, rel))
        print(('removed' if a.clean else 'WARNING: stale .lean files in the output directory (not generated this time; use --clean)') + ':', stale)
    if a.emit_cover:
        json.dump(dict(edges={e: spec_of(trees[e]) for e in EDGES}), open(a.emit_cover, 'w'), indent=1)
        print('cover spec written to', a.emit_cover)
    print(f'{len(out.files)} modules emitted to {a.outdir} ({out.rewritten} (re)written): {len(rows)} rows, {len(windows)} windows; '
          f'theta = {qs(P.theta)} = {float(P.theta):.9f}, h = {qs(P.h)}; smallest transport-box margin '
          f'{smallest[0]} = {float(smallest[1]):.3e}')


if __name__ == '__main__':
    try:
        main()
    except (AssertionError, ValueError) as e:       # configuration errors: short message instead of a traceback
        sys.exit(f'gen_return86.py: error: {e}')
