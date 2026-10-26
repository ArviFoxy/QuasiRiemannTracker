"""Lean certificates of the mixed-step face family.

Mirrors (mathematically, exactly) `Family/{Formulas3,High3,Packed3,Validity3}.lean`:
  field3P, sg3N, weak3N, sec3B, cell3N (1D covers for `pos1I`) and highU3 (packed HIGH trees) for every
  piece, the data module, the packed-data extraction (Lean `#eval`), and the junction steps
  (fan face 46 -> piece 0 at y = 0, piece j at y = 1 - Dy -> piece j+1 at y = 0).

usage (always with QRH_K=9/2):
  python3 gen_family3.py data OUTDIR                 # Family/Gen/Data3.lean
  python3 gen_family3.py extract LAKE_DIR CK CS      # packed HIGH / sector data from Lean (#eval)
  QRH_CK=CK QRH_CS=CS python3 gen_family3.py pieces OUTDIR [j,...]
  python3 gen_family3.py junctions OUTDIR            # Family/Gen/Junctions3.lean

Variable caps (`Family/{Formulas3c,High3c,Packed3c,Validity3c}.lean`): QRH_CAPRAMP="J:c0,c1,..." gives
piece J the cap polynomial c0 + c1*y + ... (faces `node3c`, certificates `Certs3c`); `extract` then takes
an optional piece list and merges the new lines into the existing CK/CS files.
"""
import sys, os, json, time, math, subprocess
from fractions import Fraction as Fr
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
sys.path.insert(0, HERE)
import polyq as P
import ipoly as I
import cert_proto as CP
import gen_faceless_I as GI
import mixed_family as MF
import mixed_certs as MC
import lean_certs as LC

assert os.environ.get('QRH_K') == '9/2', "export QRH_K=9/2"
SIG = [float(x) for x in os.environ.get(
    'QRH_SIG3', '0.016,0.0215,0.027,0.0325,0.038,0.0435,0.049,0.054,0.0595').split(',')]
FLOW = os.environ.get('QRH_FLOW3', os.path.join(HERE, 'flow_k92.json'))
FAN = os.environ.get('QRH_FAN3', os.path.join(HERE, 'fan_k92_cap0.075.json'))
DEN = Fr(1, 2**15)
E, R, F = Fr(1, 10**17), Fr(1, 10**12), Fr(1, 10**10)
CAP = Fr(3, 40)
PKG = 'Submissions.arvi_mixed_step'
NS = 'QRH.MixedStep.Family'
OPENS = ("open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite "
         "QRH.RepeatedMarks.Faceless")
CK = os.environ.get('QRH_CK')
# pieces with a variable cap: {piece: cap polynomial}
CAPRAMP = {int(it.split(':')[0]): [Fr(c) for c in it.split(':')[1].split(',')]
           for it in os.environ.get('QRH_CAPRAMP', '7:3/40,1/100').split(';') if it.strip()}
CS = os.environ.get('QRH_CS')


def build():
    rows = json.load(open(FLOW))
    fan = json.load(open(FAN))
    last = fan[-1]
    s0 = Fr(16, 1000)
    assert abs(float(s0) - SIG[0]) < 1e-12
    E0 = Fr(last['B']) - Fr(last['L'])*s0
    fam = MF.build(rows, SIG, E0, CAP, L0exact=Fr(last['L']))
    assert fam.Dy == Fr(1, 2**16)
    return fam, fan


def q(x):
    x = Fr(x)
    return f"({x.numerator}/{x.denominator})" if x.denominator != 1 else f"({x.numerator})"


def poly_lean(p):
    return "[" + ", ".join(q(c) for c in p) + "]"


# ---------- mirrors of the Lean polynomials (Family/Formulas3.lean, High3.lean) ----------
def polys(fam, j):
    B, L, B0, L0 = fam.polys(j)
    return B, L, B0, L0, [fam.sig[j], fam.H[j]]


def capP(j):
    """the cap of piece j as a polynomial in y (constant `capM` unless ramped)"""
    return CAPRAMP.get(j, [CAP])


def cap0P(fam, j):
    """the parent's cap cp(y - Dy) (`Piece.cap0P`)"""
    return P.shift(capP(j), -fam.Dy) if j in CAPRAMP else [CAP]


def endP3(fam, j, e):
    return polys(fam, j)[4] if e == 0 else capP(j)


def capField(fam, j):
    """`Piece.capFieldP`: cp > 0, 1 - cp > 0, cp - s > 0, cp(. - Dy) - s > 0, 1 - cp(. - Dy) > 0"""
    cp, c0, sv = capP(j), cap0P(fam, j), polys(fam, j)[4]
    return [cp, P.sub([1], cp), P.sub(cp, sv), P.sub(c0, sv), P.sub([1], c0)]


def atoms(fam, j, b):
    B, L, B0, L0, sv = polys(fam, j)
    t = P.sub(B, P.mul(L, P.sub(b, [E])))
    A = P.smul(1 - DEN, P.add(P.add(P.mul(L0, b), P.sub(t, B0)), P.smul(6*R, B0)))
    D = P.smul(DEN, P.sub(P.smul(6, B0), L0))
    return dict(B=B, L=L, B0=B0, L0=L0, t=t, A=A, D=D, b=b)


def field3P(fam, j):
    B, L, B0, L0, sv = polys(fam, j)
    return [B, P.sub([1], B), P.sub(L, [1]), P.sub(P.smul(Fr(3, 2) - DEN, L0), P.smul(3, B0)),
            P.sub(P.smul(Fr(9, 2), B0), P.smul(Fr(7, 4) - DEN, L0)), P.sub(L0, L), P.sub(B0, [Fr(22, 23)]),
            P.sub([1], B0), P.sub(L0, [1])]


def sg3N(fam, j, b):
    a = atoms(fam, j, b); A, D, t, B0, L0 = a['A'], a['D'], a['t'], a['B0'], a['L0']
    C0 = cap0P(fam, j)
    T = P.add(t, b)
    Lr = P.sub([Fr(49, 100)], P.smul(Fr(9, 2), b))
    return [P.smul(DEN, D), P.mul(P.sub(b, [2*E]), D), P.smul(R, D), P.sub(P.smul(Fr(1, 75) - R, D), A),
            P.sub(P.mul(P.sub([1 - 6*R - 4*E], P.smul(Fr(1, 2), T)), D), P.smul(6, A)),
            P.sub(P.mul(B0, P.sub(P.smul(1 - 6*R, D), P.smul(6, A))), P.mul(P.add(T, [4*E]), D)),
            P.sub(D, P.smul((1 - DEN)*DEN, P.mul(C0, L0))),
            P.sub(P.smul(R - 14*E, D), P.smul((1 - DEN)*DEN*E, P.add(B0, P.mul(C0, L0)))),
            P.smul(R - 20*E, D), P.mul(Lr, D), P.smul(Fr(1, 100) - 10*E, D),
            P.sub(P.mul(P.sub(P.add([Fr(5, 6) - 9*R - F], P.smul(Fr(499, 1000), Lr)), T), D), P.smul(9, A)),
            P.sub(P.mul(P.sub([1 - 5*R - F], T), D), P.smul(5, A)),
            P.sub(P.mul(P.sub([Fr(49, 50) - 4*R - F], T), D), P.smul(4, A)),
            P.sub(P.mul(P.sub([Fr(49, 50) - Fr(9, 2)*R - F], T), D), P.smul(Fr(9, 2), A)),
            P.sub(P.mul(P.sub(Lr, [7*R + F]), D), P.smul(7, A)),
            P.sub(P.mul(P.sub(b, [2*E]), D), A), P.add(A, P.smul(Fr(1, 10**30), D))]


def weak3N(fam, j, b):
    a = atoms(fam, j, b); A, D, t, B0, L0 = a['A'], a['D'], a['t'], a['B0'], a['L0']
    FD = P.sub(P.smul(1 - 6*R, D), P.smul(6, A))
    return P.sub(P.mul(cap0P(fam, j), P.mul(L0, FD)), P.sub(P.mul(B0, FD), P.mul(t, D)))


def sec3N(fam, j, b, jj, nu):
    a = atoms(fam, j, b); A, D, t = a['A'], a['D'], a['t']
    AD = P.add(P.smul(R, D), A)
    FD = P.sub(P.smul(1 - 6*R - E, D), P.smul(6, A))
    tt = 15 - 6*nu
    HD = P.add(P.smul(tt, P.sub(AD, P.smul(nu, P.mul(P.add(t, b), D)))),
               P.smul(nu, P.sub(P.smul(10, D), P.smul(60, AD))))
    bD = P.mul(b, D)
    if jj == 0:
        return P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(nu/2, FD), P.smul(1 - nu, bD)), P.smul(F, D))))
    if jj == 1:
        return P.sub(P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(Fr(5, 6), FD), P.smul(1 - nu, bD)), P.smul(F, D)))),
                     P.smul(10*nu, FD))
    return P.sub(P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(nu/2, P.sub(FD, P.smul(Fr(1, 50), D))), P.smul(1 - nu, bD)),
                                         P.smul(F, D)))), P.smul(10*nu/50, D))


def pw(p_, n):
    return [Fr(1)] if n == 0 else P.mul(p_, pw(p_, n - 1))


def qpolys(fam, j):
    B, L, B0, L0, sv = polys(fam, j)
    N = P.smul(1 - DEN, L0); S = P.sub(P.smul(6, B0), L0); beta = P.sub(P.smul(Fr(3, 4), S), N)
    return N, beta, S


def sec3B(fam, j, b, jj):
    c = CP.cubic4([sec3N(fam, j, b, jj, nu) for nu in CP.NU_PTS])
    N, beta, S = qpolys(fam, j)
    a0 = P.add(P.add(P.mul(c[0], pw(S, 3)), P.mul(c[1], P.mul(N, pw(S, 2)))),
               P.add(P.mul(c[2], P.mul(pw(N, 2), S)), P.mul(c[3], pw(N, 3))))
    a1 = P.mul(beta, P.add(P.add(P.mul(c[1], pw(S, 2)), P.smul(2, P.mul(c[2], P.mul(N, S)))), P.smul(3, P.mul(c[3], pw(N, 2)))))
    a2 = P.mul(pw(beta, 2), P.add(P.mul(c[2], S), P.smul(3, P.mul(c[3], N))))
    a3 = P.mul(pw(beta, 3), c[3])
    return [a0, P.add(a0, P.smul(Fr(1, 3), a1)), P.add(P.add(a0, P.smul(Fr(2, 3), a1)), P.smul(Fr(1, 3), a2)),
            P.add(P.add(a0, a1), P.add(a2, a3))]


def cell3N(fam, j, b):
    a = atoms(fam, j, b); A, D = a['A'], a['D']
    return P.sub(P.sub(P.smul(1 - 6*R - E, D), P.smul(6, A)), P.smul(2, P.mul(P.sub(b, [2*E]), D)))


def gateGDn(Dn, Na, NF, TD, SD, fee, K, Bh, Lh, hc, nu, p, k):
    """`Faceless.gateGDnP` / `gateGDnPc`: Dn · gateG(Na/Dn, TD/Dn, SD/Dn, NF/Dn, …), cleared; the HIGH
    parent's cap `hc` is a polynomial."""
    i, jj = k
    one = [Fr(1)]
    dI = one if i == 0 else [1 - p]
    eP = one if jj < 2 else P.add(Lh, [-2*p])
    gP = one if jj < 2 else Lh
    bI = P.smul(2*p*K, SD) if i == 0 else P.smul(p, NF)
    hP = [P.smul(2*p, SD), P.mul(P.smul(2*p, hc), NF), P.mul(P.smul(2*p, Bh), NF)][jj]
    gM = P.add(P.smul(12*nu, P.mul(dI, eP)), P.smul(5 - 6*nu, P.add(P.smul(2, eP), P.mul(dI, gP))))
    tt = 15 - 6*nu
    base = P.add(P.smul(tt, P.sub(Na, P.smul(nu, TD))),
                 P.add(P.smul(nu, P.sub(P.smul(10, Dn), P.smul(60, Na))),
                       P.add(P.smul(tt*(1 - 2*p)*nu, SD), P.add(P.smul(-10*nu, NF), P.smul(-fee*tt, Dn)))))
    N = P.add(P.smul(10, P.mul(NF, P.mul(dI, eP))),
              P.smul(5 - 6*nu, P.add(P.smul(2, P.mul(eP, bI)), P.mul(dI, hP))))
    return P.add(P.mul(gM, base), P.smul(nu*tt, N))


def highU3(fam, j, b, k):
    a = atoms(fam, j, b); A, D, t, B0, L0 = a['A'], a['D'], a['t'], a['B0'], a['L0']
    AD = P.add(P.smul(R, D), A)
    NF = P.sub(P.smul(1 - 6*R - E, D), P.smul(6, A))
    TD = P.mul(P.add(t, b), D)
    SD = P.sub(P.mul(P.sub(b, [2*E]), D), A)
    vals = {(nu, p): gateGDn(D, AD, NF, TD, SD, F, 8, B0, L0, cap0P(fam, j), nu, p, k)
            for nu in CP.NU_PTS for p in CP.NU_PTS}
    rowsp = {nu: CP.cubic4([vals[(nu, p)] for p in CP.NU_PTS]) for nu in CP.NU_PTS}
    C = [[None]*4 for _ in range(4)]
    for jj in range(4):
        col = CP.cubic4([rowsp[nu][jj] for nu in CP.NU_PTS])
        for i in range(4):
            C[i][jj] = col[i]
    al, be, S = qpolys(fam, j)
    U = [[[] for _ in range(4)] for _ in range(4)]
    for a_ in range(4):
        for jj in range(4):
            acc = []
            for i in range(a_, 4):
                acc = P.add(acc, P.smul(comb(i, a_), P.mul(P.mul(C[i][jj], pw(al, i - a_)),
                                                          P.mul(pw(be, a_), pw(S, 3 - i)))))
            U[a_][jj] = acc
    return U


# ---------- covers and trees ----------
def cover1(p):
    p = P.trim(p)
    D = 1
    for c in p:
        D = math.lcm(D, Fr(c).denominator)
    ip = [int(Fr(c)*D) for c in p]
    cov = I.dyadic_cover(ip, 0, 0, maxe=16)
    assert cov is not None
    return cov


def cov_lean(cov):
    return "[" + ", ".join(f"({k}, {e})" for (k, e) in cov) + "]"


def tree_depth(T):
    return 0 if T[0] == 'leaf' else 1 + max(tree_depth(T[1]), tree_depth(T[2]))


def tree_emax(T):
    if T[0] == 'leaf':
        return max((e for cov in T[1] for (_, e) in cov), default=0)
    return max(tree_emax(T[1]), tree_emax(T[2]))


def load_ck(path):
    import re
    out = {}
    for line in open(path):
        tag, D, X, lit = line.rstrip('\n').split('|')
        polys_ = [[int(x) for x in m.split(',') if x.strip()] for m in re.findall(r'\[([^\[\]!]*)\]', lit)]
        assert len(polys_) == 16, tag
        out[tag] = (int(D), int(X), [polys_[4 * a:4 * a + 4] for a in range(4)])
    return out


def load_cs(path):
    out = {}
    for line in open(path):
        tag, D, X, lit = line.rstrip('\n').split('|')
        out[tag] = (int(D), int(X), [int(x) for x in lit.strip('[]').split(',') if x.strip()])
    return out


HEAD = lambda imps: "\n".join([f"import {m}" for m in imps] + ["", "set_option autoImplicit false",
                                "set_option maxRecDepth 100000", "", f"namespace {NS}", OPENS, ""])
TAIL = ["", f"end {NS}", ""]
DATA = f"{PKG}.Family.Gen.Data3"
DATAC = f"{PKG}.Family.Gen.Data3c"


def gen_data(fam, out):
    L = [HEAD([f"{PKG}.Family.Validity3"])]
    for j in range(len(fam.H)):
        L.append(f"def mpiece{j} : Piece := ⟨{q(fam.sig[j])}, {q(fam.H[j])}, {q(fam.Dy)}, {poly_lean(fam.Ey[j])}⟩")
    L += TAIL
    open(os.path.join(out, "Data3.lean"), 'w').write("\n".join(L))
    # the caps of the variable-cap pieces (a separate module: the constant-cap pieces do not depend on it)
    L = [f"/- Generated by research/mixed-step/gen_family3.py: the cap polynomials of the variable-cap pieces "
         "(`Family/Validity3c.lean`). -/", HEAD([DATA, f"{PKG}.Family.Validity3c"])]
    for j in sorted(CAPRAMP):
        L.append(f"/-- The cap of piece {j} (`Family/Validity3c.lean`). -/")
        L.append(f"def mcap{j} : Poly := {poly_lean(CAPRAMP[j])}")
    L += TAIL
    open(os.path.join(out, "Data3c.lean"), 'w').write("\n".join(L))


def gen_piece(fam, j, out, CKD, CSD):
    t0 = time.time()
    pc = f"mpiece{j}"
    ramp = j in CAPRAMP
    cpn = f"mcap{j}"
    # Lean expressions of the certificate polynomials (constant cap: Validity3; variable cap: Validity3c)
    endL = (lambda e: f"({pc}.endP3c {cpn} {e})") if ramp else (lambda e: f"({pc}.endP3 {e})")
    sgL = (lambda e, jj: f"{pc}.sg3Nc {cpn} {endL(e)} {jj}") if ramp else (lambda e, jj: f"{pc}.sg3N {endL(e)} {jj}")
    wkL = (lambda e: f"{pc}.weak3Nc {cpn} {endL(e)}") if ramp else (lambda e: f"{pc}.weak3N {endL(e)}")
    DAT = DATAC if ramp else DATA
    L = [HEAD([DAT])]
    names = {}
    for i, p in enumerate(field3P(fam, j)):
        nm = f"m{j}_field_{i}"; names[('field', i)] = nm
        L.append(f"theorem {nm} : pos1I ({pc}.field3P {i}) {cov_lean(cover1(p))} = true := by decide +kernel")
    if ramp:
        for i, p in enumerate(capField(fam, j)):
            nm = f"m{j}_capfield_{i}"; names[('capfield', i)] = nm
            L.append(f"theorem {nm} : pos1I ({pc}.capFieldP {cpn} {i}) {cov_lean(cover1(p))} = true := by decide +kernel")
    for e in (0, 1):
        b = endP3(fam, j, e)
        for jj, p in enumerate(sg3N(fam, j, b)):
            nm = f"m{j}_scal_{e}_{jj}"; names[('scal', e, jj)] = nm
            L.append(f"theorem {nm} : pos1I ({sgL(e, jj)}) {cov_lean(cover1(p))} = true := by decide +kernel")
        nm = f"m{j}_weak_{e}"; names[('weak', e)] = nm
        L.append(f"theorem {nm} : pos1I ({wkL(e)}) {cov_lean(cover1(weak3N(fam, j, b)))} = true := by decide +kernel")
        for s3 in range(3):
            ps = sec3B(fam, j, b, s3)
            for i in range(4):
                nm = f"m{j}_sec_{e}_{s3}_{i}"; names[('sec', e, s3, i)] = nm
                D, Xs, cS = CSD[nm]
                g = 0
                for x in cS:
                    g = math.gcd(g, x)
                prim = [x // g for x in cS]
                # the data is a positive multiple of sec3B, so the cover of sec3B serves it
                cov = cov_lean(cover1(ps[i]))
                L += [f"def cS_{nm} : IPoly := [" + ", ".join(str(x) for x in prim) + "]",
                      f"theorem {nm}_dec : Pk.decS3 {D} 1 {pc} {endL(e)} {s3} {i} {g} {Xs} cS_{nm} = true := by decide +kernel",
                      f"theorem {nm}_pos1 : (!({cov} : List (ℕ × ℕ)).isEmpty && IPoly.posOn cS_{nm} 0 0 {cov}) = true := by decide +kernel",
                      f"theorem {nm} : PosOn01 ({pc}.sec3B {endL(e)} {s3} {i}) := Pk.secPos_of_decS3 _ _ _ _ _ _ _ _ _ _ {nm}_dec {nm}_pos1"]
        nm = f"m{j}_cell_{e}"; names[('cell', e)] = nm
        L.append(f"theorem {nm} : pos1I ({pc}.cell3N {endL(e)}) {cov_lean(cover1(cell3N(fam, j, b)))} = true := by decide +kernel")
    L += TAIL
    open(os.path.join(out, f"Scalar{j}.lean"), 'w').write("\n".join(L))
    print(f"piece {j}: scalar certificates ({time.time()-t0:.1f}s)", flush=True)
    highs = {}
    for e in (0, 1):
        for k in [(i, jj) for i in range(2) for jj in range(3)]:
            t0 = time.time()
            U = highU3(fam, j, endP3(fam, j, e), k)
            U = [[P.trim(U[a][bb]) for bb in range(4)] for a in range(4)]
            Dd, c = I.to_int16(U)
            T = GI.find_I(c, 0, 0, 0, 1)
            assert T is not None, (j, e, k)
            nl, ni = GI.stats_I(T)
            tag = f"m{j}_high_{e}_{k[0]}{k[1]}"
            highs[(e, k)] = tag
            D, Xd, cK = CKD[tag]
            g = 0
            for a in range(4):
                for bb in range(4):
                    for x in cK[a][bb]:
                        g = math.gcd(g, x)
            prim = [[[x // g for x in cK[a][bb]] for bb in range(4)] for a in range(4)]
            num, den = None, None
            for a in range(4):
                for bb in range(4):
                    assert len(prim[a][bb]) == len(c[a][bb]) or all(x == 0 for x in prim[a][bb][len(c[a][bb]):]), (tag, a, bb)
                    for x, z in zip(prim[a][bb], c[a][bb]):
                        if num is None and x != 0:
                            num, den = z, x
                        assert x * num == z * den, (tag, a, bb)
            assert num * den > 0, tag
            arr = "![" + ",\n  ".join("![" + ", ".join("[" + ", ".join(str(x) for x in prim[a][bb]) + "]"
                                                    for bb in range(4)) + "]" for a in range(4)) + "]"
            hU = (f"{pc}.highU3c {cpn} {endL(e)} ({k[0]}, {k[1]})" if ramp else
                  f"{pc}.highU3 {endL(e)} ({k[0]}, {k[1]})")
            decL = (f"Pk.decKgX3c {D} 1 {pc} {cpn} {endL(e)} ({k[0]}, {k[1]}) {g} {Xd} cK_{tag}" if ramp else
                    f"Pk.decKgX3 {D} 1 {pc} {endL(e)} ({k[0]}, {k[1]}) {g} {Xd} cK_{tag}")
            posL = ("Pk.coeffPos_of_decKgXZ3c _ _ _ _ _ _ _ _ _ _ _ _" if ramp else
                    "Pk.coeffPos_of_decKgXZ3 _ _ _ _ _ _ _ _ _ _ _")
            Lz = max(len(prim[a][bb]) for a in range(4) for bb in range(4))
            sumAbs = sum(abs(x) for a in range(4) for bb in range(4) for x in prim[a][bb])
            XZ = (sumAbs + 1) * 2 ** (3 * (tree_depth(T) + 1) + 16 + tree_emax(T) * Lz)
            body = [HEAD([DAT]), f"def cK_{tag} : Fin 4 → Fin 4 → IPoly :=", "  " + arr, "",
                    f"def tree_{tag} : IPoly.UTreeI :=", "  " + GI.tree_lean_I(T), "",
                    f"theorem {tag}_dec : {decL} = true := by",
                    "  decide +kernel", "",
                    f"theorem {tag}_tree : IPoly.checkZ cK_{tag} {XZ} {Lz} tree_{tag} = true := by",
                    "  decide +kernel", "",
                    f"theorem {tag}_pos : HighCoeffPos ({hU}) :=",
                    f"  {posL} {tag}_dec {tag}_tree"] + TAIL
            open(os.path.join(out, f"High{j}_{e}_{k[0]}{k[1]}.lean"), 'w').write("\n".join(body))
            print(f"piece {j} high {e} {k}: leaves {nl} intervals {ni} ({time.time()-t0:.1f}s)", flush=True)
    imps = [DAT, f"{PKG}.Family.Gen.Scalar{j}"] + [f"{PKG}.Family.Gen.High{j}_{e}_{k[0]}{k[1]}" for (e, k) in highs]
    A = [HEAD(imps),
         (f"theorem {pc}_certs : {pc}.Certs3c {cpn} where" if ramp else f"theorem {pc}_certs : {pc}.Certs3 where"),
         f"  sig0 := by norm_num [{pc}]",
         f"  H0 := by norm_num [{pc}]",
         f"  Dy0 := by norm_num [{pc}]"]
    if ramp:
        A += ["  capField i := by",
              "    fin_cases i",
              "    exacts [" + ", ".join(f"⟨_, {names[('capfield', i)]}⟩" for i in range(5)) + "]"]
    else:
        A += [f"  capS := by norm_num [{pc}, capM]"]
    A += ["  field i := by",
         "    fin_cases i",
         "    exacts [" + ", ".join(f"⟨_, {names[('field', i)]}⟩" for i in range(9)) + "]",
         "  scal e jj := by",
         "    fin_cases e <;> fin_cases jj",
         "    exacts [" + ", ".join(f"⟨_, {names[('scal', e, jj)]}⟩" for e in (0, 1) for jj in range(18)) + "]",
         "  weak e := by",
         "    fin_cases e",
         "    exacts [" + ", ".join(f"⟨_, {names[('weak', e)]}⟩" for e in (0, 1)) + "]",
         "  sec e s i := by",
         "    fin_cases e <;> fin_cases s <;> fin_cases i",
         "    exacts [" + ", ".join(names[('sec', e, s3, i)] for e in (0, 1) for s3 in range(3) for i in range(4)) + "]",
         "  cell e := by",
         "    fin_cases e",
         "    exacts [" + ", ".join(f"⟨_, {names[('cell', e)]}⟩" for e in (0, 1)) + "]",
         "  high e k := by",
         "    rcases k with ⟨i, jj⟩",
         "    fin_cases e <;> fin_cases i <;> fin_cases jj",
         "    exacts [" + ", ".join(f"{highs[(e, (i, jj))]}_pos" for e in (0, 1) for i in range(2) for jj in range(3)) + "]"] + TAIL
    open(os.path.join(out, f"Piece{j}.lean"), 'w').write("\n".join(A))


# ---------- packed data from Lean ----------
def data_factors(fam, j):
    from gen_certk import factor
    D = 1
    for qq in tuple(polys(fam, j)) + ([CAP], capP(j), cap0P(fam, j)):
        for c in qq:
            D = math.lcm(D, Fr(c).denominator)
    return sorted(factor(D).items())


def extract(fam, lake, ckf, csf, pieces=None):
    from gen_certk import MIN_DELTA, PAD_PRIMES, lean_factors, lean_nats
    n = len(fam.H)
    pieces = list(range(n)) if pieces is None else pieces
    L = [f"import {DATAC if CAPRAMP else DATA}", "", "open QRH.RepeatedMarks.Faceless QRH.MixedStep.Family", "",
         "def showI (q : IPoly) : String := \"[\" ++ \", \".intercalate (q.map toString) ++ \"]\"", "",
         "instance : Inhabited Pk.PZ := ⟨Pk.zero⟩", "",
         "def ptIdx (x : ℚ) : Nat := if x = 0 then 0 else if x = 1 then 1 else if x = -1 then 2 else 3", "",
         "def coeffsKv (X Δ : ℕ) (P : Piece) (val : ℚ → ℚ → Pk.PZ) : Array (Array Pk.PZ) :=",
         "  let pts : List ℚ := [0, 1, -1, 2]",
         "  let samples : Array (Array Pk.PZ) :=",
         "    (pts.map fun ν => (pts.map fun p => val ν p).toArray).toArray",
         "  let f : ℚ → ℚ → Pk.PZ := fun ν p => (samples[ptIdx ν]!)[ptIdx p]!",
         "  let cA : Array (Array Pk.PZ) :=",
         "    ((List.finRange 4).map fun i => ((List.finRange 4).map fun j => Pk.bicubicZ Δ f i j).toArray).toArray",
         "  let α := Pk.ofPoly X Δ P.alpha3P 1",
         "  let β := Pk.ofPoly X Δ P.beta3P 1",
         "  let D := Pk.ofPoly X Δ P.S3P 1",
         "  ((List.finRange 4).map fun a => ((List.finRange 4).map fun j =>",
         "    Pk.cuZ Δ (fun i j => (cA[i.val]!)[j.val]!) α β D a j).toArray).toArray", "",
         "def coeffsK (X Δ : ℕ) (P : Piece) (b : Poly) (k : QRH.RepeatedMarks.Branch) : Array (Array Pk.PZ) :=",
         "  coeffsKv X Δ P (fun ν p => Pk.valPZ3 X Δ 1 P b k ν p)", "",
         "def coeffsKc (X Δ : ℕ) (P : Piece) (cp b : Poly) (k : QRH.RepeatedMarks.Branch) : Array (Array Pk.PZ) :=",
         "  coeffsKv X Δ P (fun ν p => Pk.valPZ3c X Δ 1 P cp b k ν p)", "",
         "def alignK (Δ : ℕ) (c : Array (Array Pk.PZ)) : Array (Array Pk.PZ) :=",
         "  let E := c.foldl (fun acc row => row.foldl (fun acc' r => max r.e acc') acc) 0",
         "  c.map fun row => row.map fun r => Pk.scale Δ r (E - r.e)", "",
         "def litKv (Δ : ℕ) (cf : ℕ → Array (Array Pk.PZ)) : String :=",
         "  let a1 := alignK Δ (cf 1)",
         "  let X := a1.foldl (fun acc row => row.foldl (fun acc' r => max (max r.pos1 r.neg1) acc') acc) 0 + 1",
         "  let aX := alignK Δ (cf X)",
         "  toString X ++ \"|\" ++ \"![\" ++ \", \".intercalate (aX.toList.map fun row => \"![\" ++ \", \".intercalate",
         "    (row.toList.map fun r => showI (Pk.unpack X r)) ++ \"]\") ++ \"]\"", "",
         "def litK (Δ : ℕ) (P : Piece) (b : Poly) (k : QRH.RepeatedMarks.Branch) : String :=",
         "  litKv Δ (fun X => coeffsK X Δ P b k)", "",
         "def litKc (Δ : ℕ) (P : Piece) (cp b : Poly) (k : QRH.RepeatedMarks.Branch) : String :=",
         "  litKv Δ (fun X => coeffsKc X Δ P cp b k)", "",
         "def litS (Δ : ℕ) (P : Piece) (b : Poly) (j : Fin 3) (i : Fin 4) : String :=",
         "  let r1 := Pk.sec3BZ 1 Δ 1 P b j i",
         "  let X := max r1.pos1 r1.neg1 + 1",
         "  let r := Pk.sec3BZ X Δ 1 P b j i",
         "  (if r.ok then \"\" else \"NOTOK\") ++ toString X ++ \"|\" ++ showI (Pk.unpack X r)", ""]
    L += MIN_DELTA + [
        "def branches : List QRH.RepeatedMarks.Branch := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]", "",
        "def okHigh (P : Piece) (Δ : ℕ) : Bool :=",
        "  [(0 : Fin 2), 1].all fun e => branches.all fun k =>",
        "    (coeffsK 1 Δ P (P.endP3 e) k).all fun row => row.all (·.ok)", "",
        "def okSec (P : Piece) (Δ : ℕ) : Bool :=",
        "  [(0 : Fin 2), 1].all fun e => [(0 : Fin 3), 1, 2].all fun j => [(0 : Fin 4), 1, 2, 3].all fun i =>",
        "    (Pk.sec3BZ 1 Δ 1 P (P.endP3 e) j i).ok", "",
        "def okHighc (P : Piece) (cp : Poly) (Δ : ℕ) : Bool :=",
        "  [(0 : Fin 2), 1].all fun e => branches.all fun k =>",
        "    (coeffsKc 1 Δ P cp (P.endP3c cp e) k).all fun row => row.all (·.ok)", "",
        "def okSecc (P : Piece) (cp : Poly) (Δ : ℕ) : Bool :=",
        "  [(0 : Fin 2), 1].all fun e => [(0 : Fin 3), 1, 2].all fun j => [(0 : Fin 4), 1, 2, 3].all fun i =>",
        "    (Pk.sec3BZ 1 Δ 1 P (P.endP3c cp e) j i).ok", ""]
    nh = ns = 0
    for j in pieces:
        ramp = j in CAPRAMP
        okH = f"(okHighc mpiece{j} mcap{j})" if ramp else f"(okHigh mpiece{j})"
        okS = f"(okSecc mpiece{j} mcap{j})" if ramp else f"(okSec mpiece{j})"
        endL = (lambda e: f"(mpiece{j}.endP3c mcap{j} {e})") if ramp else (lambda e: f"(mpiece{j}.endP3 {e})")
        L.append(f"def deltaH{j} : ℕ := minDelta {okH} {lean_factors(data_factors(fam, j))} {lean_nats(PAD_PRIMES)}")
        L.append(f"def deltaS{j} : ℕ := minDelta {okS} {lean_factors(data_factors(fam, j))} {lean_nats(PAD_PRIMES)}")
        for e in (0, 1):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                tag = f"m{j}_high_{e}_{k[0]}{k[1]}"
                lit = (f"litKc deltaH{j} mpiece{j} mcap{j} {endL(e)} ({k[0]}, {k[1]})" if ramp else
                       f"litK deltaH{j} mpiece{j} {endL(e)} ({k[0]}, {k[1]})")
                L.append(f"#eval IO.println (\"{tag}|\" ++ toString deltaH{j} ++ \"|\" ++ {lit})")
                nh += 1
            for s3 in range(3):
                for i in range(4):
                    tag = f"m{j}_sec_{e}_{s3}_{i}"
                    L.append(f"#eval IO.println (\"{tag}|\" ++ toString deltaS{j} ++ \"|\" ++ "
                             f"litS deltaS{j} mpiece{j} {endL(e)} {s3} {i})")
                    ns += 1
    src = os.path.join(lake, "Scratch", "ExtractMixed.lean")
    os.makedirs(os.path.dirname(src), exist_ok=True)
    open(src, 'w').write("\n".join(L) + "\n")
    env = dict(os.environ)
    env['PATH'] = '/home/user/lean-env/lean-4.34.1-linux/bin:' + env['PATH']
    res = subprocess.run(["lake", "env", "lean", src], cwd=lake, capture_output=True, text=True, env=env)
    lines = [l for l in res.stdout.splitlines() if "|" in l and l.startswith("m")]
    hl = [l for l in lines if "_high_" in l]
    sl = [l for l in lines if "_sec_" in l]
    bad = [l for l in lines if "NOTOK" in l or l.split("|")[1] == "0"]
    if len(hl) != nh or len(sl) != ns or bad:
        sys.stderr.write(res.stdout[-3000:] + res.stderr[-3000:])
        raise SystemExit(f"expected {nh}+{ns} good lines, got {len(hl)}+{len(sl)}, bad {len(bad)}")
    if len(pieces) < n:   # merge: keep the other pieces' lines of the existing files
        keep = lambda f: [l for l in open(f).read().splitlines()
                          if l and int(l.split('_')[0][1:]) not in pieces] if os.path.exists(f) else []
        hl, sl = keep(ckf) + hl, keep(csf) + sl
    open(ckf, 'w').write("\n".join(hl) + "\n")
    open(csf, 'w').write("\n".join(sl) + "\n")
    print("wrote", len(hl), "HIGH and", len(sl), "sector certificates")


# ---------- junction steps ----------
def node_at(fam, j, y):
    B, L, B0, L0 = fam.polys(j)
    b, l, b0, l0 = P.ev(B, y), P.ev(L, y), P.ev(B0, y), P.ev(L0, y)
    qq = (1 - DEN)*l0/(6*b0 - l0)
    return MC.face(b, l, P.ev(capP(j), y), qq)


def src_lean(nm):
    return nm


def gen_junctions(fam, fan, out):
    L = [HEAD([DATA, f"{PKG}.Fan.Steps"])]
    nfan = len(fan) - 1
    fanlast = {k: Fr(v) for k, v in fan[-1].items()}
    pars = [(fanlast, f"QRH.MixedStep.Fan.fan{nfan}")]
    for j in range(1, len(fam.H)):
        pars.append((node_at(fam, j - 1, 1 - fam.Dy), f"(mpiece{j - 1}.node3 (1 - mpiece{j - 1}.Dy))"))
    for j, (par, pname) in enumerate(pars):
        n = node_at(fam, j, Fr(0))
        ok, msgs, trees = MC.check_node(n, par, par, Fr(8))
        assert ok and MC.cell_ok(n, par), (j, msgs)
        cr = LC.crossing(n, par)
        cname = f"(mpiece{j}.node3 0)"
        tl = lambda bb: ("fun k => (![" + ", ".join("![" + ", ".join(LC.tree_lean(trees[(bb, (i, jj))]) for jj in range(3)) + "]"
                                                    for i in range(2)) + "] : Fin 2 → Fin 3 → Split) k.1 k.2")
        L += [f"def junction{j}_treesL : Branch → Split := {tl(cr)}",
              f"def junction{j}_treesR : Branch → Split := {tl(n['cap'])}",
              f"theorem junction{j}_validC : SourceValidC3 {cname} {pname} {pname} := by decide +kernel",
              f"theorem junction{j}_highL : HighCertAt3 {cname} {pname} {pname} 8 (crossing {cname} {pname}) junction{j}_treesL := by",
              "  decide +kernel",
              f"theorem junction{j}_highR : HighCertAt3 {cname} {pname} {pname} 8 {cname}.cap junction{j}_treesR := by",
              "  decide +kernel",
              f"theorem junction{j}_cell : CellRatio3 {cname} {pname} := by decide +kernel",
              f"theorem junction{j}_valid : SourceValid3 {cname} {pname} {pname} := by",
              f"  refine sourceValid3_of_certs _ _ _ junction{j}_validC ?_ junction{j}_cell",
              "  intro b hb",
              "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb",
              "  rcases hb with rfl | rfl",
              f"  · exact ⟨_, junction{j}_highL⟩",
              f"  · exact ⟨_, junction{j}_highR⟩", ""]
        print(f"junction {j}: ok (den3 = {float(1 + n['q'] - 6*n['q']*par['B']/par['L']):.3e})", flush=True)
    L += TAIL
    open(os.path.join(out, "Junctions3.lean"), 'w').write("\n".join(L))


# ---------- the generated chain (Graph/MixedChain.lean) ----------
def gen_chain(fam, fan, out, iP=35747):
    nfan = len(fan) - 1
    npc = len(fam.H)
    last = npc - 1
    ramp = last in CAPRAMP
    assert all(j == last for j in CAPRAMP), "only the last piece may have a variable cap"
    imps = [f"{PKG}.Graph.Chain3c" if ramp else f"{PKG}.Graph.Chain3",
            "Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.Start",
            f"{PKG}.Fan.Steps", f"{PKG}.Fan.StepsX", f"{PKG}.Family.Gen.Junctions3", f"{PKG}.Family.Gen.JunctionsX"] + \
        [f"{PKG}.Family.Gen.Piece{j}" for j in range(npc)]
    C = node_at(fam, last, 1 - fam.Dy)
    Pf = node_at(fam, last, Fr(iP)*fam.Dy)
    L = ["/- Generated by research/mixed-step/gen_family3.py: the mixed source chain.",
         f"Sil's face -> {nfan} fan steps -> junction 0 -> piece 0 -> ... -> junction {last} -> piece {last}.",
         f"The count face C is the last face of piece {last}; the physical face P is its grid face {iP}. -/"]
    L += [f"import {m}" for m in imps] + ["", "set_option autoImplicit false", "set_option maxHeartbeats 400000", "",
          "namespace QRH.MixedStep.Graph", "noncomputable section",
          "open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite",
          "open QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless QRH.MixedStep.Family QRH.MixedStep.Fan", ""]
    nodeL = (lambda y: f"mpiece{last}.node3c mcap{last} ({y})") if ramp else (lambda y: f"mpiece{last}.node3 ({y})")
    L += [f"/-- The count face (`C`, the last face of the family). -/",
          f"def faceC : Source := {nodeL(f'1 - mpiece{last}.Dy')}",
          f"/-- The physical face (`P`). -/",
          f"def faceP : Source := {nodeL(f'{iP} * mpiece{last}.Dy')}", ""]
    for nm, n in (("faceC", C), ("faceP", Pf)):
        for fld in ("B", "L", "cap"):
            v = Fr(n[fld])
            L.append(f"lemma {nm}_{fld} : {nm}.{fld} = {v.numerator}/{v.denominator} := by decide +kernel")
    L.append("")
    fanname = lambda k: "QRH.RepeatedMarks.start" if k == 0 else f"fan{k}"
    L += ["theorem mixed_chain_sources (step : NFStep3) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)",
          "    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) :",
          "    QRH.Record1252270103Graph.P faceC ∧ QRH.Record1252270103Graph.P faceP := by",
          "  have f0 := QRH.RepeatedMarks.start_source hβ hk"]
    for k in range(1, nfan + 1):
        good = "QRH.RepeatedMarks.start_good" if k == 1 else f"(parent_good_of_high3 fan{k}_valid)"
        L.append(f"  have f{k} := step _ _ _ hβ hk fan{k}_valid fan{k}_x {good} "
                 f"(by unfold QRH.Record1252270103Graph.NFAccounting; decide +kernel) f{k-1} f{k-1}")
    prev = f"f{nfan}"
    for j in range(npc):
        L.append(f"  have j{j} := step _ _ _ hβ hk junction{j}_valid junction{j}_x (parent_good_of_high3 junction{j}_valid) "
                 f"(nf_accounting_node3 _ _) {prev} {prev}")
        if j in CAPRAMP:
            assert P.ev(capP(j), 0) == CAP
            L.append(f"  rw [← node3c_zero mpiece{j} mcap{j} (by decide +kernel)] at j{j}")
            L.append(f"  have e{j} := piece_last3c step hβ hk mpiece{j} mcap{j} mpiece{j}_certs (by norm_num [mpiece{j}]) j{j}")
        else:
            L.append(f"  have e{j} := piece_last3 step hβ hk mpiece{j} mpiece{j}_certs (by norm_num [mpiece{j}]) j{j}")
        prev = f"e{j}"
    srcs = (f"piece_sources3c step hβ hk mpiece{last} mcap{last}" if ramp else f"piece_sources3 step hβ hk mpiece{last}")
    L += [f"  refine ⟨e{last}, ?_⟩",
          f"  have := {srcs} mpiece{last}_certs (by norm_num [mpiece{last}]) j{last} {iP}",
          "    (by norm_num)",
          "  simpa [faceP] using this", "", "end", "end QRH.MixedStep.Graph", ""]
    open(os.path.join(out, "MixedChain.lean"), 'w').write("\n".join(L))
    print("faceC", float(C['B']), float(C['L']), "faceP", float(Pf['B']), float(Pf['L']))


if __name__ == "__main__":
    mode = sys.argv[1]
    fam, fan = build()
    if mode == 'data':
        os.makedirs(sys.argv[2], exist_ok=True)
        gen_data(fam, sys.argv[2])
    elif mode == 'extract':
        extract(fam, sys.argv[2], sys.argv[3], sys.argv[4],
                [int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else None)
    elif mode == 'pieces':
        out = sys.argv[2]
        pcs = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else range(len(fam.H))
        CKD, CSD = load_ck(CK), load_cs(CS)
        for j in pcs:
            gen_piece(fam, j, out, CKD, CSD)
    elif mode == 'junctions':
        gen_junctions(fam, fan, sys.argv[2])
    elif mode == 'chain':
        gen_chain(fam, fan, sys.argv[2])
