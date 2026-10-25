"""Generate all Lean certificate files of the faceless source chain.

Mirrors (mathematically, exactly) Faceless/{Family,HighCert,ScalarCert,Validity}.lean:
  fieldP, sgN, weakN, secB, cellN (1D, `pos1I`) and highU (`certI`) for every piece, plus the
  concrete first step (natural -> piece0.node 0) and the junction steps.

usage: python3 gen_all.py OUTDIR [pieces]
"""
import sys, os, json, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import polyq as P
import ipoly as I
import family2 as F2
import cert2 as C2
import cert_proto as CP
import gen_faceless_I as GI
import lean_certs as LC

SIG = [float(x) for x in os.environ.get('QRH_SIG', '0.0123480,0.01942,0.0252,0.0310,0.0367,0.0424270').split(',')]
M = 16
PKG = os.environ.get('QRH_PKG', 'Submissions.arvi_repeated_marks_20261024')
NS = 'QRH.RepeatedMarks.Faceless'
E, R, F = F2.FEES
CAP = F2.CAPMAX
K_N = Fr(os.environ.get('QRH_K', '11243277/2500000'))


def q(x):
    x = Fr(x)
    return f"({x.numerator}/{x.denominator})" if x.denominator != 1 else f"({x.numerator})"


def poly_lean(p):
    return "[" + ", ".join(q(c) for c in p) + "]"


# ---------- mirrors of the Lean polynomials ----------
def atoms(fam, j, b):
    B, L, B0, L0, sv = fam.polys(j)
    den = fam.den
    t = P.sub(B, P.mul(L, P.sub(b, [E])))
    A = P.add(P.smul(1 - den, P.add(P.mul(L0, b), P.sub(t, B0))), P.smul(6*R, B0))
    D = P.smul(6*den, B0)
    return dict(B=B, L=L, B0=B0, L0=L0, sv=sv, t=t, A=A, D=D, b=b)


def endP(fam, j, e):
    return fam.polys(j)[4] if e == 0 else [CAP]


def fieldP(fam, j):
    B, L, B0, L0, sv = fam.polys(j)
    den = fam.den
    return [B, P.sub([1], B), P.sub(L, [1]), P.sub(P.smul(1 - den, L0), P.smul(3, B0)),
            P.sub(P.smul(Fr(9, 2), B0), P.smul(1 - den, L0)), P.sub(L0, L), P.sub(B0, [Fr(22, 23)]),
            P.sub([1], B0), P.sub(L0, [1])]


def sgN(fam, j, b):
    a = atoms(fam, j, b); A, D, t, B0, L0 = a['A'], a['D'], a['t'], a['B0'], a['L0']
    den = fam.den
    S6 = P.smul(6, B0); Mm = P.mul(D, S6); T = P.add(t, b)
    Lr = P.sub([Fr(49, 100)], P.smul(K_N, b))
    return [P.smul(den, Mm), P.mul(P.sub(b, [2*E]), Mm), P.mul(A, S6), P.mul(P.sub(P.smul(Fr(1, 75), D), A), S6),
            P.mul(P.sub(P.mul(D, P.sub([1 - 4*E], P.smul(Fr(1, 2), T))), P.smul(6, A)), S6),
            P.mul(P.sub(P.mul(B0, P.sub(D, P.smul(6, A))), P.mul(D, P.add(T, [4*E]))), S6),
            P.mul(P.sub(S6, P.smul((1 - den)*CAP, L0)), D),
            P.mul(P.sub(P.smul(6*(R - ((1 - den)/6 + 14)*E), B0), P.smul((1 - den)*CAP*E, L0)), D),
            P.mul(P.sub(A, P.smul(20*E, D)), S6), P.mul(Lr, Mm), P.smul(Fr(1, 100) - 10*E, Mm),
            P.mul(P.sub(P.mul(D, P.add([Fr(5, 6) - F], P.sub(P.smul(Fr(499, 1000), Lr), T))), P.smul(9, A)), S6),
            P.mul(P.sub(P.mul(D, P.sub([1 - F], T)), P.smul(5, A)), S6),
            P.mul(P.sub(P.mul(D, P.sub([Fr(49, 50) - F], T)), P.smul(4, A)), S6),
            P.mul(P.sub(P.mul(D, P.sub([Fr(49, 50) - F], T)), P.smul(Fr(9, 2), A)), S6),
            P.mul(P.sub(P.mul(D, P.sub(Lr, [F])), P.smul(7, A)), S6)]


def weakN(fam, j, b):
    a = atoms(fam, j, b); A, D, t, B0, L0 = a['A'], a['D'], a['t'], a['B0'], a['L0']
    FD = P.sub(D, P.smul(6, A))
    return P.sub(P.smul(CAP, P.mul(L0, FD)), P.sub(P.mul(B0, FD), P.mul(t, D)))


def secN(fam, j, b, jj, nu):
    a = atoms(fam, j, b); A, D, t = a['A'], a['D'], a['t']
    NF = P.sub(P.smul(1 - E, D), P.smul(6, A)); tt = 15 - 6*nu
    HD = P.add(P.smul(tt, P.sub(A, P.smul(nu, P.mul(P.add(t, b), D)))), P.smul(nu, P.sub(P.smul(10, D), P.smul(60, A))))
    bD = P.mul(b, D)
    if jj == 6:
        return P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(nu/2, NF), P.smul(1 - nu, bD)), P.smul(F, D))))
    if jj == 7:
        return P.sub(P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(Fr(5, 6), NF), P.smul(1 - nu, bD)), P.smul(F, D)))),
                     P.smul(10*nu, NF))
    return P.sub(P.add(HD, P.smul(tt, P.sub(P.sub(P.smul(nu/2, P.sub(NF, P.smul(Fr(1, 50), D))), P.smul(1 - nu, bD)),
                                         P.smul(F, D)))), P.smul(10*nu/50, D))


def secB(fam, j, b, jj):
    B, L, B0, L0, sv = fam.polys(j)
    den = fam.den
    c = CP.cubic4([secN(fam, j, b, jj, nu) for nu in CP.NU_PTS])
    N = P.smul(1 - den, L0); S = P.smul(6, B0); beta = P.sub(P.smul(Fr(9, 2), B0), N)
    pw = lambda p_, n: [Fr(1)] if n == 0 else P.mul(p_, pw(p_, n - 1))
    a0 = P.add(P.add(P.mul(c[0], pw(S, 3)), P.mul(c[1], P.mul(N, pw(S, 2)))),
               P.add(P.mul(c[2], P.mul(pw(N, 2), S)), P.mul(c[3], pw(N, 3))))
    a1 = P.mul(beta, P.add(P.add(P.mul(c[1], pw(S, 2)), P.smul(2, P.mul(c[2], P.mul(N, S)))), P.smul(3, P.mul(c[3], pw(N, 2)))))
    a2 = P.mul(pw(beta, 2), P.add(P.mul(c[2], S), P.smul(3, P.mul(c[3], N))))
    a3 = P.mul(pw(beta, 3), c[3])
    return [a0, P.add(a0, P.smul(Fr(1, 3), a1)), P.add(P.add(a0, P.smul(Fr(2, 3), a1)), P.smul(Fr(1, 3), a2)),
            P.add(P.add(a0, a1), P.add(a2, a3))]


def cellN(fam, j, b):
    a = atoms(fam, j, b); A, D = a['A'], a['D']
    return P.sub(P.sub(P.smul(1 - E, D), P.smul(6, A)), P.smul(2, P.mul(P.sub(b, [2*E]), D)))


def cover1(p):
    """dyadic intervals for pos1I (integer test on D·p)."""
    p = P.trim(p)
    D = 1
    from math import lcm
    for c in p:
        D = lcm(D, Fr(c).denominator)
    ip = [int(Fr(c)*D) for c in p]
    cov = I.dyadic_cover(ip, 0, 0, maxe=16)
    assert cov is not None
    return cov


def cov_lean(cov):
    return "[" + ", ".join(f"({k}, {e})" for (k, e) in cov) + "]"


HEAD = lambda imps: "\n".join([f"import {PKG}.{m}" for m in imps] + ["", "set_option autoImplicit false",
                                "set_option maxRecDepth 100000", "", f"namespace {NS}", ""])
TAIL = ["", f"end {NS}", ""]


def gen_piece(fam, j, out):
    t0 = time.time()
    L = [HEAD(["Faceless.Gen.Data"])]
    names = {}
    for i, p in enumerate(fieldP(fam, j)):
        nm = f"p{j}_field_{i}"; names[('field', i)] = nm
        L.append(f"theorem {nm} : pos1I (piece{j}.fieldP {i}) {cov_lean(cover1(p))} = true := by decide +kernel")
    for e in (0, 1):
        b = endP(fam, j, e)
        for jj, p in enumerate(sgN(fam, j, b)):
            nm = f"p{j}_scal_{e}_{jj}"; names[('scal', e, jj)] = nm
            L.append(f"theorem {nm} : pos1I (piece{j}.sgN (piece{j}.endP {e}) {jj}) {cov_lean(cover1(p))} = true := by decide +kernel")
        nm = f"p{j}_weak_{e}"; names[('weak', e)] = nm
        L.append(f"theorem {nm} : pos1I (piece{j}.weakN (piece{j}.endP {e})) {cov_lean(cover1(weakN(fam, j, b)))} = true := by decide +kernel")
        for s3 in range(3):
            ps = secB(fam, j, b, s3 + 6)
            for i in range(4):
                nm = f"p{j}_sec_{e}_{s3}_{i}"; names[('sec', e, s3, i)] = nm
                L.append(f"theorem {nm} : pos1I (piece{j}.secB (piece{j}.endP {e}) ({s3} + 6) {i}) {cov_lean(cover1(ps[i]))} = true := by decide +kernel")
        nm = f"p{j}_cell_{e}"; names[('cell', e)] = nm
        L.append(f"theorem {nm} : pos1I (piece{j}.cellN (piece{j}.endP {e})) {cov_lean(cover1(cellN(fam, j, b)))} = true := by decide +kernel")
    L += TAIL
    open(os.path.join(out, f"Scalar{j}.lean"), 'w').write("\n".join(L))
    print(f"piece {j}: scalar certificates ({time.time()-t0:.1f}s)", flush=True)
    # HIGH
    highs = {}
    for e in (0, 1):
        for k in [(i, jj) for i in range(2) for jj in range(3)]:
            t0 = time.time()
            bk = 'cross' if e == 0 else 'cap'
            U = C2.high_polys2(fam, j, bk, k)
            U = [[P.trim(U[a][bb]) for bb in range(4)] for a in range(4)]
            Dd, c = I.to_int16(U)
            T = GI.find_I(c, 0, 0, 0, 1)
            assert T is not None, (j, e, k)
            nl, ni = GI.stats_I(T)
            tag = f"p{j}_high_{e}_{k[0]}{k[1]}"
            highs[(e, k)] = tag
            body = [HEAD(["Faceless.Gen.Data"]), f"def tree_{tag} : IPoly.UTreeI :=", "  " + GI.tree_lean_I(T), "",
                    f"theorem {tag} : certI (piece{j}.highU (piece{j}.endP {e}) ({k[0]}, {k[1]})) tree_{tag} = true := by",
                    "  decide +kernel"] + TAIL
            open(os.path.join(out, f"High{j}_{e}_{k[0]}{k[1]}.lean"), 'w').write("\n".join(body))
            print(f"piece {j} high {e} {k}: leaves {nl} intervals {ni} ({time.time()-t0:.1f}s)", flush=True)
    # assembly
    imps = ["Faceless.Validity", f"Faceless.Gen.Scalar{j}"] + [f"Faceless.Gen.High{j}_{e}_{k[0]}{k[1]}" for (e, k) in highs]
    A = [HEAD(imps),
         f"theorem piece{j}_certs : piece{j}.Certs where",
         f"  sig0 := by norm_num [piece{j}]",
         f"  H0 := by norm_num [piece{j}]",
         f"  Dy0 := by norm_num [piece{j}]",
         f"  capS := by norm_num [piece{j}, capF]",
         "  field i := by",
         "    fin_cases i",
         "    exacts [" + ", ".join(f"⟨_, {names[('field', i)]}⟩" for i in range(9)) + "]",
         "  scal e jj := by",
         "    fin_cases e <;> fin_cases jj",
         "    exacts [" + ", ".join(f"⟨_, {names[('scal', e, jj)]}⟩" for e in (0, 1) for jj in range(16)) + "]",
         "  weak e := by",
         "    fin_cases e",
         "    exacts [" + ", ".join(f"⟨_, {names[('weak', e)]}⟩" for e in (0, 1)) + "]",
         "  sec e s i := by",
         "    fin_cases e <;> fin_cases s <;> fin_cases i",
         "    exacts [" + ", ".join(f"⟨_, {names[('sec', e, s3, i)]}⟩" for e in (0, 1) for s3 in range(3) for i in range(4)) + "]",
         "  cell e := by",
         "    fin_cases e",
         "    exacts [" + ", ".join(f"⟨_, {names[('cell', e)]}⟩" for e in (0, 1)) + "]",
         "  high e k := by",
         "    rcases k with ⟨i, jj⟩",
         "    fin_cases e <;> fin_cases i <;> fin_cases jj",
         "    exacts [" + ", ".join(f"⟨_, {highs[(e, (i, jj))]}⟩" for e in (0, 1) for i in range(2) for jj in range(3)) + "]"] + TAIL
    open(os.path.join(out, f"Piece{j}.lean"), 'w').write("\n".join(A))


def gen_data(fam, out):
    L = [HEAD(["Faceless.Validity"])]
    for j in range(len(fam.H)):
        L.append(f"def piece{j} : Piece := ⟨{q(fam.sig[j])}, {q(fam.H[j])}, {q(fam.Dy)}, {poly_lean(fam.Ey[j])}⟩")
    L += TAIL
    open(os.path.join(out, "Data.lean"), 'w').write("\n".join(L))


if __name__ == "__main__":
    out = sys.argv[1]
    pieces = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else None
    fam, _ = F2.build2(SIG, m=M)
    os.makedirs(out, exist_ok=True)
    gen_data(fam, out)
    for j in (pieces if pieces is not None else range(len(fam.H))):
        gen_piece(fam, j, out)
