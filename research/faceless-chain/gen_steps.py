"""Lean file for the concrete steps of the faceless chain: natural -> piece0.node 0 and the junctions
piece(j-1).node (1 - Dy) -> piece j.node 0. Each is SourceValid2 by `decide +kernel`, the HIGH part
through Bernstein trees (`HighValid`, then `highPos_of_valid`).
usage: python3 gen_steps.py OUTDIR"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import lean_certs as LC
import family2 as F2
import polyq as P
from gen_all import SIG, M, PKG, NS, HEAD, TAIL

def node_at(fam, j, y):
    B, L, B0, L0, sv = fam.polys(j)
    q = (1 - fam.den)*P.ev(L0, y)/(6*P.ev(B0, y))
    return dict(B=P.ev(B, y), L=P.ev(L, y), cap=F2.CAPMAX, q=q, allowance=F2.FEES[0], lowFee=F2.FEES[1], highFee=F2.FEES[2])

NATURAL = dict(B=Fr(1), L=Fr(11243277, 2500000), cap=Fr(11, 200), q=Fr(0), allowance=Fr(1, 10**12),
               lowFee=Fr(1, 10**8), highFee=Fr(1, 10**7))

def trees_lean(trees, b):
    rows = []
    for i in range(2):
        rows.append("![" + ", ".join(LC.tree_lean(trees[(b, (i, j))]) for j in range(3)) + "]")
    return "fun k => (![" + ", ".join(rows) + "] : Fin 2 → Fin 3 → Split) k.1 k.2"

if __name__ == "__main__":
    out = sys.argv[1]
    fam, _ = F2.build2(SIG, m=M)
    Dy = fam.Dy
    steps = [("step0", "piece0.node 0", "natural", node_at(fam, 0, Fr(0)), NATURAL)]
    for j in range(1, len(fam.H)):
        par = node_at(fam, j - 1, 1 - Dy)
        steps.append((f"junction{j}", f"piece{j}.node 0", f"piece{j-1}.node (1 - piece{j-1}.Dy)", node_at(fam, j, Fr(0)), par))
    L = [HEAD(["Faceless.Gen.Data"]), "open Record1252270103Finite QRH.RepeatedMarks.Finite", ""]
    for name, nt, pt, n, par in steps:
        ok, msgs, trees = LC.check_node(n, par, par, Fr(8))
        assert ok, (name, msgs)
        cr = LC.crossing(n, par)
        L += [f"def {name}_treesL : Branch → Split := {trees_lean(trees, cr)}",
              f"def {name}_treesR : Branch → Split := {trees_lean(trees, n['cap'])}",
              f"theorem {name}_validC : SourceValidC ({nt}) ({pt}) (some ({pt})) := by decide +kernel",
              f"theorem {name}_highL : HighCertAt ({nt}) ({pt}) ({pt}) 8 (crossing ({nt}) ({pt})) {name}_treesL := by",
              "  decide +kernel",
              f"theorem {name}_highR : HighCertAt ({nt}) ({pt}) ({pt}) 8 ({nt}).cap {name}_treesR := by",
              "  decide +kernel",
              f"theorem {name}_q : ({nt}).q < 3/4 := by decide +kernel",
              f"theorem {name}_cell : CellRatio ({nt}) ({pt}) := by decide +kernel",
              f"theorem {name}_valid : SourceValid2 ({nt}) ({pt}) (some ({pt})) := by",
              f"  refine ⟨{name}_validC, highPos_of_valid _ _ _ _ {name}_q ?_, {name}_q, {name}_cell⟩",
              "  intro h hh b hb",
              "  simp only [Option.mem_def, Option.some.injEq] at hh",
              "  subst hh",
              "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb",
              "  rcases hb with rfl | rfl",
              f"  · exact ⟨_, {name}_highL⟩",
              f"  · exact ⟨_, {name}_highR⟩", ""]
        print(name, "ok; crossing", float(cr))
    L += TAIL
    open(os.path.join(out, "Steps.lean"), 'w').write("\n".join(L))
