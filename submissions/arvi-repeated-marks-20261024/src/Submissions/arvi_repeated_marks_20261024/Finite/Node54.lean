/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node53
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node54 : Source := ⟨(599928999719/625000000000),(29877986564809/10000000000000),(549989/10000000),(519213135359/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node54_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node54_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, (.p .leaf (.p .leaf (.p .leaf (.p .leaf (.p .leaf (.p .leaf (.p (.p .leaf .leaf) .leaf)))))))]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node54_validC : SourceValidC node54 node53 (some node53) := by decide +kernel
theorem node54_highL : HighCertAt node54 node53 node53 8 (crossing node54 node53) node54_treesL := by
  decide +kernel
theorem node54_highR : HighCertAt node54 node53 node53 8 node54.cap node54_treesR := by
  decide +kernel
theorem node54_cell : CellRatio node54 node53 := by decide +kernel
theorem node54_valid : SourceValid2 node54 node53 (some node53) := by
  refine ⟨node54_validC, ?_, by decide +kernel, node54_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node54_highL⟩
  · exact ⟨_, node54_highR⟩
end QRH.RepeatedMarks.Finite
