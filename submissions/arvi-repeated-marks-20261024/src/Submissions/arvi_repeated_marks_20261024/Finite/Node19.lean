/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node18
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node19 : Source := ⟨(1237080693053/1250000000000),(39252630980147/10000000000000),(39/1000),(132215848079/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node19_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node19_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node19_validC : SourceValidC node19 node18 (some node18) := by decide +kernel
theorem node19_highL : HighCertAt node19 node18 node18 8 (crossing node19 node18) node19_treesL := by
  decide +kernel
theorem node19_highR : HighCertAt node19 node18 node18 8 node19.cap node19_treesR := by
  decide +kernel
theorem node19_cell : CellRatio node19 node18 := by decide +kernel
theorem node19_valid : SourceValid2 node19 node18 (some node18) := by
  refine ⟨node19_validC, ?_, by decide +kernel, node19_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node19_highL⟩
  · exact ⟨_, node19_highR⟩
end QRH.RepeatedMarks.Finite
