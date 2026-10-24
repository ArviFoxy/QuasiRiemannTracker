/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node20
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node21 : Source := ⟨(9881819856047/10000000000000),(38628363415951/10000000000000),(1/25),(651533864901/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node21_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf (.p (.p .leaf (.p .leaf .leaf)) .leaf))), .leaf, (.p .leaf (.p .leaf (.p (.p .leaf (.p .leaf .leaf)) .leaf)))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node21_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node21_validC : SourceValidC node21 node20 (some node20) := by decide +kernel
theorem node21_highL : HighCertAt node21 node20 node20 8 (crossing node21 node20) node21_treesL := by
  decide +kernel
theorem node21_highR : HighCertAt node21 node20 node20 8 node21.cap node21_treesR := by
  decide +kernel
theorem node21_cell : CellRatio node21 node20 := by decide +kernel
theorem node21_valid : SourceValid2 node21 node20 (some node20) := by
  refine ⟨node21_validC, ?_, by decide +kernel, node21_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node21_highL⟩
  · exact ⟨_, node21_highR⟩
end QRH.RepeatedMarks.Finite
