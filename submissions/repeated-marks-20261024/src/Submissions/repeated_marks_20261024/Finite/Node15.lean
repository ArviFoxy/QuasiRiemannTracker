/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node14
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node15 : Source := ⟨(1240163657039/1250000000000),(40363005874339/10000000000000),(37/1000),(339037936791/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node15_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node15_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node15_validC : SourceValidC node15 node14 (some node14) := by decide +kernel
theorem node15_highL : HighCertAt node15 node14 node14 8 (crossing node15 node14) node15_treesL := by
  decide +kernel
theorem node15_highR : HighCertAt node15 node14 node14 8 node15.cap node15_treesR := by
  decide +kernel
theorem node15_cell : CellRatio node15 node14 := by decide +kernel
theorem node15_valid : SourceValid2 node15 node14 (some node14) := by
  refine ⟨node15_validC, ?_, by decide +kernel, node15_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node15_highL⟩
  · exact ⟨_, node15_highR⟩
end QRH.RepeatedMarks.Finite
