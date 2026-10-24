/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node04
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node05 : Source := ⟨(498606329639/500000000000),(43068338155003/10000000000000),(4/125),(359907778259/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node05_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node05_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node05_validC : SourceValidC node05 node04 (some node04) := by decide +kernel
theorem node05_highL : HighCertAt node05 node04 node04 8 (crossing node05 node04) node05_treesL := by
  decide +kernel
theorem node05_highR : HighCertAt node05 node04 node04 8 node05.cap node05_treesR := by
  decide +kernel
theorem node05_cell : CellRatio node05 node04 := by decide +kernel
theorem node05_valid : SourceValid2 node05 node04 (some node04) := by
  refine ⟨node05_validC, ?_, by decide +kernel, node05_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node05_highL⟩
  · exact ⟨_, node05_highR⟩
end QRH.RepeatedMarks.Finite
