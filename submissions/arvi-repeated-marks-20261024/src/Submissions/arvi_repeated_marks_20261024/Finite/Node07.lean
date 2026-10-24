/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node06
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node07 : Source := ⟨(1245466807123/1250000000000),(42567308304631/10000000000000),(33/1000),(712055410319/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node07_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node07_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node07_validC : SourceValidC node07 node06 (some node06) := by decide +kernel
theorem node07_highL : HighCertAt node07 node06 node06 8 (crossing node07 node06) node07_treesL := by
  decide +kernel
theorem node07_highR : HighCertAt node07 node06 node06 8 node07.cap node07_treesR := by
  decide +kernel
theorem node07_cell : CellRatio node07 node06 := by decide +kernel
theorem node07_valid : SourceValid2 node07 node06 (some node06) := by
  refine ⟨node07_validC, ?_, by decide +kernel, node07_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node07_highL⟩
  · exact ⟨_, node07_highR⟩
end QRH.RepeatedMarks.Finite
