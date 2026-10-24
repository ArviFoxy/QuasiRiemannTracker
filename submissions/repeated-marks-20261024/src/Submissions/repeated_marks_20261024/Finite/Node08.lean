/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node07
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node08 : Source := ⟨(2489840404077/2500000000000),(165302467557/39062500000),(67/2000),(354097724009/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node08_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node08_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node08_validC : SourceValidC node08 node07 (some node07) := by decide +kernel
theorem node08_highL : HighCertAt node08 node07 node07 8 (crossing node08 node07) node08_treesL := by
  decide +kernel
theorem node08_highR : HighCertAt node08 node07 node07 8 node08.cap node08_treesR := by
  decide +kernel
theorem node08_cell : CellRatio node08 node07 := by decide +kernel
theorem node08_valid : SourceValid2 node08 node07 (some node07) := by
  refine ⟨node08_validC, ?_, by decide +kernel, node08_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node08_highL⟩
  · exact ⟨_, node08_highR⟩
end QRH.RepeatedMarks.Finite
