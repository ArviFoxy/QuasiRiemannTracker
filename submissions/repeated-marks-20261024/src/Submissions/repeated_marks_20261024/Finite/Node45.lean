/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node44
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node45 : Source := ⟨(4843207302629/5000000000000),(16077891278939/5000000000000),(13/250),(276770038079/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node45_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node45_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node45_validC : SourceValidC node45 node44 (some node44) := by decide +kernel
theorem node45_highL : HighCertAt node45 node44 node44 8 (crossing node45 node44) node45_treesL := by
  decide +kernel
theorem node45_highR : HighCertAt node45 node44 node44 8 node45.cap node45_treesR := by
  decide +kernel
theorem node45_cell : CellRatio node45 node44 := by decide +kernel
theorem node45_valid : SourceValid2 node45 node44 (some node44) := by
  refine ⟨node45_validC, ?_, by decide +kernel, node45_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node45_highL⟩
  · exact ⟨_, node45_highR⟩
end QRH.RepeatedMarks.Finite
