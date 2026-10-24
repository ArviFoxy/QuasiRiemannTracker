/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node12
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node13 : Source := ⟨(9932969555737/10000000000000),(5115740117337/1250000000000),(9/250),(686724714111/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node13_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node13_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node13_validC : SourceValidC node13 node12 (some node12) := by decide +kernel
theorem node13_highL : HighCertAt node13 node12 node12 8 (crossing node13 node12) node13_treesL := by
  decide +kernel
theorem node13_highR : HighCertAt node13 node12 node12 8 node13.cap node13_treesR := by
  decide +kernel
theorem node13_cell : CellRatio node13 node12 := by decide +kernel
theorem node13_valid : SourceValid2 node13 node12 (some node12) := by
  refine ⟨node13_validC, ?_, by decide +kernel, node13_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node13_highL⟩
  · exact ⟨_, node13_highR⟩
end QRH.RepeatedMarks.Finite
