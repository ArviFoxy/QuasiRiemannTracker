/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node22
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node23 : Source := ⟨(4934194513233/5000000000000),(9521616940511/2500000000000),(41/1000),(321644805073/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node23_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node23_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node23_validC : SourceValidC node23 node22 (some node22) := by decide +kernel
theorem node23_highL : HighCertAt node23 node22 node22 8 (crossing node23 node22) node23_treesL := by
  decide +kernel
theorem node23_highR : HighCertAt node23 node22 node22 8 node23.cap node23_treesR := by
  decide +kernel
theorem node23_cell : CellRatio node23 node22 := by decide +kernel
theorem node23_valid : SourceValid2 node23 node22 (some node22) := by
  refine ⟨node23_validC, ?_, by decide +kernel, node23_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node23_highL⟩
  · exact ⟨_, node23_highR⟩
end QRH.RepeatedMarks.Finite
