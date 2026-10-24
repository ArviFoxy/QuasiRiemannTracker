/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node50
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node51 : Source := ⟨(4813683599899/5000000000000),(30590551019763/10000000000000),(549989/10000000),(530028044973/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node51_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), (.p .leaf .leaf), (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node51_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node51_validC : SourceValidC node51 node50 (some node50) := by decide +kernel
theorem node51_highL : HighCertAt node51 node50 node50 8 (crossing node51 node50) node51_treesL := by
  decide +kernel
theorem node51_highR : HighCertAt node51 node50 node50 8 node51.cap node51_treesR := by
  decide +kernel
theorem node51_cell : CellRatio node51 node50 := by decide +kernel
theorem node51_valid : SourceValid2 node51 node50 (some node50) := by
  refine ⟨node51_validC, ?_, by decide +kernel, node51_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node51_highL⟩
  · exact ⟨_, node51_highR⟩
end QRH.RepeatedMarks.Finite
