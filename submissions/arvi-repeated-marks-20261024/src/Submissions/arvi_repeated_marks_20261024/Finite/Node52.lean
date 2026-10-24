/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node51
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node52 : Source := ⟨(9618940091529/10000000000000),(15188603253317/5000000000000),(549989/10000000),(26335941829/50000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node52_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node52_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node52_validC : SourceValidC node52 node51 (some node51) := by decide +kernel
theorem node52_highL : HighCertAt node52 node51 node51 8 (crossing node52 node51) node52_treesL := by
  decide +kernel
theorem node52_highR : HighCertAt node52 node51 node51 8 node52.cap node52_treesR := by
  decide +kernel
theorem node52_cell : CellRatio node52 node51 := by decide +kernel
theorem node52_valid : SourceValid2 node52 node51 (some node51) := by
  refine ⟨node52_validC, ?_, by decide +kernel, node52_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node52_highL⟩
  · exact ⟨_, node52_highR⟩
end QRH.RepeatedMarks.Finite
