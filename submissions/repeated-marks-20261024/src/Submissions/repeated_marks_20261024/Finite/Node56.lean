/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node55
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node56 : Source := ⟨(9578164749307/10000000000000),(14687879836123/5000000000000),(549989/10000000),(511658124777/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node56_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), (.p .leaf .leaf), (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node56_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, (.p .leaf (.p .leaf (.p .leaf (.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf)))))]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node56_validC : SourceValidC node56 node55 (some node55) := by decide +kernel
theorem node56_highL : HighCertAt node56 node55 node55 8 (crossing node56 node55) node56_treesL := by
  decide +kernel
theorem node56_highR : HighCertAt node56 node55 node55 8 node56.cap node56_treesR := by
  decide +kernel
theorem node56_cell : CellRatio node56 node55 := by decide +kernel
theorem node56_valid : SourceValid2 node56 node55 (some node55) := by
  refine ⟨node56_validC, ?_, by decide +kernel, node56_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node56_highL⟩
  · exact ⟨_, node56_highR⟩
end QRH.RepeatedMarks.Finite
