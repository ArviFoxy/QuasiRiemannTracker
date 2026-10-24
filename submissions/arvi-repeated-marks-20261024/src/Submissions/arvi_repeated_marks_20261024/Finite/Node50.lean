/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node49
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node50 : Source := ⟨(9638411815791/10000000000000),(482402285963/156250000000),(109/2000),(106839419883/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node50_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node50_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node50_validC : SourceValidC node50 node49 (some node49) := by decide +kernel
theorem node50_highL : HighCertAt node50 node49 node49 8 (crossing node50 node49) node50_treesL := by
  decide +kernel
theorem node50_highR : HighCertAt node50 node49 node49 8 node50.cap node50_treesR := by
  decide +kernel
theorem node50_cell : CellRatio node50 node49 := by decide +kernel
theorem node50_valid : SourceValid2 node50 node49 (some node49) := by
  refine ⟨node50_validC, ?_, by decide +kernel, node50_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node50_highL⟩
  · exact ⟨_, node50_highR⟩
end QRH.RepeatedMarks.Finite
