/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node23
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node24 : Source := ⟨(9862482036823/10000000000000),(9463705277351/2500000000000),(83/2000),(639769485277/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node24_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node24_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node24_validC : SourceValidC node24 node23 (some node23) := by decide +kernel
theorem node24_highL : HighCertAt node24 node23 node23 8 (crossing node24 node23) node24_treesL := by
  decide +kernel
theorem node24_highR : HighCertAt node24 node23 node23 8 node24.cap node24_treesR := by
  decide +kernel
theorem node24_cell : CellRatio node24 node23 := by decide +kernel
theorem node24_valid : SourceValid2 node24 node23 (some node23) := by
  refine ⟨node24_validC, ?_, by decide +kernel, node24_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node24_highL⟩
  · exact ⟨_, node24_highR⟩
end QRH.RepeatedMarks.Finite
