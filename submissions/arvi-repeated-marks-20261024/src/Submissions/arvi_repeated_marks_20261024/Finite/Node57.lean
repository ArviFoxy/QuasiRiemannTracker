/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node56
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node57 : Source := ⟨(597879479977/625000000000),(29087829441903/10000000000000),(549989/10000000),(507483352827/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node57_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p (.p .leaf .leaf) .leaf), (.p .leaf .leaf), (.p (.p .leaf .leaf) .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node57_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, (.p .leaf (.p .leaf (.p .leaf (.p (.p .leaf (.p (.p .leaf (.p .leaf .leaf)) .leaf)) .leaf))))]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node57_validC : SourceValidC node57 node56 (some node56) := by decide +kernel
theorem node57_highL : HighCertAt node57 node56 node56 8 (crossing node57 node56) node57_treesL := by
  decide +kernel
theorem node57_highR : HighCertAt node57 node56 node56 8 node57.cap node57_treesR := by
  decide +kernel
theorem node57_cell : CellRatio node57 node56 := by decide +kernel
theorem node57_valid : SourceValid2 node57 node56 (some node56) := by
  refine ⟨node57_validC, ?_, by decide +kernel, node57_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node57_highL⟩
  · exact ⟨_, node57_highR⟩
end QRH.RepeatedMarks.Finite
