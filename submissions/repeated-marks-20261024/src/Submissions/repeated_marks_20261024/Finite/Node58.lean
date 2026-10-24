/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node57
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node58 : Source := ⟨(1912184686337/2000000000000),(14483089485293/5000000000000),(549989/10000000),(505248067171/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node58_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p (.p .leaf .leaf) .leaf), (.p .leaf .leaf), (.p (.p .leaf .leaf) .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node58_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, (.p .leaf (.p .leaf (.p .leaf (.p (.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf)) .leaf))))]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node58_validC : SourceValidC node58 node57 (some node57) := by decide +kernel
theorem node58_highL : HighCertAt node58 node57 node57 8 (crossing node58 node57) node58_treesL := by
  decide +kernel
theorem node58_highR : HighCertAt node58 node57 node57 8 node58.cap node58_treesR := by
  decide +kernel
theorem node58_cell : CellRatio node58 node57 := by decide +kernel
theorem node58_valid : SourceValid2 node58 node57 (some node57) := by
  refine ⟨node58_validC, ?_, by decide +kernel, node58_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node58_highL⟩
  · exact ⟨_, node58_highR⟩
end QRH.RepeatedMarks.Finite
