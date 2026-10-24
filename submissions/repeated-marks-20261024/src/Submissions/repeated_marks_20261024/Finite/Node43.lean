/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node42
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node43 : Source := ⟨(4852183928749/5000000000000),(32658471778601/10000000000000),(51/1000),(35074748959/62500000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node43_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node43_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node43_validC : SourceValidC node43 node42 (some node42) := by decide +kernel
theorem node43_highL : HighCertAt node43 node42 node42 8 (crossing node43 node42) node43_treesL := by
  decide +kernel
theorem node43_highR : HighCertAt node43 node42 node42 8 node43.cap node43_treesR := by
  decide +kernel
theorem node43_cell : CellRatio node43 node42 := by decide +kernel
theorem node43_valid : SourceValid2 node43 node42 (some node42) := by
  refine ⟨node43_validC, ?_, by decide +kernel, node43_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node43_highL⟩
  · exact ⟨_, node43_highR⟩
end QRH.RepeatedMarks.Finite
