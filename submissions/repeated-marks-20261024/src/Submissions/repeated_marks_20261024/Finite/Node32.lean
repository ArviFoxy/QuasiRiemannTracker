/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node31
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node32 : Source := ⟨(9799577573603/10000000000000),(35587101777759/10000000000000),(91/2000),(605382288209/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node32_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p .leaf .leaf) .leaf)), (.p .leaf .leaf), (.p .leaf (.p (.p .leaf .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node32_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node32_validC : SourceValidC node32 node31 (some node31) := by decide +kernel
theorem node32_highL : HighCertAt node32 node31 node31 8 (crossing node32 node31) node32_treesL := by
  decide +kernel
theorem node32_highR : HighCertAt node32 node31 node31 8 node32.cap node32_treesR := by
  decide +kernel
theorem node32_cell : CellRatio node32 node31 := by decide +kernel
theorem node32_valid : SourceValid2 node32 node31 (some node31) := by
  refine ⟨node32_validC, ?_, by decide +kernel, node32_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node32_highL⟩
  · exact ⟨_, node32_highR⟩
end QRH.RepeatedMarks.Finite
