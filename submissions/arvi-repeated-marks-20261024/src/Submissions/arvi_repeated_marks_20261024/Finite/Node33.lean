/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node32
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node33 : Source := ⟨(4896435493289/5000000000000),(4420443609617/1250000000000),(23/500),(601983173263/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node33_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node33_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node33_validC : SourceValidC node33 node32 (some node32) := by decide +kernel
theorem node33_highL : HighCertAt node33 node32 node32 8 (crossing node33 node32) node33_treesL := by
  decide +kernel
theorem node33_highR : HighCertAt node33 node32 node32 8 node33.cap node33_treesR := by
  decide +kernel
theorem node33_cell : CellRatio node33 node32 := by decide +kernel
theorem node33_valid : SourceValid2 node33 node32 (some node32) := by
  refine ⟨node33_validC, ?_, by decide +kernel, node33_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node33_highL⟩
  · exact ⟨_, node33_highR⟩
end QRH.RepeatedMarks.Finite
