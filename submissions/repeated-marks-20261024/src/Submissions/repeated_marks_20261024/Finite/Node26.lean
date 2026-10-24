/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node25
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node26 : Source := ⟨(2461607242691/2500000000000),(37243253844099/10000000000000),(17/400),(630472052819/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node26_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf (.p .leaf .leaf))), .leaf, (.p .leaf (.p .leaf (.p .leaf .leaf)))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node26_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node26_validC : SourceValidC node26 node25 (some node25) := by decide +kernel
theorem node26_highL : HighCertAt node26 node25 node25 8 (crossing node26 node25) node26_treesL := by
  decide +kernel
theorem node26_highR : HighCertAt node26 node25 node25 8 node26.cap node26_treesR := by
  decide +kernel
theorem node26_cell : CellRatio node26 node25 := by decide +kernel
theorem node26_valid : SourceValid2 node26 node25 (some node25) := by
  refine ⟨node26_validC, ?_, by decide +kernel, node26_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node26_highL⟩
  · exact ⟨_, node26_highR⟩
end QRH.RepeatedMarks.Finite
