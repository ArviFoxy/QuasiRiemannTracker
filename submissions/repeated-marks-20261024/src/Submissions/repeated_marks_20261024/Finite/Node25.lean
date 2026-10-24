/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node24
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node25 : Source := ⟨(9854501780219/10000000000000),(4693486020391/1250000000000),(21/500),(127022298013/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node25_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node25_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node25_validC : SourceValidC node25 node24 (some node24) := by decide +kernel
theorem node25_highL : HighCertAt node25 node24 node24 8 (crossing node25 node24) node25_treesL := by
  decide +kernel
theorem node25_highR : HighCertAt node25 node24 node24 8 node25.cap node25_treesR := by
  decide +kernel
theorem node25_cell : CellRatio node25 node24 := by decide +kernel
theorem node25_valid : SourceValid2 node25 node24 (some node24) := by
  refine ⟨node25_validC, ?_, by decide +kernel, node25_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node25_highL⟩
  · exact ⟨_, node25_highR⟩
end QRH.RepeatedMarks.Finite
