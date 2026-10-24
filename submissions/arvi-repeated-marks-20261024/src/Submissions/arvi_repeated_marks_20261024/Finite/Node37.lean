/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node36
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node37 : Source := ⟨(9758307462501/10000000000000),(856421531311/250000000000),(6/125),(585300992157/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node37_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node37_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node37_validC : SourceValidC node37 node36 (some node36) := by decide +kernel
theorem node37_highL : HighCertAt node37 node36 node36 8 (crossing node37 node36) node37_treesL := by
  decide +kernel
theorem node37_highR : HighCertAt node37 node36 node36 8 node37.cap node37_treesR := by
  decide +kernel
theorem node37_cell : CellRatio node37 node36 := by decide +kernel
theorem node37_valid : SourceValid2 node37 node36 (some node36) := by
  refine ⟨node37_validC, ?_, by decide +kernel, node37_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node37_highL⟩
  · exact ⟨_, node37_highR⟩
end QRH.RepeatedMarks.Finite
