/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node17
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node18 : Source := ⟨(9902093122043/10000000000000),(39489482180973/10000000000000),(77/2000),(83086157639/125000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node18_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node18_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node18_validC : SourceValidC node18 node17 (some node17) := by decide +kernel
theorem node18_highL : HighCertAt node18 node17 node17 8 (crossing node18 node17) node18_treesL := by
  decide +kernel
theorem node18_highR : HighCertAt node18 node17 node17 8 node18.cap node18_treesR := by
  decide +kernel
theorem node18_cell : CellRatio node18 node17 := by decide +kernel
theorem node18_valid : SourceValid2 node18 node17 (some node17) := by
  refine ⟨node18_validC, ?_, by decide +kernel, node18_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node18_highL⟩
  · exact ⟨_, node18_highR⟩
end QRH.RepeatedMarks.Finite
