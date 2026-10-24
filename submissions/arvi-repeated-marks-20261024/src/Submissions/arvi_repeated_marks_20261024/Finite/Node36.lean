/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node35
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node36 : Source := ⟨(9767710828723/10000000000000),(1727535822343/500000000000),(19/400),(117938891267/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node36_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node36_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node36_validC : SourceValidC node36 node35 (some node35) := by decide +kernel
theorem node36_highL : HighCertAt node36 node35 node35 8 (crossing node36 node35) node36_treesL := by
  decide +kernel
theorem node36_highR : HighCertAt node36 node35 node35 8 node36.cap node36_treesR := by
  decide +kernel
theorem node36_cell : CellRatio node36 node35 := by decide +kernel
theorem node36_valid : SourceValid2 node36 node35 (some node35) := by
  refine ⟨node36_validC, ?_, by decide +kernel, node36_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node36_highL⟩
  · exact ⟨_, node36_highR⟩
end QRH.RepeatedMarks.Finite
