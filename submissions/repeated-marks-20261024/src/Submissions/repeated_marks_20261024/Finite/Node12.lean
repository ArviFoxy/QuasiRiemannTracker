/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node11
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node12 : Source := ⟨(9937841236083/10000000000000),(1646780198239/400000000000),(71/2000),(690462096723/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node12_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node12_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node12_validC : SourceValidC node12 node11 (some node11) := by decide +kernel
theorem node12_highL : HighCertAt node12 node11 node11 8 (crossing node12 node11) node12_treesL := by
  decide +kernel
theorem node12_highR : HighCertAt node12 node11 node11 8 node12.cap node12_treesR := by
  decide +kernel
theorem node12_cell : CellRatio node12 node11 := by decide +kernel
theorem node12_valid : SourceValid2 node12 node11 (some node11) := by
  refine ⟨node12_validC, ?_, by decide +kernel, node12_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node12_highL⟩
  · exact ⟨_, node12_highR⟩
end QRH.RepeatedMarks.Finite
