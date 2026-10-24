/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node10
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node11 : Source := ⟨(1988837037093/2000000000000),(5186854461683/1250000000000),(7/200),(695489792889/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node11_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node11_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node11_validC : SourceValidC node11 node10 (some node10) := by decide +kernel
theorem node11_highL : HighCertAt node11 node10 node10 8 (crossing node11 node10) node11_treesL := by
  decide +kernel
theorem node11_highR : HighCertAt node11 node10 node10 8 node11.cap node11_treesR := by
  decide +kernel
theorem node11_cell : CellRatio node11 node10 := by decide +kernel
theorem node11_valid : SourceValid2 node11 node10 (some node10) := by
  refine ⟨node11_validC, ?_, by decide +kernel, node11_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node11_highL⟩
  · exact ⟨_, node11_highR⟩
end QRH.RepeatedMarks.Finite
