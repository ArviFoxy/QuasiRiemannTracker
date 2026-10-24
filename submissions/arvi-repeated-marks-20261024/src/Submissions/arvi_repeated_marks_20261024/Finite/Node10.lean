/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node09
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node10 : Source := ⟨(4974433380841/5000000000000),(41741234441723/10000000000000),(69/2000),(699278094279/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node10_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node10_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node10_validC : SourceValidC node10 node09 (some node09) := by decide +kernel
theorem node10_highL : HighCertAt node10 node09 node09 8 (crossing node10 node09) node10_treesL := by
  decide +kernel
theorem node10_highR : HighCertAt node10 node09 node09 8 node10.cap node10_treesR := by
  decide +kernel
theorem node10_cell : CellRatio node10 node09 := by decide +kernel
theorem node10_valid : SourceValid2 node10 node09 (some node09) := by
  refine ⟨node10_validC, ?_, by decide +kernel, node10_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node10_highL⟩
  · exact ⟨_, node10_highR⟩
end QRH.RepeatedMarks.Finite
