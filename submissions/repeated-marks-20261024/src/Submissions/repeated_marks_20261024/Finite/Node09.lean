/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node08
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node09 : Source := ⟨(4976714506207/5000000000000),(41987842589397/10000000000000),(17/500),(703076848209/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node09_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node09_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node09_validC : SourceValidC node09 node08 (some node08) := by decide +kernel
theorem node09_highL : HighCertAt node09 node08 node08 8 (crossing node09 node08) node09_treesL := by
  decide +kernel
theorem node09_highR : HighCertAt node09 node08 node08 8 node09.cap node09_treesR := by
  decide +kernel
theorem node09_cell : CellRatio node09 node08 := by decide +kernel
theorem node09_valid : SourceValid2 node09 node08 (some node08) := by
  refine ⟨node09_validC, ?_, by decide +kernel, node09_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node09_highL⟩
  · exact ⟨_, node09_highR⟩
end QRH.RepeatedMarks.Finite
