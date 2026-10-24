/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node01
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node02 : Source := ⟨(156019893037/156250000000),(10978480425547/2500000000000),(61/2000),(733003907649/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node02_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node02_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node02_validC : SourceValidC node02 node01 (some node01) := by decide +kernel
theorem node02_highL : HighCertAt node02 node01 node01 8 (crossing node02 node01) node02_treesL := by
  decide +kernel
theorem node02_highR : HighCertAt node02 node01 node01 8 node02.cap node02_treesR := by
  decide +kernel
theorem node02_cell : CellRatio node02 node01 := by decide +kernel
theorem node02_valid : SourceValid2 node02 node01 (some node01) := by
  refine ⟨node02_validC, ?_, by decide +kernel, node02_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node02_highL⟩
  · exact ⟨_, node02_highR⟩
end QRH.RepeatedMarks.Finite
