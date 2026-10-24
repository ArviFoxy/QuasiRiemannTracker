/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node29
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node30 : Source := ⟨(2454263256659/2500000000000),(7236913994717/2000000000000),(89/2000),(614412538029/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node30_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node30_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node30_validC : SourceValidC node30 node29 (some node29) := by decide +kernel
theorem node30_highL : HighCertAt node30 node29 node29 8 (crossing node30 node29) node30_treesL := by
  decide +kernel
theorem node30_highR : HighCertAt node30 node29 node29 8 node30.cap node30_treesR := by
  decide +kernel
theorem node30_cell : CellRatio node30 node29 := by decide +kernel
theorem node30_valid : SourceValid2 node30 node29 (some node29) := by
  refine ⟨node30_validC, ?_, by decide +kernel, node30_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node30_highL⟩
  · exact ⟨_, node30_highR⟩
end QRH.RepeatedMarks.Finite
