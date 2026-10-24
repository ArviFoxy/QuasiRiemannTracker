/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node13
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node14 : Source := ⟨(2481592990423/2500000000000),(10151021770719/2500000000000),(73/2000),(340882226431/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node14_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node14_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node14_validC : SourceValidC node14 node13 (some node13) := by decide +kernel
theorem node14_highL : HighCertAt node14 node13 node13 8 (crossing node14 node13) node14_treesL := by
  decide +kernel
theorem node14_highR : HighCertAt node14 node13 node13 8 node14.cap node14_treesR := by
  decide +kernel
theorem node14_cell : CellRatio node14 node13 := by decide +kernel
theorem node14_valid : SourceValid2 node14 node13 (some node13) := by
  refine ⟨node14_validC, ?_, by decide +kernel, node14_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node14_highL⟩
  · exact ⟨_, node14_highR⟩
end QRH.RepeatedMarks.Finite
