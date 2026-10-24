/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node38
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node39 : Source := ⟨(9741576319033/10000000000000),(16872715591833/5000000000000),(49/1000),(115506355689/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node39_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node39_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node39_validC : SourceValidC node39 node38 (some node38) := by decide +kernel
theorem node39_highL : HighCertAt node39 node38 node38 8 (crossing node39 node38) node39_treesL := by
  decide +kernel
theorem node39_highR : HighCertAt node39 node38 node38 8 node39.cap node39_treesR := by
  decide +kernel
theorem node39_cell : CellRatio node39 node38 := by decide +kernel
theorem node39_valid : SourceValid2 node39 node38 (some node38) := by
  refine ⟨node39_validC, ?_, by decide +kernel, node39_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node39_highL⟩
  · exact ⟨_, node39_highR⟩
end QRH.RepeatedMarks.Finite
