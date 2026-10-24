/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node19
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node20 : Source := ⟨(9889279085681/10000000000000),(38939164650661/10000000000000),(79/2000),(656289947759/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node20_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node20_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node20_validC : SourceValidC node20 node19 (some node19) := by decide +kernel
theorem node20_highL : HighCertAt node20 node19 node19 8 (crossing node20 node19) node20_treesL := by
  decide +kernel
theorem node20_highR : HighCertAt node20 node19 node19 8 node20.cap node20_treesR := by
  decide +kernel
theorem node20_cell : CellRatio node20 node19 := by decide +kernel
theorem node20_valid : SourceValid2 node20 node19 (some node19) := by
  refine ⟨node20_validC, ?_, by decide +kernel, node20_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node20_highL⟩
  · exact ⟨_, node20_highR⟩
end QRH.RepeatedMarks.Finite
