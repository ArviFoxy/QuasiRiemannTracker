/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node26
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node27 : Source := ⟨(9840256092479/10000000000000),(740292574449/200000000000),(43/1000),(62700059281/100000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node27_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node27_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node27_validC : SourceValidC node27 node26 (some node26) := by decide +kernel
theorem node27_highL : HighCertAt node27 node26 node26 8 (crossing node27 node26) node27_treesL := by
  decide +kernel
theorem node27_highR : HighCertAt node27 node26 node26 8 node27.cap node27_treesR := by
  decide +kernel
theorem node27_cell : CellRatio node27 node26 := by decide +kernel
theorem node27_valid : SourceValid2 node27 node26 (some node26) := by
  refine ⟨node27_validC, ?_, by decide +kernel, node27_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node27_highL⟩
  · exact ⟨_, node27_highR⟩
end QRH.RepeatedMarks.Finite
