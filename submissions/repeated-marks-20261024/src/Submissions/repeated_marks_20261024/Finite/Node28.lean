/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node27
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node28 : Source := ⟨(1966384110631/2000000000000),(18355759100797/5000000000000),(87/2000),(31120889219/50000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node28_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node28_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node28_validC : SourceValidC node28 node27 (some node27) := by decide +kernel
theorem node28_highL : HighCertAt node28 node27 node27 8 (crossing node28 node27) node28_treesL := by
  decide +kernel
theorem node28_highR : HighCertAt node28 node27 node27 8 node28.cap node28_treesR := by
  decide +kernel
theorem node28_cell : CellRatio node28 node27 := by decide +kernel
theorem node28_valid : SourceValid2 node28 node27 (some node27) := by
  refine ⟨node28_validC, ?_, by decide +kernel, node28_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node28_highL⟩
  · exact ⟨_, node28_highR⟩
end QRH.RepeatedMarks.Finite
