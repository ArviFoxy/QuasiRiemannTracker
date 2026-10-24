/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.Node16
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node17 : Source := ⟨(495460100233/500000000000),(3980543251947/1000000000000),(19/500),(133906194839/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node17_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf .leaf)]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node17_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node17_validC : SourceValidC node17 node16 (some node16) := by decide +kernel
theorem node17_highL : HighCertAt node17 node16 node16 8 (crossing node17 node16) node17_treesL := by
  decide +kernel
theorem node17_highR : HighCertAt node17 node16 node16 8 node17.cap node17_treesR := by
  decide +kernel
theorem node17_cell : CellRatio node17 node16 := by decide +kernel
theorem node17_valid : SourceValid2 node17 node16 (some node16) := by
  refine ⟨node17_validC, ?_, by decide +kernel, node17_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node17_highL⟩
  · exact ⟨_, node17_highR⟩
end QRH.RepeatedMarks.Finite
