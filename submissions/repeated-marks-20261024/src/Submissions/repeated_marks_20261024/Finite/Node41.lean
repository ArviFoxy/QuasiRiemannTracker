/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node40
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node41 : Source := ⟨(1215246879749/1250000000000),(33164639987729/10000000000000),(1/20),(568815578627/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node41_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p .leaf .leaf) .leaf)), .leaf, (.p .leaf (.p (.p .leaf .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node41_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node41_validC : SourceValidC node41 node40 (some node40) := by decide +kernel
theorem node41_highL : HighCertAt node41 node40 node40 8 (crossing node41 node40) node41_treesL := by
  decide +kernel
theorem node41_highR : HighCertAt node41 node40 node40 8 node41.cap node41_treesR := by
  decide +kernel
theorem node41_cell : CellRatio node41 node40 := by decide +kernel
theorem node41_valid : SourceValid2 node41 node40 (some node40) := by
  refine ⟨node41_validC, ?_, by decide +kernel, node41_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node41_highL⟩
  · exact ⟨_, node41_highR⟩
end QRH.RepeatedMarks.Finite
