/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node46
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node47 : Source := ⟨(2416356691447/2500000000000),(31584674012381/10000000000000),(53/1000),(68124779281/125000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node47_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf)), (.p .leaf .leaf), (.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node47_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node47_validC : SourceValidC node47 node46 (some node46) := by decide +kernel
theorem node47_highL : HighCertAt node47 node46 node46 8 (crossing node47 node46) node47_treesL := by
  decide +kernel
theorem node47_highR : HighCertAt node47 node46 node46 8 node47.cap node47_treesR := by
  decide +kernel
theorem node47_cell : CellRatio node47 node46 := by decide +kernel
theorem node47_valid : SourceValid2 node47 node46 (some node46) := by
  refine ⟨node47_validC, ?_, by decide +kernel, node47_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node47_highL⟩
  · exact ⟨_, node47_highR⟩
end QRH.RepeatedMarks.Finite
