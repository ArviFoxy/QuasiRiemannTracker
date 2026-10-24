/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node45
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node46 : Source := ⟨(4837981352553/5000000000000),(15934714564541/5000000000000),(21/400),(549301804821/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node46_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node46_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node46_validC : SourceValidC node46 node45 (some node45) := by decide +kernel
theorem node46_highL : HighCertAt node46 node45 node45 8 (crossing node46 node45) node46_treesL := by
  decide +kernel
theorem node46_highR : HighCertAt node46 node45 node45 8 node46.cap node46_treesR := by
  decide +kernel
theorem node46_cell : CellRatio node46 node45 := by decide +kernel
theorem node46_valid : SourceValid2 node46 node45 (some node45) := by
  refine ⟨node46_validC, ?_, by decide +kernel, node46_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node46_highL⟩
  · exact ⟨_, node46_highR⟩
end QRH.RepeatedMarks.Finite
