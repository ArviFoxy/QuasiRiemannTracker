/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node00 : Source := ⟨(4996896781579/5000000000000),(44513371937687/10000000000000),(59/2000),(742370820723/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node00_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node00_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node00_validC : SourceValidC node00 natural (some natural) := by decide +kernel
theorem node00_highL : HighCertAt node00 natural natural 8 (crossing node00 natural) node00_treesL := by
  decide +kernel
theorem node00_highR : HighCertAt node00 natural natural 8 node00.cap node00_treesR := by
  decide +kernel
theorem node00_cell : CellRatio node00 natural := by decide +kernel
theorem node00_valid : SourceValid2 node00 natural (some natural) := by
  refine ⟨node00_validC, ?_, by decide +kernel, node00_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node00_highL⟩
  · exact ⟨_, node00_highR⟩
end QRH.RepeatedMarks.Finite
