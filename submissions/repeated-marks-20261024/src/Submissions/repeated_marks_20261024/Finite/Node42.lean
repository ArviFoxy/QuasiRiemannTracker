/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node41
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node42 : Source := ⟨(971447426693/1000000000000),(32947226333779/10000000000000),(101/2000),(113096683061/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node42_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf .leaf), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node42_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node42_validC : SourceValidC node42 node41 (some node41) := by decide +kernel
theorem node42_highL : HighCertAt node42 node41 node41 8 (crossing node42 node41) node42_treesL := by
  decide +kernel
theorem node42_highR : HighCertAt node42 node41 node41 8 node42.cap node42_treesR := by
  decide +kernel
theorem node42_cell : CellRatio node42 node41 := by decide +kernel
theorem node42_valid : SourceValid2 node42 node41 (some node41) := by
  refine ⟨node42_validC, ?_, by decide +kernel, node42_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node42_highL⟩
  · exact ⟨_, node42_highR⟩
end QRH.RepeatedMarks.Finite
