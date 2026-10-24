/- Repeated marks: a node of the final source graph, checked by `decide +kernel`. -/
import Submissions.repeated_marks_20261024.Finite.Node39
set_option autoImplicit false
set_option maxRecDepth 100000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite
def node40 : Source := ⟨(2432954951101/2500000000000),(8363547985253/2500000000000),(99/2000),(573192819511/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
def node40_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf .leaf)), .leaf, (.p .leaf (.p .leaf .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def node40_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem node40_validC : SourceValidC node40 node39 (some node39) := by decide +kernel
theorem node40_highL : HighCertAt node40 node39 node39 8 (crossing node40 node39) node40_treesL := by
  decide +kernel
theorem node40_highR : HighCertAt node40 node39 node39 8 node40.cap node40_treesR := by
  decide +kernel
theorem node40_cell : CellRatio node40 node39 := by decide +kernel
theorem node40_valid : SourceValid2 node40 node39 (some node39) := by
  refine ⟨node40_validC, ?_, by decide +kernel, node40_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, node40_highL⟩
  · exact ⟨_, node40_highR⟩
end QRH.RepeatedMarks.Finite
