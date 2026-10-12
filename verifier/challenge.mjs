import { standardChallenge } from "../core/standard-challenge.mjs";
import { manifest } from "./manifest.mjs";
import { pins } from "./common.mjs";
export const THEOREM = "QRH.canonical_bound";
export function challenge(m) {
  manifest(m);
  return standardChallenge(m.theta);
}
export function solutionWrapper(m) {
  manifest(m);
  return `import ${m.entrypoint.module}\n\n${challenge(m).replace("import Mathlib\n", "").replace("  sorry", `  exact ${m.entrypoint.declaration} χ hs hpole`)}`;
}
export function comparatorConfig() {
  return {
    challenge_module: "Challenge",
    solution_module: "Solution",
    theorem_names: [THEOREM],
    definition_names: [],
    permitted_axioms: pins.allowed_axioms,
    external_kernels: { nanoda: ["/opt/bin/nanoda_bin"] },
  };
}
