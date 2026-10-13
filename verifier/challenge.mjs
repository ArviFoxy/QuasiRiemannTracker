import { standardChallenge } from "../core/standard-challenge.mjs";
import { manifest } from "./manifest.mjs";
export const THEOREM = "QRH.canonical_bound";
export function challenge(m) {
  m = manifest(m);
  return standardChallenge(m.theta);
}
export function solutionWrapper(m) {
  m = manifest(m);
  return `import ${m.entrypoint.module}\n\n${challenge(m).replace("import Mathlib\n", "").replace("  sorry", `  exact ${m.entrypoint.declaration} χ hs hpole`)}`;
}
