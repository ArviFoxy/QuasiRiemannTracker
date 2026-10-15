import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { rational } from "./rational.mjs";
import { exactBound } from "./exact-bound.mjs";
export function standardChallenge(theta, exact_bound) {
  rational(theta.numerator, theta.denominator);
  if (BigInt(theta.numerator) <= 0n) throw Error("Bound must be positive");
  const expression = exactBound(
    exact_bound ?? `${theta.numerator}/${theta.denominator}`,
  ).lean;
  const template = readFileSync(
    new URL("../verifier/upstream-challenge.lean", import.meta.url),
    "utf8",
  );
  const pins = JSON.parse(
    readFileSync(new URL("../verifier/pins.json", import.meta.url), "utf8"),
  );
  if (
    createHash("sha256").update(template).digest("hex") !==
    pins.challenge_sha256
  )
    throw Error("Trusted challenge template changed");
  return template
    .replace("namespace OAI\n\nnamespace DirichletCharacter", "namespace QRH")
    .replace("LFunction_ne_zero_of_seven_eighths_lt_re", "canonical_bound")
    .replace("(7 / 8 : ℝ)", `(${expression} : ℝ)`)
    .replace("end DirichletCharacter\n\nend OAI", "end QRH");
}
