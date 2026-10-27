import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { leanImports } from "../verifier/actions/imports.mjs";
import { submissionDirectory } from "../verifier/submission-paths.mjs";
test("reads Lean module imports and ignores declarations, strings and comments", () => {
  assert.deepEqual(
    leanImports(`
import Mathlib OAI.NumberTheory.First
public import
  OAI.NumberTheory.Second
import Candidate.Main
/- outer /- nested -/
import OAI.Comment
-/
-- import OAI.LineComment
namespace OAI.NumberTheory
#check OAI.NumberTheory.Unimported.theorem
 def text := "\nimport OAI.String\n"
`),
    [
      "Candidate.Main",
      "Mathlib",
      "OAI.NumberTheory.First",
      "OAI.NumberTheory.Second",
    ],
  );
});
test("the standard theta-one proof needs no upstream OAI library build", () => {
  const directory = submissionDirectory(
    "classical-euler-product",
    readdirSync("submissions"),
  );
  assert.deepEqual(
    leanImports(
      readFileSync(`submissions/${directory}/src/Candidate/Main.lean`, "utf8"),
    ),
    ["Submissions.classical_euler_product.Main"],
  );
});
