import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { upstreamImports } from "../verifier/actions/imports.mjs";
test("builds actual upstream imports and ignores declarations, strings and comments", () => {
  assert.deepEqual(
    upstreamImports(`
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
    ["OAI.NumberTheory.First", "OAI.NumberTheory.Second"],
  );
});
test("the standard theta-one proof needs no upstream OAI library build", () => {
  assert.deepEqual(
    upstreamImports(
      readFileSync(
        "submissions/classical-euler-product/src/Candidate/Main.lean",
        "utf8",
      ),
    ),
    [],
  );
});
