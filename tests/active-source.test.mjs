import test from "node:test";
import assert from "node:assert/strict";
import { activeSource } from "../bench/active-source.mjs";

test("comments and documentation are not part of the proof", () => {
  const source = `/-! Module documentation. -/
import Mathlib.Data.Nat.Basic  -- the base

/-- A documented lemma /- with a nested comment -/ still inside. -/
theorem foo (n : ℕ) : n = n := by
  rfl -- done
/- trailing -/`;
  assert.equal(
    activeSource(source),
    "import Mathlib.Data.Nat.Basic\ntheorem foo (n : ℕ) : n = n := by\nrfl",
  );
});

test("comment markers inside string and character literals are kept", () => {
  const source = `def a := "x -- not a comment /- nor this -/ y"
def b := '"'
def c := "quote \\" -- still a string"
def d := 'a'
-- gone`;
  assert.equal(
    activeSource(source),
    `def a := "x -- not a comment /- nor this -/ y"\ndef b := '"'\ndef c := "quote \\" -- still a string"\ndef d := 'a'`,
  );
});

test("primes in names are not character literals", () => {
  const source = `theorem h' (x' : ℕ) : x' = x' := rfl -- ok\ntheorem h'' := h' "s -- inside"`;
  assert.equal(
    activeSource(source),
    `theorem h' (x' : ℕ) : x' = x' := rfl\ntheorem h'' := h' "s -- inside"`,
  );
});

test("layout does not change the result", () => {
  const compact = "theorem foo : True := by\ntrivial";
  const spread = "theorem   foo :\tTrue := by   \n\n\n      trivial\n\n";
  assert.equal(activeSource(spread), compact);
  assert.equal(activeSource(compact), compact);
  assert.equal(activeSource("-- only a comment\n/- and another -/\n"), "");
});

test("an unterminated block comment or string does not hang or throw", () => {
  assert.equal(activeSource("def a := 1\n/- never closed"), "def a := 1");
  assert.equal(
    activeSource('def a := "never closed'),
    'def a := "never closed',
  );
});
