import test from "node:test";
import assert from "node:assert/strict";
import { gzipSync } from "node:zlib";
import {
  aliveCode,
  commandHead,
  commandKeyword,
  readDump,
  withoutDead,
  withoutDebris,
  withoutEmptyBlocks,
} from "../bench/alive.mjs";

// A dump in the form Dump.lean writes: names are numbered per module.
function dump(module, constants, aliases = [], extra = {}) {
  const names = [];
  const id = (n) => {
    if (!names.includes(n)) names.push(n);
    return names.indexOf(n);
  };
  const raw = constants.map(
    ({ name, kind = "thm", range, uses = [], lean, rfl }) => ({
      n: id(name),
      k: kind,
      ...(range && { r: range }),
      ...(lean && { m: 1 }),
      ...(rfl && { d: 1 }),
      u: uses.map(id),
    }),
  );
  return readDump(
    JSON.stringify({ module, names, aliases, constants: raw, ...extra }),
  );
}
const lines = (...text) => text.join("\n") + "\n";
const run = (modules, dumps, sources) =>
  aliveCode({
    modules,
    dumps: new Map(dumps.map((d) => [d.module, d])),
    source: (m) => sources[m.name],
  });

test("a command's keyword is found past doc comments, attributes and modifiers", () => {
  assert.equal(commandKeyword("theorem a : True := trivial", 0), "theorem");
  assert.equal(
    commandKeyword(
      "/-- A /- nested -/ doc. -/\n@[simp, grind =] private lemma a",
      0,
    ),
    "lemma",
  );
  assert.equal(
    commandKeyword("-- note\nprotected noncomputable def f", 0),
    "def",
  );
  assert.equal(commandKeyword('@[x] macro "t" : tactic => skip', 0), "macro");
  assert.equal(commandKeyword("   ", 0), null);
});

test("dead declarations are cut out by position and the rest of the file stays", () => {
  const source = lines(
    "import Mathlib",
    "namespace A",
    "theorem used : True := trivial",
    "theorem dead (n : Nat) :",
    "    n = n := rfl",
    "def alsoUsed := 1",
    "end A",
  );
  const text = withoutDead(source, [
    { range: [3, 0, 3, 30], alive: true },
    { range: [4, 0, 5, 16], alive: false },
    { range: [6, 0, 6, 17], alive: true },
  ]);
  // The line break after a cut declaration stays; blank lines do not count later.
  assert.equal(
    text,
    lines(
      "import Mathlib",
      "namespace A",
      "theorem used : True := trivial",
      "",
      "def alsoUsed := 1",
      "end A",
    ),
  );
});

test("columns count characters, so a cut after an astral character lands in the right place", () => {
  const source = 'def a := "𝔸𝔸" theorem dead : True := trivial\ndef b := 2\n';
  const text = withoutDead(source, [{ range: [1, 14, 1, 44], alive: false }]);
  assert.equal(text, 'def a := "𝔸𝔸" \ndef b := 2\n');
});

test("only declarations are ever cut: a dead macro or a notation stays", () => {
  const source = lines(
    'macro "t" : tactic => `(tactic| skip)',
    "theorem dead : True := trivial",
  );
  const text = withoutDead(source, [
    { range: [1, 0, 1, 37], alive: false },
    { range: [2, 0, 2, 30], alive: false },
  ]);
  assert.equal(text.includes("macro"), true);
  assert.equal(text.includes("theorem"), false);
});

test("a dead part of an alive declaration is not cut twice", () => {
  const source = lines("structure S where", "  a : Nat", "  b : Nat");
  const text = withoutDead(source, [
    { range: [1, 0, 3, 9], alive: true },
    { range: [3, 2, 3, 9], alive: false },
  ]);
  assert.equal(text, source);
});

test("alive code follows what the root needs, across modules and through lifted proofs", () => {
  const modules = [
    { name: "Lib.A", owner: "s" },
    { name: "Lib.Unused", owner: "s" },
    { name: "Submissions.S.Main", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    "Lib.A": lines(
      "theorem helper : True := trivial",
      "theorem unrelated : True := trivial",
      "def value := 3",
    ),
    "Lib.Unused": lines("theorem nothing : True := trivial"),
    "Submissions.S.Main": lines(
      "import Lib.A",
      "theorem bound : 1 = 1 := by",
      "  exact (helper.proof_1 ▸ rfl)",
    ),
    "Candidate.Main": lines(
      "import Submissions.S.Main",
      "export Submissions.S (bound)",
    ),
  };
  const dumps = [
    dump("Lib.A", [
      { name: "helper", range: [1, 0, 1, 32] },
      { name: "helper.proof_1" },
      { name: "unrelated", range: [2, 0, 2, 35] },
      { name: "value", kind: "def", range: [3, 0, 3, 14] },
    ]),
    dump("Lib.Unused", [{ name: "nothing", range: [1, 0, 1, 33] }]),
    dump("Submissions.S.Main", [
      {
        name: "Submissions.S.bound",
        range: [2, 0, 3, 30],
        uses: ["helper.proof_1"],
      },
    ]),
    dump("Candidate.Main", [], [["Candidate.bound", "Submissions.S.bound"]]),
  ];
  const result = run(modules, dumps, sources);
  assert.equal(result.root, "Submissions.S.bound");
  assert.equal(result.modules, 3);
  assert.equal(result.text.includes("helper"), true);
  assert.equal(result.text.includes("unrelated"), false);
  assert.equal(result.text.includes("def value"), false);
  assert.equal(result.text.includes("nothing"), false);
  assert.equal(result.text.includes("export Submissions.S (bound)"), true);
  assert.equal(result.declarations, 2);
  assert.equal(result.removed, 2);
  assert.equal(result.active_bytes, Buffer.byteLength(result.text));
  assert.equal(result.gzip_bytes, gzipSync(result.text, { level: 9 }).length);
});

test("constants declared together are alive together, and an inductive's constructors come with it", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "inductive T where",
      "  | a | b",
      "theorem bound : T.a = T.a := rfl",
      "theorem gone : T.b = T.b := rfl",
    ),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump("M", [
      { name: "T", kind: "induct", range: [1, 0, 2, 9], uses: ["T.a", "T.b"] },
      { name: "T.a", kind: "ctor", range: [1, 0, 2, 9], uses: ["T"] },
      { name: "T.b", kind: "ctor", range: [1, 0, 2, 9], uses: ["T"] },
      { name: "T.rec", kind: "rec", uses: ["T"] },
      { name: "bound", range: [3, 0, 3, 32], uses: ["T.a"] },
      { name: "gone", range: [4, 0, 4, 32], uses: ["T.b"] },
    ]),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(text.includes("inductive T"), true);
  assert.equal(text.includes("theorem gone"), false);
});

test("helpers of tactics and macros stay alive in a file that is involved, wherever they are used", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Dead", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "def helper : Lean.MetaM Unit := pure ()",
      "def plain := 1",
      'elab "t" : tactic => helper',
      "theorem bound : True := trivial",
    ),
    Dead: lines("def metaHelper : Lean.MetaM Unit := pure ()"),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump("M", [
      { name: "helper", kind: "def", range: [1, 0, 1, 40], lean: true },
      { name: "plain", kind: "def", range: [2, 0, 2, 14] },
      { name: "bound", range: [4, 0, 4, 30] },
    ]),
    dump("Dead", [
      { name: "metaHelper", kind: "def", range: [1, 0, 1, 44], lean: true },
    ]),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(text.includes("def helper"), true);
  assert.equal(text.includes("def plain"), false);
  assert.equal(text.includes("elab"), true);
  assert.equal(text.includes("metaHelper"), false);
});

test("a submission without a root, or a missing graph, is an error", () => {
  const modules = [{ name: "M", owner: "s" }];
  const sources = { M: "" };
  assert.throws(
    () => run(modules, [dump("M", [{ name: "x" }])], sources),
    /Candidate.bound is not declared/,
  );
  assert.throws(() => run(modules, [], sources), /No declaration graph for M/);
});

test("a namespace or section that only sets up context for dead code goes with it", () => {
  const source = lines(
    "import Mathlib",
    "open Foo",
    "namespace Dead",
    "open Bar",
    "variable (n : Nat)",
    "section Inner",
    "open Baz",
    "end Inner",
    "end Dead",
    "namespace Live",
    "open Qux",
    "theorem alive : True := trivial",
    "end Live",
  );
  assert.equal(
    withoutEmptyBlocks(source),
    lines(
      "import Mathlib",
      "open Foo",
      "namespace Live",
      "open Qux",
      "theorem alive : True := trivial",
      "end Live",
    ),
  );
});

test("a block with anything that outlives it, or that is not understood, stays whole", () => {
  for (const inside of [
    'notation "x" => 1',
    "attribute [simp] foo",
    "instance : Inhabited Nat := ⟨0⟩",
    'macro "t" : tactic => `(tactic| skip)',
    "  continuation of something",
  ]) {
    const source = lines("namespace A", "open B", inside, "end A");
    assert.equal(withoutEmptyBlocks(source), source);
  }
  // A nested block with content keeps every block around it.
  const nested = lines("namespace A", "section", "def x := 1", "end", "end A");
  assert.equal(withoutEmptyBlocks(nested), nested);
  // Local notation and scoped context are only for the block itself.
  const local = lines(
    "section",
    'local notation "y" => 2',
    "attribute [local simp] foo",
    "end",
  );
  assert.equal(withoutEmptyBlocks(local), "");
});

test("mutual blocks and stray ends are not mistaken for namespaces", () => {
  const mutual = lines("namespace A", "mutual", "def f := 1", "end", "end A");
  assert.equal(withoutEmptyBlocks(mutual), mutual);
  const stray = lines("end", "namespace B", "end B", "end");
  assert.equal(withoutEmptyBlocks(stray), lines("end", "end"));
});

test("checks, printouts and examples leave nothing behind and are not counted", () => {
  const source = lines(
    "theorem a : True := trivial",
    "#print axioms a",
    "#eval do",
    "  let x := 1",
    "",
    "  IO.println x",
    "example : True := by",
    "  have : 1 = 1 := rfl",
    "",
    "  trivial",
    "#guard_msgs in",
    "theorem b : True := trivial",
    "exampleOfSomething := 1",
  );
  assert.equal(
    withoutDebris(source),
    lines(
      "theorem a : True := trivial",
      "theorem b : True := trivial",
      "exampleOfSomething := 1",
    ),
  );
});

test("alive code leaves out the comments, checks and empty blocks of the files it keeps", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "/-! Module doc with theorem and #print words -/",
      "namespace Dead",
      "open Foo",
      "theorem dead : True := trivial",
      "end Dead",
      "theorem bound : True := trivial -- trailing note",
      "#print axioms bound",
      "example : True := trivial",
    ),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump("M", [
      { name: "Dead.dead", range: [4, 0, 4, 31] },
      { name: "bound", range: [6, 0, 6, 31] },
    ]),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(
    text,
    lines("theorem bound : True := trivial", "export M (bound)"),
  );
});

test("the commands that apply to a dead declaration go with it, and only those", () => {
  const source = lines(
    "namespace A",
    "omit [Fintype F] in",
    "theorem dead : True := trivial",
    "open Foo",
    "set_option maxHeartbeats 400000 in",
    "open Bar in",
    "omit [A]",
    "  [B] in",
    "/-- doc -/",
    "theorem alsoDead : True := trivial",
    "omit [C] in",
    "theorem alive : True := trivial",
    "end A",
  );
  const text = withoutDead(source, [
    { range: [3, 0, 3, 30], alive: false },
    { range: [9, 0, 10, 34], alive: false },
    { range: [12, 0, 12, 30], alive: true },
  ]);
  assert.equal(
    text,
    lines(
      "namespace A",
      "",
      "open Foo",
      "",
      "omit [C] in",
      "theorem alive : True := trivial",
      "end A",
    ),
  );
});

test("what the text of an alive declaration names stays, even if its proof does not use it", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "theorem unusedArg : True := trivial",
      "theorem bound : True := by simp [unusedArg]",
      "theorem other : True := trivial",
    ),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump(
      "M",
      [
        { name: "unusedArg", range: [1, 0, 1, 33] },
        { name: "bound", range: [2, 0, 2, 41] },
        { name: "other", range: [3, 0, 3, 31] },
      ],
      [],
      { references: [["bound", "unusedArg"]] },
    ),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(text.includes("theorem unusedArg"), true);
  assert.equal(text.includes("theorem other"), false);
});

test("what an alive file names outside any declaration stays, and a dead file's does not", () => {
  const modules = [
    { name: "A", owner: "s" },
    { name: "B", owner: "s" },
    { name: "Dead", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    A: lines(
      "theorem simpLemma : True := trivial",
      "theorem lemmaForDead : True := trivial",
    ),
    B: lines(
      "import A",
      "attribute [simp] simpLemma",
      "theorem bound : True := trivial",
    ),
    Dead: lines("import A", "attribute [simp] lemmaForDead"),
    "Candidate.Main": lines("export B (bound)"),
  };
  const dumps = [
    dump("A", [
      { name: "simpLemma", range: [1, 0, 1, 35] },
      { name: "lemmaForDead", range: [2, 0, 2, 38] },
    ]),
    dump("B", [{ name: "bound", range: [3, 0, 3, 30] }], [], {
      context: ["simpLemma"],
    }),
    dump("Dead", [], [], { context: ["lemmaForDead"] }),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(text.includes("theorem simpLemma"), true);
  assert.equal(text.includes("lemmaForDead"), false);
});

test("the attributes of a command are read from its list, however they are written", () => {
  const head = commandHead(
    "/-- doc -/\n@[simp↓, local norm_cast, to_additive (attr := simp), ext]\nprivate lemma a",
    0,
  );
  assert.equal(head.keyword, "lemma");
  assert.deepEqual(head.attributes, [
    "simp",
    "norm_cast",
    "to_additive",
    "ext",
  ]);
  assert.deepEqual(commandHead("@[simp] @[inline]\ndef f", 0).attributes, [
    "simp",
    "inline",
  ]);
  assert.deepEqual(commandHead("theorem t", 0).attributes, []);
});

test("a simp lemma proved by rfl, or a simp definition, stays when it only mentions what is alive", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Dead", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "def helper := 1",
      "@[simp] theorem rflLemma : helper = 1 := rfl",
      "@[simp] theorem otherLemma : helper + 0 = 1 := by simp [helper]",
      "@[simp] def unfolded := helper",
      "instance : Inhabited Nat := ⟨helper⟩",
      "@[inline] def inlined := 2",
      "def onlyDead := 3",
      "@[simp] theorem needsDead : onlyDead = 3 := rfl",
      "theorem bound : helper = 1 := by simp",
    ),
    Dead: lines("@[simp] theorem simpInDead : True := rfl"),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump("M", [
      { name: "helper", kind: "def", range: [1, 0, 1, 15] },
      { name: "rflLemma", range: [2, 0, 2, 44], uses: ["helper"], rfl: true },
      { name: "otherLemma", range: [3, 0, 3, 64], uses: ["helper"] },
      { name: "unfolded", kind: "def", range: [4, 0, 4, 28], uses: ["helper"] },
      {
        name: "instInhabitedNat",
        kind: "def",
        range: [5, 0, 5, 37],
        uses: ["helper"],
      },
      { name: "inlined", kind: "def", range: [6, 0, 6, 28] },
      { name: "onlyDead", kind: "def", range: [7, 0, 7, 17] },
      {
        name: "needsDead",
        range: [8, 0, 8, 47],
        uses: ["onlyDead"],
        rfl: true,
      },
      { name: "bound", range: [9, 0, 9, 36], uses: ["helper"] },
    ]),
    dump("Dead", [{ name: "simpInDead", range: [1, 0, 1, 42], rfl: true }]),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  for (const kept of [
    "def helper",
    "rflLemma",
    "def unfolded",
    "theorem bound",
  ])
    assert.equal(text.includes(kept), true, kept);
  // A simp lemma that the proof used is in its term, so it is only alive when something names it;
  // one that mentions something dead cannot have been used by anything alive.
  for (const gone of [
    "otherLemma",
    "instance : Inhabited",
    "inlined",
    "onlyDead",
    "needsDead",
    "simpInDead",
  ])
    assert.equal(text.includes(gone), false, gone);
});

test("ambient declarations that depend on each other join one after the other", () => {
  const modules = [
    { name: "M", owner: "s" },
    { name: "Candidate.Main", owner: "s" },
  ];
  const sources = {
    M: lines(
      "def base := 1",
      "@[simp] theorem second : base = 1 := rfl",
      "@[simp] theorem third : second = second := rfl",
      "theorem bound : base = base := rfl",
    ),
    "Candidate.Main": lines("export M (bound)"),
  };
  const dumps = [
    dump("M", [
      { name: "base", kind: "def", range: [1, 0, 1, 13] },
      { name: "second", range: [2, 0, 2, 40], uses: ["base"], rfl: true },
      { name: "third", range: [3, 0, 3, 46], uses: ["second"], rfl: true },
      { name: "bound", range: [4, 0, 4, 34], uses: ["base"] },
    ]),
    dump("Candidate.Main", [], [["Candidate.bound", "bound"]]),
  ];
  const { text } = run(modules, dumps, sources);
  assert.equal(
    text.includes("theorem second") && text.includes("theorem third"),
    true,
  );
});
