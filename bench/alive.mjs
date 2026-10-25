// Alive code: the Lean source a submission's root proof needs, and nothing else.
//
// Declarations are followed from Candidate.bound through everything their types
// and values mention, using the declaration graph that bench/alive/Dump.lean
// reads from the compiled modules. A declaration that nothing alive needs is left
// out of its file, and a file with no alive declaration is left out altogether.
// What remains is read the way size is counted everywhere else: without comments
// or layout, in build order, gzipped.
//
// Everything that is not a declaration of the proof stays in a file that has an
// alive declaration: imports, namespaces, open and variable lines, notation,
// macros and tactics. They cannot be told apart from what an alive declaration
// uses, so counting them keeps code from hiding there. Definitions that deal in
// Lean's own syntax and meta types are alive wherever their file is, because
// that is where tactics and macros keep their helpers.
import { createHash } from "node:crypto";
import {
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { gunzipSync, gzipSync } from "node:zlib";
import { withoutComments, withoutLayout } from "./active-source.mjs";

export const ROOT = "Candidate.bound";

// What a declaration leaves behind when it is dead: nothing in the environment.
// Anything else at a declaration's position (a macro, a tactic, a notation) is
// kept.
const removable = new Set([
  "theorem",
  "lemma",
  "def",
  "abbrev",
  "instance",
  "structure",
  "class",
  "inductive",
  "coinductive",
  "opaque",
  "axiom",
  "example",
  "irreducible_def",
]);
const modifiers = new Set([
  "private",
  "protected",
  "noncomputable",
  "unsafe",
  "partial",
  "nonrec",
  "public",
  "meta",
  "local",
  "scoped",
]);

// The first keyword of the command that starts at an offset, after any doc
// comment, attributes and modifiers.
export function commandKeyword(source, start) {
  let i = start;
  for (;;) {
    while (i < source.length && /\s/.test(source[i])) i++;
    if (source.startsWith("/-", i)) {
      let depth = 0;
      for (; i < source.length; i++) {
        if (source.startsWith("/-", i)) {
          depth++;
          i++;
        } else if (source.startsWith("-/", i)) {
          i++;
          if (!--depth) {
            i++;
            break;
          }
        }
      }
    } else if (source.startsWith("--", i)) {
      while (i < source.length && source[i] !== "\n") i++;
    } else if (source.startsWith("@[", i)) {
      let depth = 0;
      for (; i < source.length; i++) {
        if (source[i] === "[") depth++;
        else if (source[i] === "]" && !--depth) {
          i++;
          break;
        }
      }
    } else {
      const word = /^[A-Za-z_]+/.exec(source.slice(i, i + 40))?.[0];
      if (!word) return null;
      if (!modifiers.has(word)) return word;
      i += word.length;
    }
  }
}

// Offsets into a string of Lean positions: lines count from 1 and columns count
// characters, not UTF-16 units, from 0.
function offsets(source) {
  const starts = [0];
  for (let i = source.indexOf("\n"); i >= 0; i = source.indexOf("\n", i + 1))
    starts.push(i + 1);
  return (line, column) => {
    const start = starts[line - 1];
    if (start === undefined) return source.length;
    let end = starts[line] === undefined ? source.length : starts[line] - 1;
    if (!/[\ud800-\udfff]/.test(source.slice(start, end)))
      return Math.min(start + column, end);
    let i = start;
    for (let seen = 0; seen < column && i < end; seen++)
      i += source.codePointAt(i) > 0xffff ? 2 : 1;
    return i;
  };
}

// The text of a file without its dead declarations. ranges are
// [line, column, endLine, endColumn] for each group of constants declared
// together, with whether any of them is alive.
export function withoutDead(source, groups) {
  const at = offsets(source);
  const spans = groups.map(({ range, alive }) => ({
    start: at(range[0], range[1]),
    end: at(range[2], range[3]),
    alive,
  }));
  const kept = spans.filter(
    ({ start, alive }) =>
      alive || !removable.has(commandKeyword(source, start)),
  );
  const dead = spans
    .filter((s) => !kept.includes(s))
    // Inside a kept declaration (a structure field, a deriving clause).
    .filter((s) => !kept.some((k) => k.start <= s.start && s.end <= k.end))
    .sort((a, b) => a.start - b.start || b.end - a.end);
  let out = "",
    from = 0;
  for (const { start, end } of dead) {
    if (end <= from) continue;
    out += source.slice(from, Math.max(from, start));
    from = Math.max(from, end);
  }
  return out + source.slice(from);
}

// What a namespace or section can hold without mattering once the declarations
// in it are gone: scoped context, and nothing that outlives the block.
const context =
  /^\s*(?:$|--|(?:open|variable|universe|omit|include|set_option|section|namespace|end)\b|noncomputable\s+section\b|attribute\s+\[local\b|local\s+(?:notation|infix|infixl|infixr|prefix|postfix|macro|syntax|macro_rules)\b|scoped\b)/;

// Commands that report or check and leave nothing behind: #print, #check, #eval
// and the like, and examples. Each runs to the next line that starts at the
// margin. Meant for text without comments, so that none of them is cut short.
export function withoutDebris(source) {
  const lines = source.split("\n"),
    out = [];
  for (let i = 0; i < lines.length; i++) {
    if (/^(?:#[a-z_]+|example)\b/.test(lines[i])) {
      while (i + 1 < lines.length && /^(?:\s*$|\s+\S)/.test(lines[i + 1])) i++;
    } else out.push(lines[i]);
  }
  return out.join("\n");
}

// Namespaces and sections that only set up context for declarations that are
// gone, whole, so the opens and variables of dead code do not count as alive.
// A block with anything else in it stays, with all of its context.
export function withoutEmptyBlocks(source) {
  const lines = source.split("\n"),
    drop = new Set(),
    stack = [];
  const holds = () => {
    if (stack.length) stack.at(-1).content = true;
  };
  lines.forEach((line, i) => {
    if (/^(?:noncomputable\s+)?(?:section|namespace)\b/.test(line))
      stack.push({ start: i, content: false });
    else if (/^mutual\b/.test(line)) stack.push({ start: i, content: true });
    else if (/^end\b/.test(line)) {
      const block = stack.pop();
      if (!block) return;
      if (block.content) holds();
      else for (let j = block.start; j <= i; j++) drop.add(j);
    } else if (!context.test(line)) holds();
  });
  return lines.filter((_, i) => !drop.has(i)).join("\n");
}

// A dump read back into names: { module, aliases, constants: [{ name, kind,
// range, lean, uses: [names] }] }.
export function readDump(text) {
  const raw = JSON.parse(text);
  const names = raw.names;
  return {
    module: raw.module,
    aliases: raw.aliases,
    constants: raw.constants.map((c) => ({
      name: names[c.n],
      kind: c.k,
      range: c.r ?? null,
      lean: Boolean(c.m),
      uses: c.u.map((i) => names[i]),
    })),
  };
}

export const readDumpFile = (bytes) => readDump(gunzipSync(bytes).toString());

// An auxiliary constant (a proof lifted out of a theorem, a match, an equation)
// has no position of its own: it belongs to the declaration whose name it extends.
function declaredAs(name, ranges) {
  for (let n = name; ; ) {
    if (ranges.has(n)) return n;
    const cut = n.lastIndexOf(".");
    if (cut < 0) return null;
    n = n.slice(0, cut);
  }
}

// modules: the submission's modules in build order, each { name, owner };
// dumps: Map of module name to its dump; source(module) gives its text.
export function aliveCode({ modules, dumps, source, root = ROOT }) {
  const consts = new Map(),
    aliases = new Map(),
    inModule = new Map();
  for (const m of modules) {
    const dump = dumps.get(m.name);
    if (!dump) throw Error(`No declaration graph for ${m.name}`);
    inModule.set(m.name, dump.constants);
    for (const c of dump.constants)
      consts.set(c.name, { ...c, module: m.name });
    for (const [alias, target] of dump.aliases) aliases.set(alias, target);
  }
  let target = root;
  for (
    let hops = 0;
    !consts.has(target) && aliases.has(target) && hops < 16;
    hops++
  )
    target = aliases.get(target);
  if (!consts.has(target))
    throw Error(`${root} is not declared in this submission`);

  // Everything the root needs, and the helpers of the tactics and macros in
  // the files that are involved.
  const alive = new Set(),
    liveModules = new Set([consts.get(target).module]),
    queue = [target];
  // The file that names the root is part of the proof even if it declares nothing.
  for (const m of modules)
    if (m.name === "Candidate.Main") liveModules.add(m.name);
  for (;;) {
    while (queue.length) {
      const name = queue.pop();
      if (alive.has(name)) continue;
      const c = consts.get(name);
      if (!c) continue;
      alive.add(name);
      liveModules.add(c.module);
      for (const used of c.uses) if (!alive.has(used)) queue.push(used);
    }
    for (const c of consts.values())
      if (
        c.lean &&
        c.kind !== "thm" &&
        liveModules.has(c.module) &&
        !alive.has(c.name)
      )
        queue.push(c.name);
    if (!queue.length) break;
  }

  const parts = [];
  let declarations = 0,
    removed = 0;
  for (const m of modules) {
    if (!liveModules.has(m.name)) continue;
    const constants = inModule.get(m.name);
    const ranges = new Map(
      constants.filter((c) => c.range).map((c) => [c.name, c.range]),
    );
    const groups = new Map();
    for (const c of constants) {
      const home = declaredAs(c.name, ranges);
      if (home === null) continue;
      const key = ranges.get(home).join(",");
      const group = groups.get(key) ?? {
        range: ranges.get(home),
        alive: false,
      };
      group.alive ||= alive.has(c.name);
      groups.set(key, group);
    }
    const text = source(m);
    const kept = withoutEmptyBlocks(
      withoutDebris(withoutComments(withoutDead(text, [...groups.values()]))),
    );
    declarations += [...groups.values()].filter((g) => g.alive).length;
    removed += [...groups.values()].filter((g) => !g.alive).length;
    const active = withoutLayout(kept);
    if (active) parts.push(active);
  }
  const text = parts.join("\n") + "\n";
  return {
    text,
    root: target,
    modules: liveModules.size,
    declarations,
    removed,
    active_bytes: Buffer.byteLength(text),
    gzip_bytes: gzipSync(text, { level: 9 }).length,
  };
}

// node --max-old-space-size=8192 bench/alive.mjs [ID...]
// Works out the alive code of each submission whose declaration graphs have been
// kept (bench/measure.py does that as submissions finish compiling) and writes
// ALIVE/<id>.json with the sizes and ALIVE/<id>.txt.gz with the text, so that it
// can be read.
const invoked =
  process.argv[1] &&
  import.meta.url === pathToFileURL(resolve(process.argv[1])).href;
if (invoked) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const bench = resolve(process.env.QRH_BENCH_ROOT ?? join(root, ".bench"));
  const out = join(bench, "alive");
  mkdirSync(out, { recursive: true });
  const ids =
    process.argv.length > 2
      ? process.argv.slice(2)
      : readdirSync(join(bench, "plans"))
          .map((f) => f.replace(/\.json$/, ""))
          .sort();
  const cache = new Map();
  const graph = (key) => {
    if (!cache.has(key))
      cache.set(
        key,
        readDumpFile(readFileSync(join(bench, "dumps", `${key}.json.gz`))),
      );
    return cache.get(key);
  };
  for (const id of ids) {
    const index = join(bench, "dumps", "index", `${id}.json`);
    if (!existsSync(index)) {
      console.log(`${id}: no declaration graphs yet`);
      continue;
    }
    const plan = JSON.parse(
      readFileSync(join(bench, "plans", `${id}.json`), "utf8"),
    );
    const keys = JSON.parse(readFileSync(index, "utf8"));
    if (keys.length !== plan.modules.length)
      throw Error(`${id}: the graphs are of another list of modules`);
    const dumps = new Map(plan.modules.map((m, i) => [m.name, graph(keys[i])]));
    const source = (m) => {
      const bytes = readFileSync(join(root, "submissions", m.owner, m.path));
      if (createHash("sha256").update(bytes).digest("hex") !== m.sha256)
        throw Error(`${id}: ${m.name} changed since it was compiled`);
      return bytes.toString();
    };
    const { text, ...result } = aliveCode({
      modules: plan.modules,
      dumps,
      source,
    });
    writeFileSync(
      join(out, `${id}.json`),
      JSON.stringify(
        {
          id,
          source_tree: plan.source_tree,
          total_modules: plan.modules.length,
          ...result,
        },
        null,
        2,
      ) + "\n",
    );
    writeFileSync(join(out, `${id}.txt.gz`), gzipSync(text, { level: 9 }));
    console.log(
      `${id}: ${result.modules}/${plan.modules.length} modules, ${result.declarations} declarations alive, ` +
        `${result.removed} dead, ${(result.active_bytes / 2 ** 20).toFixed(2)} MiB, ` +
        `${(result.gzip_bytes / 2 ** 10).toFixed(0)} KiB gzipped`,
    );
    if (cache.size > 12000) cache.clear();
  }
}
