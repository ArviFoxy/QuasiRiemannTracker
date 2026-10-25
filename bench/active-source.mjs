// The text a Lean proof is written in: comments removed and whitespace
// normalized, so documentation and layout do not count as proof.
// String and character literals are kept whole, so markers inside them stay.
const identifier = /[A-Za-z0-9_'.]/;
const character = /^'(?:\\(?:x[0-9a-fA-F]{2}|u\{?[0-9a-fA-F]+\}?|.)|[^'\\\n])'/;

// The source with its comments taken out and everything else, layout included,
// as it was.
export function withoutComments(source) {
  let out = "",
    depth = 0,
    i = 0;
  while (i < source.length) {
    const pair = source.slice(i, i + 2);
    if (depth) {
      // Block comments nest in Lean.
      if (pair === "/-") {
        depth++;
        i += 2;
      } else if (pair === "-/") {
        depth--;
        i += 2;
        if (!depth) out += " ";
      } else i++;
    } else if (pair === "/-") {
      depth = 1;
      i += 2;
    } else if (pair === "--") {
      while (i < source.length && source[i] !== "\n") i++;
    } else if (source[i] === '"') {
      let end = i + 1;
      while (end < source.length && source[end] !== '"')
        end += source[end] === "\\" ? 2 : 1;
      out += source.slice(i, end + 1);
      i = end + 1;
    } else if (source[i] === "'" && !identifier.test(source[i - 1] ?? "")) {
      // 'x' is a character, but h' is a name.
      const match = character.exec(source.slice(i, i + 12));
      out += match ? match[0] : "'";
      i += match ? match[0].length : 1;
    } else out += source[i++];
  }
  return out;
}

// One line per line of code: indentation and runs of spaces collapsed, no blank lines.
export function withoutLayout(source) {
  return source
    .split("\n")
    .map((line) => line.replace(/[ \t]+/g, " ").trim())
    .filter(Boolean)
    .join("\n");
}

export const activeSource = (source) => withoutLayout(withoutComments(source));
