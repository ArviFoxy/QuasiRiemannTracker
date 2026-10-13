// Read dependency names as data; setup builds only files in the pinned library.
export function upstreamImports(source) {
  let clean = "",
    depth = 0,
    quoted = false;
  for (let i = 0; i < source.length; i++) {
    const pair = source.slice(i, i + 2),
      ch = source[i];
    if (depth) {
      if (pair === "/-") {
        depth++;
        i++;
        clean += "  ";
      } else if (pair === "-/") {
        depth--;
        i++;
        clean += "  ";
      } else clean += ch === "\n" ? "\n" : " ";
    } else if (quoted) {
      if (ch === "\\") {
        i++;
        clean += "  ";
      } else {
        if (ch === '"') quoted = false;
        clean += ch === "\n" ? "\n" : " ";
      }
    } else if (pair === "/-") {
      depth++;
      i++;
      clean += "  ";
    } else if (pair === "--") {
      while (i < source.length && source[i] !== "\n") {
        clean += " ";
        i++;
      }
      clean += "\n";
    } else if (ch === '"') {
      quoted = true;
      clean += " ";
    } else clean += ch;
  }
  const result = new Set();
  for (const match of clean.matchAll(
    /^\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Z][A-Za-z0-9_.]*(?:\s+[A-Z][A-Za-z0-9_.]*)*)/gm,
  ))
    for (const name of match[1].split(/\s+/))
      if (/^OAI(?:\.[A-Za-z0-9_]+)+$/.test(name)) result.add(name);
  return [...result].sort();
}
