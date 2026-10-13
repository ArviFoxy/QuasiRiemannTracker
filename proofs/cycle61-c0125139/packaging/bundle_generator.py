"""Deterministic packaging rehearsal; emitted sources require their own replay.

Keep originals and a transformation map. Dependency pins remain unchanged.
Imports and module scopes change; exact-source qualification repairs are recorded.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import runpy


LOCAL = {"Cycle61", "Cycle25", "LocalMoment", "ZetaZeroFree"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def mask_comments(text):
    chars = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text[i:i + 2] == "/-":
                chars[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text[i:i + 2] == "-/":
                chars[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif text[i:i + 2] == "/-":
            chars[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text[i:i + 2] == "--":
            while i < len(text) and text[i] != "\n":
                chars[i] = " "
                i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
    if depth:
        raise ValueError("Unterminated comment")
    return "".join(chars)


def remove_headers(text, expected):
    found, lines, changes = [], [], []
    in_header = True
    masked = mask_comments(text).splitlines(keepends=True)
    original = text.splitlines(keepends=True)
    for number, (line, code) in enumerate(zip(original, masked), 1):
        active = code.strip()
        if in_header and active:
            match = re.fullmatch(r"import\s+([A-Za-z_0-9.\s]+)", active)
            if match:
                found.extend(match[1].split())
                # Replace code only: retain copyright/documentation comments.
                line = "".join(" " if c != "\n" and m != " " else c
                               for c, m in zip(line, code))
                changes.append(number)
            else:
                if active in {"prelude", "module"}:
                    raise ValueError("Module/prelude sources need an explicit packaging rule")
                in_header = False
        lines.append(line)
    if set(found) != set(expected):
        raise ValueError(f"Header disagreement: {found} versus {expected}")
    return "".join(lines), changes


def token_mask(text):
    masked = list(mask_comments(text))
    i = 0
    while i < len(text):
        if masked[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            for j in range(start, min(i, len(text))):
                if masked[j] != "\n":
                    masked[j] = " "
        else:
            i += 1
    return "".join(masked)


def apply_change(body, change, name):
    if "code_pattern" in change:
        matches = list(re.finditer(change["code_pattern"], token_mask(body)))
        if len(matches) != change["count"]:
            raise ValueError("Token repair occurrence changed: " + name)
        for match in reversed(matches):
            body = body[:match.start()] + match.expand(change["new"]) + body[match.end():]
        return body
    if "pattern" in change:
        if len(re.findall(change["pattern"], body)) != change["count"]:
            raise ValueError("Qualification repair occurrence changed: " + name)
        return re.sub(change["pattern"], change["new"], body)
    if body.count(change["old"]) != change["count"]:
        raise ValueError("Qualification repair occurrence changed: " + name)
    return body.replace(change["old"], change["new"])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, required=True)
    ap.add_argument("--entry", action="append", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--frozen-build", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    ap.add_argument("--repairs", type=Path, help="Exact-source, counted literal qualification repairs")
    ap.add_argument("--modules-per-bundle", type=int, default=3)
    args = ap.parse_args()
    if not 1 <= args.modules_per_bundle <= 8:
        ap.error("Bundle size must be between 1 and 8 modules")
    project, out = args.project.resolve(), args.out.resolve()
    frozen = args.frozen_build.resolve()
    source = frozen / "src"
    evidence = args.evidence.resolve()
    inventory_path = frozen / "input-inventory.json"
    inventory = json.loads(inventory_path.read_text())
    # Verify every closed input before emitting any transformed source.
    bindings = {}
    for name, item in inventory["sources"].items():
        current = project / "formalization" / item["path"]
        snap = source / item["path"]
        current_bytes, frozen_bytes = current.read_bytes(), snap.read_bytes()
        if current_bytes != frozen_bytes or digest(frozen_bytes) != item["sha256"]:
            raise ValueError("Current/frozen source mismatch: " + name)
        bindings[name] = item["sha256"]
    (evidence / "source-binding.json").write_text(json.dumps(dict(input_inventory_sha256=digest(inventory_path.read_bytes()), frozen_build=str(frozen), modules=bindings, verified_current_and_frozen=True), indent=2)+"\n")
    parse = runpy.run_path(str(project / "tools/rebuild_source.py"))["imports"]
    repairs = json.loads(args.repairs.read_text()) if args.repairs else {}
    order, records, active = [], {}, set()

    def visit(name):
        if name.split(".")[0] not in LOCAL or name in records:
            return
        if name in active:
            raise ValueError("Dependency cycle: " + name)
        active.add(name)
        path = source.joinpath(*name.split(".")).with_suffix(".lean")
        data = path.read_bytes()
        dependencies = parse(data.decode("utf-8"))
        for dep in sorted(dependencies):
            visit(dep)
        body, removed = remove_headers(data.decode("utf-8"), dependencies)
        repair = repairs.get(name)
        if repair:
            if repair["source_sha256"] != digest(data):
                raise ValueError("Qualification repair source changed: " + name)
            for change in repair["replacements"]:
                body = apply_change(body, change, name)
        records[name] = dict(source_sha256=digest(data), bytes=len(data), imports=dependencies,
                             body=body, original=data, removed_import_lines=removed,
                             qualification_repairs=repair)
        active.remove(name)
        order.append(name)

    for entry in sorted(set(args.entry)):
        visit(entry)
    groups = []
    for name in order:
        if not groups or len(groups[-1]) >= args.modules_per_bundle or sum(
                records[n]["bytes"] for n in groups[-1]) + records[name]["bytes"] > 900_000:
            groups.append([])
        groups[-1].append(name)
    mapping = {name: f"Candidate.Bundles.B{i:03d}" for i, group in enumerate(groups) for name in group}
    if len(groups) + 1 > 256:
        raise ValueError("Saved 256-file packaging cap exceeded")
    out.mkdir(parents=True, exist_ok=False)
    bundle_records = []
    for i, group in enumerate(groups):
        module = f"Candidate.Bundles.B{i:03d}"
        imports = sorted({mapping.get(dep, dep) for name in group for dep in records[name]["imports"]}
                         - {module})
        text = "/- Packaging rehearsal. Original notices retained; separate replay required. -/\n"
        text += "".join("import " + dep + "\n" for dep in imports)
        for name in group:
            record = records[name]
            original = evidence / "originals" / (name.replace(".", "/") + ".lean")
            original.parent.mkdir(parents=True, exist_ok=True)
            original.write_bytes(record["original"])
            text += f"\n/- BEGIN ORIGINAL {name}; sha256 {record['source_sha256']} -/\nsection\n"
            text += record["body"] + f"\nend\n/- END ORIGINAL {name} -/\n"
        dest = out / "src" / (module.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
        bundle_records.append(dict(module=module, imports=imports, originals=group,
                                   sha256=digest(dest.read_bytes()), bytes=dest.stat().st_size))
    manifest = dict(kind="frozen_source_transformed_package_unverified", entries=args.entry,
                    transformation="Dependency-ordered grouping, import remapping, anonymous sections, and recorded exact-source qualification repairs",
                    modules={n: {k: v for k, v in r.items() if k not in {"body", "original"}}
                             | {"bundle": mapping[n]} for n, r in records.items()},
                    bundles=bundle_records,
                    limitations="No original object authenticates this transformed package. Not a final proof or accepted submission.")
    (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(dict(modules=len(order), bundles=len(groups),
                          bytes=sum(b["bytes"] for b in bundle_records), out=str(out))))


if __name__ == "__main__":
    main()
