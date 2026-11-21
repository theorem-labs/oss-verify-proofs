"""Compare a generated walk with a shipped witness, without running Rocq.

The supplied reference pins must be reachable from the shipped entry proof.
Reference-only declarations are distinguished from required missing declarations;
every generated declaration/tactic is also checked for retained R-typed references.
"""
import argparse
import json
from dataclasses import replace
from pathlib import Path
import subprocess

from . import carriers, census, units
from .rocqparse import Index, REF_RE, blank_text, parse_file


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo")
    parser.add_argument("--unit", required=True)
    parser.add_argument("--reference", default="origin/main")
    parser.add_argument("--reference-entry", required=True, help="BudgetWit MODULE.DECL, without BudgetWit prefix")
    parser.add_argument("--pin", action="append", required=True, help="reference MODULE.DECL=released MODULE.DECL")
    parser.add_argument("--generated", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    try:
        return check(args)
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print(f"control: {error}")
        return 1


def walk_scope(reference_modules, reached_modules, excluded):
    """The reference files this comparison reads, and the ones it leaves alone.

    One twin directory can hold several witnesses: other images of the same
    harness, and walks the compared entry never reaches. Those files have no
    counterpart in the generated walk, so they are not this comparison's
    reference. Every declaration of a file the entry does reach must still pair,
    which is what keeps a shrunk comparison from passing unnoticed.
    """
    walk = (reference_modules & reached_modules) - excluded
    return walk, sorted(reference_modules - reached_modules - excluded)


def check(args):
    unit = units.load(args.unit, args.repo)
    ref_dir = unit.lib_dir / unit.twin_dir
    ref_package = unit.package + "." + unit.twin_dir
    validated = set()

    def validate(path):
        path = Path(path)
        if path in validated:
            return
        relative = path.relative_to(unit.repo).as_posix()
        source = subprocess.run(["git", "show", args.reference + ":" + relative],
                                cwd=unit.repo, capture_output=True, check=True).stdout
        if source != path.read_bytes():
            raise ValueError(f"{relative}: checkout differs from {args.reference}; use a worktree of the pinned source")
        validated.add(path)

    for path in sorted(ref_dir.rglob("*.v")):
        validate(path)
    reference = Index(ref_dir, ref_package)
    profile = carriers.detect(unit.lib_dir)
    profile = replace(profile, package=unit.package)
    source = Index(unit.lib_dir, unit.package, profile=profile, twin_dir=unit.twin_dir)
    entry = ref_package + "." + args.reference_entry
    if entry not in reference.by_full:
        raise ValueError("reference entry not found: " + entry)

    def closure(index, initial):
        reached, queue = set(), list(initial)
        while queue:
            name = queue.pop()
            if name in reached:
                continue
            item = index.by_full.get(name)
            if item is None:
                raise ValueError("reference declaration not found: " + name)
            reached.add(name)
            for match in REF_RE.finditer(blank_text(item.text)):
                target = index.resolve(match[1], item.module)
                if target and target != name and target not in reached:
                    queue.append(target)
        return reached

    reference_reached = closure(reference, [entry])
    pins, roots = [], []
    for text in args.pin:
        if text.count("=") != 1:
            raise ValueError("--pin needs reference MODULE.DECL=released MODULE.DECL")
        before, after = text.split("=", 1)
        reference_name, source_name = ref_package + "." + before, unit.qualify(after)
        if reference_name not in reference_reached:
            raise ValueError(f"{reference_name}: not reachable from {entry}")
        if source_name not in source.by_full:
            raise ValueError("released pin not found: " + source_name)
        ref_item, src_item = reference.by_full[reference_name], source.by_full[source_name]
        if profile.twin_name(src_item.name) != ref_item.name:
            raise ValueError(f"pin name mismatch: {source_name} -> {reference_name}")
        pins.append({"reference": reference_name, "released": source_name,
                     "reference_file": reference.files[ref_item.module].path,
                     "reference_line": ref_item.line,
                     "released_file": source.files[src_item.module].path,
                     "released_line": src_item.line})
        roots.append(source_name)
    cen = census.Census(source, roots, unit)
    cen.walk()

    pairs = {}
    unpaired_reference = []
    entry_module = reference.by_full[entry].module
    reached_modules = {reference.by_full[name].module for name in reference_reached}
    walk_modules, skipped_modules = walk_scope(
        set(reference.files), reached_modules, {entry_module, ref_package + ".Rzb"})
    for module, vf in reference.files.items():
        if module not in walk_modules:
            continue
        originals = set()
        for _, required in vf.requires:
            resolved = source._full_module(required, module)
            if resolved:
                originals.add(resolved)
        for item in vf.decls():
            candidates = {original.full for original_module in originals
                          for original in source.files[original_module].decls()
                          if profile.twin_name(original.name) == item.name}
            if len(candidates) != 1:
                unpaired_reference.append({"reference": item.full, "candidates": sorted(candidates)})
            else:
                pairs[item.full] = candidates.pop()

    output = Path(args.generated)
    manifest = json.loads((output / "budgetwit.json").read_text(encoding="utf8"))
    if manifest["package"] != unit.package:
        raise ValueError("generated manifest belongs to another unit")
    back = {(home, name): full for full, (home, name) in manifest["twins"].items()}
    generated, retained, unpaired_generated = set(), [], []
    for home, owner in sorted(manifest["modules"].items()):
        if owner not in source.files:
            raise ValueError("generated owner not found: " + owner)
        validate(source.files[owner].path)
        path = output / (home + ".v")
        vf = parse_file(str(path), ref_package + "." + home)
        for item in vf.decls():
            original = back.get((home, item.name), owner + "." + item.name)
            if original not in source.by_full:
                unpaired_generated.append(item.full)
            else:
                generated.add(original)
        for item in vf.items:
            if item.kind not in ("decl", "ltac", "notation"):
                continue
            for match in REF_RE.finditer(blank_text(item.text)):
                target = source.resolve(match[1], owner)
                target_item = source.by_full.get(target)
                if (target_item is not None and target_item.kind == "decl" and cen.rtyped(target)
                        and target != owner + "." + item.name):
                    row = {"file": str(path), "line": item.line + item.text.count("\n", 0, match.start()),
                           "declaration": item.name, "released": target}
                    if row not in retained:
                        retained.append(row)

    reference_source = set(pairs.values())
    required = {pairs[name] for name in reference_reached if name in pairs}
    missing = sorted(required - generated)
    reference_only = sorted(reference_source - generated)
    generated_only = sorted(generated - reference_source)
    for full in sorted(generated | reference_source):
        validate(source.files[source.by_full[full].module].path)
    report = {"unit": unit.name, "reference": args.reference, "entry": entry,
              "pins": pins, "source_files_validated": len(validated),
              "reference_declarations": sorted(reference_source),
              "generated_declarations": sorted(generated),
              "required_reference_declarations": sorted(required),
              "missing_required": missing, "reference_only": reference_only,
              "reference_only_unused": sorted(set(reference_only) - required),
              "generated_only": generated_only, "retained_r_typed_references": retained,
              "reference_modules_not_reached": skipped_modules,
              "unpaired_reference": unpaired_reference, "unpaired_generated": unpaired_generated}
    report["passed"] = not (missing or retained or unpaired_reference or unpaired_generated)
    path = Path(args.out)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf8")
    for pin in pins:
        print(f"PIN {pin['reference']}:{pin['reference_line']} -> {pin['released']}:{pin['released_line']}")
    for module in skipped_modules:
        print("NOT_REACHED_BY_ENTRY " + module)
    for name in reference_only:
        print(("MISSING_REQUIRED " if name in required else "REFERENCE_ONLY_UNUSED ") + name)
    for name in generated_only:
        print("GENERATED_ONLY " + name)
    for item in retained:
        print(f"RETAINED_R_REFERENCE {item['file']}:{item['line']} {item['declaration']} -> {item['released']}")
    for item in unpaired_reference:
        print("UNPAIRED_REFERENCE " + json.dumps(item, sort_keys=True))
    for name in unpaired_generated:
        print("UNPAIRED_GENERATED " + name)
    print(f"{'PASS' if report['passed'] else 'FAIL'}: {len(reference_source)} reference declarations, "
          f"{len(required)} required from entry, {len(generated)} generated; "
          f"{len(missing)} missing required, {len(retained)} retained R-typed references; {path}")
    return int(not report["passed"])


if __name__ == "__main__":
    raise SystemExit(main())
