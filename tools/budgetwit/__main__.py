"""Command-line interface for image-specific budget-witness twins."""
import argparse
from collections import defaultdict
from dataclasses import replace
import csv
import json
from pathlib import Path
import re
import sys

from . import about_check, carriers, census, gen_v, images, retarget, roots, units
from .rocqparse import Index, parse_file


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("detect", "census", "gen", "genall", "image", "sibling", "probe", "about"):
        p = sub.add_parser(name)
        p.add_argument("--repo", help="repository root; default: git root of cwd")
        p.add_argument("--unit", help="PROJECT/HARNESS")
        p.add_argument("--root", help="external proof-library directory (instead of --unit)")
        if name in ("detect", "census", "gen", "genall"):
            p.add_argument("--image", default="plain")
            p.add_argument("--start", action="append", help="startup MODULE.NAME; repeatable or comma-separated")
            p.add_argument("--usage", action="append", help="usage MODULE.NAME; repeatable or comma-separated")
        if name in ("census", "gen", "genall"):
            p.add_argument("--roots", help="comma-separated census roots, replacing discovery")
            p.add_argument("--overrides", help="per-unit mapping/skip TSV")
        if name in ("census", "gen", "probe"):
            p.add_argument("--out", required=True)
        if name in ("genall", "image", "sibling"):
            p.add_argument("--out-dir", required=True)
        if name in ("gen", "genall"):
            p.add_argument("--admit", action="store_true", help="statement probes only; never commit generated admissions")
        if name == "gen":
            p.add_argument("--module", required=True)
            p.add_argument("--names", help="comma-separated declarations")
            p.add_argument("--twin-module")
            p.add_argument("--identity", action="store_true")
            p.add_argument("--tsv", help="previous census table (otherwise census is computed)")
            p.add_argument("--ltacs", help="previous tactic table")
            p.add_argument("--note")
        if name in ("image", "sibling"):
            p.add_argument("--from", dest="source", required=name == "image", default="plain")
            p.add_argument("--to", dest="target", required=name == "image", default="plain")
            p.add_argument("--source-dir", help="already-written source BudgetWit directory")
        if name == "sibling":
            target = p.add_mutually_exclusive_group(required=True)
            target.add_argument("--to-unit", help="target project/harness")
            target.add_argument("--to-root", help="target external proofs/lib directory")
            p.add_argument("--renames", required=True, help="JSON reviewed renames with reason/reviewed_by")
            p.add_argument("--files", action="append", help="comma-separated relative walk-twin filenames")
            p.add_argument("--report", help="JSON accounting/refusal report; default OUT/budgetwit-retarget.json")
            p.add_argument("--three-way", action="store_true", help="retain checked Git diff3 candidates and conflicts")
        if name in ("probe", "about"):
            p.add_argument("--map", required=True)
        if name == "probe":
            p.add_argument("--twin", required=True)
            p.add_argument("--r1-module", required=True)
            p.add_argument("--tsv")
            p.add_argument("--overrides")
            p.add_argument("--pairs", help="comma-separated original=twin pairs")
            p.add_argument("--rename", action="append", default=[])
        if name == "about":
            p.add_argument("--log", required=True)
            p.add_argument("--allow", action="append", default=[])
    return parser


def names(values):
    return [name.strip() for value in values or [] for name in value.split(",") if name.strip()]


def get_unit(args):
    if args.unit or args.root:
        return units.load(args.unit, args.repo, args.root)
    if args.command == "probe":
        repo = units.repository(args.repo)
        matches = []
        for path in (repo / "projects").glob("*/*/proofs/lib/dune"):
            package = units.package_from_dune(path.parent)
            if args.r1_module.startswith(package + "."):
                matches.append(path.parent)
        if len(matches) == 1:
            return units.load(repo=repo, root=matches[0])
        raise ValueError("probe needs --unit/--root or an unambiguous fully-qualified --r1-module")
    return units.load(args.unit, args.repo, args.root)


def discover(unit, args):
    return roots.discover(unit, image=args.image, start=names(args.start), usage=names(args.usage))


def compute(unit, args):
    if args.roots:
        profile = replace(carriers.detect(unit.lib_dir), package=unit.package)
        ix = Index(unit.lib_dir, unit.package, profile=profile, twin_dir=unit.twin_dir)
        selected = names([args.roots])
    else:
        found = discover(unit, args)
        profile, ix, selected = found.profile, found.index, found.roots
    if profile.bridge_only:
        raise ValueError("ITree: twin route does not apply; use the no-allocation bridge")
    cen = census.Census(ix, selected, unit, overrides=args.overrides)
    cen.walk()
    return ix, cen, cen.rows()


def tactic_map(cen):
    result = {}
    for name in cen.ltacs:
        item = cen.ix.by_full[name]
        override = cen.omaps.get(name)
        result[name] = (override[0] if override else
                        cen.omods[item.module][0] if item.module in cen.omods else
                        cen.profile.twin_module(item.module))
    return result


def write_census(path, rows, cen):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=census.COLS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    tactics = path.with_name(path.stem + "-ltacs.tsv")
    with tactics.open("w", encoding="utf8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(("r1_module", "name", "line", "twin_module", "names"))
        for name, home in sorted(tactic_map(cen).items()):
            item = cen.ix.by_full[name]
            writer.writerow((item.module[len(cen.ix.pkg) + 1:], item.name, item.line, home,
                             ";".join(sorted(cen.ltacs[name]))))
    print(f"{path}: {len(rows)} twins, {sum(r['lines'] for r in rows)} R1 lines, "
          f"{len({r['r1_module'] for r in rows})} files; {len(cen.ltacs)} tactics; {tactics}")


def generate(ix, twins, module, home, selected, args, ltacs):
    note = getattr(args, "note", None)
    if args.admit and not note:
        note = "STATEMENT CHECK ONLY: admitted proofs; never commit this probe input"
    generator = gen_v.Gen(ix, module, twins, home, identity=getattr(args, "identity", False),
                          note=note, admit=args.admit)
    generator.ltac_home = ltacs
    text = generator.generate(selected)
    for line, why in generator.hand:
        print(f"HAND {module}:{line}: {why}", file=sys.stderr)
    return text


def generate_command(unit, args):
    ix, cen, rows = compute(unit, args)
    # Render first: a missing prover template must not leave a partial twin set.
    template = ix.profile.render(unit)
    twins = {unit.qualify(r["r1_module"] + "." + r["name"]): (r["twin_module"], r["twin_name"]) for r in rows}
    tactics = tactic_map(cen)
    if args.command == "gen":
        if args.tsv:
            twins.update(gen_v.load_twins(args.tsv, unit.package))
        if args.ltacs:
            tactics.update(gen_v.load_ltacs(args.ltacs, unit.package))
        module = args.module
        if module.endswith(".v"):
            module = str(Path(module).resolve().relative_to(unit.lib_dir).with_suffix("")).replace("/", ".")
        module = unit.qualify(module)
        if module not in ix.files:
            raise ValueError("no such released module: " + module)
        home = args.twin_module or Path(args.out).stem
        selected = names([args.names]) if args.names else [r["name"] for r in rows if unit.qualify(r["r1_module"]) == module and not r["existing"]]
        for name in selected:
            full = module + "." + name
            renamed = name if args.identity else twins.get(full, (home, ix.profile.twin_name(name)))[1]
            twins[full] = (home, renamed)
        tactics = {name: home if ix.by_full[name].module == module else owner
                   for name, owner in tactics.items()}
        text = generate(ix, twins, module, home, selected, args, tactics)
        path = Path(args.out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf8")
        print(f"{path}: {text.count(chr(10))} lines, {text.count('(* HAND: grant *)')} grant markers")
        write_manifest(path.parent, unit, twins, {home: module})
        return
    output = Path(args.out_dir)
    groups = defaultdict(list)
    owners = {}
    for row in rows:
        if row["existing"]:
            continue
        key = (unit.qualify(row["r1_module"]), row["twin_module"])
        groups[key].append(row["name"])
    for name, home in tactics.items():
        groups.setdefault((ix.by_full[name].module, home), [])
    rendered = {"Rzb": template}
    for (module, home), selected in sorted(groups.items()):
        if home in rendered:
            raise ValueError(f"twin module collision: {home}; use --overrides to split modules")
        rendered[home] = generate(ix, twins, module, home, selected, args, tactics)
        owners[home] = module
    output.mkdir(parents=True, exist_ok=True)
    for home, text in rendered.items():
        (output / (home + ".v")).write_text(text, encoding="utf8")
    write_census(output / "twins.tsv", rows, cen)
    write_manifest(output, unit, twins, owners)
    print(f"{output}: {len(rendered)} .v files, {sum(t.count(chr(10)) for t in rendered.values())} lines, "
          f"{sum(t.count('(* HAND: grant *)') for t in rendered.values())} (* HAND: grant *) markers")


def write_manifest(directory, unit, twins, owners):
    path = Path(directory) / "budgetwit.json"
    previous = json.loads(path.read_text(encoding="utf8")) if path.exists() else {}
    if previous and previous.get("package") != unit.package:
        raise ValueError(f"{path}: belongs to another unit")
    data = {"package": unit.package, "unit": unit.name,
            "twins": {**previous.get("twins", {}), **{k: list(v) for k, v in twins.items()}},
            "modules": {**previous.get("modules", {}), **owners}}
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf8")


def probe(unit, args):
    module = unit.qualify(args.r1_module)
    twin = Path(args.twin)
    home = twin.stem
    manifest_path = twin.parent / "budgetwit.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf8")) if manifest_path.exists() else {}
    mappings = manifest.get("twins", {})
    mappings.update(gen_v.load_twins(args.tsv, unit.package))
    profile = replace(carriers.detect(unit.lib_dir), package=unit.package)
    overrides, _, _ = gen_v.load_overrides(args.overrides, unit.package)
    for name, (tm, tn, _) in overrides.items():
        mappings[name] = (tm, tn or profile.twin_name(name.rsplit(".", 1)[-1]))
    back = {tn: full.rsplit(".", 1)[-1] for full, (tm, tn) in mappings.items()
            if tm == home and full.rsplit(".", 1)[0] == module}
    if args.pairs:
        pairs = [tuple(value.split("=", 1)) for value in names([args.pairs])]
        if any(len(pair) != 2 for pair in pairs):
            raise ValueError("--pairs entries must be original=twin")
    else:
        original_path = unit.lib_dir.joinpath(*module[len(unit.package) + 1:].split(".")).with_suffix(".v")
        originals = {it.name for it in parse_file(str(original_path), module).decls()}
        pairs = []
        for name, _ in about_check.scan_twin(str(twin), unit.package + "." + unit.twin_dir + "." + home):
            original = back.get(name)
            if original is None and name in originals:
                original = name  # a non-R sibling copied under its released name
            if original is None:
                candidate = [n for n in originals if profile.twin_name(n) == name]
                if len(candidate) == 1:
                    original = candidate[0]
            if original is None:
                raise ValueError(f"{twin}: cannot pair {name}; supply --tsv, manifest, or --pairs")
            pairs.append((original, name))
    if not pairs:
        raise ValueError(f"{twin}: no declarations to query")
    identifiers = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", twin.read_text(encoding="utf8")))
    renames = {full.rsplit(".", 1)[-1]: tn for full, (_, tn) in mappings.items() if tn in identifiers}
    renames.update({old: new for old, new in profile.rename_rules if new in identifiers})
    extra = {}
    for value in args.rename:
        if "=" not in value:
            raise ValueError("--rename needs old=new")
        a, b = value.split("=", 1)
        extra[a] = b
    about_check.write_probe(str(twin), args.out, args.map, module, pairs,
                            census=renames, extra_renames=extra,
                            package=unit.package, twin_dir=unit.twin_dir)
    print(f"{args.out}: {len(pairs)} declarations, {2 * len(pairs)} About queries; {args.map}")


def main(argv=None):
    parser = arguments()
    args = parser.parse_args(argv)
    try:
        if args.command == "about":
            meta = json.loads(Path(args.map).read_text(encoding="utf8"))
            if not meta.get("pairs") or not meta.get("entries"):
                raise ValueError("About map contains no declaration pairs/markers")
            log = Path(args.log).read_text(encoding="utf8", errors="replace")
            rows = about_check.check(meta, log, allow=args.allow)
            for verdict, before, after, why in rows:
                print(f"{verdict:8} {before} -> {after}" + (f"  {why}" if why else ""))
            bad = sum(v in ("DIFF", "NOREAD") for v, *_ in rows)
            print(f"{len(rows)} declarations, {bad} not SAME")
            return int(bool(bad))
        unit = get_unit(args)
        if args.command == "detect":
            found = discover(unit, args)
            print(f"family {found.profile.family}; image {found.image}; package {unit.package}")
            for evidence in found.profile.evidence:
                print(f"carrier {evidence}")
            if found.profile.node_step:
                step = found.profile.node_step
                print(f"node_ok {step.relation} {step.configuration}; soundness {step.soundness_mode}; "
                      f"transparency {step.requires_transparency}; {step.evidence}")
            for kind, selected in (("start", found.start), ("usage", found.usage)):
                for root in selected:
                    print(f"{kind} {root}")
            if found.profile.bridge_only:
                raise ValueError("ITree: twin route does not apply; use the no-allocation bridge")
        elif args.command == "census":
            _, cen, rows = compute(unit, args)
            write_census(args.out, rows, cen)
        elif args.command in ("gen", "genall"):
            generate_command(unit, args)
        elif args.command == "image":
            count, addresses, modules = images.substitute(unit, args.source, args.target, args.out_dir, args.source_dir)
            print(f"{args.out_dir}: {count} files, {addresses} substituted addresses, {modules} module renames")
        elif args.command == "sibling":
            target = units.load(args.to_unit, args.repo, args.to_root)
            count, addresses, renamed, report = retarget.sibling(
                unit, target, args.source, args.target, args.out_dir, args.renames,
                args.source_dir, names(args.files), args.report, three_way=args.three_way)
            print(f"{args.out_dir}: {count} files, {addresses} substituted addresses, {renamed} renames; {report}")
        elif args.command == "probe":
            probe(unit, args)
    except (ValueError, OSError, KeyError) as error:
        print(f"budgetwit: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
