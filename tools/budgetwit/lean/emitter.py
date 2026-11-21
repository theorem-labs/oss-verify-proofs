"""Inclusive range copying and exact identifier substitution, not a Lean parser."""
import hashlib
import json
from pathlib import Path
import re

from ..carriers import PROFILES, substitute

TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def renames(path):
    out = {}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        old, new = line.split("\t")
        if old in out:
            raise ValueError(f"{path}: duplicate rename {old}")
        out[old] = new
    return out


def twin(text, ranges, names, drop_private=False):
    lines = text.splitlines(keepends=True)
    ordered = sorted(ranges)
    if any(left[1] >= right[0] for left, right in zip(ordered, ordered[1:])):
        raise ValueError("overlapping ranges within one piece")
    result = []
    for start, end in ranges:
        if not 1 <= start <= end <= len(lines):
            raise ValueError(f"invalid inclusive range {start}-{end} for {len(lines)} lines")
        result.extend(lines[start - 1:end])
    text = TOKEN.sub(lambda m: names.get(m[0], m[0]), "".join(result))
    if drop_private:
        text = re.sub(r"(?m)^(\s*)private (?=(?:theorem|def|abbrev|opaque)\b)", r"\1", text)
    return text


def profile_for(spec):
    profile = next((p for p in PROFILES if p.family == spec["family"]), None)
    if profile is None or not profile.lean_soundness_template:
        raise ValueError(f"{spec['family']}: no Lean carrier template")
    return profile


def values(unit, profile):
    prefix = unit.package.removesuffix(".proofs.lib")
    directory, module = profile.lean_carrier_directory, profile.lean_carrier_module
    if not directory or not module:
        raise ValueError(f"{profile.family}: missing Lean carrier location")
    twin_namespace = prefix + ".BudgetWit.Rzb"
    return {"package": unit.package, "unit_prefix": prefix,
            "root": prefix.split(".")[0], "carrier_directory": directory,
            "carrier_module": module, "prelude_module": profile.prelude_module,
            "support_modules": " ".join(profile.support_modules),
            "cfg_module": ".".join((directory, profile.cfg_directory, "Cfg")),
            "original_relation": ".".join((unit.package, directory, module, profile.relation)),
            "twin_relation": twin_namespace + "." + profile.twin_relation,
            "twin_namespace": twin_namespace}


def generate(manifest, unit, output):
    manifest, output = Path(manifest), Path(output)
    spec = json.loads(manifest.read_text())
    profile = profile_for(spec)
    outputs = [file["output"] for file in spec["files"]]
    if len(set(outputs)) != len(outputs):
        raise ValueError("duplicate output in manifest")
    generated = []
    for file in spec["files"]:
        chunks = []
        for piece in file["pieces"]:
            if "carrier" in piece:
                chunks.append(profile.render_lean(unit))
            elif "fragment" in piece:
                fragment = (manifest.parent / piece["fragment"]).read_text()
                if "ranges" in piece:
                    fragment = twin(fragment, piece["ranges"], {})
                chunks.append(substitute(fragment, values(unit, profile)))
            else:
                source = unit.directory / piece["source"]
                raw = source.read_bytes()
                if hashlib.sha256(raw).hexdigest() != piece["sha256"]:
                    raise ValueError(f"source changed: {source}; review and re-pin its ranges")
                names = renames(manifest.parent / piece["renames"]) if "renames" in piece else {}
                chunks.append(twin(raw.decode(), piece["ranges"], names, piece.get("drop_private", False)))
        target = output / file["output"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("".join(chunks))
        generated.append(target)
    return generated
