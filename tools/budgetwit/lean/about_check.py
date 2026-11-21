"""Generate a Lean elaborator check; execution belongs on the Lean farm."""
from pathlib import Path
import re

from ..carriers import substitute
from .emitter import TOKEN, profile_for, values


def audit_macros(text, old_names):
    for macro in re.finditer(r"(?ms)^(?:(?:private|local) )?macro\b[^\n]*(?:\n[ \t]+[^\n]*)*", text):
        stale = {token for token in TOKEN.findall(macro[0]) if token.rsplit(".", 1)[-1] in old_names}
        if stale:
            raise ValueError(f"unrenamed released carrier call inside macro: {sorted(stale)}")


def validate_pairs(spec, unit, output):
    old_names = {pair["original"].rsplit(".", 1)[-1] for pair in spec.get("types", [])
                 if pair["original"].rsplit(".", 1)[-1] != pair["twin"].rsplit(".", 1)[-1]}
    public = set()
    for file in spec["files"]:
        module = file["output"].removesuffix(".lean").replace("/", ".")
        text = (Path(output) / file["output"]).read_text()
        audit_macros(text, old_names)
        public.update(module + "." + name for name in re.findall(
            r"^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?(?:noncomputable\s+)?theorem\s+([A-Za-z_]\w*)", text, re.M))
    pairs = spec.get("types", [])
    paired = [pair["twin"] for pair in pairs]
    if len(set(paired)) != len(paired):
        raise ValueError("duplicate discharged-type twin")
    fresh = spec.get("fresh", {})
    if any(not reason.strip() for reason in fresh.values()) or set(fresh) & set(paired):
        raise ValueError("fresh theorems need a reason and must not also be paired")
    if public != set(paired) | set(fresh):
        raise ValueError(f"unpaired public theorems: {sorted(public - set(paired) - set(fresh))}; "
                         f"unknown pairs/exemptions: {sorted((set(paired) | set(fresh)) - public)}")
    for pair in pairs:
        module, name = pair["original"].rsplit(".", 1)
        source = unit.directory / (module.replace(".", "/") + ".lean")
        if not re.search(r"^(?:protected\s+)?(?:theorem|def|abbrev)\s+" + re.escape(name) + r"\b", source.read_text(), re.M):
            raise ValueError(f"original declaration not found: {pair['original']} in {source}")
    return len(public), len(paired), len(fresh)


def probe(spec, unit):
    pairs = spec.get("types", [])
    if not pairs:
        raise ValueError("no discharged-type pairs in manifest")
    substitutions = values(unit, profile_for(spec))
    prefix = substitutions["unit_prefix"]
    template = Path(__file__).with_name("TypeCheck.lean.in").read_text()
    lines = [substitute(template, substitutions), "\n"]
    for pair in pairs:
        mode = pair["mode"]
        if mode not in ("equal", "extra_grant"):
            raise ValueError(f"unknown type comparison mode {mode!r}")
        command = "budget_twin" if mode == "equal" else "budget_strengthened"
        lines.append(f"#{command} {prefix}.{pair['original']} => {prefix}.{pair['twin']}\n")
    strengthened = next((pair for pair in pairs if pair["mode"] == "extra_grant"), None)
    if strengthened:
        lines.append(f"#budget_reject {prefix}.{strengthened['original']} => {prefix}.{strengthened['twin']}\n")
    lines.append("#budget_grant_controls\n")
    for theorem in ("usage_never_refused", "plain_budget_witness", "plain_halts_not_vacuous"):
        lines.append(f"#print axioms {prefix}.BudgetWitness.{theorem}\n")
    return "".join(lines)
