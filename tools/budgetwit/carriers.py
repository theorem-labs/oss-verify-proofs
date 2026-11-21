"""Measured carrier families and their naming/soundness-template policies."""
from dataclasses import dataclass, replace
from functools import cached_property
from pathlib import Path
import re

from .rocqparse import QID, blank_text, parse_file


@dataclass(frozen=True)
class Evidence:
    file: Path
    line: int
    declaration: str
    text: str

    def __str__(self):
        return f"{self.file}:{self.line}: {self.text.strip()}"


@dataclass(frozen=True)
class NodeStep:
    relation: str
    configuration: str
    soundness_mode: str
    evidence: Evidence

    @property
    def requires_transparency(self):
        return self.soundness_mode == "fixed"


@dataclass(frozen=True)
class CarrierProfile:
    family: str
    file_pattern: str
    inductive_pattern: str
    relation: str
    cut_constructors: tuple[str, ...]
    node_constructors: tuple[str, ...]
    index_arguments: tuple[str, ...]
    seed_names: tuple[str, ...]
    node_builders: tuple[str, ...]
    rename_rules: tuple[tuple[str, str], ...]
    soundness_template: str
    evidence: tuple[Evidence, ...] = ()
    bridge_only: bool = False
    skip: tuple[str, ...] = ()
    package: str = ""
    prelude_module: str = ""
    support_modules: tuple[str, ...] = ()
    cfg_directory: str = ""
    lean_soundness_template: str = ""
    lean_index_arguments: tuple[str, ...] = ()
    lean_carrier_directory: str = ""
    lean_carrier_module: str = ""
    node_step: NodeStep | None = None

    @property
    def name(self):
        return self.family

    @property
    def template_path(self):
        return Path(__file__).parent / self.soundness_template

    @property
    def twin_relation(self):
        return self.twin_name(self.relation)

    def twin_name(self, name):
        for old, new in self.rename_rules:
            if name == old:
                return new
            if name.startswith(old + "_"):
                return new + name[len(old):]
        return name + "_b"

    def twin_module(self, module):
        relative = module.removeprefix(self.package + ".") if self.package else module
        if self.family == "YK15":
            return relative.rsplit(".", 1)[-1] + "B"
        return relative.replace(".", "_") + "B"

    @cached_property
    def node_re(self):
        names = set(self.node_builders) | {self.twin_name(n) for n in self.node_builders}
        return re.compile(r"(?<![A-Za-z0-9_'.])(?:" + QID + r"\.)?(?:" +
                          "|".join(re.escape(n) for n in sorted(names)) + r")(?![A-Za-z0-9_'])")

    @cached_property
    def tactic_words(self):
        names = self.seed_names + self.node_builders + ("node_ok", "node_chk")
        return re.compile(r"(?<![A-Za-z0-9_'])(?:" +
                          "|".join(re.escape(n) for n in names) + r")(?:_[A-Za-z0-9_']+)?(?![A-Za-z0-9_'])")

    def seeds(self, ix):
        out = set()
        carrier_files = {e.file.resolve() for e in self.evidence}
        for name, item in ix.by_full.items():
            if item.kind != "decl":
                continue
            if item.name in self.seed_names and name == item.full:
                if item.name != self.relation or Path(ix.files[item.module].path).resolve() in carrier_files:
                    out.add(name)
        if not out:
            raise ValueError(f"{self.family}: no carrier seeds in index")
        return out

    def overrides(self, ix):
        """Declarations supplied by the handwritten soundness template, not twins."""
        template = self.template_path.read_text(encoding="utf8")
        supplied = {it.name for it in parse_file(str(self.template_path), "Rzb", src=template).decls()}
        supplied.update(re.findall(r"^\|\s*(\w+)\s*:", template, re.M))
        out = {}
        carrier_files = {e.file.resolve() for e in self.evidence}
        for name, item in ix.by_full.items():
            path = ix.files[item.module].path
            if Path(path).resolve() not in carrier_files:
                continue
            short = name.rsplit(".", 1)[-1]
            twin = self.twin_name(short)
            if twin in supplied:
                out[name] = ("Rzb", twin, True)
        return out

    def render(self, unit):
        text = self.template_path.read_text(encoding="utf8")
        if text.startswith("TODO owner:"):
            raise ValueError(f"{self.family}: soundness template is a carrier-prover stub: {self.template_path}")
        if self.family == "YK15" and (self.node_step is None
                                      or self.node_step.soundness_mode not in ("MayFail", "fixed")):
            raise ValueError("YK15: no supported node_ok step configuration was detected")
        carrier = self.evidence[0].file.relative_to(unit.lib_dir).with_suffix("")
        directory = ".".join(carrier.parts[:-1])
        values = {"package": unit.package, "carrier_directory": directory,
                  "carrier_module": carrier.name, "prelude_module": self.prelude_module,
                  "support_modules": " ".join(self.support_modules),
                  "cfg_module": ".".join(part for part in (directory, self.cfg_directory) if part)}
        for mod in (self.prelude_module,) + self.support_modules:
            if not mod:
                continue
            path = unit.lib_dir.joinpath(*carrier.parts[:-1], mod + ".v")
            if not path.exists():
                raise ValueError(f"{self.family} template requires support module: {path}")
        if self.node_step and self.node_step.requires_transparency:
            cfg_path = unit.lib_dir.joinpath(*carrier.parts[:-1], self.cfg_directory, "Cfg.v")
            cfg = parse_file(str(cfg_path), "Cfg")
            transparent = next((it for it in cfg.decls() if it.name == "cfg_transparent"), None)
            configurations = set(re.findall(r"\bsstep_cfg\s+" + QID + r"\s+(" + QID + r")\b",
                                            blank_text(transparent.text))) if transparent else set()
            if configurations != {self.node_step.configuration}:
                raise ValueError(f"{cfg_path}: cfg_transparent must cover the node_ok configuration "
                                 f"{self.node_step.configuration}; found {sorted(configurations)}")
        return substitute(text, values)

    def render_lean(self, unit):
        if not self.lean_soundness_template:
            raise ValueError(f"{self.family}: no Lean soundness template")
        from .lean.emitter import values
        path = Path(__file__).parent / self.lean_soundness_template
        return substitute(path.read_text(encoding="utf8"), values(unit, self))


def substitute(text, values):
    missing = set(re.findall(r"\{\{(\w+)\}\}", text)) - values.keys()
    if missing:
        raise ValueError("missing template substitutions: " + ", ".join(sorted(missing)))
    return re.sub(r"\{\{(\w+)\}\}", lambda m: values[m[1]], text)


def detect_node_step(vf, indices):
    """Read the filtered step of the measured carrier's node_ok definition.

    The AllocMode carrier's soundness theorem is specialized at MayFail. A
    carrier with a fixed configuration needs the additional transparency proof.
    """
    node = next((it for it in vf.decls() if it.name == "node_ok"), None)
    if node is None:
        raise ValueError(f"{vf.path}: YK15 carrier has no node_ok definition")
    text = blank_text(node.text)
    configurations = set(re.findall(r"\bsstep_cfg\s+" + QID + r"\s+(" + QID + r")\b", text))
    if len(configurations) != 1:
        raise ValueError(f"{vf.path}:{node.line}: expected one node_ok step configuration, "
                         f"found {sorted(configurations)}")
    configuration = next(iter(configurations))
    bound = {name for it in vf.items if it.start < node.start and it.kind == "sectdecl"
             and node.sections[:len(it.sections)] == it.sections for name in it.names or ()}
    if "AllocMode" in indices and configuration == "mcfg":
        mode = "MayFail"
    elif not indices and configuration.rsplit(".", 1)[-1] not in bound:
        mode = "fixed"
    else:
        mode = "unsupported"
    start = re.search(r"\bDefinition\s+node_ok\b", text)
    line = vf.lineno(node.start + start.start()) if start else node.line
    evidence = Evidence(Path(vf.path), line, "node_ok", vf.src.splitlines()[line - 1])
    return NodeStep("sstep_cfg", configuration, mode, evidence)


RZ_RULES = (("realizes", "rzb"), ("rz", "rzb"))
PROFILES = (
    CarrierProfile("YK15", r"(?:^|/)YK15\.v$", r"realizes", "realizes", ("rz_cut",),
                   ("rz_node", "rz_silent"), ("AllocMode",), ("realizes", "knode", "SR", "mreal"),
                   ("rz_node", "rz_silent", "rz_emit1", "rz_alt2", "rz_silent1", "rz_silent_allI",
                    "rz_silent_all", "node_chk", "node_ok_of_pnode", "SR_node"),
                   RZ_RULES + (("SR", "SRb"), ("mreal", "mreal_b"), ("knode", "knode_b")),
                   "carriers/YK15.v.in", prelude_module="YZ00",
                   support_modules=("YK16", "YK0n", "YK0i", "YK0v", "YK02", "YK1i"), cfg_directory="R",
                   lean_soundness_template="carriers/YK15.lean.in", lean_index_arguments=("AllocMode",),
                   lean_carrier_directory="Reusable", lean_carrier_module="YK15"),
    CarrierProfile("ShapeAlg", r"(?:^|/)ShapeAlg\.v$", r"realizes", "realizes",
                   ("rz_cut", "rz_refused", "rz_side"), ("rz_node", "rz_silent"), ("StepCfg",),
                   ("realizes",), ("rz_node", "rz_silent", "rz_emit1", "rz_silent1", "rz_alt2", "rz_silent_allI"),
                   RZ_RULES, "carriers/ShapeAlg.v.in"),
    CarrierProfile("SpinAlg", r"(?:^|/)SpinAlg[^/]*\.v$", r"srealizes0?", "srealizes", (),
                   ("srz_node", "srz_silent"), ("scfg",), ("srealizes", "srealizes0"),
                   ("srz_node", "srz_silent", "srz_emit1", "srz_silent1"),
                   (("srealizes", "rzb"), ("srealizes0", "rzb0"), ("srz", "rzb")), "carriers/SpinAlg.v.in"),
    CarrierProfile("RealizesCfg", r"(?:^|/)(?:RealizesCfg|ShapeAlgCfg)\.v$", r"realizes_cfg", "realizes_cfg", (),
                   ("rzc_node", "rz_node_cfg"), ("cfg",), ("realizes_cfg",),
                   ("rzc_node", "rz_node_cfg", "rzc_emit1", "rzc_silent1", "rz_emit1_cfg", "rz_silent1_cfg"),
                   (("realizes_cfg", "rzb"), ("rzc", "rzb")), "carriers/RealizesCfg.v.in"),
    CarrierProfile("FwSafety", r"(?:^|/)Fw/(?:Safety|Refusable)\.v$", r"wsteps", "star_cfg", (), (), (),
                   ("star_a", "syscall_spec_ns", "safe", "triple", "triple1"),
                   ("star_cfg_step", "wsteps_step"), (("star_cfg", "star_budget"),), "carriers/FwSafety.v.in"),
    CarrierProfile("ITree", r".*\.v$", r"(?:impl|implM|tree_ok)", "impl", (), (), (),
                   ("impl", "implM", "tree_ok"), (), (), "carriers/ITree.v.in", bridge_only=True),
)


def specialize(profile, evidence, vf):
    """Bind every family field to the carrier actually used by a walk."""
    primary = evidence[0]
    relation = next(it for it in vf.decls() if it.name == primary.declaration)
    constructors = tuple(relation.constructors or ())
    cuts = tuple(n for n in profile.cut_constructors if n in constructors)
    nodes = tuple(n for n in profile.node_constructors if n in constructors)
    indices = tuple(n for n in profile.index_arguments
                    if re.search(r"\b" + re.escape(n) + r"\b", vf.blank[:relation.start]))
    step = detect_node_step(vf, indices) if profile.family == "YK15" else None
    template = "carriers/YK15Fixed.v.in" if step and step.requires_transparency else profile.soundness_template
    return replace(profile, relation=primary.declaration if profile.family != "FwSafety" else "star_cfg",
                   evidence=tuple(evidence), cut_constructors=cuts, node_constructors=nodes,
                   index_arguments=indices, node_step=step, soundness_template=template,
                   skip=profile.skip + tuple(vf.module + "." + name for name in cuts))


def detect(lib_dir):
    """Return a measured profile plus all matching declaration file:line evidence.

    A tree can contain secondary carriers for sanitizer lanes. Prefer the base
    carrier when present; discovery reports roots separately rather than treating
    an imported secondary carrier as evidence for a particular path.
    """
    lib_dir = Path(lib_dir).resolve()
    hits = {p.family: [] for p in PROFILES}
    for path in sorted(lib_dir.rglob("*.v")):
        if "BudgetWit" in path.relative_to(lib_dir).parts:
            continue
        eligible = [p for p in PROFILES if re.search(p.file_pattern, path.as_posix())]
        if not eligible:
            continue
        text = path.read_text(encoding="utf8")
        blank = blank_text(text)
        for p in eligible:
            keyword = r"(?:Inductive|CoInductive)" if p.family != "ITree" else r"(?:Inductive|CoInductive|Definition|Fixpoint)"
            for match in re.finditer(r"\b" + keyword + r"\s+(" + p.inductive_pattern + r")\b", blank):
                line = text.count("\n", 0, match.start()) + 1
                hits[p.family].append(Evidence(path, line, match[1], text.splitlines()[line - 1]))
    for family in ("YK15", "FwSafety", "ShapeAlg", "RealizesCfg", "SpinAlg", "ITree"):
        evidence = hits[family]
        if not evidence:
            continue
        if family == "ShapeAlg" and hits["RealizesCfg"]:
            family, evidence = "RealizesCfg", hits["RealizesCfg"]
        profile = next(p for p in PROFILES if p.family == family)
        evidence.sort(key=lambda e: (len(e.file.relative_to(lib_dir).parts), e.file.as_posix()))
        primary = evidence[0]
        module = str(primary.file.relative_to(lib_dir).with_suffix("")).replace("/", ".")
        return specialize(profile, evidence, parse_file(str(primary.file), module))
    raise ValueError(f"{lib_dir}: no recognised carrier declaration (Inductive/CoInductive realizes, srealizes, realizes_cfg, wsteps; or impl/implM/tree_ok bridge)")
