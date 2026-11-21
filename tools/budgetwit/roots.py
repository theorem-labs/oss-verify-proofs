"""Image-specific startup/usage discovery with explicit ambiguity refusals."""
from dataclasses import dataclass, replace
from pathlib import Path
import re

from . import carriers
from .rocqparse import Index, PROOF_KW, REF_RE, blank_text, _top_level_split
from .units import ImageReferences


ARGC = re.compile(r"(?:\bargc\b\s*<>\s*2|(?:Z\.of_nat\s*\()?\s*length\s+(?:\(in_argv\s+\w+\)|\w+)\s*\)?\s*<>\s*2(?:%nat)?)")
USAGE = re.compile(r"\b(?:msg_usage|pieces_usage|MSG_USAGE_PRE|MSG_USAGE_POST|DUsage|main_usage_stmt)\b")
HALT = re.compile(r"\b(?:t_exit|diag|io_diag|TDIE|SX|EXIT|at_exit|DUsage|SWr)\b|m_halted\s*.*(?:<>|≠)\s*None")
RELATION = re.compile(r"\b(realizes_cfg|srealizes0?|realizes|implM?|tree_ok|cpsE|NODE|evt)\b")
INIT = re.compile(r"\b(?:init_config|init_ms|init_machine_state)\b")


@dataclass(frozen=True)
class Root:
    name: str
    file: Path
    line: int
    evidence: tuple[str, ...]

    def __str__(self):
        return f"{self.name} — {self.file}:{self.line}\n    " + "\n    ".join(self.evidence)


@dataclass
class Discovery:
    profile: carriers.CarrierProfile
    start: list[Root]
    usage: list[Root]
    index: Index
    image: str

    @property
    def roots(self):
        return [r.name for r in self.start + self.usage]


class DiscoveryError(ValueError):
    pass


def section_context(vf, item):
    stack = [[]]
    for current in vf.items:
        if current.start >= item.start:
            break
        if current.kind == "section_open":
            stack.append([])
        elif current.kind == "section_close":
            if len(stack) > 1:
                stack.pop()
        elif current.kind in ("hypothesis", "variable", "context", "let"):
            stack[-1].append(current)
    return [x for frame in stack for x in frame]


def statement(ix, item, seen=None):
    """Expose a named statement alias, not every predicate in its hypotheses."""
    seen = set() if seen is None else seen
    if item.full in seen:
        return "", []
    seen.add(item.full)
    text = blank_text(item.stmt or item.text)
    alias = re.fullmatch(r"\s*(?:Lemma|Theorem|Corollary|Fact)\s+\w+\s*:\s*(" +
                         r"[A-Za-z_][A-Za-z0-9_'.]*" + r")\s*\.\s*", text)
    if alias:
        other = ix.by_full.get(ix.resolve(alias[1], item.module))
        if other is not None and other.kw == "Definition":
            expanded, more = statement(ix, other, seen)
            return text + "\n" + expanded, [f"{ix.files[other.module].path}:{other.line}: statement alias {other.name}"] + more
    return text, []


def discover(unit, image="plain", start=None, usage=None, index=None):
    image, image_module = unit.image(image) if unit.images else (image, image.title())
    ix = index or Index(unit.lib_dir, unit.package, twin_dir=unit.twin_dir)
    image_references = ImageReferences(unit, ix)

    def belongs(item):
        referenced = image_references.for_item(item)
        return not referenced or referenced == {image}

    starts, usages, certificates, argc_suppliers = [], [], [], []
    profile = carriers.detect(unit.lib_dir)
    for module, vf in ix.files.items():
        for item in vf.decls():
            if item.kw not in PROOF_KW or not belongs(item):
                continue
            raw_statement = blank_text(item.stmt or "")
            if not (INIT.search(raw_statement) or USAGE.search(raw_statement)
                    or ARGC.search(raw_statement) or re.search(r"\busage\w*\b|\bfacts?_hold", raw_statement)):
                continue
            text, evidence = statement(ix, item)
            context = section_context(vf, item)
            context_text = "\n".join(blank_text(c.text) for c in context)
            relation = RELATION.search(text)
            segments = list(_top_level_split(text, ["->"]))
            conclusion = text[slice(*segments[-1])]
            conclusion_relation = RELATION.search(conclusion)
            certificate_init = bool(INIT.search(conclusion) and re.search(r"\bst_ok\b", conclusion)
                                    and (ARGC.search(text) or ARGC.search(context_text)))
            continuation = (len(RELATION.findall(text)) >= 2 or certificate_init
                            or re.search(r"\b(?:init_ms|init_machine_state)\b", conclusion))
            if (INIT.search(conclusion) and (conclusion_relation or certificate_init)
                    and continuation
                    and (not unit.images or image_references.in_text(text, item.module) == {image})):
                root = Root(item.full, Path(vf.path), item.line,
                            tuple(["conclusion names this image's initialization and " + (conclusion_relation[1] if conclusion_relation else "certificate st_ok continuation")] + evidence))
                starts.append(root)
            arg = ARGC.search(text) or ARGC.search(context_text)
            if arg and USAGE.search(text) and HALT.search(text) and relation:
                context_evidence = [f"{vf.path}:{c.line}: {c.text.strip()}" for c in context if ARGC.search(blank_text(c.text))]
                root = Root(item.full, Path(vf.path), item.line,
                            tuple(["argc != 2; usage diagnostic; terminal/exit continuation"] + evidence + context_evidence))
                usages.append(root)
            if (relation and relation[1] == "NODE" and USAGE.search(text) and HALT.search(text)):
                certificates.append(Root(item.full, Path(vf.path), item.line,
                                         ("certificate NODE has usage diagnostic and SX 2 continuation",)))
            if arg and re.search(r"\bfacts?_holds?\b", text):
                argc_suppliers.append(Root(item.full, Path(vf.path), item.line,
                                           ("argc != 2 supplies the certificate's fact premise",)))

    def bind_profile(candidates):
        nonlocal profile
        texts = [statement(ix, ix.by_full[root.name])[0] for root in candidates]
        families = set()
        evidence = {}
        for root, text in zip(candidates, texts):
            item = ix.by_full[root.name]
            family = ("RealizesCfg" if re.search(r"\brealizes_cfg\b", text) else
                      "SpinAlg" if re.search(r"\bsrealizes0?\b", text) else
                      "ITree" if re.search(r"\b(?:implM?|tree_ok)\b", text) else
                      ("YK15" if profile.family == "YK15" else "ShapeAlg")
                      if re.search(r"\brealizes\b", text) else None)
            if family:
                families.add(family)
            visible = ix.by_full.get(ix.resolve(profile.relation, item.module))
            if visible is not None and re.fullmatch(profile.inductive_pattern, visible.name or ""):
                path = Path(ix.files[visible.module].path)
                evidence[(path, visible.line)] = carriers.Evidence(path, visible.line, visible.name, (visible.stmt or "").splitlines()[0])
            for reference in RELATION.finditer(text):
                target = ix.by_full.get(ix.resolve(reference[1], item.module))
                if target is not None and target.kw in ("Inductive", "CoInductive", "Definition", "Fixpoint"):
                    path = Path(ix.files[target.module].path)
                    evidence[(path, target.line)] = carriers.Evidence(path, target.line, target.name, (target.stmt or "").splitlines()[0])
        if len(families) == 1:
            family = next(iter(families))
            profile = next(p for p in carriers.PROFILES if p.family == family)
        matching = [e for e in evidence.values() if re.fullmatch(profile.inductive_pattern, e.declaration)]
        if not matching:
            matching = [e for e in profile.evidence
                        if image_references.module_images.get(unit.qualify(str(e.file.relative_to(unit.lib_dir).with_suffix("")).replace("/", ".")), set()) in (set(), {image})]
        if matching:
            matching.sort(key=lambda e: (e.file.as_posix(), e.line))
            primary = matching[0]
            vf = ix.files[unit.qualify(str(primary.file.relative_to(unit.lib_dir).with_suffix("")).replace("/", "."))]
            base = next(p for p in carriers.PROFILES if p.family == profile.family)
            profile = carriers.specialize(base, matching, vf)

    bind_profile(usages or certificates)

    def select(candidates, override, kind):
        if override:
            result = []
            for requested in override:
                full = unit.qualify(requested)
                item = ix.by_full.get(full)
                if item is None:
                    raise DiscoveryError(f"--{kind}: declaration not found: {requested}")
                result.append(Root(full, Path(ix.files[item.module].path), item.line,
                                   ("explicit --" + kind + " override",)))
            return result
        # A statement alias is a packaging wrapper, not the underlying walk.
        direct = [r for r in candidates if RELATION.search(blank_text(ix.by_full[r.name].stmt or ""))]
        if direct:
            candidates = direct
        if kind == "start":
            configurations = [r for r in candidates if re.search(r"\binit_config\b", ix.by_full[r.name].stmt or "")]
            if configurations:
                candidates = configurations
        if len(candidates) != 1:
            listing = "\n".join(str(r) for r in candidates) or "  (none)"
            carrier_evidence = "\n".join("carrier " + str(e) for e in profile.evidence)
            raise DiscoveryError(f"family {profile.family}; image {image}\n{carrier_evidence}\n{unit.name}/{image}: {kind} discovery has {len(candidates)} candidates; pass --{kind} MODULE.NAME (repeatable)\n{listing}")
        return candidates

    # Certificate-generated paths have a node root AND its argc fact supplier.
    if certificates:
        # A certificate walk's entry node is the candidate no other candidate
        # consumes. This follows proof references, not numeric file suffixes.
        consumed = set()
        certificate_names = {r.name for r in certificates}
        for root in certificates:
            item = ix.by_full[root.name]
            for reference in REF_RE.finditer(blank_text(item.proof or "")):
                target = ix.resolve(reference[1], item.module)
                if target in certificate_names and target != root.name:
                    consumed.add(target)
        certificates = [r for r in certificates if r.name not in consumed]
        concrete = [r for r in argc_suppliers if image_references.for_item(ix.by_full[r.name]) == {image}]
        if concrete:
            argc_suppliers = concrete
    if not usages and certificates:
        if len(certificates) == 1 and len(argc_suppliers) == 1 and not usage:
            selected_usage = certificates + argc_suppliers
        else:
            selected_usage = select(certificates + argc_suppliers, usage, "usage")
    else:
        selected_usage = select(usages, usage, "usage")
    selected_start = select(starts, start, "start")
    bind_profile(selected_usage)
    profile = replace(profile, package=unit.package)
    ix.profile = profile
    return Discovery(profile, selected_start, selected_usage, ix, image)
