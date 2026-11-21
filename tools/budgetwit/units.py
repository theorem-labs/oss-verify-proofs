"""Repository and external proof-library metadata; no third-party YAML parser."""
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess

from .rocqparse import blank_text, parse_file


@dataclass(frozen=True)
class Statement:
    name: str
    released_theorems: tuple[str, ...]
    images: tuple[str, ...]
    line: int


@dataclass(frozen=True)
class Unit:
    repo: Path
    name: str
    directory: Path
    lib_dir: Path
    package: str
    image_modules: dict[str, str]
    statements: tuple[Statement, ...]
    twin_dir: str = "BudgetWit"
    excluded: tuple[str, ...] = ("TraceHaltingMF.", "ZTraceSpecMF.",
                                  "TraceHalting.", "ZTraceSpec.")

    @property
    def images(self):
        return tuple(self.image_modules)

    def qualify(self, name):
        return name if name.startswith(self.package + ".") else self.package + "." + name

    def image(self, name):
        name = name.replace("-", "_")
        if name not in self.image_modules:
            raise ValueError(f"{self.name}: no image {name!r}; available: {', '.join(self.images)}")
        return name, self.image_modules[name]


def repository(path=None):
    if path:
        return Path(path).resolve()
    result = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                            text=True, capture_output=True, check=False)
    if result.returncode:
        raise ValueError("not in a git repository; pass --repo or --root")
    return Path(result.stdout.strip())


def package_from_dune(lib_dir):
    dune = lib_dir / "dune"
    text = re.sub(r";[^\n]*", "", dune.read_text(encoding="utf8"))
    names = re.findall(r"\(name\s+([A-Za-z_][A-Za-z0-9_.']*)\s*\)", text)
    if len(names) != 1 or not re.search(r"\(rocq\.theory\b", text):
        raise ValueError(f"{dune}: expected one named rocq.theory, found {names}")
    if "(include_subdirs qualified)" not in re.sub(r"\s+", " ", text):
        raise ValueError(f"{dune}: nested libraries require (include_subdirs qualified)")
    return names[0]


def section_keys(text, section):
    """(indent, key) of each mapping key of a top-level harness metadata section, in order: indent 2 for an immediate
    key, 4 for a key of one of those. The section is its line `<section>:` and the indented, blank or comment lines
    after it, up to the next line that starts a top-level key. The one scan yaml_keys and yaml_subkeys read."""
    lines = text.splitlines()
    try:
        start = lines.index(section + ":") + 1
    except ValueError:
        return
    for line in lines[start:]:
        if line and not line[0].isspace() and not line.startswith("#"):
            break
        match = re.match(r"^(  |    )([A-Za-z_][A-Za-z0-9_-]*):(?:\s|$)", line)
        if match:
            yield len(match[1]), match[2].replace("-", "_")


def yaml_keys(text, section):
    """Read only immediate mapping keys of a top-level harness metadata section (section_keys).

    This is deliberately not a YAML implementation: complex keys/flow mappings are
    refused rather than interpreted differently from the enrollment tools.
    """
    return tuple(key for indent, key in section_keys(text, section) if indent == 2)


def yaml_subkeys(text, section):
    """{key: (subkey, ...)}: the keys of each immediate mapping key of a top-level harness metadata section, read as
    yaml_keys reads those, one indent deeper (harness.yaml `classifiers`: build, then role; section_keys). Keys in a
    flow mapping are not read, so an image they would name is refused rather than taken on a guess."""
    out, key = {}, None
    for indent, name in section_keys(text, section):
        if indent == 2:
            key = name
            out[key] = ()
        elif key is not None:
            out[key] += (name,)
    return out


def load(unit=None, repo=None, root=None):
    if not unit and not root:
        raise ValueError("pass --unit PROJECT/HARNESS or --root PROOF_LIBRARY")
    if root:
        lib = Path(root).resolve()
        directory = lib.parent.parent
        repo = Path(repo).resolve() if repo else directory
        name = unit or directory.name
    else:
        repo = repository(repo)
        parts = unit.split("/")
        if len(parts) != 2 or any(p in ("", ".", "..") for p in parts):
            raise ValueError("--unit must be PROJECT/HARNESS")
        directory = repo / "projects" / unit
        lib = directory / "proofs" / "lib"
        name = unit
    if not lib.is_dir():
        raise ValueError(f"proof library does not exist: {lib}")
    package = package_from_dune(lib)
    image_modules = {}
    images_path = directory / "Images.v"
    if images_path.exists():
        text = blank_text(images_path.read_text(encoding="utf8"))
        for match in re.finditer(r"\bDefinition\s+(\w+)\s*:\s*Image\s*:=\s*mkImage\s+(\w+)\.", text):
            image_modules[match[1]] = match[2]
    image_dune = directory / "images" / "dune"
    if image_dune.exists():
        targets = {target for block in re.findall(r"\(targets\s+([^)]*)\)", image_dune.read_text(encoding="utf8"))
                   for target in block.split() if target.endswith(".v")}
        missing = {module + ".v" for module in image_modules.values()} - targets
        if missing:
            raise ValueError(f"{image_dune}: image module targets missing: {', '.join(sorted(missing))}")
    metadata = directory / "harness.yaml"
    yaml = metadata.read_text(encoding="utf8") if metadata.exists() else ""
    builds = yaml_keys(yaml, "builds")
    # Images.v defines each build's image, and the image of each original and classifier harness.yaml lists (oft
    # generate's claims.images_v, by shapes.original_ident and shapes.classifier_ident): each build must have its
    # image, and any other image must be one of those, so an Images.v that still defines a build harness.yaml no
    # longer lists is refused
    missing = set(builds) - set(image_modules)
    if missing:
        raise ValueError(f"{images_path}: no image of harness.yaml builds {sorted(missing)}; "
                         f"it defines {sorted(image_modules)}")
    listed = set(builds) | {build + "_original" for build in yaml_keys(yaml, "originals")}
    listed |= {f"classifier_{role}_{build}" for build, roles in yaml_subkeys(yaml, "classifiers").items()
               for role in roles}
    stray = set(image_modules) - listed
    if builds and stray:
        raise ValueError(f"{images_path}: images {sorted(stray)} are of no harness.yaml build, original or "
                         f"classifier; it lists {sorted(listed)}")
    statements_path = directory / "Statements.v"
    statements = []
    theorem_path = lib / "Theorems.v"
    theorem_items = parse_file(str(theorem_path), package + ".Theorems").decls() if theorem_path.exists() else []
    declared = yaml_keys(yaml, "statements")
    if statements_path.exists():
        vf = parse_file(str(statements_path), package + ".Statements")
        for item in vf.decls():
            if declared and item.name not in declared:
                continue
            names = tuple(t.full for t in theorem_items
                          if t.name == item.name or t.name.endswith("_" + item.name)
                          or re.search(r"\bStatements\." + re.escape(item.name) + r"\b", t.stmt))
            imgs = tuple(sorted(set(re.findall(r"\bImages\.(\w+)", blank_text(item.stmt)))))
            statements.append(Statement(item.name, names, imgs, item.line))
        missing = set(declared) - {s.name for s in statements}
        if missing:
            raise ValueError(f"{statements_path}: metadata statements missing: {', '.join(sorted(missing))}")
    return Unit(Path(repo), name, directory, lib, package, image_modules, tuple(statements))

class ImageReferences:
    """Resolve image aliases per declaration before using module import evidence."""

    def __init__(self, unit, index):
        self.unit = unit
        self.index = index
        self.cache = {}
        self.module_images = {}
        self.module_refs = {}
        for module, vf in index.files.items():
            self.module_images[module] = {name for name, image_module in unit.image_modules.items()
                                          if any(required.endswith(".images." + image_module)
                                                 for _, required in vf.requires)}
            self.module_refs[module] = [target for _, required in vf.requires
                                        if (target := index._full_module(required, module))]
        changed = True
        while changed:
            changed = False
            for module, references in self.module_refs.items():
                before = len(self.module_images[module])
                for target in references:
                    self.module_images[module].update(self.module_images[target])
                changed |= len(self.module_images[module]) != before

    def in_text(self, text, module, seen=None):
        from .rocqparse import REF_RE
        seen = set() if seen is None else seen
        found = {name for name, image_module in self.unit.image_modules.items()
                 if re.search(r"\b" + re.escape(image_module) + r"\.(?:M\.|init_pc|phdrs)", text)}
        for ref in REF_RE.finditer(text):
            full = self.index.resolve(ref[1], module)
            item = self.index.by_full.get(full)
            if item is None or item.kw not in ("Definition", "Let") or item.full in seen:
                continue
            if full not in self.cache:
                seen.add(item.full)
                self.cache[full] = self.in_text(blank_text(item.stmt or item.text), item.module, seen)
                seen.remove(item.full)
            found.update(self.cache[full])
        return found

    def for_item(self, item):
        found = self.in_text(blank_text(item.stmt or item.text), item.module)
        return found or self.module_images[item.module]

