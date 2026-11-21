"""Lean's tree reader, returning the same Unit/Statement records as Rocq."""
from pathlib import Path
import re

from ..units import Statement, Unit


def load(name, repo):
    repo = Path(repo).resolve()
    project, harness = name.split("/")
    base = repo / "lean-proofs" / project / harness
    candidates = list(base.glob(f"*/{project}/{harness}/Images.lean"))
    if len(candidates) != 1:
        raise ValueError(f"{base}: expected one root namespace, found {candidates}")
    image_file = candidates[0]
    directory = image_file.parent
    text = image_file.read_text()
    match = re.search(r"^namespace ([A-Za-z_][\w.]*)\.Images\s*$", text, re.M)
    if not match:
        raise ValueError(f"{image_file}: no Images namespace")
    prefix = match[1]
    if directory.relative_to(base).parts != tuple(prefix.split(".")):
        raise ValueError(f"{image_file}: namespace does not match its path: {prefix}")
    images = {key: prefix + ".images." + module for key, module in re.findall(
        r"^def (\w+)\s*:\s*Image\s*:=\s*Image\.mkImage\s+(\w+)\.M\.loaded_segments\b", text, re.M)}
    if not images:
        raise ValueError(f"{image_file}: no image definitions")
    statements_file = directory / "Statements.lean"
    text = statements_file.read_text()
    declarations = list(re.finditer(r"^def (\w+)\s*:\s*Prop\s*:=", text, re.M))
    aliases_file = directory / "proofs/lib/Theorems.lean"
    aliases = re.findall(r"^theorem (\w+)\s*:\s*Statements\.(\w+)\s*:=", aliases_file.read_text(), re.M)
    statements = []
    for i, declaration in enumerate(declarations):
        body = text[declaration.end():declarations[i + 1].start() if i + 1 < len(declarations) else len(text)]
        statements.append(Statement(declaration[1], tuple(a for a, s in aliases if s == declaration[1]),
                                    tuple(dict.fromkeys(re.findall(r"\bImages\.(\w+)", body))),
                                    text.count("\n", 0, declaration.start()) + 1))
    return Unit(repo, name, directory, directory / "proofs/lib", prefix + ".proofs.lib",
                images, tuple(statements))
