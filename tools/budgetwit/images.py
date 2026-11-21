"""Address-only image twins, checked against corresponding released source lines."""
from pathlib import Path
import re

from .rocqparse import Index
from .retarget import Rewriter, checked_addresses, corresponding_module, referenced_modules, render_files, write_files



def substitute(unit, source, target, out_dir, source_dir=None):
    source, source_module = unit.image(source)
    target, target_module = unit.image(target)
    if source == target:
        raise ValueError("--from and --to must name different images")
    source_dir = Path(source_dir) if source_dir else unit.lib_dir / unit.twin_dir
    output = Path(out_dir)
    files = sorted(source_dir.rglob("*.v"))
    if not files:
        raise ValueError(f"{source_dir}: no already-written witness .v files")
    if output.resolve() == source_dir.resolve():
        raise ValueError("image output must differ from the source witness directory")
    ix = Index(unit.lib_dir, unit.package, twin_dir=unit.twin_dir)
    images = {}
    for module, vf in ix.files.items():
        images[module] = {name for name, image_module in unit.image_modules.items()
                          if any(required.endswith(".images." + image_module) for _, required in vf.requires)}
    lane_cache = {}

    def lane(module, seen=None):
        if module in lane_cache:
            return lane_cache[module]
        if images[module]:
            return images[module]
        seen = set() if seen is None else seen
        if module in seen:
            return set()
        seen.add(module)
        found = set()
        for _, required in ix.files[module].requires:
            resolved = ix._full_module(required, module)
            if resolved:
                found.update(lane(resolved, seen))
        lane_cache[module] = found
        return found

    pairs = {}
    referenced = referenced_modules(files, ix, unit)
    queue = sorted(referenced, reverse=True)
    while queue:
        module = queue.pop()
        if module in pairs:
            continue
        original = ix.files[module]
        if lane(module) != {source}:
            # Aggregators importing multiple lanes and image-independent algebra
            # are shared modules, not an image-specific released walk.
            if len(lane(module)) == 1 and source not in lane(module):
                raise ValueError(f"{original.path}:1: referenced source module belongs to images {sorted(lane(module))}, not {source}")
            pairs[module] = module
            continue
        candidates = [(m, vf) for m, vf in ix.files.items() if m != module and lane(m) == {target}]
        pairs[module] = corresponding_module(original, unit.lib_dir, unit.lib_dir, candidates, target)
        for _, required in original.requires:
            resolved = ix._full_module(required, module)
            if resolved:
                queue.append(resolved)

    # Image-independent helpers can have exact counterparts in the image lane.
    # Derive that namespace from already image-identified released pairs, then
    # check the counterpart too instead of inventing a mixed import rewrite.
    changed = True
    while changed:
        changed = False
        namespaces = {}
        for before, after in pairs.items():
            if before != after:
                old, new = before.rsplit(".", 1)[0], after.rsplit(".", 1)[0]
                if old in namespaces and namespaces[old] != new:
                    raise ValueError(f"{old}: conflicting corresponding target namespaces")
                namespaces[old] = new
        for before, after in list(pairs.items()):
            if before != after or len(lane(before)) > 1:
                continue
            prefix = next((name for name in sorted(namespaces, key=len, reverse=True)
                           if before.startswith(name + ".")), None)
            if prefix is None:
                continue
            counterpart = namespaces[prefix] + before[len(prefix):]
            if counterpart not in ix.files or lane(counterpart) - {target}:
                continue
            pairs[before] = counterpart
            changed = True
            for _, required in ix.files[before].requires:
                dependency = ix._full_module(required, before)
                if dependency and dependency not in pairs:
                    pairs[dependency] = dependency

    replacements = {source_module: target_module, "Images." + source: "Images." + target}
    replacements.update(pairs)
    alias_re = re.compile(r"\b" + re.escape(source_module) + r"_[A-Za-z0-9_']+\b")
    for before, after in pairs.items():
        if before != after:
            target_text = ix.files[after].src
            for name in alias_re.findall(ix.files[before].src):
                replacement = target_module + name[len(source_module):]
                if re.search(r"\b" + re.escape(replacement) + r"\b", target_text):
                    replacements[name] = replacement
    # Directory imports are renamed only when the whole discovered directory map
    # has one target directory. Conflicting mappings are refused.
    directories = {}
    for a, b in pairs.items():
        if a == b:
            continue
        before, after = a.rsplit(".", 1)[0], b.rsplit(".", 1)[0]
        if before in directories and directories[before] != after:
            raise ValueError(f"{before}: corresponding sources require conflicting target directories")
        directories[before] = after
    replacements.update({a: b for a, b in directories.items() if a != unit.package})
    target_prefixes = set()
    for before, after in pairs.items():
        if before == after:
            continue
        left = before[len(unit.package) + 1:].split(".")
        right = after[len(unit.package) + 1:].split(".")
        if len(right) > len(left) and right[-len(left):] == left:
            target_prefixes.add(".".join(right[:-len(left)]))
    if len(target_prefixes) > 1:
        raise ValueError("corresponding released modules give conflicting target witness namespaces: " + ", ".join(sorted(target_prefixes)))
    if target_prefixes:
        replacements[unit.package + "." + unit.twin_dir] = unit.package + "." + next(iter(target_prefixes)) + "." + unit.twin_dir
    rewrite = Rewriter(replacements, pairs)
    source_pairs = [(ix.files[a], ix.files[b]) for a, b in pairs.items() if a != b]
    addresses, _, failures = checked_addresses(source_pairs, rewrite)
    if failures:
        first = failures[0]
        raise ValueError(f"{first['path']}:{first['line']}: {first['message']}")
    rendered, address_count, module_count, _ = render_files(files, source_dir, output, rewrite, addresses)
    write_files(rendered)
    return len(rendered), address_count, module_count
