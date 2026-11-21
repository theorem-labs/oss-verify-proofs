"""Checked relocations shared by image and sibling-harness witness ports.

Correspondence is textual, not a proof of equivalence. Every copied source file
must agree after namespace changes, profile consequences, reviewed renames and
hex-literal pairs. Other changes are diagnostics for a manual patch, never edits
silently carried into the witness.
"""
from dataclasses import asdict, dataclass
import difflib
import json
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from . import carriers
from .rocqparse import Index, QID, blank_text
from .units import ImageReferences

HEX = re.compile(r"(?<![A-Za-z0-9_'])0[xX][0-9A-Fa-f]+(?![A-Za-z0-9_'])")
TOKEN = re.compile(r"(?:" + QID + r"|[0-9]+)\Z")
PROVENANCE = re.compile(r"made from\s+([^:\n]+\.v)\s*:")
SOURCE_FILE = re.compile(r"(?:[A-Za-z_][A-Za-z0-9_']*/)*[A-Za-z_][A-Za-z0-9_']*\.v")
REQUIRE = re.compile(r"(\bFrom\s+)(" + QID + r")(\s+Require(?:\s+(?:Import|Export))?\s+)([^.]*)(\.)")


@dataclass
class Rewritten:
    text: str
    count: int
    lines: list[int]
    contexts: list[dict]


class Rewriter:
    def __init__(self, replacements, pairs, drop_context=None):
        self.replacements = dict(replacements)
        self.pairs = pairs
        self.pattern = re.compile(r"(?<![A-Za-z0-9_'])((?:" + "|".join(
            re.escape(n) for n in sorted(replacements, key=len, reverse=True)) + r"))(?![A-Za-z0-9_'])") if replacements else None
        binder = r"[A-Za-z_][A-Za-z0-9_']*\s*:\s*(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
        self.context = re.compile(r"\s*Context\s+(?:\{" + binder + re.escape(drop_context) + r"\}|\(" + binder
                                  + re.escape(drop_context) + r"\))\.\s*\Z") if drop_context else None

    def __call__(self, text, context):
        lines, kept, removed = [], [], []
        code_lines = blank_text(text).splitlines(keepends=True) if self.context else ()
        for number, line in enumerate(text.splitlines(keepends=True), 1):
            if self.context and self.context.fullmatch(line) and self.context.fullmatch(code_lines[number - 1]):
                removed.append({'line': number, 'text': line.rstrip('\r\n')})
            else:
                lines.append(number)
                kept.append(line)
        text = ''.join(kept)
        count = 0

        def module(match):
            nonlocal count
            replacement = self.replacements[match[1]]
            count += int(replacement != match[1])
            return replacement

        def replace(value):
            return self.pattern.sub(module, value) if self.pattern else value

        out, cursor = [], 0
        for match in REQUIRE.finditer(text):
            out.append(replace(text[cursor:match.start()]))
            prefix = match[2]
            words = match[4].split()
            mapped = [self.pairs[prefix + '.' + name] for name in words if prefix + '.' + name in self.pairs]
            if mapped:
                parents = {name.rsplit('.', 1)[0] for name in mapped}
                if len(parents) != 1 or (len(mapped) != len(words) and parents != {prefix}):
                    line = text.count('\n', 0, match.start())
                    original = lines[line] if line < len(lines) else line + 1
                    raise ValueError(f'{context}:{original}: mixed shared/relocated imports cannot be renamed without changing command structure')
                parent = next(iter(parents))
                count += int(parent != prefix)
            else:
                parent = replace(prefix)
            out.append(match[1] + parent + match[3] + replace(match[4]) + match[5])
            cursor = match.end()
        out.append(replace(text[cursor:]))
        return Rewritten(''.join(out), count, lines, removed)


def provenance_modules(text, unit):
    """Expand a made-from list in order, inheriting its explicit directory."""
    found = {}
    for match in PROVENANCE.finditer(text):
        residue = SOURCE_FILE.sub('', match[1])
        if re.sub(r"\band\b|[, \t]+", '', residue):
            raise ValueError(f'unrecognized released-source provenance list: {match[1]!r}')
        directory = Path()
        for name in SOURCE_FILE.findall(match[1]):
            path = Path(name)
            if len(path.parts) > 1:
                directory = path.parent
            else:
                path = directory / path
            found[unit.qualify(str(path.with_suffix('')).replace('/', '.'))] = None
    return tuple(found)


def referenced_modules(files, index, unit):
    found = set()
    for path in files:
        text = path.read_text(encoding='utf8')
        for module in index.files:
            if re.search(r"(?<![A-Za-z0-9_'])" + re.escape(module) + r"(?![A-Za-z0-9_'])", text):
                found.add(module)
        found.update(name for name in provenance_modules(text, unit) if name in index.files)
        for match in REQUIRE.finditer(blank_text(text)):
            found.update(match[2] + '.' + short for short in match[4].split()
                         if match[2] + '.' + short in index.files)
    return found


def corresponding_module(original, source_root, target_root, candidates, label):
    relative = Path(original.path).relative_to(source_root)
    candidates = [(name, vf) for name, vf in candidates if Path(vf.path).name == relative.name]
    exact = [(name, vf) for name, vf in candidates if Path(vf.path).relative_to(target_root) == relative]
    if exact:
        candidates = exact

    def score(candidate):
        parts = Path(candidate[1].path).relative_to(target_root).parts
        count = 0
        for a, b in zip(reversed(relative.parts), reversed(parts)):
            if a != b:
                break
            count += 1
        return count

    if candidates:
        best = max(map(score, candidates))
        candidates = [candidate for candidate in candidates if score(candidate) == best]
    if len(candidates) != 1:
        raise ValueError(f'{original.path}: expected one corresponding {label} source; found {len(candidates)}: '
                         + ', '.join(name for name, _ in candidates))
    return candidates[0][0]


def _code_hex_sub(replace, text, code):
    return HEX.sub(lambda m: replace(m) if code[m.start():m.end()] == m[0] else m[0], text)


def checked_addresses(pairs, rewrite):
    """Account for all source differences; retain full hunks for every bad file."""
    addresses, evidence, failures = {}, {}, []
    for left, right in pairs:
        prepared = rewrite(left.src, left.path)
        a, b = prepared.text.splitlines(), right.src.splitlines()
        a_code, b_code = blank_text(prepared.text).splitlines(), blank_text(right.src).splitlines()
        problem = None
        if len(a) != len(b):
            n = min(len(a), len(b))
            line = prepared.lines[n] if n < len(prepared.lines) else len(left.src.splitlines()) + 1
            problem = (line, f'line count {len(a)} differs from {right.path} ({len(b)}); not address-only')
        else:
            for n, (x, y) in enumerate(zip(a, b)):
                line = prepared.lines[n]
                old, new = HEX.findall(a_code[n]), HEX.findall(b_code[n])
                if len(old) != len(new) or (_code_hex_sub(lambda _: '<address>', x, a_code[n])
                                             != _code_hex_sub(lambda _: '<address>', y, b_code[n])):
                    problem = problem or (line, f'difference is not address-only against {right.path}:{n + 1}\n  source: {x}\n  target: {y}')
                    continue
                for before, after in zip(old, new):
                    if before in addresses and addresses[before] != after:
                        problem = problem or (line, f'address {before} has inconsistent targets {addresses[before]} '
                                               f'({evidence[before]}) and {after}')
                    else:
                        addresses[before] = after
                        evidence.setdefault(before, f'{left.path}:{line}')
        if problem:
            diff = ''.join(difflib.unified_diff([s + '\n' for s in a], [s + '\n' for s in b],
                                                str(left.path) + ' (after declared/profile rewrites)', str(right.path)))
            failures.append({'path': str(left.path), 'line': problem[0], 'target': str(right.path),
                             'message': problem[1], 'diff': diff})
    return addresses, evidence, failures


def render_files(files, source_dir, output, rewrite, addresses):
    rendered, changes = [], []
    address_count = rename_count = 0
    for path in files:
        prepared = rewrite(path.read_text(encoding='utf8'), path)
        count = 0

        def address(match):
            nonlocal count
            value = match[0]
            if value in addresses and addresses[value] != value:
                count += 1
                return addresses[value]
            return value

        text = _code_hex_sub(address, prepared.text, blank_text(prepared.text))
        rendered.append((output / path.relative_to(source_dir), text))
        changes.append({'file': str(path.relative_to(source_dir)), 'addresses': count,
                        'renames': prepared.count, 'removed_contexts': prepared.contexts})
        address_count += count
        rename_count += prepared.count
    return rendered, address_count, rename_count, changes


def write_files(rendered):
    for path, text in rendered:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding='utf8')


def profile_adaptations(source, target):
    if source.family != target.family:
        raise ValueError(f'incompatible carrier families: {source.family} -> {target.family}; needs a manual proof port')
    a, b = source.node_step, target.node_step
    renames, drop, reasons = {}, None, []
    if a and b and a.soundness_mode == 'MayFail' and b.soundness_mode == 'fixed':
        renames = {name: name.replace('grant_ok', 'budget_ok', 1)
                   for name in ('grant_ok', 'grant_ok_instr', 'grant_ok_no', 'grant_ok_exit')}
        if 'AllocMode' in source.index_arguments and 'AllocMode' not in target.index_arguments:
            drop = 'AllocMode'
        reasons.append({'reason': 'MayFail node grants become fixed-configuration budget obligations with transparency',
                        'source_node_step': asdict(a), 'target_node_step': asdict(b),
                        'renames': renames, 'drop_context': drop})
    elif a and b and a.soundness_mode != b.soundness_mode:
        raise ValueError(f'node-step transition {a.soundness_mode} -> {b.soundness_mode} needs a manual proof port')
    return renames, drop, reasons


def reviewed_renames(path, source_text, target_text, automatic, derived):
    metadata = json.loads(Path(path).read_text(encoding='utf8'))
    if not isinstance(metadata, dict) or set(metadata) - {'renames', 'manual_patches'} or not isinstance(metadata.get('renames'), list):
        raise ValueError(f'{path}: expected an object with renames list and optional manual_patches list')
    declared = {}
    source_code, target_code = blank_text(source_text), blank_text(target_text)
    for row in metadata['renames']:
        if (not isinstance(row, dict) or set(row) != {'from', 'to', 'reason', 'reviewed_by'}
                or any(not isinstance(row.get(key), str) or not row[key].strip()
                       for key in ('from', 'to', 'reason', 'reviewed_by'))):
            raise ValueError(f'{path}: every rename needs exactly from, to, reason, reviewed_by (nonempty strings)')
        before, after = row['from'], row['to']
        if not TOKEN.fullmatch(before) or not TOKEN.fullmatch(after) or before == after:
            raise ValueError(f'{path}: rename is not a changed identifier/decimal token: {before!r} -> {after!r}')
        if before in declared:
            raise ValueError(f'{path}: duplicate rename for {before}')
        short = before.rsplit('.', 1)[-1]
        if short.startswith(('grant_ok', 'budget_ok')) or short == 'AllocMode':
            expected = automatic(before, path).text
            if short not in derived or after != expected:
                raise ValueError(f'{path}: {before} -> {after} disagrees with the carrier profiles (expected {expected})')
        else:
            old = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(before) + r"(?![A-Za-z0-9_'])")
            new = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(after) + r"(?![A-Za-z0-9_'])")
            if not old.search(source_code) or not new.search(target_code):
                raise ValueError(f'{path}: reviewed rename {before} -> {after} is not present in the corresponding source/target text')
        declared[before] = after
    patches = metadata.get('manual_patches', [])
    if not isinstance(patches, list) or any(not isinstance(p, str) or not p.strip() for p in patches):
        raise ValueError(f'{path}: manual_patches must be a list of nonempty patch names; they are recorded, never applied')
    return declared, metadata


def merge_twin(ours, base, theirs):
    """Return Git's diff3 candidate and exit status; never modify an input."""
    with TemporaryDirectory(prefix='budgetwit-merge-') as directory:
        root = Path(directory)
        paths = [root / name for name in ('witness.v', 'source.v', 'target.v')]
        for path, text in zip(paths, (ours, base, theirs)):
            path.write_text(text, encoding='utf8')
        result = subprocess.run(
            ['git', 'merge-file', '--diff3', '-p', '-L', 'witness', '-L', 'source release', '-L', 'target release',
             *(str(path) for path in paths)], cwd=root, encoding='utf8', capture_output=True, check=False)
    if not 0 <= result.returncode <= 127:
        raise ValueError(f'git merge-file failed ({result.returncode}): {result.stderr.strip()}')
    return result.stdout, result.returncode


def sibling(source_unit, target_unit, source, target, out_dir, renames, source_dir=None, selected=(), report_path=None,
            three_way=False):
    source, source_module = source_unit.image(source)
    target, target_module = target_unit.image(target)
    if source_unit.lib_dir.resolve() == target_unit.lib_dir.resolve():
        raise ValueError('sibling requires two different harness trees; use image for one harness')
    source_dir = Path(source_dir) if source_dir else source_unit.lib_dir / source_unit.twin_dir
    output = Path(out_dir)
    if output.resolve() == source_dir.resolve():
        raise ValueError('sibling output must differ from the source witness directory')
    files = sorted(source_dir.rglob('*.v'))
    if selected:
        requested = {name if name.endswith('.v') else name + '.v' for name in selected}
        found = {p.relative_to(source_dir).as_posix(): p for p in files}
        if requested - found.keys():
            raise ValueError(f'{source_dir}: selected witness files not found: {sorted(requested - found.keys())}')
        files = [found[name] for name in sorted(requested)]
    if not files:
        raise ValueError(f'{source_dir}: no already-written witness .v files')
    a = Index(source_unit.lib_dir, source_unit.package, twin_dir=source_unit.twin_dir)
    b = Index(target_unit.lib_dir, target_unit.package, twin_dir=target_unit.twin_dir)
    a_lanes, b_lanes = ImageReferences(source_unit, a), ImageReferences(target_unit, b)
    owners = {}
    for path in files:
        matches = provenance_modules(path.read_text(encoding='utf8'), source_unit)
        if not matches or not set(matches) <= a.files.keys():
            raise ValueError(f'{path}:1: expected existing released-source provenance; select walk twins with --files; tops are manual')
        owners[path] = matches
    references = referenced_modules(files, a, source_unit)
    pairs = {}
    for module in sorted(references):
        lanes = a_lanes.module_images[module]
        if lanes - {source}:
            raise ValueError(f'{a.files[module].path}:1: source imports images {sorted(lanes)}, not just {source}')
        candidates = [(name, vf) for name, vf in b.files.items()
                      if not b_lanes.module_images[name] - {target}]
        pairs[module] = corresponding_module(a.files[module], source_unit.lib_dir, target_unit.lib_dir,
                                             candidates, target_unit.name + '/' + target)
    source_profile, target_profile = carriers.detect(source_unit.lib_dir), carriers.detect(target_unit.lib_dir)
    derived, drop, profile_changes = profile_adaptations(source_profile, target_profile)
    replacements = {source_unit.package: target_unit.package, source_module: target_module,
                    'Images.' + source: 'Images.' + target}
    for unit, index, image_module, side in ((source_unit, a, source_module, 'source'),
                                           (target_unit, b, target_module, 'target')):
        roots = {required.rsplit('.images.', 1)[0] for vf in index.files.values() for _, required in vf.requires
                 if required.endswith('.images.' + image_module)}
        if len(roots) != 1:
            raise ValueError(f'{unit.name}: expected one {side} image namespace, found {sorted(roots)}')
        if side == 'source':
            source_root = next(iter(roots))
        else:
            replacements[source_root] = next(iter(roots))
    replacements.update(pairs)
    directories = {}
    for before, after in pairs.items():
        old, new = before.rsplit('.', 1)[0], after.rsplit('.', 1)[0]
        if old in directories and directories[old] != new:
            raise ValueError(f'{old}: corresponding sources require conflicting target directories')
        directories[old] = new
    replacements.update(directories)
    replacements.update(derived)
    automatic = Rewriter(replacements, pairs, drop_context=drop)
    checked_pairs = [(a.files[name], b.files[pairs[name]])
                     for name in sorted({name for modules in owners.values() for name in modules})]
    source_text = '\n'.join(vf.src for vf, _ in checked_pairs) + '\n' + '\n'.join(p.read_text(encoding='utf8') for p in files)
    target_text = '\n'.join(vf.src for _, vf in checked_pairs)
    declared, metadata = reviewed_renames(renames, source_text, target_text, automatic, derived)
    replacements.update(declared)
    rewrite = Rewriter(replacements, pairs, drop_context=drop)
    addresses, evidence, failures = checked_addresses(checked_pairs, rewrite)
    report_path = Path(report_path) if report_path else output / 'budgetwit-retarget.json'
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report = {'source_unit': source_unit.name, 'target_unit': target_unit.name, 'source_image': source,
              'target_image': target, 'source_dir': str(source_dir), 'output': str(output),
              'profile_changes': profile_changes, 'declared_renames': metadata['renames'],
              'walk_owners': {str(path.relative_to(source_dir)): list(modules) for path, modules in owners.items()},
              'manual_patches': metadata.get('manual_patches', []), 'module_pairs': pairs,
              'checked_sources': [{'source': x.path, 'target': y.path} for x, y in checked_pairs],
              'address_pairs': {old: {'target': new, 'source': evidence[old]} for old, new in addresses.items() if old != new},
              'unaccounted': failures, 'method': 'three-way' if three_way else 'tokens',
              'merge_candidates': [], 'written': False}
    if not failures:
        rendered, count, renamed, changes = render_files(files, source_dir, output, rewrite, addresses)
        canonical = {path.relative_to(output).as_posix(): text for path, text in rendered}
    if three_way:
        for path in files:
            relative = path.relative_to(source_dir)
            modules = owners[path]
            base = '\n'.join(rewrite(a.files[name].src, a.files[name].path).text for name in modules)
            theirs = '\n'.join(b.files[pairs[name]].src for name in modules)
            ours = rewrite(path.read_text(encoding='utf8'), path).text
            candidate, status = merge_twin(ours, base, theirs)
            destination = report_path.parent / 'merge' / relative.with_suffix('.merge')
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(candidate, encoding='utf8')
            entry = {'file': relative.as_posix(), 'candidate': str(destination), 'git_exit_code': status,
                     'source_owners': list(modules)}
            if not failures and not status and candidate != canonical[relative.as_posix()]:
                entry['unaccounted_changes'] = ''.join(difflib.unified_diff(
                    canonical[relative.as_posix()].splitlines(keepends=True), candidate.splitlines(keepends=True),
                    'declared-change result', 'three-way candidate'))
            report['merge_candidates'].append(entry)
    merge_conflicts = [entry for entry in report['merge_candidates']
                       if entry['git_exit_code'] or entry.get('unaccounted_changes')]
    if failures or merge_conflicts:
        for failure in failures:
            relative = Path(failure['path']).relative_to(source_unit.lib_dir)
            patch = report_path.parent / 'manual' / relative.with_suffix('.patch')
            patch.parent.mkdir(parents=True, exist_ok=True)
            patch.write_text(failure['diff'], encoding='utf8')
            failure['manual_patch_required'] = str(patch)
        report_path.write_text(json.dumps(report, indent=2, default=str) + '\n', encoding='utf8')
        if failures:
            first = failures[0]
            raise ValueError(f"{first['path']}:{first['line']}: {first['message']}\n"
                             f'{len(failures)} source files need manual patches; no witness files written; report {report_path}')
        raise ValueError(f"{merge_conflicts[0]['candidate']}: three-way result has conflicts or unaccounted changes; "
                         f'no witness files written; report {report_path}')
    write_files(rendered)
    report.update(written=True, files=changes, substituted_addresses=count, renames=renamed)
    report_path.write_text(json.dumps(report, indent=2, default=str) + '\n', encoding='utf8')
    return len(rendered), count, renamed, report_path
