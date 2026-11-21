set -euo pipefail
# The subjects.  Two shapes name the package:
#   * `from ossv import` / `from ossv.` / `import ossv` -- the third deliberately loose, because
#     `import ossv_statements` is the flat form of exactly the same dependency and is the defect this
#     step exists for.  `from ossv.` was added on 2026-11-06: the log-search tool of bin/
#     reaches the package as `from ossv.search_log import cli` and had never been a subject,
#     so it had never been run with only src/ on the path.  The anchor below is what found it;
#   * `"ossv-launch"` -- the five launchers of pyproject.toml's [project.scripts], which hold no import of
#     their own and reach the package through bin/ossv-launch (its header says why).
# bin/ossv-launch itself is no subject and is skipped by neither rule: it is a bootstrap, not a tool, and
# exits 1 by design when run by name.  The five launchers run it, so it is checked five times over.
subjects="$RUNNER_TEMP/deployed-layout-subjects.txt"
: > "$subjects"
for f in bin/*; do
  [ -f "$f" ] || continue
  grep -q 'from ossv import\|from ossv\.\|import ossv\|"ossv-launch"' "$f" || continue
  printf '%s\n' "$f" >> "$subjects"
done
count=$(grep -c . "$subjects" || true)
echo "entry points that name the ossv package: $count"
sed 's/^/  /' "$subjects"
# A loop over a glob that matches nothing exits 0 and reads exactly like a pass, so the subjects are
# asserted before any of them runs.  Three bars, because the first two of them do not bite on their own:
#
#   * non-zero.  Cleared by a pattern that decayed to matching one file.
#   * every name of [project.scripts].  This was the whole floor until the review of pull request 667
#     (finding 3c) ran the case neither its author nor its reviewer had: a bin/ decayed to exactly the
#     five launchers PASSES it, reporting "all 5 entry point(s) import" while exercising one import path
#     five times -- the shape of failure this step exists to prevent.  It is kept because it names which
#     half of the subject rule broke, and it is not the floor.
#   * the expected set, computed below from the tree by a SECOND implementation of the same rule.
#     This is the floor, and it is no longer a number anybody keeps up to date.  The loop above walks
#     bin/ in bash; the check below walks it again in python and the two sets must be EQUAL, so a
#     subject the loop drops -- a `continue` that fires too early, a glob that misses a name, a quoting
#     slip -- fails the step naming the file, while a tool that starts or stops importing the package
#     needs no edit here at all.  It was a hand-kept number until 2026-11-06 (Dispatch OSSV-276): it
#     moved four times in one day across two streams, once per tool that began importing the package,
#     and every such pull request had to touch this workflow to say so.
[ "$count" -gt 0 ] || { echo "::error::no file of dev/stream/bin names the ossv package: this check ran nothing"; exit 1; }
python - "$subjects" <<'DEPLOYED_LAYOUT_FLOOR'
import ast
import sys
import tomllib
from pathlib import Path

PATTERNS = ("from ossv import", "from ossv.", "import ossv", '"ossv-launch"')


def candidates(where=Path("bin")):
    """The files of WHERE the bash loop walks: `bin/*`, so no dotfile, and no directory.

    The loop's glob skips a name beginning with a dot and `[ -f ]` skips anything that is
    not a file, so this skips both. A DOTFILE THAT IMPORTED THE PACKAGE IS MISSED BY BOTH
    HALVES and by the anchor, which never sees it either: this check cannot find one, and
    naming that is better than a reader assuming otherwise. Nothing in bin/ is a dotfile
    today.
    """
    for path in sorted(where.iterdir()):
        if path.name.startswith(".") or not path.is_file():
            continue
        yield path


def names_the_package(blob):
    """This step's own rule, as the bash loop applies it: the four patterns, as bytes.

    Bytes and not text: `grep` matches bytes, so a file this cannot decode must be judged
    the same way it is rather than dropped from the set, which would turn a real
    difference into a pass. Every file of bin/ decodes as UTF-8 today; this is about not
    depending on that.
    """
    return any(p.encode() in blob for p in PATTERNS)


def is_the_package(name, where=Path("src")):
    """True when NAME is this repository's ossv package, dotted or FLAT.

    `ossv` and `ossv.x` are plain. `ossv_x` is the flat form of the same dependency and is
    the defect this whole step exists for -- the log-search tool of bin/, line 13, uses it
    today -- and the patterns above catch `import ossv_x` but not `from ossv_x import y`. The
    old measured count went red on that; a review of 2026-11-06 changed one real tool to it
    and this check stayed green with the tool never run.

    A flat name counts only when the module it names is really there, as src/ossv/<m>.py or
    src/ossv/<m>/. Six bin/test_ossv_vm_*.py import a sibling `ossv_vm_fake_gcs` that way,
    which is not the package and must not turn the tree red.
    """
    if name == "ossv" or name.startswith("ossv."):
        return True
    if not name.startswith("ossv_"):
        return False
    flat = name[len("ossv_"):].split(".", 1)[0]
    return (where / "ossv" / f"{flat}.py").is_file() or (where / "ossv" / flat).is_dir()


def imports_the_package(blob):
    """True when BLOB is python that reaches `ossv`, read from its syntax rather than its text.

    This is the independent anchor, and it is the point of this check. The two halves
    above share one rule, so between them they can only catch the LOOP disagreeing with
    it; neither can catch the RULE going stale. A review on 2026-11-06 showed how: change
    a tool from `from ossv import x` to `from ossv.x import y` and it leaves the subject
    set in silence, which is exactly the hand-kept count's one real job.

    It reads `importlib.import_module("ossv.x")` and `__import__("ossv.x")` as imports,
    because they are: bin/ossv-dashboard loads ossv.statements and ossv.dashboard_collect
    that way on purpose, to defer the cost, and it is a subject today only because one
    other line also imports statically. Remove that line and the file still needs the
    package, which is the whole question this step asks.

    It is tried on EVERY file, not only one whose first line names python. A second review
    on 2026-11-06 found three shebangs that are python and do not say so --
    `#!/usr/bin/env -S uv run --script`, a byte-order mark before the shebang, and a file
    with no shebang at all -- and each left the subject set in silence. A file that is not
    python does not parse, and falls back to the pattern rule alone.
    """
    try:
        tree = ast.parse(blob)
    except (SyntaxError, ValueError):
        # Both, because which one a NUL byte raises has moved between versions: 3.12 and
        # 3.14 raise SyntaxError for it, and ValueError is what other builds raise. Either
        # way it is a source python could not run.
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            if any(is_the_package(a.name) for a in node.names):
                return True
        elif isinstance(node, ast.ImportFrom):
            if node.module and is_the_package(node.module):
                return True
        elif isinstance(node, ast.Call):
            named = getattr(node.func, "id", None) or getattr(node.func, "attr", None)
            if named in ("import_module", "__import__") and node.args:
                first = node.args[0]
                if isinstance(first, ast.Constant) and isinstance(first.value, str) and is_the_package(first.value):
                    return True
    return False


def expected(where=Path("bin")):
    """Every file of WHERE that this step should collect, by both rules."""
    found = set()
    for path in candidates(where):
        try:
            blob = path.read_bytes()
        except OSError:
            # grep skips a file it cannot read, so this does too: a permission is not a
            # subject rule, and crashing here would fail a tree that is fine.
            continue
        if names_the_package(blob) or imports_the_package(blob):
            found.add(str(path))
    return found


def main(argv):
    # read_bytes().decode(), and split("\n") rather than split() or splitlines(): a file
    # name may hold a space, which split() breaks into pieces, and a CR, a form feed or a
    # vertical tab, which splitlines() breaks and the bash loop does not. read_text is not
    # enough either -- it turns a CR into a newline before the split ever runs -- and
    # read_text(newline="") needs 3.13 while CI runs 3.12. Each of these fails a tree that
    # is fine.
    subjects = {line for line in Path(argv[1]).read_bytes().decode("utf-8").split("\n") if line}
    want = expected()
    missing, extra = sorted(want - subjects), sorted(subjects - want)
    if missing or extra:
        print(f"::error::the subjects this step collected are not the files of dev/stream/bin that "
              f"import the ossv package. Collected and should not have: {', '.join(extra) or 'none'}. "
              f"Did not collect and should have: {', '.join(missing) or 'none'}. A name in the second "
              f"list imports the package in a form this step's four patterns do not match, so add the "
              f"form to them; a name in the first is a bug in the loop. A check that reads less than "
              f"the tree holds reports less, so this is a failure and not a clean run.")
        return 1
    scripts = tomllib.loads(Path("pyproject.toml").read_text(encoding="utf-8"))["project"]["scripts"]
    absent = sorted(n for n in scripts if f"bin/{n}" not in subjects)
    if absent:
        print(f"::error::[project.scripts] declares {len(scripts)} entry point(s) and this check did not "
              f"collect {', '.join(absent)}: its subject rule no longer reaches the package's own launchers")
        return 1
    print(f"all {len(scripts)} [project.scripts] launcher(s) are among the subjects")
    print(f"floor: {len(subjects)} subject(s), which is every file of bin/ that imports the package")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
DEPLOYED_LAYOUT_FLOOR
# PYTHONPATH=src: the package importable as `ossv`, and nothing of bin/ on the path beyond the directory
# python itself adds for the script it runs.  `< /dev/null` because the loop's own
# stdin is the worklist: a subject that read stdin would eat the subjects after it and the step would
# report a short list as a pass.  None reads stdin today.
failed=""
while read -r f; do
  if PYTHONPATH=src timeout 60 python "$f" --help < /dev/null > /dev/null 2> "$RUNNER_TEMP/deployed-layout-err.txt"; then
    echo "ok    $f"
  else
    echo "::error::FAILS with only src/ on the path: $f"
    sed 's/^/      /' "$RUNNER_TEMP/deployed-layout-err.txt"
    failed="$failed $f"
  fi
done < "$subjects"
[ -z "$failed" ] || { echo "::error::import with only src/ on the path:$failed"; exit 1; }
echo "all $count entry point(s) import with only src/ on the path"
