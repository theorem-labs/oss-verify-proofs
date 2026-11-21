set -euo pipefail
read -r -a units <<< "${UNITS:-}"
[ "${#units[@]}" -gt 0 ] || { echo "this job checks no unit's statements"; exit 0; }
# -P: the base's copy alone on the path, not the working directory before it (python puts that first)
PYTHONPATH="$RUNNER_TEMP/base-tools" python -P - "$WORK" "${units[@]}" <<'PY'
import os, sys
from oft import facts, generate, layout
root, units = sys.argv[1], sys.argv[2:]
tree = facts.load(root)
def holds_exactly(path, text):
    if os.path.islink(path) or not os.path.isfile(path):
        return False
    with open(path, "rb") as f:
        return f.read() == text.encode("utf-8")
bad = []
for unit in units:
    p, hn = layout.split_unit(unit)
    h = tree.projects[p].harnesses[hn]
    rendered = {os.path.join(layout.proofs_dir(p, hn, layout.NEW), "dune"): generate.barrier_dune(),
                os.path.join(layout.statement_dir(p, hn), "dune"): generate.harness_dune(h)}
    d = layout.proofs_dir(p, hn, layout.NEW)
    while True:
        for f in layout.DUNE_FILES:
            path = os.path.join(d, f)
            if path == "dune-project" or not os.path.lexists(os.path.join(root, path)):
                continue
            if path not in rendered:
                bad.append("%s: no directory above %s's statements holds a build file" % (path, unit))
            elif not holds_exactly(os.path.join(root, path), rendered[path]):
                bad.append("%s: differs from its rendering (run ./oft generate)" % path)
        if not d:
            break
        d = os.path.dirname(d)
for line in bad:
    print("::error::%s" % line)
if bad:
    sys.exit(1)
print("the build files above the statements of %d unit(s) are the tools' own rendering" % len(units))
PY
