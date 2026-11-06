#!/bin/bash
# tools/oft/ci/port-check.sh: the check of a tree moved to the per-project layout in the checker image, as
# CI's check job checks a tree.  An operator runs it on a scratch checkout to see a ported tree check.
#
#   WORK      the checkout to port and check; it changes in place
#   TOOLS     the tools/ directory to run: its oft and its ci/check-units.sh
#   and every variable tools/oft/ci/check-units.sh reads (UNITS, PROOF_UNITS, PROJECTS, CX_UNITS, FINDINGS, ASSETS,
#   PYDEPS, CACHE, GH_TOKEN), which it gets unchanged
#
# In WORK it runs `oft port-layout` (not with --no-port, which checks the tree in the layout it has), `oft generate`
# and `oft lint`; any of them that fails stops the script.  Then it runs check-units.sh, unchanged, through a docker
# of its own that gives each container with a writable /work (the view of one unit's part that check-units.sh checks
# it in) the folder WORK/_build/oft-port-check as its temporary folder, mounted at /oft-port-check: oft check keeps
# its logs in its temporary files, which so outlive the container and the view.  Last it prints how many
# [overriding-logical-loadpath] warnings those logs hold, the warning a ported tree gives a rocq call that loads a
# proof library under its statement folder (the layout plan, "The dune barrier").  Its exit status is check-units.sh's.
set -euo pipefail
: "${WORK:?}" "${TOOLS:?}"
port=1
case "$#:${1:-}" in
  0:) ;;
  1:--no-port) port=0 ;;
  *) echo "usage: port-check.sh [--no-port]" >&2; exit 2 ;;
esac
oft() { PYTHONPATH="$TOOLS" python3 -m oft --root "$WORK" "$@"; }
if [ "$port" = 1 ]; then oft port-layout; fi
oft generate
oft lint

logs="$WORK/_build/oft-port-check"
rm -rf -- "$logs"
mkdir -p -- "$logs"
PORT_CHECK_DOCKER="$(command -v docker)" || { echo "port-check.sh: no docker on PATH" >&2; exit 1; }
export PORT_CHECK_DOCKER
shim="$(mktemp -d)"
trap 'rm -rf -- "$shim"' EXIT
cat > "$shim/docker" <<'EOF'
#!/bin/bash
# port-check.sh's docker: a `docker run` that mounts a writable /work (a unit's view) keeps its temporary files in
# WORK/_build/oft-port-check, mounted at /oft-port-check; any other call goes to docker as it is
if [ "${1:-}" = run ]; then
  prev=
  for a in "$@"; do
    if [ "$prev" = -v ] && [[ "$a" == *:/work ]]; then
      shift
      exec "$PORT_CHECK_DOCKER" run -v "$WORK/_build/oft-port-check:/oft-port-check" -e TMPDIR=/oft-port-check "$@"
    fi
    prev=$a
  done
fi
exec "$PORT_CHECK_DOCKER" "$@"
EOF
chmod +x "$shim/docker"
rc=0
PATH="$shim:$PATH" bash "$TOOLS/oft/ci/check-units.sh" || rc=$?
n="$({ grep -ro --include='*.log' 'overriding-logical-loadpath' "$logs" || true; } | wc -l)"
echo "overriding-logical-loadpath warnings: $n (oft check's logs in $logs)"
exit "$rc"
