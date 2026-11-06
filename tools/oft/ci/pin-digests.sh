#!/usr/bin/env bash
# pin-digests.sh COMMIT: the two digests tools/oft/migration-pin.yaml names for the change whose tree is COMMIT's, as
# .github/workflows/pr.yml's plan step computes them over a pull request's merge commit, one line each:
#   digest <64 hex>   the plan step's head_digest: every file of tools/ and theories/ with its mode, object id and path,
#                     in git's order, and the attributes git checks those files out with, the pin file left out
#   tree <64 hex>     the plan step's tree_digest: every file of the tree with its mode, object id and path, in git's
#                     order, the pin file left out (the tree a deferred check's pin names)
# The pin file is left out of both, so a pin set on the base moves neither.  Run it anywhere in a clone that has
# COMMIT (it reads from the top of the clone).  It shares nothing with pr.yml but its commands;
# tools/oft/tests/test_workflow_verdicts.PlanToolsTest holds the two equal.  The plan step runs on a runner whose git
# has no configuration of its own, so the commands here leave out what a clone's configuration could add: paths are
# quoted as git's default quotes them (core.quotePath), and no attributes file of the user or the system counts.  The
# clone's own attributes file ($GIT_DIR/info/attributes), which no configuration turns off, stops the script when it
# holds anything.
# Exit 0; 1 when the clone has no working tree, COMMIT is no commit here, the clone has its own attributes, or git
# fails; 2 for a usage error.
set -euo pipefail
[ $# -eq 1 ] || { echo "usage: pin-digests.sh COMMIT" >&2; exit 2; }
export GIT_ATTR_NOSYSTEM=1
g=(git -c core.quotePath=true -c core.attributesFile=/dev/null)
top=$("${g[@]}" rev-parse --show-toplevel) || { echo "pin-digests.sh: run it in a clone with a working tree" >&2; exit 1; }
cd "$top"
commit=$("${g[@]}" rev-parse --verify --quiet "$1^{commit}") || { echo "pin-digests.sh: $1 is no commit here" >&2; exit 1; }
info=$("${g[@]}" rev-parse --git-path info/attributes)
[ ! -s "$info" ] || {
  echo "pin-digests.sh: $info sets attributes that a runner's checkout does not have, so the digest would differ" >&2
  exit 1; }
files=$("${g[@]}" ls-tree -r "$commit" -- tools theories | grep -v $'\ttools/oft/migration-pin\\.yaml$')
digest=$({ echo "$files"
           cut -f2 <<< "$files" | "${g[@]}" check-attr --stdin --source="$commit" \
             text eol crlf filter ident working-tree-encoding
         } | sha256sum | cut -d' ' -f1)
tree=$("${g[@]}" ls-tree -r "$commit" | { grep -v $'\ttools/oft/migration-pin\\.yaml$' || [ $? -eq 1 ]; } |
       sha256sum | cut -d' ' -f1)
printf 'digest %s\ntree %s\n' "$digest" "$tree"
