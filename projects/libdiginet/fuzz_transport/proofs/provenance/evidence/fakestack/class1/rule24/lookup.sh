#!/bin/sh
# Rule-24 lookup of the donors of astack_malloc_realizes at class 1 and 2 in the released set: origin/ossv/recipes REF,
# path-scoped per unit (projects/<P>/<U>/proofs), one git grep at a time, never the whole commit.
#   lookup.sh HUB [REF]      outputs beside this file: units.txt, grep-stmt.txt, grep-decl.txt, files-sm12.txt
set -eu
HUB=$1 REF=${2:-refs/remotes/origin/ossv/recipes}
here=$(cd "$(dirname "$0")" && pwd)
git -C "$HUB" rev-parse "$REF" > "$here/ref.txt"
git -C "$HUB" ls-tree -r --name-only "$REF" projects/ | awk -F/ '$4 == "proofs" && $5 == "lib" {print $2 "/" $3}' | sort -u \
  > "$here/units.txt"
# 1. a statement of the predicate at class 1 or 2 (hypotheses and conjunct lines dropped)
P1='stack_malloc_realizes +[A-Za-z_0-9]+ +[A-Za-z_0-9]+ +[12]\b|stack_malloc[12]_contract'
# 2. every Theorem / Lemma / Corollary whose name says class 1 or 2 (statements split over lines, other predicates)
P2='(Theorem|Lemma|Corollary)[[:space:]]+[A-Za-z0-9_]*stack_malloc_?[12]([^0-9][A-Za-z0-9_]*)?[[:space:]]*:'
: > "$here/grep-stmt.txt"; : > "$here/grep-decl.txt"
while read -r u; do
  echo "## git grep -nE '$P1' $REF -- projects/$u/proofs" >> "$here/grep-stmt.txt"
  git -C "$HUB" grep -nE "$P1" "$REF" -- "projects/$u/proofs" < /dev/null | grep -v 'Hypothesis\|/\\' | cut -c1-300 \
    >> "$here/grep-stmt.txt" || true
  echo "## git grep -nE '$P2' $REF -- projects/$u/proofs" >> "$here/grep-decl.txt"
  git -C "$HUB" grep -nE "$P2" "$REF" -- "projects/$u/proofs" < /dev/null | cut -c1-260 >> "$here/grep-decl.txt" || true
done < "$here/units.txt"
# 3. the files named for class 1 / 2 of the fake stack
git -C "$HUB" ls-tree -r --name-only "$REF" projects/ | grep -E 'proofs/lib/.*(StackMalloc[12]|SM[12])[A-Za-z]*\.v$' \
  > "$here/files-sm12.txt" || true
wc -l "$here/units.txt" "$here/grep-stmt.txt" "$here/grep-decl.txt" "$here/files-sm12.txt"
