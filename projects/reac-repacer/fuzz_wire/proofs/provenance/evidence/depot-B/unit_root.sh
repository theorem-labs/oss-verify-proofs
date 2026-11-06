# unit_root.sh -- sourced by step1.sh, step2.sh and reloc.sh: where a unit's proof tree lies, by the layout that a commit
# or an extracted tree has, so no script hard-codes one layout. UNIT names the unit; HUB the proofs repository.
#
# unit_root REV  prints the unit's proofs root at commit REV: projects/reac-repacer/$UNIT/proofs (its lib under it), or
#                the earlier proofs/reac-repacer/$UNIT; refuses (status 1) when REV holds the unit's lib in neither.
# tgt_lib DIR    prints the unit's lib inside an extracted tree DIR; refuses when DIR holds it in both layouts or in none.

unit_root() {
  if git -C "$HUB" cat-file -e "$1:projects/reac-repacer/$UNIT/proofs/lib" 2>/dev/null; then
    echo "projects/reac-repacer/$UNIT/proofs"
  elif git -C "$HUB" cat-file -e "$1:proofs/reac-repacer/$UNIT/lib" 2>/dev/null; then
    echo "proofs/reac-repacer/$UNIT"
  else
    echo "unit_root: $1 holds no lib of $UNIT in either layout" >&2
    return 1
  fi
}

tgt_lib() {
  local a="$1/projects/reac-repacer/$UNIT/proofs/lib" b="$1/proofs/reac-repacer/$UNIT/lib"
  if [ -d "$a" ] && [ ! -d "$b" ]; then
    echo "$a"
  elif [ -d "$b" ] && [ ! -d "$a" ]; then
    echo "$b"
  else
    echo "tgt_lib: $1 holds the lib of $UNIT in both layouts or in none" >&2
    return 1
  fi
}
