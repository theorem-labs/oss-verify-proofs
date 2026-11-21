set -euo pipefail
since= record=
none() { echo "no lint record is read: $1"; }
hex='^[0-9a-f]{40}$'
if [ -z "$MATCHED" ]; then
  none "none was restored (no lint of this pull request with these tools passed, or the cache was not read)"
elif [ ! -f "$RECORD" ]; then
  none "the entry $MATCHED holds no record"
else
  r_pr= r_kind= r_into= r_tools= r_p1= r_p2= r_tree=
  while read -r k v w; do
    case "$k" in
      pr) r_pr=$v ;; kind) r_kind=$v ;; into) r_into=$v ;; tools) r_tools=$v ;;
      parents) r_p1=$v; r_p2=$w ;; tree) r_tree=$v ;;
    esac
  done < "$RECORD"
  tools=$(git -C head rev-parse --verify --quiet "$BASE:tools") || tools=
  if [ "$r_pr" != "$PR" ]; then
    none "the record names pull request '$r_pr', not $PR"
  elif [ "$r_kind" != "$KIND" ]; then
    none "the record names the kind of change '$r_kind', and this run's is $KIND"
  elif [ "$r_into" != "$INTO" ]; then
    none "the record is of a lint into '$r_into', and this run's is into $INTO"
  elif ! [[ "$r_tools" =~ $hex && "$r_p1" =~ $hex && "$r_p2" =~ $hex && "$r_tree" =~ $hex ]]; then
    none "the record does not name four object ids"
  elif [ "$r_tools" != "$tools" ]; then
    none "the record's base tools/ tree is $r_tools, and this run's is ${tools:-unreadable}"
  else
    deepen=()
    [ "$(git -C head rev-parse --is-shallow-repository)" != true ] || deepen=(--unshallow)
    if ! git -C head fetch --no-tags --filter=blob:none "${deepen[@]}" origin "$r_p1" "$r_p2"; then
      none "the parents the record names, $r_p1 and $r_p2, cannot be fetched"
    elif ! tree=$(git -C head merge-tree --write-tree --no-messages "$r_p1" "$r_p2"); then
      none "the parents the record names do not merge cleanly"
    elif [ "$tree" != "$r_tree" ]; then
      none "the parents the record names merge to $tree, not to the tree $r_tree it names"
    elif ! held=$(git -c core.quotePath=false -C head diff --no-renames --name-only "$tree" HEAD \
        | PYTHONPATH=base/tools python -c '
import sys
from oft import layout, lint
units = set(lint.base_pending_entries("base")) | set(lint.base_pending_entries("head"))
changed = sys.stdin.buffer.read().decode("utf-8", "surrogateescape").split("\n")
print(" ".join(sorted({u for u in map(layout.unit_of, changed) if u is not None and u in units})))'); then
      none "the licence-pending entries of the base and of this tree cannot be read"
    elif [ -n "$held" ]; then
      none "a file of $held, which a licence-pending entry names, differs from that tree"
    else
      since=$(git -C head -c user.name=pr.yml -c user.email=pr.yml@invalid commit-tree "$tree" \
        -m "the tree the last passing lint of pull request $PR read (made here, never pushed)")
      record=$MATCHED
      echo "lint record $MATCHED holds: lint compares with the tree $tree, as commit $since"
    fi
  fi
fi
{ echo "since=$since"; echo "record=$record"; } >> "$GITHUB_OUTPUT"
