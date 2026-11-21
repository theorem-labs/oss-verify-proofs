set -euo pipefail
# fail closed: the parts this run planned are checked here, as they are today
no() { echo "the checks run here: $1"; echo "checked_elsewhere=false" >> "$GITHUB_OUTPUT"; exit 0; }
if [ "$DEFERRED" = true ]; then
  # the tree the base pins with a deferred check: the pin names that tree, and what it defers is the check
  # jobs, not the rules that judged it, so it holds whichever tools the plan step named
  [ -n "$CHECK_OF_RECORD" ] || { echo "::error::a deferred check with no check of record"; exit 1; }
  { echo "checked_elsewhere=true"; echo "checked_elsewhere_note=the check of record: $CHECK_OF_RECORD"
  } >> "$GITHUB_OUTPUT"
  echo "the tree the base pins for a deferred check; the check of record: $CHECK_OF_RECORD"
  exit 0
fi
case "$GITHUB_EVENT_NAME" in
  merge_group) ;;
  pull_request)
    # a draft's check waits until it is ready for review, and required reads it as a draft first: unchanged
    [ "$HOLD" != draft ] || no "a draft"
    case "$PR" in ''|*[!0-9]*) no "no pull request number" ;; esac
    [[ "$PR_HEAD" =~ ^[0-9a-f]{40}$ ]] || no "the event gave no head commit for pull request $PR"
    # the tree the plan keyed is the merge commit checked out in head/, so it must merge that very head: its
    # second parent, read from the commit itself as the base step reads its first (a clone one commit deep
    # gives HEAD no parents to rev-parse)
    merged=$(git -C head cat-file -p HEAD | sed -n 's/^parent //p' | sed -n 2p) || merged=
    [ "$merged" = "$PR_HEAD" ] || \
      no "this run's merge commit merges ${merged:-no second parent}, not the event's head $PR_HEAD" ;;
  *) no "neither a pull request nor a merge queue group" ;;
esac
[ "$ROUTED" = true ] || no "no base to compare with"
[ -s "$RUNNER_TEMP/changed.txt" ] || no "no changed path read from the change's diff"
# the paths, by the base's tools (plan.py, which keys.NOT_THE_CHECKER leaves out of every key)
PYTHONPATH=base/tools python -c 'import sys; from oft import plan
for path in plan.paths_a_check_reads(open(sys.argv[1]).read().split("\n")): print(path)' \
  "$RUNNER_TEMP/changed.txt" > "$RUNNER_TEMP/vm-paths.txt" || no "the change's paths cannot be read"
if [ -s "$RUNNER_TEMP/vm-paths.txt" ]; then
  no "$(wc -l < "$RUNNER_TEMP/vm-paths.txt") changed path(s) a check reads, the first $(head -n 1 "$RUNNER_TEMP/vm-paths.txt")"
fi
if [ "$GITHUB_EVENT_NAME" = pull_request ]; then
  # a pull request's run: the pull request itself, for the head this run's merge commit merges
  prs="$PR" last="$PR" of="pull request $PR"
else
  # the pull requests of the group: the queue branch's own, and one per commit from the base to this commit
  case "$REF_NAME" in
    gh-readonly-queue/*/pr-*-"$BASE") last="${REF_NAME##*/pr-}"; last="${last%-"$BASE"}" ;;
    *) no "the queue branch $REF_NAME does not name this group's base $BASE" ;;
  esac
  case "$last" in ''|*[!0-9]*) no "the queue branch $REF_NAME names no pull request" ;; esac
  gh api "repos/$GITHUB_REPOSITORY/compare/$BASE...$GROUP_HEAD" > "$RUNNER_TEMP/vm-compare.json" \
    || no "the group's commits cannot be read"
  jq -e 'type == "object" and (.commits | type) == "array"' "$RUNNER_TEMP/vm-compare.json" > /dev/null 2>&1 \
    || no "the compare of this group is no commit list"
  total=$(jq -r '.total_commits // ""' "$RUNNER_TEMP/vm-compare.json")
  read_commits=$(jq -r '.commits | length' "$RUNNER_TEMP/vm-compare.json")
  case "$total" in ''|*[!0-9]*) no "the compare of $BASE with this commit gave no count" ;; esac
  [ "$total" = "$read_commits" ] || \
    no "the group has $total commit(s) and one page of the compare read $read_commits"
  [ "$total" -gt 0 ] || no "the group has no commit of its own"
  prs=$(jq -r '.commits[].commit.message | split("\n")[0]' "$RUNNER_TEMP/vm-compare.json" \
    | sed -n 's/.*(#\([0-9][0-9]*\))$/\1/p')
  [ "$(grep -c '^[0-9]' <<< "$prs" || true)" = "$total" ] || \
    no "a commit of the group names no pull request at the end of its first line"
  # one pull request per commit, and the queue branch's is the last commit's: a group is one commit per entry
  [ "$(sort -nu <<< "$prs" | grep -c '^[0-9]' || true)" = "$total" ] || \
    no "the group's $total commit(s) name fewer pull requests: $(tr '\n' ' ' <<< "$prs")"
  [ "$(tail -n 1 <<< "$prs")" = "$last" ] || \
    no "the queue branch names pull request $last and the group's last commit names $(tail -n 1 <<< "$prs")"
  prs=$(sort -nu <<< "$prs") of="every pull request of this group"
fi
evidence=
# one `<pull request> <unit> <key>` line per evidence key line: the pull request names whose entry a key
# that differs belongs to, and the two last fields alone are what plan.vm_evidence_keys reads
: > "$RUNNER_TEMP/vm-key-prs.txt"
: > "$RUNNER_TEMP/vm-checkers.txt"
for VM_PR in $prs; do
  if [ "$GITHUB_EVENT_NAME" = pull_request ]; then
    VM_HEAD="$PR_HEAD"
  else
    VM_HEAD=$(gh api "repos/$GITHUB_REPOSITORY/pulls/$VM_PR" --jq '.head.sha') \
      || no "pull request $VM_PR cannot be read"
    [[ "$VM_HEAD" =~ ^[0-9a-f]{40}$ ]] || no "pull request $VM_PR gave no head commit"
  fi
  # vm evidence
  # merge-pr.sh's VM evidence comment on pull request VM_PR for the commit VM_HEAD: posted by the App
  # (user.type Bot), its first line exactly `<!-- vm-evidence head=<VM_HEAD> mode=<pvc|xh|checklog> -->`,
  # and changed since by nobody but the App either (GitHub keeps every editor in userContentEdits, which only
  # GraphQL gives).  `said` becomes that comment's "(mode): <its url>", its node id, and one
  # `key <unit> <key>` line for each `<!-- vm-evidence-key unit=<project>/<harness> key=<64 hex> -->` line
  # after the marker in it, the unit's build key at the tree its check of record ran on, and one
  # `checker <id>` line for each `<!-- vm-evidence-checker id=<64 hex> -->` line after the marker, the
  # keys.checker of the tree that check of record ran on: a key says nothing about the tools that
  # computed it, so the marker names them, and a marker with no such line, with more than one, or with
  # another id than this tree's is refused where the keys are read (plan.vm_evidence_checker).
  # Of the comments
  # that carry the marker the newest answers, since a later run of merge-pr.sh posts a later comment:
  # --slurp hands the whole list to one jq program, so `last` is the newest of every page, not of each;
  # the CLI refuses --slurp with its own --jq, so the pages go through jq here, with HEAD_SHA exported.
  # A marker for another commit, by anyone else, or not on the first line counts for nothing, and so does
  # a comment anyone else changed and a read that fails: `said` is empty then.  What is checked is the
  # comment, not the VM check it reports.
  # shellcheck disable=SC2016  # a jq program: $lines and $mode are jq's, not the shell's
  said="$(export HEAD_SHA="$VM_HEAD"
    gh api --paginate --slurp "repos/$GITHUB_REPOSITORY/issues/$VM_PR/comments?per_page=100" | jq -r '
    [ .[][] | select(.user.login == env.VM_EVIDENCE_BY and .user.type == "Bot")
      | (.body | split("\n")) as $lines
      | first(("pvc", "xh", "checklog")
              | select($lines[0] == "<!-- vm-evidence head=\(env.HEAD_SHA) mode=\(.) -->")) as $mode
      | {mode: $mode, url: .html_url, node: .node_id,
         keys: [$lines[1:][]
                | capture("^<!-- vm-evidence-key unit=(?<unit>[^ ]+) key=(?<key>[0-9a-f]{64}) -->$")],
         checker: [$lines[1:][]
                   | capture("^<!-- vm-evidence-checker id=(?<id>[0-9a-f]{64}) -->$").id]}
    ] | last // empty
    | "(\(.mode)): \(.url)", "node \(.node)", (.keys[] | "key \(.unit) \(.key)"),
      (.checker[] | "checker \(.)")')" || said=
  if [ -n "$said" ]; then
    # The comment's author and every editor of it are the App: GraphQL names an App `Bot` and gives its
    # login without the `[bot]` REST appends, so the author must be a Bot whose login and `[bot]` is
    # VM_EVIDENCE_BY and every editor a Bot of that same login.  An edit list that is no list, more edits
    # than this one page holds, and a read that fails all count as a stranger; a read that fails says so
    # with the error, since a token refused this field would otherwise look like a comment someone changed.
    err="$(mktemp)"   # the read's stderr, apart from its answer: a warning on success must not change it
    # shellcheck disable=SC2016  # a GraphQL query: $id is GraphQL's, not the shell's
    strangers="$(gh api graphql -f query='query($id: ID!) { node(id: $id) { ... on IssueComment {
        author { __typename login }
        userContentEdits(first: 100) { totalCount nodes { editor { __typename login } } } } } }' \
      -F id="$(sed -n 's/^node //p' <<< "$said" | head -n 1)" \
      --jq '.data.node as $c | ($c.author.login // "") as $who
            | [ (if $c.author.__typename == "Bot" and ($who + "[bot]") == env.VM_EVIDENCE_BY
                 then 0 else 1 end),
                (if ($c.userContentEdits.nodes | type) == "array" then 0 else 1 end),
                (if ($c.userContentEdits.totalCount // 0) > 100 then 1 else 0 end),
                ([$c.userContentEdits.nodes[]?
                  | select(.editor.__typename != "Bot" or (.editor.login // "") != $who)] | length)
             ] | add' 2> "$err")" \
     || { echo "::warning::the editors of pull request $VM_PR's evidence comment cannot be read:"\
            "$(tr '\r\n' '  ' < "$err")"; strangers=unread; }
    rm -f "$err"
    [ "$strangers" = 0 ] || said=
  fi
  # end of vm evidence
  [ -n "$said" ] || \
    no "pull request $VM_PR has no VM evidence comment for its head $VM_HEAD (or its comments cannot be read)"
  { grep '^key ' <<< "$said" || [ $? -eq 1 ]; } | sed "s/^key /$VM_PR /" >> "$RUNNER_TEMP/vm-key-prs.txt"
  # one `<pull request> <id>...` line per pull request, with the checker ids its marker named, however
  # many that is: none and more than one are refusals of their own (plan.vm_evidence_checker).  The read
  # is its own command, not a substitution inside printf, whose status would hide a read that failed
  # part way and leave one id of two.
  checker_ids=$({ grep '^checker ' <<< "$said" || [ $? -eq 1 ]; } | sed 's/^checker //' | tr '\n' ' ') \
    || no "pull request $VM_PR's evidence comment cannot be read for the checker ids it names"
  printf '%s\n' "$VM_PR $checker_ids" >> "$RUNNER_TEMP/vm-checkers.txt"
  evidence="${evidence:+$evidence, }#$VM_PR $VM_HEAD $(head -n 1 <<< "$said")"
done
cut -d' ' -f2,3 "$RUNNER_TEMP/vm-key-prs.txt" > "$RUNNER_TEMP/vm-keys.txt"
# every planned part is a unit's build, with the key its check of record ran on (plan.vm_evidence_keys)
[ -s "$RUNNER_TEMP/plan.json" ] || no "the plan left no parts to read"
# A unit whose pull request's evidence recorded another key: the comment is the App's (above) and was
# measured on another tree, so a check here would measure a tree its owner never measured, and would hold
# every entry behind it meanwhile.  That entry leaves the queue instead: a group that fails takes out the
# entry its branch names and no other (GitHub, "Managing a merge queue"), so this group may fail for its
# own last entry alone; an earlier entry's stale key leaves this group its checks, and the group its own
# branch names takes it out.  Only a unit one pull request recorded, under one key, answers here: a unit
# two pull requests recorded, or one recorded under two keys, is left to the key comparison below.
stale=$(PYTHONPATH=base/tools python -c 'import json, sys; from oft import plan
recorded = {}
for line in open(sys.argv[2]):
    number, unit, key = line.split()
    recorded.setdefault(unit, set()).add((number, key))
for part in json.load(open(sys.argv[1])).get("parts", []):
    if not part.get("check") or part.get("part") != "build":
        continue
    rows = recorded.get(part["unit"], set())
    if len(rows) != 1:
        continue
    (number, was), = rows
    if was != part["key"] and not plan.rulings_allow(part["components"], was):
        print(number, part["unit"], was, part["key"])' \
  "$RUNNER_TEMP/plan.json" "$RUNNER_TEMP/vm-key-prs.txt") \
  || no "the planned parts' keys cannot be read"
if [ -n "$stale" ]; then
  # only the shape this step prints answers, as the verdict below takes only its two words: anything
  # else is a reading that did not happen, and the checks run here
  while read -r line; do
    [[ "$line" =~ ^[0-9]+\ [^\ ]+\ [0-9a-f]{64}\ [0-9a-f]{64}$ ]] \
      || no "a key that differs was not read as one pull request, one unit and two keys: $line"
  done <<< "$stale"
  # A pull request's run: its evidence was measured on another tree (its head moved after that check, or
  # something the check reads moved on the base), so the check runs here, on this run's tree
  if [ "$GITHUB_EVENT_NAME" = pull_request ]; then
    read -r stale_pr stale_unit stale_was stale_key <<< "$(head -n 1 <<< "$stale")"
    stale_said="pull request $stale_pr's VM evidence recorded key $stale_was for $stale_unit"
    no "$stale_said and this run's key for it is $stale_key"
  fi
  # the last entry's own, if it has one: that is the entry a failure here takes out
  own=$(awk -v last="$last" '$1 == last { print; exit }' <<< "$stale")
  read -r stale_pr stale_unit stale_was stale_key <<< "${own:-$(head -n 1 <<< "$stale")}"
  stale_said="pull request $stale_pr's VM evidence recorded key $stale_was for $stale_unit and this"
  stale_said="$stale_said group's key for it is $stale_key"
  if [ -n "$own" ]; then
    echo "::error::$stale_said: this entry leaves the merge queue, for its owner to measure"\
      "$stale_unit again at its new head and queue it again"
    echo "### this entry leaves the merge queue: $stale_said" >> "$GITHUB_STEP_SUMMARY"
    exit 1
  fi
  no "$stale_said, and pull request $stale_pr is not this group's last entry $last, the one a failure"\
    "here would take out"
fi
# The checker of the tree this group checks, by the base's tools and from the checkout the plan keyed:
# the id every marker must name, so that a key computed with other tools than the run used cannot stand
# for that run (the OSS Verify lead, 2026-11-06 18:10Z).
group_checker=$(PYTHONPATH=base/tools python -c 'from oft import keys
print(keys.checker("head", "HEAD"))') || no "the checker of this tree cannot be read"
echo "the checker of the tree this run checks: $group_checker"
verdict=$(PYTHONPATH=base/tools python -c 'import json, sys; from oft import plan
ok, why = plan.vm_evidence_keys(json.load(open(sys.argv[1])).get("parts", []),
                                open(sys.argv[2]).read().splitlines(), sys.argv[3],
                                open(sys.argv[4]).read().splitlines())
print(("ok " if ok else "no ") + why)' "$RUNNER_TEMP/plan.json" "$RUNNER_TEMP/vm-keys.txt" \
  "$group_checker" "$RUNNER_TEMP/vm-checkers.txt") \
  || no "the planned parts' keys cannot be read"
case "$verdict" in
  ok\ *) echo "${verdict#ok }" ;;
  no\ *) no "${verdict#no }" ;;
  *) no "the planned parts' keys were not read ($verdict)" ;;
esac
{ echo "checked_elsewhere=true"
  echo "checked_elsewhere_note=merge-pr.sh's VM evidence, each planned part's key equal to its check of"\
    "record's: $evidence"; } >> "$GITHUB_OUTPUT"
# as a deferred check does: an empty plan file leaves the drafts step plan=[] and draft_legs=[], so no
# check job and no fetch-drafts leg (whose token has contents: write) has a group to start
: > "$RUNNER_TEMP/plan.json"
echo "::notice::$of was checked on a VM, at a tree with these parts' keys: no check job runs here;"\
  "the evidence: $evidence"
{ echo "### no part is checked here: $of was checked on a VM, at a tree with these parts' keys"
  echo "The evidence: $evidence"; } >> "$GITHUB_STEP_SUMMARY"
