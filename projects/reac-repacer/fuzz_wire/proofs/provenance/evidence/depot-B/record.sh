set -euo pipefail
usage='record.sh <step2 out dir> <record dir to write, must not exist>'
OUT=${1:?$usage} REC=${2:?$usage}
[ ! -e "$REC" ] || { echo "record: $REC exists" >&2; exit 2; }
mkdir -p "$REC"
for f in files2.txt zify-flag-sets.txt overrides-knockB.tsv overrides-knockB-roles.tsv yd3d-env.patch mk-glue-B.log consumers.txt \
         closure.txt consumer-classes-B.tsv consumer-residue-B.txt rows-B.tsv rows.args consumer-apply-B.log \
         closure-glue-B.log closure-awalk-B.log notice-split-B.log ad1g-guard-B.log tail-generalize-B.log d1w-close-B.log zify-flag-false-B.log zify-flag-true-B.log \
         leak-gate-B.tsv refused-left.txt; do
  cp "$OUT/$f" "$REC/$f"
done
# the relocation diff does not ship: its added lines copy .v comments of the image-A text that name lanes (inherited
# inside a .v file, new inside a patch). It goes to the unit's internal record, and MANIFEST.md cites it there.
if [ -n "${PATCH_OUT:-}" ]; then cp "$OUT/applied/depot.patch" "$PATCH_OUT"; echo "record: the relocation diff is at $PATCH_OUT, sha256 $(sha256sum < "$PATCH_OUT" | cut -d' ' -f1)"; fi
grep -e '^reloc' -e '^port_core: ' "$OUT/reloc.log" > "$REC/reloc-summary.txt"
v=FAIL
[ ! -s "$REC/refused-left.txt" ] && grep -q 'files with refused markers 0' "$REC/reloc-summary.txt" \
  && grep -q 'Required modules found nowhere 0' "$REC/reloc-summary.txt" && v=PASS
echo "GATE depot-B-relocation RULE: PASS iff refused-left.txt is empty AND the port_core FAIL-rows line reads 'files with refused markers 0' AND it reads 'Required modules found nowhere 0'; port_core's exit code (3, from its cellcheck line) is not part of the rule. VERDICT: $v" >> "$REC/reloc-summary.txt"
# fail closed on everything the record copies from the run (every file above is input text): a host path, a worker or
# lane name (a one-letter role, a hyphen and a name, or a box or dec number), a working-branch ref or a session id is refused, and the record
# directory is removed so no partial record is left. The same pattern is in map_rows.py.
REFUSE='(^|[^A-Za-z0-9_])([hcr]-[a-z][a-z0-9]*(-[a-z0-9]+)*|box-[0-9]+|dec-[0-9]+)([^A-Za-z0-9_]|$)|cold/|01a1[0-9a-f]{4}-[0-9a-f]{4}-|/(home|mnt|tmp|dev/shm)/'
if grep -rnE "$REFUSE" "$REC" >&2; then echo "record: REFUSED: the lines above carry worker / lane / branch / session / host text" >&2; rm -rf "$REC"; exit 1; fi
echo "record: $(ls "$REC" | wc -l) files in $REC"
