set -uo pipefail
usage='compare-step1.sh <this run work dir> <other run work dir>   (port_core --work dirs of two step-1 runs)'
A=${1:?$usage} B=${2:?$usage}
n=0; d=0
for f in $(cd "$A/stage-out" && find . -name '*.v' | sort); do
  if cmp -s "$A/stage-out/$f" "$B/stage-out/$f"; then n=$((n + 1)); else d=$((d + 1)); echo "stage-out differs: ${f#./}"; fi
done
o=$(comm -13 <(cd "$A/stage-out" && find . -name '*.v' | sort) <(cd "$B/stage-out" && find . -name '*.v' | sort) | wc -l)
echo "stage-out .v: $n byte-identical, $d differ; only in the other run: $o"
for f in $(cd "$A" && ls *.tsv *.txt); do
  if cmp -s "$A/$f" "$B/$f"; then echo "same $f"; else echo "DIFFERS $f:"; diff "$A/$f" "$B/$f" | cut -c1-300 | sed 's/^/    /'; fi
done
v=FAIL; [ "$d" -eq 0 ] && [ "$o" -eq 0 ] && [ "$n" -gt 0 ] && v=PASS
echo "GATE depot-B-step1 RULE: PASS iff every stage-out .v of this run is byte-identical to the other run's (0 differ, 0 only in the other run, at least one file); the .tsv / .txt differences listed above and port_core's exit code (3, from its cellcheck line, which both runs print) are not part of the rule. VERDICT: $v ($n byte-identical, $d differ, $o only in the other run)"
