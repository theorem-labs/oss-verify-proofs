#!/bin/sh
# Rule 24 for fuzz_transport's fake-stack classes 0 and 4: compare EVERY released donor of the class on each image with
# fuzz_transport's image (smcmp.py, cmpkit 86da41d3ef68), before one is chosen.
#   cands.sh CLS HUB DONORS TARGET_DIR OUTDIR
#     CLS         0 or 4
#     HUB         the git hub holding origin/ossv/recipes
#     DONORS      a directory with <P>/bin/<H>/<H>.<build> and <P>/unstripped/<H>/<H>.<build> for each candidate below
#     TARGET_DIR  bin/fuzz_transport/ and unstripped/fuzz_transport/ (the pins of WT's harness.yaml, checked by smcmp's
#                 twin step; their sha256 printed)
#     OUTDIR      one directory per candidate, and rule24-<CLS>.tsv
# The candidates are the released files that state `astack_malloc_realizes tfibsegs B <CLS>` (the statement fuzz_transport
# takes), found by one path-scoped `git grep -lE '__asan_stack_malloc_(0|4)\b|Definition CID : Z := (0|4)\.'` per
# released unit (rule24-grep.txt); each is compared over the code table its walk runs on (its own fs_ranges, or the
# table file it takes tbl_fs from), and its resolve lines are computed for the files a relocation would carry. Every
# file is read at OLD (the last origin/ossv/recipes commit with proofs/<P/H>/lib, the layout alreloc reads), except a
# donor released only in the projects/<P/H>/proofs/lib layout (reac-pw/fuzz_pin), read at the recipes tip.
set -eu
CLS=$1 HUB=$2 DD=$3 TD=$4 OUT=$5
here=$(cd "$(dirname "$0")" && pwd)
OLD=e10f488c53fc
TIP=$(git -C "$HUB" rev-parse refs/remotes/origin/ossv/recipes | cut -c1-12)
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "cands.sh: the comparison kit copy does not match its SHA256SUMS" >&2; exit 1; }
mkdir -p "$OUT"
pin() { printf '%s\n' "$1" | awk -v b="  $2:" '$0 == b {f = 1; next} f && /sha256:/ {print $2; exit}'; }
# IMG P/H REF-KIND TABLE[:VAR] RELOC... (lib-relative; REF-KIND old = OLD and proofs/<P/H>/lib, tip = TIP and
# projects/<P/H>/proofs/lib)
case $CLS in
0) list='A libreac/fuzz_decode old A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v
A libreac/fuzz_disco old A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v
A libreac/fuzz_ctrl old A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v
A libreac/fuzz_grant old A/Rt/AF0r.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v A/Rt/AF0r.v
A libreac/fuzz_identity old A/Rt/StackMallocTbl.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v A/Rt/StackMallocTbl.v
A libreac/fuzz_pcap old A/AF0r.v A/StackMalloc0Tbl.v A/StackMalloc0.v A/AF0r.v
A plugin-hostd/fuzz_command old A/Rt/RtSM1T.v A/Rt/RtSM0T.v A/Rt/RtSM0.v A/Rt/RtSM1T.v
A reac-pw/fuzz_pin tip A/Rt/StackMallocTbl.v A/Rt/StackMalloc0Tbl.v A/Rt/StackMalloc0.v A/Rt/StackMallocTbl.v
B libreac/fuzz_decode old B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0.v
B libreac/fuzz_ctrl old B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0.v
B libreac/fuzz_grant old B/Rt/YF0r.v B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0.v B/Rt/YF0r.v
B libreac/fuzz_identity old B/Rt/StackMallocTbl.v B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0.v B/Rt/StackMallocTbl.v
B libreac/fuzz_pcap old Reusable/YF0r.v B/StackMalloc0Tbl.v B/StackMalloc0.v Reusable/YF0r.v
B plugin-hostd/fuzz_command old B/Rt/RtSM1T.v B/Rt/RtSM0T.v B/Rt/RtSM0.v B/Rt/RtSM1T.v
B reac-pw/fuzz_pin tip AU/Rt/StackMallocTbl.v AU/Rt/StackMalloc0Tbl.v AU/Rt/StackMalloc0.v AU/Rt/StackMallocTbl.v' ;;
4) list='A libreac/fuzz_grant old A/Rt/AF0r.v A/Rt/StackMalloc4Tbl.v A/Rt/StackMalloc4.v A/Rt/AF0r.v
A libreac/fuzz_identity old A/Rt/StackMallocTbl.v A/Rt/StackMalloc4Tbl.v A/Rt/StackMalloc4.v A/Rt/StackMallocTbl.v
A plugin-hostd/fuzz_command old A/Rt/RtSM1T.v A/Rt/RtSM4T.v A/Rt/RtSM4.v A/Rt/RtSM1T.v' ;;
*) echo "cands.sh: class 0 or 4" >&2; exit 1 ;;
esac
tsv="$OUT/rule24-$CLS.tsv"
printf 'img\tdonor\tref\tfiles\tdonor pin\tverdict\tranges\tpcrel walked\tpcrel whole fns\tresolve moves\tlayout move\n' > "$tsv"
printf '%s\n' "$list" | while read -r I PH kind tbl files; do
  b=asan; [ $I = B ] && b=asan-ubsan
  P=${PH%/*} H=${PH#*/}
  if [ $kind = old ]; then ref=$OLD lib=proofs/$PH/lib; else ref=$TIP lib=projects/$PH/proofs/lib; fi
  dp="$DD/$P/bin/$H/$H.$b" du="$DD/$P/unstripped/$H/$H.$b"
  tp="$TD/bin/fuzz_transport/fuzz_transport.$b" tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
  want=$(pin "$(git -C "$HUB" show "$ref:projects/$PH/harness.yaml")" $b)
  [ "$(sha256sum < "$dp" | cut -c1-64)" = "$want" ] || { echo "cands.sh: $dp is not $ref's $b pin" >&2; exit 1; }
  # the file at OLD is the file the recipes tip releases (the layout move changed no byte)
  lm=same
  if [ $kind = old ]; then
    for f in $files; do
      [ "$(git -C "$HUB" rev-parse "$OLD:proofs/$PH/lib/$f")" = "$(git -C "$HUB" rev-parse "$TIP:projects/$PH/proofs/lib/$f")" ] ||
        { lm="DIFFERS($f)"; }
    done
  fi
  o="$OUT/$H-$I"
  rc=0
  python3 "$here/smcmp.py" --hub "$HUB" --ref $ref --src $PH --donor-lib $lib --img $I --cls $CLS \
    --donor "$dp" "$du" --target "$tp" "$tu" --out "$o" --tables "$tbl" --reloc $files > "$o.log" 2>&1 || rc=1
  v=PASS; [ $rc = 0 ] || v="FAIL($(grep -c '^FAIL' "$o.log" || true))"
  ln=$(grep ' ranges paired and compared' "$o.log" || echo '')
  rg=$(printf '%s' "$ln" | sed -n 's/.*: \([0-9]* of [0-9]*\) ranges.*/\1/p')
  pw=$(printf '%s' "$ln" | sed -n 's/.*pc-relative words \([0-9]*\) (walked), \([0-9]*\) (whole functions).*/\1/p')
  pf=$(printf '%s' "$ln" | sed -n 's/.*pc-relative words \([0-9]*\) (walked), \([0-9]*\) (whole functions).*/\2/p')
  mv=$(sed -n 's/.* resolve lines: \([0-9]*\) move a value.*/\1/p' "$o.log")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' $I $PH $ref "$files" "$(echo $want | cut -c1-12)" "$v" "$rg" "$pw" "$pf" "$mv" "$lm" >> "$tsv"
  echo "$I $PH ($ref): $v; ranges $rg; pc-relative words $pw walked / $pf whole; $mv resolve moves; layout move: $lm"
done
# the closeness measure (closeness.py): words differing by a pc-relative offset over the functions every candidate walks
python3 "$here/closeness.py" $CLS "$OUT" | tee "$OUT/rule24-$CLS-closeness.txt"
