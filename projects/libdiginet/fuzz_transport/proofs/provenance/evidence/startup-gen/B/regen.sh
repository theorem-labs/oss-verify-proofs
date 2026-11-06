#!/usr/bin/env bash
# regen.sh -- ONE command that remakes this unit's image-B start-up layer (the 19 lib/B files README.md lists) from its
# pinned asan-ubsan image (image B) and its unstripped twin, with the pinned asan image (image A) and its twin. Data only;
# rule 24: no function is proved here.
#
#   SITE=<site file> UBSAN=.. UBSAN_TWIN=.. IMAGE=.. TWIN=.. OUT=.. regen.sh [STEP ...]
#
# THE KIT IS AN INTERNAL RECORD. The scripts, gates, tables and run records that do the work are not in this tree.
# KIT-MANIFEST names each kit file by its records path, its sha256, its mode and its path in the kit. The `drivers` step
# fetches every KIT-MANIFEST row from the internal records ref (SITE: RECORDS_REPO, RECORDS_REF) into $WORK/kit, checks each
# file against its KIT-MANIFEST sha256 whatever commit it came from, and refuses the run when a file is missing or has
# another sha256 (then nothing is fetched). KIT-MANIFEST lists the kit's CODE and DOC files (the record's KIT.tsv classes);
# the record's RUN files (its run outputs and logs) stay on the records ref and are not fetched. The `kit` step lays
# the fetched kit out as a lane (the kit's tools/kit_unpack.sh, which copies the CODE files and fetches by commit,
# sha256-checked, the tools the kit cites but does not hold) and the `run` step runs the kit's own tools/regen.sh on the
# four pinned files: every stage after its own control, the gates last.
#
# STEPS (none given: drivers kit run). `run FROM` resumes the kit at a stage (README.md, "The steps and the tool versions of each").
# The `drivers` step: the fetch above with its two controls (a KIT-MANIFEST with one sha256 digit changed, and one naming a
# records path the ref does not hold, are each refused), a SITE without RECORDS_REF refused, and the shipped-tree scan
# (the release scanner of record over this tree, pinned below, with a planted control).
#
# Environment:
#   SITE      an env file OUTSIDE this tree that sets every host location and workspace name of the run (site.env.example
#             lists each). This file reads RECORDS_REPO, RECORDS_REF, SCANNER and ROSTER from it; the kit reads the rest
#             (its env.sh template refuses an unset one, naming it); a name not in site.env.example is refused here.
#   UBSAN UBSAN_TWIN IMAGE TWIN   image B and its twin, image A and its twin (README.md, "The pinned build")
#   OUT       output root; work files go under WORK (default $OUT/.work), the kit under $WORK/kit, the lane under $WORK/t4
# Exit status: 0 only when every step's controls and gates pass.
set -uo pipefail
H=$(cd "$(dirname "$0")" && pwd)
: "${UBSAN:?set UBSAN}" "${UBSAN_TWIN:?set UBSAN_TWIN}" "${IMAGE:?set IMAGE}" "${TWIN:?set TWIN}" "${OUT:?set OUT}"
: "${SITE:?set SITE=<the site file of this host: every host location and workspace name of the run; see site.env.example>}"
[ -f "$SITE" ] || { echo "regen: REFUSED: SITE $SITE is not a file"; exit 2; }
case "$(cd "$(dirname "$SITE")" && pwd)/" in "$H"/*) echo "regen: REFUSED: SITE $SITE is inside this tree (it names host locations)"; exit 2 ;; esac
# the release scanner of record, pinned by the sha256 of the SHA256SUMS file in its directory (the scanner, its
# exceptions table and its tests; that directory must hold exactly those files)
SCANNER_SUMS=c300ad1fd8b65598c2ceacc2da03da7b7d0083335dd64ecb9ff54cdd91e95685
OWN_VARS="RECORDS_REPO RECORDS_REF SCANNER ROSTER"
KNOWN=$(sed -n 's/^\([A-Z_][A-Z0-9_]*\)=.*/\1/p' "$H/site.env.example" | tr '\n' ' ')
unknown=
while IFS= read -r l || [ -n "$l" ]; do
  case "$l" in ''|'#'*) continue ;; esac
  k=${l%%=*}
  case " $KNOWN " in *" $k "*) ;; *) unknown="$unknown $k"; continue ;; esac
  [ -n "${!k:-}" ] || export "$k=${l#*=}"
done < "$SITE"
[ -z "$unknown" ] || { echo "regen: REFUSED: SITE $SITE sets names site.env.example does not list:$unknown"; exit 2; }
miss=; for k in $KNOWN; do [ -n "${!k:-}" ] || miss="$miss $k"; done
[ -z "$miss" ] || { echo "regen: REFUSED: SITE $SITE does not set:$miss (see site.env.example)"; exit 2; }
# the records commit, resolved once: every kit file is read at it
RREV=$(git -C "$RECORDS_REPO" rev-parse --verify -q "$RECORDS_REF^{commit}") ||
  { echo "regen: REFUSED: RECORDS_REF $RECORDS_REF is not a commit of RECORDS_REPO $RECORDS_REPO"; exit 2; }
WORK=${WORK:-$OUT/.work}
UNIT=$(cd "$H/../../../.." && pwd)   # the unit directory: provenance/ and lib/
UNIT_TREE=$(git -C "$H" rev-parse --show-toplevel 2> /dev/null) || UNIT_TREE=$(cd "$UNIT/../../.." && pwd)
TARGET=${UNIT#"$UNIT_TREE"/proofs/}
KROOT=$WORK/kit
KH=$KROOT/proofs/$TARGET/provenance/startup-gen/B   # the kit, at its place in the records' layout below a checkout root
STEPS=${*:-drivers kit run}
mkdir -p "$OUT" "$WORK" || exit 2
LOG=$OUT/kit.$(date -u +%Y%m%dT%H%M%SZ).log
say() { printf '%s\n' "regen: $*" | tee -a "$LOG"; }
sha() { sha256sum "$1" | cut -c1-64; }

# fetch_kit KIT-MANIFEST DEST: every row of KIT-MANIFEST from the internal records ref at RREV into DEST (made new), each file
# with the sha256 and the mode KIT-MANIFEST gives. Prints the file count. A malformed row, a records path the ref does not
# hold or another sha256 prints `REFUSED: <why>`, removes what it fetched and returns 1: DEST is not made.
fetch_kit() {
  local m=$1 dest=$2 tmp rp sum mode kp more got n=0 bad=
  [ ! -e "$dest" ] || { echo "REFUSED: $dest exists"; return 1; }
  mkdir -p "$(dirname "$dest")" && tmp=$(mktemp -d "$dest.part.XXXXXX") || { echo "REFUSED: cannot make $dest"; return 1; }
  while IFS=$'\t' read -r rp sum mode kp more; do
    case "$rp" in ''|'#'*) continue ;; esac
    if ! [[ $sum =~ ^[0-9a-f]{64}$ && $mode =~ ^(644|755)$ && -n $kp && -z $more && $kp != /* && /$kp/ != */../* ]]; then
      bad="the KIT-MANIFEST row of $rp is malformed"; break
    fi
    [ ! -e "$tmp/$kp" ] || { bad="KIT-MANIFEST names the kit path $kp twice"; break; }
    mkdir -p "$(dirname "$tmp/$kp")" || { bad="cannot make the kit directory of $kp"; break; }
    git -C "$RECORDS_REPO" cat-file blob "$RREV:$rp" > "$tmp/$kp" 2> /dev/null ||
      { bad="the internal records ref at $RREV holds no $rp (kit path $kp)"; break; }
    got=$(sha "$tmp/$kp")
    [ "$got" = "$sum" ] || { bad="$kp ($rp) has sha256 $got; KIT-MANIFEST says $sum"; break; }
    chmod "$mode" "$tmp/$kp"; n=$((n + 1))
  done < "$m"
  [ -z "$bad" ] && [ "$n" -gt 0 ] || { rm -rf "$tmp"; echo "REFUSED: ${bad:-MANIFEST $m names no file}"; return 1; }
  mv -T "$tmp" "$dest" && echo "$n"
}

# scan_tree: the release scanner of record over this tree (it runs its own positive control first: each needle planted
# in a copy of the first file must be found, else it exits 3 and scans nothing); then CONTROL: a copy of this tree whose
# README.md names a worker of ROSTER must be flagged.
scan_tree() {
  local sd r nm d=$(basename "$H")
  sd=$(cd "$(dirname "$SCANNER")" && pwd) || { echo "scan: REFUSED: SCANNER $SCANNER has no directory"; return 1; }
  [ "$(sha "$sd/SHA256SUMS")" = "$SCANNER_SUMS" ] && (cd "$sd" && sha256sum --quiet -c SHA256SUMS) &&
    [ "$(cd "$sd" && find . -mindepth 1 ! -name SHA256SUMS -printf '%P\n' | sort)" = \
      "$(awk '{sub(/^\*/, "", $2); print $2}' "$sd/SHA256SUMS" | sort)" ] &&
    awk '{sub(/^\*/, "", $2); print $2}' "$sd/SHA256SUMS" | grep -xF "$(basename "$SCANNER")" > /dev/null || {
      echo "scan: REFUSED: SCANNER $SCANNER is not in the release scanner of record's directory (its SHA256SUMS sha256 $SCANNER_SUMS, every file listed there and no other)"
      return 1; }
  echo "scan: the release scanner of record: SHA256SUMS sha256 ${SCANNER_SUMS:0:12}; $(basename "$SCANNER") sha256 $(sha "$SCANNER" | cut -c1-12)"
  rm -rf "$WORK/scan"; mkdir -p "$WORK/scan/ctl" || return 1
  (cd "$(dirname "$H")" && "$SCANNER" "$WORK/scan/tree" "$d") > "$WORK/scan/tree.log" 2>&1; r=$?
  grep -E '^(control|inputs|files with)' "$WORK/scan/tree.log" | sed 's/^/scan:   /'
  [ "$r" = 0 ] || { echo "scan: FAILED: the scanner exits $r over this tree (0: no file has an uncleared hit; see $WORK/scan/tree.log)"; return 1; }
  echo "scan: this tree PASS: no file has an uncleared hit"
  nm=$(awk -F'\t' 'NR > 1 && $1 ~ /^h-[a-z0-9]+-[a-z0-9]+$/ {print $1; exit}' "$ROSTER")
  [ -n "$nm" ] || { echo "scan: CONTROL FAILED: ROSTER $ROSTER has no worker name to plant"; return 1; }
  cp -a "$H" "$WORK/scan/ctl/" && printf '\nPlanted by the scan control: the %s lane.\n' "$nm" >> "$WORK/scan/ctl/$d/README.md" || return 1
  (cd "$WORK/scan/ctl" && "$SCANNER" "$WORK/scan/ctl.out" "$d") > "$WORK/scan/ctl.log" 2>&1; r=$?
  if [ "$r" = 1 ] && grep -q "FLAGGED $d/README.md\$" "$WORK/scan/ctl.log"; then
    echo "scan: CONTROL: a copy of this tree whose README.md names a worker of ROSTER is FLAGGED (exit 1)"
  else
    echo "scan: CONTROL FAILED: the planted copy was not flagged (exit $r; see $WORK/scan/ctl.log)"; return 1
  fi
}

if [[ " $STEPS " == *" drivers "* ]]; then
  say "kit: KIT-MANIFEST sha256 $(sha "$H/KIT-MANIFEST"); the internal records ref at $RREV"
  rm -rf "$KROOT" "$WORK/kit-ctl"
  r=$(fetch_kit "$H/KIT-MANIFEST" "$KH") || { say "kit: $r"; exit 2; }
  say "kit: $r files fetched into $KH, each with its KIT-MANIFEST sha256 and mode"
  # CONTROLS: one sha256 digit changed, and a records path the ref does not hold, are each refused, nothing fetched
  awk 'BEGIN {FS = OFS = "\t"} !/^#/ && !d {$2 = substr($2, 1, 63) (substr($2, 64, 1) == "0" ? "1" : "0"); d = 1} 1' \
    "$H/KIT-MANIFEST" > "$WORK/kit-ctl.sha.tsv"
  awk 'BEGIN {FS = OFS = "\t"} !/^#/ && !d {$1 = $1 ".absent"; d = 1} 1' "$H/KIT-MANIFEST" > "$WORK/kit-ctl.path.tsv"
  for c in sha:'one sha256 digit changed' path:'a records path the ref does not hold'; do
    if r=$(fetch_kit "$WORK/kit-ctl.${c%%:*}.tsv" "$WORK/kit-ctl/${c%%:*}") || [ -e "$WORK/kit-ctl/${c%%:*}" ]; then
      say "kit: CONTROL FAILED: a KIT-MANIFEST with ${c#*:} was not refused, or left files: $r"; exit 1
    fi
    say "kit: CONTROL: a KIT-MANIFEST with ${c#*:} is REFUSED, nothing fetched: $r"
  done
  # CONTROL: a SITE without RECORDS_REF is refused before anything runs, naming it
  grep -v '^RECORDS_REF=' "$SITE" > "$WORK/site.norecords.env"
  r=$(env -u RECORDS_REF SITE="$WORK/site.norecords.env" bash "$0" drivers 2>&1 | tail -n 1)
  case "$r" in *"does not set: RECORDS_REF ("*) say "kit: CONTROL: a SITE without RECORDS_REF is REFUSED: $r" ;;
    *) say "kit: CONTROL FAILED: a SITE without RECORDS_REF was not refused: $r"; exit 1 ;; esac
  scan_tree 2>&1 | tee -a "$LOG"; [ "${PIPESTATUS[0]}" = 0 ] || { say "FAILED: the shipped-tree scan"; exit 1; }
  sha "$H/KIT-MANIFEST" > "$KROOT/MANIFEST.sha256"
fi
[ -f "$KROOT/MANIFEST.sha256" ] && [ "$(cat "$KROOT/MANIFEST.sha256")" = "$(sha "$H/KIT-MANIFEST")" ] && [ -f "$KH/tools/regen.sh" ] ||
  { say "REFUSED: $KROOT holds no kit fetched for this KIT-MANIFEST: run the drivers step first, with the same WORK"; exit 2; }

# the lane: W and LT are this run's; TR is the checkout holding this tree (the 19 files go to its lib/B); every other
# variable of the kit's env.sh template comes from SITE (the template refuses an unset one)
export W=$WORK/t4 LT=$WORK/lt TR=$UNIT_TREE
if [[ " $STEPS " == *" kit "* ]]; then
  # the lane's own output directories: the kit's regen.sh logs every stage to $W/logs and its facts stage writes
  # $W/work/facts.env; kit_unpack.sh copies CODE only and makes neither
  rm -rf "$W" && mkdir -p "$W/logs" "$W/work" "$LT" || exit 2
  cp "$KH/env.sh" "$W/env.sh" || exit 2
  ( . "$W/env.sh" && bash "$KH/tools/kit_unpack.sh" "$KH" ) 2>&1 | tee -a "$LOG"
  [ "${PIPESTATUS[0]}" = 0 ] || { say "FAILED: kit_unpack"; exit 1; }
  ( . "$W/env.sh" && python3 "$W/tools/kit_verify.py" "$W" ) 2>&1 | tee -a "$LOG"
  [ "${PIPESTATUS[0]}" = 0 ] || { say "FAILED: kit_verify"; exit 1; }
fi
if [[ " $STEPS " == *" run "* ]]; then
  FROM=; set -- $STEPS; while [ $# -gt 0 ]; do [ "$1" = run ] && [ -n "${2:-}" ] && FROM=$2; shift; done
  [ -f "$W/env.sh" ] || { say "REFUSED: no lane at $W: run the kit step first, with the same WORK"; exit 2; }
  cd "$LT" || exit 2
  bash "$W/tools/regen.sh" "$UBSAN" "$(sha "$UBSAN")" "$UBSAN_TWIN" "$(sha "$UBSAN_TWIN")" \
    "$IMAGE" "$(sha "$IMAGE")" "$TWIN" "$(sha "$TWIN")" ${FROM:+"$FROM"} 2>&1 | tee -a "$LOG"
  r=${PIPESTATUS[0]}; [ "$r" = 0 ] && say "RESULT: steps $STEPS PASS" || say "RESULT: steps $STEPS FAIL (the kit's regen.sh exits $r; see $LOG)"
  exit "$r"
fi
say "RESULT: steps $STEPS PASS"
