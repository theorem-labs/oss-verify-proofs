#!/bin/bash
# flag-gate-A.sh WORK LIB OUT
# Gate (a) of the libdiginet/fuzz_transport image-A core relocation (row TCA), re-runnable: the record
# run of port_addr_check SHA (default 205a90fd19b8, the version of record after 08:00Z; gates/pac-A.sh: one default
# pass, --fail-on-flags) over WORK/stage vs
# WORK/stage-out, triage-A.py over every flagged / GENERATOR-FILL / UNMEASURED-NAME row, and the planted controls of
# D9's records/flag-gate.txt (flag-gate.txt, sha256 2ab8cf39a96f, and flag-gate-A.sh, sha256 bbc099633d6d; internal records): two copies of stage-out
# with A/AF0l.v `pc_wrap_memcpy` planted as fuzz_transport's abort and as the value pc_asan_memcpy carries in the same
# Tfib_code sentence, and the same file unplanted, each checked with --include A/AF0l.v.
#   WORK  a port_core run dir (stage/ = donor text, stage-out/ = the relocated core, patches.log, check.tsv, ...)
#   LIB   the target lib the run used (its A/ holds the start-up layer: AB13.v, AF0m.v, AD2j.v)
#   OUT   output dir: rec.{tsv,log}, gate-<SHA first 6>-triage-rows.tsv, gate-<SHA first 6>-TRIAGE.md, plant1/, plant2/,
#         ctl-{plant1,plant2,unplanted}.{tsv,log} and -triage.{tsv,out}, flag-gate.txt (the record)
# Exit 0 only if the triage explains every row of the record run and every control behaves: each plant adds exactly one
# flagged row (the planted A/AF0l.v pc_wrap_memcpy pair, a class of the checker's flag set) to the unplanted control's
# rows, rc 4, and triage-A.py leaves that row UNEXPLAINED (rc 1); unplanted: no flagged row on that pair, triage rc 0.
# Environment (no host path is written here; pac-A.sh's own: SHA CKDIR PG TIMG (or SRC_IMG SRC_TWIN DST_IMG DST_TWIN) DONORS):
#   EV         the run's evidence dir (overrides.tsv and every patch WORK/patches.log names)
#   OVERRIDES  the run's --override file (EV/overrides.tsv)
#   DON        fuzz_grant's released lib, normalised (recipes 25e3d17bdb50); DONOR_LIB overrides it
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: flag-gate-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$(realpath "$1") LIB=$(realpath "$2") OUT=$3
HERE=$(dirname "$(realpath "$0")")
export SHA=${SHA:-205a90fd19b8}
G6=gate-${SHA:0:6}
export CKDIR=${CKDIR:?set CKDIR to the port_addr_check directory}
export SRC_IMG=${SRC_IMG:-${PG:?set PG to the fuzz_grant image tree}/bin/fuzz_grant/fuzz_grant.asan}
export SRC_TWIN=${SRC_TWIN:-$PG/unstripped/fuzz_grant/fuzz_grant.asan}
export DST_IMG=${DST_IMG:-${TIMG:?set TIMG to the fuzz_transport image dir}/stripped/fuzz_transport.asan}
export DST_TWIN=${DST_TWIN:-$TIMG/unstripped/fuzz_transport.asan}
export DONORS=${DONORS:?set DONORS to the symbolised donor tree}
: "${EV:?set EV to the evidence dir of the run}" "${DONOR_LIB:=${DON:?set DON to the released fuzz_grant lib, normalised}}"
EV=$(realpath "$EV")
OVERRIDES=$(realpath "${OVERRIDES:-$EV/overrides.tsv}")
DONOR_LIB=$(realpath "$DONOR_LIB")
[ -d "$WORK/stage" ] && [ -d "$WORK/stage-out" ] || { echo "flag-gate-A: no stage/ or stage-out/ in $WORK" >&2; exit 2; }
[ -d "$LIB/A" ] || { echo "flag-gate-A: no A/ in LIB $LIB" >&2; exit 2; }
mkdir -p "$OUT" && OUT=$(realpath "$OUT") && cd "$OUT" || exit 2
export PYTHONDONTWRITEBYTECODE=1
ln -sfn "$WORK/stage" stage && ln -sfn "$WORK/stage-out" stage-out
TRI=(--run "$WORK" --lib "$LIB" --overrides "$OVERRIDES" --evidence "$EV" --src-image "$SRC_IMG:$SRC_TWIN"
     --dst-image "$DST_IMG:$DST_TWIN" --donor-lib "$DONOR_LIB")
treesha() { (cd "$1" && find . -name '*.v' -type f -print0 | sort -z | xargs -0 sha256sum | sha256sum | cut -c1-12); }
s12() { sha256sum "$1" 2>/dev/null | cut -c1-12; }

# record run and its triage
bash "$HERE/pac-A.sh" stage stage-out rec
REC_RC=$?
[ "$REC_RC" = 5 ] && { echo "flag-gate-A: an input pin does not match (rec.log)" >&2; exit 5; }
python3 "$HERE/triage-A.py" --raw rec.tsv --log rec.log "${TRI[@]}" --out "$G6-triage-rows.tsv" \
  --md "$G6-TRIAGE.md" > rec-triage.out
REC_TRI=$?

# planted copies: fuzz_transport's abort (from the dst twin's symtab) and pc_asan_memcpy's value in the same sentence
rm -rf plant1 plant2
cp -r "$WORK/stage-out" plant1 && cp -r "$WORK/stage-out" plant2
PLANTS=$(python3 - "$DST_TWIN" <<'EOF'
import re, sys
from elftools.elf.elffile import ELFFile
ab = [s['st_value'] for s in ELFFile(open(sys.argv[1], 'rb')).get_section_by_name('.symtab').iter_symbols()
      if s.name == 'abort' and s['st_info']['type'] == 'STT_FUNC']
f = 'A/AF0l.v'
t = open('plant1/' + f).read()
old = re.findall(r'pc_wrap_memcpy := (0x[0-9a-f]+);', t)
asan = re.findall(r'pc_asan_memcpy := (0x[0-9a-f]+);', t)
assert len(ab) == 1 and len(old) == 1 and len(asan) == 1, (ab, old, asan)
vals = {'plant1': hex(ab[0]), 'plant2': asan[0]}
for d, v in vals.items():
    assert v != old[0]
    n = t.replace(f'pc_wrap_memcpy := {old[0]};', f'pc_wrap_memcpy := {v};', 1)
    assert n != t
    open(f'{d}/{f}', 'w').write(n)
print(old[0], vals['plant1'], vals['plant2'])
EOF
) || exit 2
read -r ORIG V1 V2 <<< "$PLANTS"

ctl() {  # ctl <name> <dst tree>
  bash "$HERE/pac-A.sh" stage "$2" "ctl-$1" --include A/AF0l.v
  python3 "$HERE/triage-A.py" --raw "ctl-$1.tsv" --log "ctl-$1.log" "${TRI[@]}" --stage-out "$2" \
    --out "ctl-$1-triage.tsv" > "ctl-$1-triage.out"
  echo $?
}
T1=$(ctl plant1 plant1 | tail -1)
T2=$(ctl plant2 plant2 | tail -1)
T0=$(ctl unplanted stage-out | tail -1)

# the control verdicts, read from the raw rows (never from a hand list of classes: the flag set is the checker's own)
judge() {  # judge <ctl name> <value on the pair> -> "<n flagged rows on the pc_wrap_memcpy pair> <class> <added> <removed>"
  python3 - "ctl-$1.tsv" "ctl-$1.log" ctl-unplanted.tsv "$2" stage/A/AF0l.v <<'EOF'
import collections, re, sys
raw, log, base, val, donor_file = sys.argv[1:]
donor = re.findall(r'pc_wrap_memcpy := (0x[0-9a-f]+);', open(donor_file).read())
assert len(donor) == 1, donor
t = open(log).read().split('\n')
i = next(k for k, l in enumerate(t) if re.match(r'checker \S+ rc=\d+', l))
flags = {l.strip() for l in t[i + 1:] if re.fullmatch(r'[A-Z][A-Z-]+', l.strip())}
def rows(p):
    out, hdr = [], None
    for ln in open(p, errors='replace'):
        if ln.startswith('#'):
            continue
        r = ln.rstrip('\n').split('\t')
        if hdr is None:
            hdr = r
            continue
        out.append(dict(zip(hdr, r)))
    return out
key = lambda d: (d['verdict'], d['src_file'], d['src_line'], d['dst_file'], d['dst_line'], d['sentence'], d['idx'],
                 d['src_value'])
mine = [d for d in rows(raw) if d['verdict'] in flags]
# the planted pair: donor pc_wrap_memcpy (stage/A/AF0l.v) against the value the control's copy holds
pair = [d for d in mine if d['dst_file'] == 'A/AF0l.v' and 'Tfib_code' in d['sentence'] and d['src_value'] == donor[0]
        and d['dst_value'] == val]
mk, bk = collections.Counter(key(d) for d in mine), collections.Counter(key(d) for d in rows(base) if d['verdict'] in flags)
cls = ','.join(sorted({d['verdict'] for d in pair})) or '-'
print(len(pair), cls, sum((mk - bk).values()), sum((bk - mk).values()))
EOF
}
read -r P1N P1C P1A P1R <<< "$(judge plant1 "$V1")"
read -r P2N P2C P2A P2R <<< "$(judge plant2 "$V2")"
read -r P0N P0C P0A P0R <<< "$(judge unplanted "$ORIG")"

section() {  # section <title> <log> <triage rc> <triage out>
  echo "# $1"
  grep -E '^FLAG-CLASSES ' "$2"
  grep -E '^FLAGGED ' "$2"
  grep -E '^UNMEASURED [0-9]+ rows' "$2"
  grep -E '^checker .* rc=' "$2" | sed -E 's#^checker [^ ]+ #checker <file> #'
  grep -E '^checker files: ' "$2"
  grep -E $'^GENERATOR-FILL\t' "$2" | awk -F'\t' '{print "GENERATOR-FILL " $2 " (reported, not counted)"}'
  echo "triage-A.py rc=$3: $(head -1 "$4" | sed -E 's# -> .*##')"
  sed -n '2p;4p' "$4"
  grep -E '^UNEXPLAINED ' "$4" | cut -c1-240
}
rc_of() { grep -E '^checker .* rc=' "$1" | grep -oE 'rc=[0-9]+' | cut -d= -f2; }
{
  echo "# gate (a) of libdiginet/fuzz_transport image-A core (row TCA): $(date -u +%FT%TZ)"
  echo "command: gates/flag-gate-A.sh $WORK $LIB $OUT (gates: pac-A.sh $(s12 "$HERE/pac-A.sh"), flag-gate-A.sh $(s12 "$HERE/flag-gate-A.sh"), triage-A.py $(s12 "$HERE/triage-A.py"))"
  echo "checker: $CKDIR/versions/$SHA/port_addr_check.py sha256 $(s12 "$CKDIR/versions/$SHA/port_addr_check.py"); one default pass, --paired-only --summary --donors-from $DONORS --fail-on-flags"
  echo "images: src $SRC_IMG $(s12 "$SRC_IMG") twin $(s12 "$SRC_TWIN"); dst $DST_IMG $(s12 "$DST_IMG") twin $(s12 "$DST_TWIN")"
  echo "inputs: WORK/stage tree $(treesha "$WORK/stage") ($(find "$WORK/stage" -name '*.v' | wc -l) files), WORK/stage-out tree $(treesha "$WORK/stage-out") ($(find "$WORK/stage-out" -name '*.v' | wc -l) files), port_core $(awk '$1=="port_core.py"{print substr($2,1,12)}' "$WORK/versions.txt" 2>/dev/null); LIB/A/AB13.v $(s12 "$LIB/A/AB13.v"), AF0m.v $(s12 "$LIB/A/AF0m.v"), AD2j.v $(s12 "$LIB/A/AD2j.v"); overrides $(s12 "$OVERRIDES"); patches (WORK/patches.log)$(awk '/^== /{print $2}' "$WORK/patches.log" | while read -r p; do b=$(basename "$p" .patch); printf ' %s %s' "$b" "$(s12 "$EV/$b.patch")"; done); donor lib A/AB13.v $(s12 "$DONOR_LIB/A/AB13.v"), AF0m.v $(s12 "$DONOR_LIB/A/AF0m.v"), AD2j.v $(s12 "$DONOR_LIB/A/AD2j.v")"
  section "record run" rec.log "$REC_TRI" rec-triage.out
  section "control: A/AF0l.v pc_wrap_memcpy planted as $V1 (abort; the file's value is $ORIG)" ctl-plant1.log "$T1" ctl-plant1-triage.out
  echo "planted pair flagged: $P1N row(s), class $P1C; against the unplanted control's flagged rows: $P1A added, $P1R removed"
  section "control: A/AF0l.v pc_wrap_memcpy planted as $V2 (pc_asan_memcpy, a value of the same sentence)" ctl-plant2.log "$T2" ctl-plant2-triage.out
  echo "planted pair flagged: $P2N row(s), class $P2C; against the unplanted control's flagged rows: $P2A added, $P2R removed"
  section "control: the same file unplanted" ctl-unplanted.log "$T0" ctl-unplanted-triage.out
  echo "pc_wrap_memcpy pair flagged: $P0N row(s)"
} > flag-gate.txt
ok=1
[ "$REC_RC" = 4 ] || [ "$REC_RC" = 0 ] || ok=0
[ "$REC_TRI" = 0 ] || ok=0
for p in 1 2; do
  if [ $p = 1 ]; then n=$P1N a=$P1A r=$P1R t=$T1; else n=$P2N a=$P2A r=$P2R t=$T2; fi
  [ "$n" = 1 ] && [ "$a" = 1 ] && [ "$r" = 0 ] && [ "$(rc_of ctl-plant$p.log)" = 4 ] && [ "$t" = 1 ] && \
    grep -q '^UNEXPLAINED raw [0-9]* [A-Z-]* A/AF0l.v' "ctl-plant$p-triage.out" || ok=0
done
[ "$P0N" = 0 ] && [ "$T0" = 0 ] || ok=0
echo "controls: $([ $ok = 1 ] && echo PASS || echo FAIL) (each plant: exactly one flagged row added to the unplanted control's rows and none removed, on the planted A/AF0l.v pc_wrap_memcpy pair, rc 4, that row UNEXPLAINED by triage-A.py; unplanted: the pair not flagged, triage rc 0; record: checker rc 4 or 0, triage rc 0)" >> flag-gate.txt
# the record again, now with the controls embedded
python3 "$HERE/triage-A.py" --raw rec.tsv --log rec.log "${TRI[@]}" --out "$G6-triage-rows.tsv" \
  --md "$G6-TRIAGE.md" --controls flag-gate.txt > rec-triage.out || ok=0
tail -1 flag-gate.txt
[ $ok = 1 ]
