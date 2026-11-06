#!/bin/bash
# run_gates.sh -- reac-repacer/fuzz_wire image B (asan-ubsan) start-up data set (19 files, lib/B layout): every gate,
# each with its control FIRST. rule 24: proves no function (start-up facts). The twin of the fuzz_uci image-B gate run
# (UCI/sub/gates/run_gates.sh, UCI/GATES-uciB.md gate table); every unit number is MEASURED from the fuzz_wire images
# in the run that uses it, never copied. Tool set of record: commit dbb5a97ad14 tools/startup-set (FT, run through
# its frozen-run.sh with its bundle: codeptr 12348302dfd2, pins 4778073f01be, keyset f050b43e480e, ifchk f5cde600cc18);
# the other tools are copies in tools/ (sha256 in logs/SHA256.tools.txt; each change listed in REPORT.md).
#
#   bash run_gates.sh [G0 GD G1 ... G14 HDR | CTL]   default: GD G1 G2 G3 G3s G3f G4 ... G14 HDR, in order. G0
#                          (snapshot + inputs) runs first whenever any gate runs, unless NOSNAP=1. Each gate runs on
#                          the files PRESENT in WK/gen (G0 lists present / missing: fewer than 19 is UNEXPECTED); its
#                          controls run first, whatever is present.
#   AF0M_A=<image A's AF0m.v> enables the `pins stamp --pair` run of G7d, AD1G_PATCHED=<the B core's YD1g.v> the G9p
#   ifchk run against it (each is UNEXPECTED, rc PENDING, when its file is not given).
#   GD compares the 19 with lib/B at the base commit GD.expect names; GD.expect states each file's change class, and
#   the WANT of every GD step on the 19 comes from it.
# Every RESULT line states the rc a correct run gives (want N) and OK / UNEXPECTED; the run's exit status is its own:
# 1 when any RESULT line of this run is UNEXPECTED or states no want, or the log copy fails, else 0 (the summary at the
# end lists them; logs/SUMMARY.out). CTL (not in the default list) is the runner's own control: a planted step whose
# rc 1 is wanted (OK) and, unless CTL_PLANT=ok, a planted failing step (want 0, rc 1: UNEXPECTED, so the run exits 1).
# Every host path comes from env.sh. Reads WK/gen, WK/raw, the images, the donor lib; writes only logs/ (here) and
# LT/gates. Every kept log passes `klog` = the bundle path as $BUNDLE, then env.sh's scrub, then redact.py.
# The notes dir is sshfs: the run first copies this directory (scripts + tools) and the lane tools it calls (nsW.py with
# its pg-reloc, hdrcheck.py) to LT/gates/src and runs from there, writes every log to LT/gates/logs, and at the end
# copies the logs here (logs/ is replaced by that set).
set -uo pipefail
G=$(cd "$(dirname "$0")" && pwd)
if [ -z "${GATES_HOME:-}" ]; then
  . "$G/../../env.sh"
  [ -d "$LT/gates/src" ] && chmod -R u+w "$LT/gates/src"; rm -rf "$LT/gates/src"; mkdir -p "$LT/gates/src/lanetools"
  cp -r "$G/." "$LT/gates/src/"; chmod -R u+w "$LT/gates/src"; rm -rf "$LT/gates/src/logs" "$LT/gates/src/run_gates.sh.new"
  cp -r "$W/tools/nsW.py" "$W/tools/hdrcheck.py" "$W/tools/pg-reloc" "$LT/gates/src/lanetools/"
  GATES_HOME=$G exec bash "$LT/gates/src/run_gates.sh" "$@"
fi
GH=$GATES_HOME
. "$GH/../../env.sh"
X=$LT/gates; T=$G/tools; L=$X/logs; LTOOLS=$G/lanetools
export PYTHONDONTWRITEBYTECODE=1
BUNDLE=${FR3##* }                                  # the bundle of record (FT's startup-set tsv)
FRT="bash $FT/frozen-run.sh $BUNDLE"
# G3's address cache and donor builds come from env.sh (PAC_CACHE, DONOR_BINS); G3r's map and relocation tools from
# env.sh too (MAPTOOL, RELOCTOOL): a tool is named here by its role, never by its file name or path
NS=OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire
ALL19="YB01 YB03 YB05 YB12 YB13 YB1h YB1k YB1l YB1m YB1v YCej YD1k YD1y YD2i YD2j YE23 YE37 YE3i YF0m"
UNM=$WK/nm/wireB.nm.txt; UNMS=$WK/nm/wireB.nmS.txt  # nm of the unstripped twin (fuzz_wire B's names)
CBN=$X/in/cgifB.nm                                 # cgif B recovered nm, '#' lines removed (G0)
OD=$LT/od/fuzz_wire.asan-ubsan.objdump.txt         # riscv64-alpine-linux-musl-objdump -d of a copy of the twin
AD1G=$LT/pcB/stage-out/B/YD1g.v                    # port_core B stage-out YD1g (ifchk --ad1g)
IMGTOPV=$LT/pcB/stage-out/B/YImgTop.v              # port_core B stage-out YImgTop (the module YD1k's bound names)
GDX=$G/GD.expect                                   # GD's expectations: the base commit and each file's change class
GDBL=proofs/reac-repacer/fuzz_wire/lib/B           # lib/B at GD's base: the base predates the per-project layout, so it is read at the path it holds
mkdir -p "$L" "$X/raw" "$X/ctl"
klog() { sed "s#$BUNDLE#\$BUNDLE#g" | scrub | python3 "$G/redact.py" "$LTOOLS/hdrcheck.py"; }
lg() { local n=$1; shift; "$@" > "$X/raw/$n" 2>&1; local r=$?; klog < "$X/raw/$n" > "$L/$n"; return $r; }
in_dir() { (cd "$1" && shift && "$@"); }
rc() {  # LABEL RC [WANT]: the rc a correct run gives is WANT (default 0); OK / UNEXPECTED
  local w=${3:-0}
  if [ "$2" = "$w" ]; then echo "RESULT $1 rc=$2 (want $w) OK"; else echo "RESULT $1 rc=$2 (want $w) UNEXPECTED"; fi
}
present() { for n in $ALL19; do [ -f "$X/in/gen/$n.v" ] && printf '%s ' "$n"; done; }
has() { [ -f "$X/in/gen/$1.v" ]; }
imgtop() { python3 - "$1" <<'EOF'
import sys
from elftools.elf.elffile import ELFFile
e = ELFFile(open(sys.argv[1], 'rb'))
print('%#x' % ((max(s['p_vaddr'] + s['p_memsz'] for s in e.iter_segments() if s['p_type'] == 'PT_LOAD') + 0xfff) & ~0xfff))
EOF
}

G0() {  # snapshot of the files + their raw twins; cgif inputs; sha256 of every input and tool
  # GD compares with the base commit of GD.expect, not with an earlier snapshot: none is kept
  rm -rf "$X/prev" "$L/SHA256.inputs.prev.txt"
  rm -rf "$X/in"; mkdir -p "$X/in/gen" "$X/in/raw" "$X/in/cgif/A"
  local n miss=""
  for n in $ALL19; do
    if [ -f "$WK/gen/$n.v" ]; then cp "$WK/gen/$n.v" "$X/in/gen/"; else miss="$miss $n"; fi
    [ -f "$WK/raw/$n.v" ] && cp "$WK/raw/$n.v" "$X/in/raw/"
    cp "$DLIBC/$n.v" "$X/in/cgif/"; cp "$DLIBC/A/A${n:1}.v" "$X/in/cgif/A/"
  done
  [ -f "$WK/gen/YCej.universe.json" ] && cp "$WK/gen/YCej.universe.json" "$X/in/gen/"
  cp "$DLIBC/YF0l.v" "$DLIBC/YB1w.v" "$X/in/cgif/"; cp "$DLIBC/A/AF0l.v" "$DLIBC/A/AF0m.v" "$DLIBC/A/AB01.v" "$X/in/cgif/A/"
  grep -v '^#' "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" > "$CBN"
  {
    echo "# G0 snapshot: the files of WK/gen, their donor-namespace twins (WK/raw), images, names, tool inputs"
    (cd "$X/in/gen" && sha256sum *.v *.json 2>/dev/null)
    (cd "$X/in/raw" && sha256sum *.v 2>/dev/null | sed 's/  /  raw\//')
    sha256sum "$UB" "$UBs" "$CB" "$CA" "$UA" "$UAs" "$UNM" "$UNMS" "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" \
      "$S/syms/cgif_file_fuzzer.asan.nm" "$CBN" "$OD" "$LT/od/fuzz_wire.asan-ubsan.debug" "$AD1G" "$IMGTOPV" \
      "$BUNDLE" "$FT/frozen-run.sh" "$WK/ctl/YB12.cgif.v"
    echo "# donor lib: git archive 25e3d17bdb50 of proofs/cgif/cgif_file_fuzzer/lib (DLIBC)"
    (cd "$X/in/cgif" && sha256sum *.v A/*.v)
  } > "$X/raw/SHA256.inputs.txt"; klog < "$X/raw/SHA256.inputs.txt" > "$L/SHA256.inputs.txt"
  { (cd "$T" && find . -type f ! -name '*.pyc' ! -path '*__pycache__*' | sort | xargs sha256sum)
    (cd "$G" && sha256sum run_gates.sh codeptr-decl.sh pac_table.py redact.py GD.expect)
    (cd "$FT" && sha256sum frozen-run.sh frozen/codeptr.py.frozen-* frozen/pins.py.frozen-* frozen/keyset.py.frozen-* \
       frozen/ifchk.py.frozen-* frozen/gen_ad1k.py.frozen-* | sed 's#  #  FT/#')
    (cd "$LTOOLS" && sha256sum nsW.py hdrcheck.py pg-reloc/0e4e065eab9f/port_core.py | sed 's#  #  W/tools/#'); } > "$X/raw/SHA256.tools.txt"
  klog < "$X/raw/SHA256.tools.txt" > "$L/SHA256.tools.txt"
  # the two gen_ad1k versions lowbeg.py imports (G11): 43a0cf0abc67 (FT's bundle, dbb5) and 814c81b8966e (8cd71d3a4bb)
  local b tag rest bun fz name sha
  for b in dbb5:"$BUNDLE":"$FT/frozen" 8cd7:"$T/frozen/startup-set-8cd71d3a4bb.tsv":"$T/frozen"; do
    tag=${b%%:*}; rest=${b#*:}; bun=${rest%%:*}; fz=${rest#*:}
    rm -rf "$X/bundle-$tag"; mkdir -p "$X/bundle-$tag"
    while IFS=$'\t ' read -r name sha; do case "$name" in ''|'#'*) continue;; esac
      mkdir -p "$X/bundle-$tag/$(dirname "$name")"; cp "$fz/$(basename "$name").frozen-$sha" "$X/bundle-$tag/$name"; done < "$bun"
    ln -sfn "$FT/pautrlen" "$X/bundle-$tag/pautrlen"
  done
  echo "G0 snapshot: $(ls "$X/in/gen"/*.v 2>/dev/null | wc -l) of 19 files present: $(present)"
  echo "G0 missing:${miss:- none}"
  rc "G0 the 19 files present in WK/gen" "$([ -z "$miss" ] && echo 0 || echo 1)"
  echo "G0 raw twins present: $(cd "$X/in/raw" && ls *.v 2>/dev/null | sed 's/\.v$//' | tr '\n' ' ')"
  echo "G0 cgif B nm: $(sha256sum "$CBN" | cut -c1-12) ('#'-stripped \$S/syms/cgif_file_fuzzer.asan-ubsan.nm $(sha256sum "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" | cut -c1-12))"
  echo "G0 pin $(sha256sum "$UB" | cut -c1-64); twin $(sha256sum "$UBs" | cut -c1-12); objdump of the twin copy $(sha256sum "$OD" | cut -c1-12) (copy $(sha256sum "$LT/od/fuzz_wire.asan-ubsan.debug" | cut -c1-12))"
  if [ -f "$W/logs/final/SHA256.lib-B.txt" ]; then
    echo "G0 snapshot vs the finalize list W/logs/final/SHA256.lib-B.txt: $(cd "$X/in/gen" && sha256sum -c "$W/logs/final/SHA256.lib-B.txt" 2>&1 | awk '{c[$NF]++} END {for (k in c) printf "%s %d; ", k, c[k]}')"
  fi
  local head; head=$(git -C "$TR" rev-parse HEAD)
  echo "G0 snapshot vs lib/B of the trunk clone at HEAD $head: $(for n in $ALL19; do git -C "$TR" show "HEAD:projects/reac-repacer/fuzz_wire/proofs/lib/B/$n.v" 2>/dev/null | cmp -s - "$X/in/gen/$n.v" && echo EQUAL || echo DIFFERENT; done | sort | uniq -c | awk '{printf "%s%s %s", (NR > 1 ? "; " : ""), $1, $2}')"
}

gd_parse() {  # EXPECT: prints `base <sha>` and one line `<name> <class> <commits> <lines>` per file ('-' for an equal
              # file); rc 1 when EXPECT is malformed: not exactly one base line (a full commit sha), a name that is not
              # one of the 19 or is named twice, one of the 19 not named, an unknown class, or a comment / comment-pass /
              # require / code line without its commit(s), its changed lines and a reason
  python3 - "$1" "$ALL19" <<'EOF'
import re, sys
names = sys.argv[2].split()
base, rows, bad = [], {}, []
for k, l in enumerate(open(sys.argv[1]).read().split('\n'), 1):
    w = l.split()
    if not w or w[0].startswith('#'):
        continue
    if w[0] == 'base':
        base.append(w[1] if len(w) == 2 and re.fullmatch(r'[0-9a-f]{40}', w[1]) else None)
        continue
    n, c = w[0], (w[1] if len(w) > 1 else '')
    if n not in names or n in rows:
        bad.append('line %d: %s %s' % (k, n, 'is named twice' if n in rows else 'is not one of the 19'))
    elif c == 'equal' and len(w) == 2:
        rows[n] = (c, '-', '-')
    elif (c in ('comment', 'comment-pass', 'require', 'code') and len(w) >= 6 and w[3] == 'lines'
          and re.fullmatch(r'[0-9a-f]{12,40}(,[0-9a-f]{12,40})*', w[2]) and re.fullmatch(r'[1-9]\d*(,[1-9]\d*)*', w[4])):
        rows[n] = (c, w[2], w[4])
    else:
        bad.append('line %d: %s: neither `equal` nor `comment|comment-pass|require|code <commit>[,<commit>] lines <n>[,<n>] <reason>`' % (k, n))
if len(base) != 1 or base[0] is None:
    bad.append('%d base line(s): exactly one, with a full 40-digit commit sha, is needed' % len(base))
bad += ['%s is not named' % n for n in names if n not in rows]
print('base', base[0] if len(base) == 1 and base[0] else '-')
for n in names:
    if n in rows:
        print(n, *rows[n])
for b in bad:
    print('  GD.expect REFUSED: %s' % b, file=sys.stderr)
sys.exit(1 if bad else 0)
EOF
}

gd_files() {  # PARSED BASEDIR SNAPDIR: each file's steps, every WANT from its class in GD.expect:
              #   equal    byte-equal to the base (want 0)
              #   comment  bytes differ (1); comment-stripped EQUAL, stripcmp (0); Require sentences only, reqdiff (1)
              #   comment-pass  the same steps and wants as comment (a comment-only pass over lib/B, with no REASONS
              #            entry in mk_gdexpect.py; the writer checks it against the run of record's bytes too)
              #   require  bytes differ (1); comment-stripped EQUAL (1); Require sentences only (0)
              #   code     bytes differ (1); comment-stripped EQUAL (1); Require sentences only (1)
              # and, for every class but equal, the changed lines are exactly the ones GD.expect names (0) and the
              # commits of the trunk clone that change lib/B/<name>.v since the base are exactly the ones it names (0)
  local p=$1 bd=$2 sd=$3 base n c cm ln r
  base=$(awk '$1 == "base" {print $2}' "$p")
  while read -r -u 3 n c cm ln; do
    [ "$n" = base ] && continue
    cmp -s "$bd/$n.v" "$sd/$n.v"; r=$?
    if [ "$c" = equal ]; then rc "GD $n [equal]: byte-equal to the base" $r 0; continue; fi
    rc "GD $n [$c]: bytes differ from the base" $r 1
    python3 "$T/stripcmp.py" "$bd/$n.v" "$sd/$n.v" | sed 's/^/  /'; r=${PIPESTATUS[0]}
    rc "GD $n [$c]: comment-stripped EQUAL (stripcmp)" $r "$([ "$c" = comment ] || [ "$c" = comment-pass ] && echo 0 || echo 1)"
    python3 "$T/reqdiff.py" "$bd" "$sd" "$n" | tail -1 | sed 's/^/  /'; r=${PIPESTATUS[0]}
    rc "GD $n [$c]: Require sentences only (reqdiff)" $r "$([ "$c" = require ] && echo 0 || echo 1)"
    python3 - "$bd/$n.v" "$sd/$n.v" "$ln" <<'EOF'; rc "GD $n [$c]: the changed lines are exactly lines $ln" $? 0
import sys
a, b = (open(p).read().split('\n') for p in sys.argv[1:3])
want = [int(x) for x in sys.argv[3].split(',')]
got = [i + 1 for i, (x, y) in enumerate(zip(a, b)) if x != y] if len(a) == len(b) else None
print('  %s: %d / %d lines, changed lines %s; GD.expect: %s' % (sys.argv[2].split('/')[-1], len(a), len(b), got, want))
sys.exit(0 if got == want else 1)
EOF
    git -C "$TR" log --format=%H "$base..HEAD" -- "$GDBL/$n.v" "projects/reac-repacer/fuzz_wire/proofs/lib/B/$n.v" > "$X/raw/GD.commits.$n" 2>&1
    python3 - "$cm" "$X/raw/GD.commits.$n" <<'EOF'; rc "GD $n [$c]: the commits that change lib/B/$n.v since the base are exactly $cm" $? 0
import re, sys
named, got = sys.argv[1].split(','), open(sys.argv[2]).read().split()
ok = (all(re.fullmatch(r'[0-9a-f]{40}', g) for g in got) and len(got) == len(named)
      and all(sum(g.startswith(x) for g in got) == 1 for x in named) and all(any(g.startswith(x) for x in named) for g in got))
print('  commits of the trunk clone (base..HEAD) that change the file: %s; GD.expect: %s' % ([g[:12] for g in got], named))
sys.exit(0 if ok else 1)
EOF
  done 3< "$p"
}

gd_ctl() {  # PARSED SNAPDIR LOG LABEL...: gd_files on a planted input; its RESULT lines are kept as CONTROL-RESULT lines in
            # logs/LOG (they are not steps of this run); rc 0 iff the UNEXPECTED steps are exactly the LABELs
  local p=$1 sd=$2 log=$3; shift 3
  gd_files "$p" "$X/gdbase" "$sd" 2>&1 | sed 's/^RESULT /CONTROL-RESULT /' > "$X/raw/$log"; klog < "$X/raw/$log" > "$L/$log"
  python3 - "$L/$log" "$@" <<'EOF'
import sys
bad = sorted(l.split(' rc=')[0][len('CONTROL-RESULT '):] for l in open(sys.argv[1])
             if l.startswith('CONTROL-RESULT ') and l.rstrip().endswith(' UNEXPECTED'))
print('  UNEXPECTED steps on the planted input (logs/%s): %d %s' % (sys.argv[1].split('/')[-1], len(bad), bad))
sys.exit(0 if bad == sorted(sys.argv[2:]) else 1)
EOF
}

GD() {  # the 19 against lib/B at the base commit GD.expect names: each file's change class, every WANT from GD.expect
  local n r base wr=0 ws=0 sr=0
  echo "=== GD.expect (sha256 $(sha256sum "$GDX" | cut -c1-12)): the base commit and each file's change class ==="
  grep -v '^#' "$GDX" | grep . | cut -c1-300 | sed 's/^/  /'
  gd_parse "$GDX" > "$X/gd.parsed"; rc "GD GD.expect read (one base; each of the 19 named once; a changed file with its commit(s), lines and reason)" $? 0
  base=$(awk '$1 == "base" {print $2}' "$X/gd.parsed")
  rm -rf "$X/gdbase"; mkdir -p "$X/gdbase"; r=0
  for n in $ALL19; do git -C "$TR" show "$base:$GDBL/$n.v" > "$X/gdbase/$n.v" 2>/dev/null || r=1; done
  (cd "$X/gdbase" && sha256sum *.v) > "$X/raw/SHA256.gdbase.txt"; klog < "$X/raw/SHA256.gdbase.txt" > "$L/SHA256.gdbase.txt"
  rc "GD base: lib/B of commit $base, the 19 read from the trunk clone (logs/SHA256.gdbase.txt)" $r 0
  git -C "$TR" merge-base --is-ancestor "$base" HEAD 2>/dev/null
  rc "GD base $base is an ancestor of the trunk clone's HEAD $(git -C "$TR" rev-parse HEAD)" $? 0
  echo "=== GD CONTROL 1: a copy of the base YB12 with one numeral changed (x_memset +4) must be refused ==="
  rm -rf "$X/ctl/gd"; mkdir -p "$X/ctl/gd"; cp "$X/gdbase"/*.v "$X/ctl/gd/"
  python3 - "$X/ctl/gd/YB12.v" <<'EOF'; rc "GD plant" $?
import re, sys
t = open(sys.argv[1]).read()
m = re.search(r'x_memset := (0x[0-9a-f]+)', t)
open(sys.argv[1], 'w').write(t[:m.start(1)] + hex(int(m.group(1), 16) + 4) + t[m.end(1):])
print('planted: x_memset %s -> %s' % (m.group(1), hex(int(m.group(1), 16) + 4)))
EOF
  lg GD.reqdiff.control.log python3 "$T/reqdiff.py" "$X/gdbase" "$X/ctl/gd" YB12; rc "GD reqdiff PLANTED numeral" $? 1; tail -1 "$L/GD.reqdiff.control.log"
  echo "=== GD CONTROL 2 (a Require sentence over two lines): a copy of the base YB1l whose YA0* Require is written in the OTHER form -- the two-line form 'From .. Require Import' / '<modules>.' where the base has one line + a blank line, or one line + a blank line where the base has the two-line form -- must PASS, and one Require line + a planted Definition on the next line must be refused ==="
  rm -rf "$X/ctl/gd2"; mkdir -p "$X/ctl/gd2/ok" "$X/ctl/gd2/bad"
  python3 - "$X/gdbase/YB1l.v" "$X/ctl/gd2" <<'EOF'; rc "GD plant 2" $?
import re, sys
lines = open(sys.argv[1]).read().split('\n')
# the base holds the YA0* Require EITHER on one line followed by a blank line, OR already in the two-line form
# (the sentence's modules on the next line). The control writes the other form, so the pair always differs in a
# Require sentence that spans two lines in one of the two versions.
one = next((k for k, l in enumerate(lines)
            if re.search(r'Require Import YA01\b', l) and l.rstrip().endswith('.') and lines[k + 1].strip() == ''), None)
two = next((k for k, l in enumerate(lines)
            if l.rstrip().endswith('Require Import') and re.match(r'^YA01\b[\w \']*\.$', lines[k + 1].strip())), None)
i = one if one is not None else two
assert i is not None, 'YB1l holds no YA0* Require in either form'
head = re.match(r'(From \S+ Require Import)', lines[i]).group(1)
mods = (lines[i][len(head):] if one is not None else lines[i + 1]).strip().rstrip('.').split()
ok, bad = list(lines), list(lines)
ok[i:i + 2] = [head, ' '.join(mods) + '.'] if one is not None else ['%s %s.' % (head, ' '.join(mods)), '']
bad[i:i + 2] = ['%s %s.' % (head, ' '.join(mods)), 'Definition gd_planted : Z := 0x1.']
open(sys.argv[2] + '/ok/YB1l.v', 'w').write('\n'.join(ok))
open(sys.argv[2] + '/bad/YB1l.v', 'w').write('\n'.join(bad))
print('planted at YB1l lines %d-%d: the base has the %s form; (a) the %s form of the same Require of %d modules; '
      '(b) one-line Require + a Definition' % (i + 1, i + 2, 'one-line' if one is not None else 'two-line',
                                               'two-line' if one is not None else 'one-line', len(mods)))
EOF
  lg GD.reqdiff.control2ok.log python3 "$T/reqdiff.py" "$X/gdbase" "$X/ctl/gd2/ok" YB1l; rc "GD reqdiff two-line Require form" $? 0; tail -1 "$L/GD.reqdiff.control2ok.log"
  lg GD.reqdiff.control2bad.log python3 "$T/reqdiff.py" "$X/gdbase" "$X/ctl/gd2/bad" YB1l; rc "GD reqdiff planted Definition" $? 1; tail -1 "$L/GD.reqdiff.control2bad.log"
  # reqdiff reads Require sentences only: a change in a COMMENT is NOT Require-only and it refuses (by design). The
  # comment-stripped comparison is the gate for a comment-only change: tools/stripcmp.py (a copy of the fuzz_uci
  # lane's, 006d278b3a92's 476ab3345401) drops every `(* ... *)` and keeps the newlines, so a code change moves a line
  # and a comment change does not.
  echo "=== GD CONTROL 3a: a copy of the base YF0m with a word added INSIDE its first comment must be comment-stripped EQUAL ==="
  rm -rf "$X/ctl/gd3"; mkdir -p "$X/ctl/gd3"
  python3 - "$X/gdbase/YF0m.v" "$X/ctl/gd3/YF0m.v" <<'EOF'; rc "GD plant 3a" $?
import sys
t = open(sys.argv[1]).read()
i = t.index('*)')
open(sys.argv[2], 'w').write(t[:i] + 'gd_planted_comment_word ' + t[i:])
print('planted: the word gd_planted_comment_word inside the first comment of YF0m')
EOF
  lg GD.stripcmp.control3a.log python3 "$T/stripcmp.py" "$X/gdbase/YF0m.v" "$X/ctl/gd3/YF0m.v"; rc "GD stripcmp comment word" $? 0; tail -1 "$L/GD.stripcmp.control3a.log"
  echo "=== GD CONTROL 3b: the CONTROL 1 copy of YB12 (x_memset +4, a code line) must be comment-stripped DIFFERENT ==="
  lg GD.stripcmp.control3b.log python3 "$T/stripcmp.py" "$X/gdbase/YB12.v" "$X/ctl/gd/YB12.v"; rc "GD stripcmp planted numeral" $? 1; tail -1 "$L/GD.stripcmp.control3b.log"
  echo "=== GD CONTROL 4: a copy of GD.expect without its YB01 line and without the commit of its YE37 line must be REFUSED ==="
  sed -e '/^YB01 /d' -e 's/^\(YE37 [a-z]*\) [0-9a-f,]* /\1 /' "$GDX" > "$X/ctl/gd4.expect"
  gd_parse "$X/ctl/gd4.expect" > /dev/null; rc "GD GD.expect read, planted copy" $? 1
  echo "=== GD CONTROL 5: a copy of GD.expect that states YE37 as comment-only and YF0m as equal must give exactly 2 UNEXPECTED steps (YE37 comment-stripped, YF0m byte-equal) ==="
  sed -e 's/^YE37 code /YE37 comment /' -e 's/^YF0m .*/YF0m equal/' "$GDX" > "$X/ctl/gd5.expect"
  gd_parse "$X/ctl/gd5.expect" > "$X/ctl/gd5.parsed"
  gd_ctl "$X/ctl/gd5.parsed" "$X/in/gen" GD.expect.control5.log 'GD YE37 [comment]: comment-stripped EQUAL (stripcmp)' 'GD YF0m [equal]: byte-equal to the base'
  rc "GD planted classes caught" $? 0
  # the steps a planted numeral trips depend on YB12's class in GD.expect: equal -> byte-equal; comment / comment-pass ->
  # comment-stripped EQUAL and the changed lines (bytes differ and reqdiff refuse in both cases, as wanted)
  local c6 l6 w6=()
  read -r c6 l6 <<< "$(awk '$1 == "YB12" {print $2, $4}' "$X/gd.parsed")"
  case $c6 in
    equal) w6=('GD YB12 [equal]: byte-equal to the base') ;;
    comment|comment-pass) w6=("GD YB12 [$c6]: comment-stripped EQUAL (stripcmp)" "GD YB12 [$c6]: the changed lines are exactly lines $l6") ;;
  esac
  echo "=== GD CONTROL 6: GD.expect on a copy of the snapshot whose YB12 has x_memset +4 must give exactly the UNEXPECTED steps YB12's class ($c6) names: ${w6[*]:-none, the class has no planted-numeral want} ==="
  rm -rf "$X/ctl/gd6"; mkdir -p "$X/ctl/gd6"; cp "$X/in/gen"/*.v "$X/ctl/gd6/"
  python3 - "$X/ctl/gd6/YB12.v" <<'EOF'; rc "GD plant 6" $?
import re, sys
t = open(sys.argv[1]).read()
m = re.search(r'x_memset := (0x[0-9a-f]+)', t)
open(sys.argv[1], 'w').write(t[:m.start(1)] + hex(int(m.group(1), 16) + 4) + t[m.end(1):])
print('planted: x_memset %s -> %s in the snapshot copy of YB12' % (m.group(1), hex(int(m.group(1), 16) + 4)))
EOF
  if [ ${#w6[@]} -gt 0 ]; then gd_ctl "$X/gd.parsed" "$X/ctl/gd6" GD.expect.control6.log "${w6[@]}"; rc "GD planted numeral caught" $? 0
  else rc "GD planted numeral caught: YB12's class $c6 has no planted-numeral want" 1 0; fi
  echo "=== GD: each of the 19 against the base, the steps its class in GD.expect wants ==="
  gd_files "$X/gd.parsed" "$X/gdbase" "$X/in/gen"
  [ -n "$(awk '$1 != "base" && ($2 == "comment" || $2 == "comment-pass" || $2 == "code")' "$X/gd.parsed")" ] && wr=1
  [ -n "$(awk '$1 != "base" && ($2 == "require" || $2 == "code")' "$X/gd.parsed")" ] && ws=1
  echo "=== GD reqdiff: the base -> this snapshot, all 19 (want $wr: 1 when GD.expect states a comment, comment-pass or code change) ==="
  lg GD.reqdiff.log python3 "$T/reqdiff.py" "$X/gdbase" "$X/in/gen" $ALL19; rc "GD reqdiff all 19" $? $wr; cut -c1-300 "$L/GD.reqdiff.log"
  echo "=== GD stripcmp: the base -> this snapshot, comment-stripped, all 19 (want $ws: 1 when GD.expect states a Require or code change) ==="
  : > "$X/raw/GD.stripcmp.log"
  for n in $ALL19; do
    python3 "$T/stripcmp.py" "$X/gdbase/$n.v" "$X/in/gen/$n.v" >> "$X/raw/GD.stripcmp.log" 2>&1 || sr=1
  done
  klog < "$X/raw/GD.stripcmp.log" > "$L/GD.stripcmp.log"
  rc "GD stripcmp all 19 (comment-stripped EQUAL)" $sr $ws
  echo "  comment-stripped EQUAL: $(grep -c 'diff lines 0$' "$L/GD.stripcmp.log") of $(grep -c 'stripcmp' "$L/GD.stripcmp.log") files"
}

G1() {  # kimg_overlap FROZEN acfd7418176d (of record) on every file; 5db341e3cd62 on YB01 / YB03
  local K=$T/kimg_overlap-acfd7418176d.py K5=$T/kimg_overlap-5db341e3cd62.py a=() c=() n
  echo "=== G1 CONTROL: kimg_overlap acfd7418176d on cgif's released lib/YB01.v / lib/YB03.v at 25e3d17bdb50, cgif B image ==="
  lg G1.kimg.acfd.control.log python3 "$K" "$DON" 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB01.v "$CB" \
    25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB03.v "$CB"
  rc "G1 kimg acfd CONTROL cgif YB01/YB03" $?; cat "$L/G1.kimg.acfd.control.log"
  for n in $ALL19; do c+=(FILE "$X/in/cgif/$n.v" "$CB"); done
  for n in $(present); do a+=(FILE "$X/in/gen/$n.v" "$UB"); done
  echo "=== G1 CONTROL (per file): the same tool on cgif's released counterpart of all 19, cgif B image ==="
  lg G1.kimg.acfd.control-all.log python3 "$K" "$DON" "${c[@]}"
  rc "G1 kimg acfd CONTROL cgif counterparts" $?; sed "s#\$LT/gates/in/##" "$L/G1.kimg.acfd.control-all.log"
  echo "=== G1 kimg_overlap acfd7418176d on the fuzz_wire B files present, fuzz_wire B pin ==="
  if [ ${#a[@]} -gt 0 ]; then
    lg G1.kimg.acfd.wireB.log python3 "$K" "$DON" "${a[@]}"
    rc "G1 kimg acfd wireB" $?; sed "s#\$LT/gates/in/##" "$L/G1.kimg.acfd.wireB.log"
  else echo "  no file present"; fi
  echo "=== G1b kimg_overlap 5db341e3cd62 (decode B's version): CONTROL cgif YB01/YB03, then fuzz_wire B YB01/YB03 ==="
  lg G1.kimg.5db3.control.log python3 "$K5" "$DON" 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB01.v "$CB" \
    25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB03.v "$CB"
  rc "G1b kimg 5db3 CONTROL" $?; cat "$L/G1.kimg.5db3.control.log"
  a=(); for n in YB01 YB03; do has $n && a+=(FILE "$X/in/gen/$n.v" "$UB"); done
  if [ ${#a[@]} -gt 0 ]; then
    lg G1.kimg.5db3.wireB.log python3 "$K5" "$DON" "${a[@]}"
    rc "G1b kimg 5db3 wireB" $?; sed "s#\$LT/gates/in/##" "$L/G1.kimg.5db3.wireB.log"
  else echo "  YB01 / YB03 not present"; fi
}

# --- codeptr declarations: each value NOT stale, keyed by role and symbol / section + offset in BOTH images.
#     Filled from pass 1 (logs/G2c.codeptr.pass1.log); the evidence for each: tools/decl_evidence_wire.py (G2e).
. "$G/codeptr-decl.sh"

G2() {  # codeptr 12348302dfd2 (start-up set of commit dbb5a97ad14), the full check: --stale-image + --stale-names + --stale-file
  echo "=== G2a CONTROL: codeptr-controls known answers (tools/frozen/codeptr-controls.wire.sh = 25c012a65b96, paths from env.sh), donor worktree \$DON ==="
  lg G2a.codeptr-controls.log bash "$T/frozen/codeptr-controls.wire.sh" "$BUNDLE" "$DON"
  rc "G2a codeptr-controls" $?; tail -3 "$L/G2a.codeptr-controls.log" | cut -c1-400
  local base=(--image "$UB" --names "$UNM" --stale-image "$CB" --stale-names "$CBN") sf=() files=() f
  echo "=== G2b POSITIVE CONTROL: cgif's UNRELOCATED YD1k / YD2i / YD2j against fuzz_wire B's image (must find, rc 1) ==="
  rm -rf "$X/ctl/cp"; mkdir -p "$X/ctl/cp"
  for f in YD1k YD2i YD2j; do cp "$DLIBC/$f.v" "$X/ctl/cp/$f.v"; sf+=(--stale-file "$X/ctl/cp/$f.v=$DLIBC/$f.v"); done
  lg G2b.codeptr.posctl.log $FRT codeptr.py "${base[@]}" "${sf[@]}" "$X/ctl/cp/YD1k.v" "$X/ctl/cp/YD2i.v" "$X/ctl/cp/YD2j.v"
  rc "G2b codeptr POSITIVE control" $? 1
  grep -v '^frozen-run' "$L/G2b.codeptr.posctl.log" | grep -E 'FINDINGS|UNMEASURED|^codeptr' | cut -c1-260
  sf=()
  for f in $(present); do sf+=(--stale-file "$X/in/gen/$f.v=$DLIBC/$f.v"); files+=("$X/in/gen/$f.v"); done
  [ ${#files[@]} -gt 0 ] || { echo "  no file present"; return; }
  echo "=== G2c PASS 1: every file present, each paired with cgif's donor file of the same name, no declaration ==="
  lg G2c.codeptr.pass1.log $FRT codeptr.py "${base[@]}" "${sf[@]}" "${files[@]}"
  rc "G2c codeptr pass 1 (findings before the declarations)" $? 1; grep -v '^frozen-run' "$L/G2c.codeptr.pass1.log" | grep -E 'FINDINGS|UNMEASURED|NOT read|^codeptr' | cut -c1-400
  if [ -f "$T/decl_evidence_wire.py" ]; then
    echo "=== G2e the evidence of every declaration, by command on BOTH images (tools/decl_evidence_wire.py) ==="
    lg G2e.decl_evidence.log python3 "$T/decl_evidence_wire.py" "$UB" "$UNMS" "$CB" "$CBN" "$X/in/gen" "$X/in/cgif"
    rc "G2e declaration evidence" $?; grep -E '^==|FAIL|^decl_evidence' "$L/G2e.decl_evidence.log" | cut -c1-300
  fi
  echo "=== G2d PASS 2: the same + ${#DECL[@]} declaration arguments (codeptr-decl.sh) ==="
  lg G2d.codeptr.pass2.log $FRT codeptr.py "${base[@]}" "${sf[@]}" ${DECL[@]+"${DECL[@]}"} "${files[@]}"
  rc "G2d codeptr pass 2 (rc 2 = files with no address literal in range are UNMEASURED)" $? 2
  grep -v '^frozen-run' "$L/G2d.codeptr.pass2.log" | grep -E 'FINDINGS|UNMEASURED|NOT read|NOT an address|declared|^codeptr' | cut -c1-400
  python3 - "$L/G2d.codeptr.pass2.log" <<'EOF'; rc "G2d pass 2 verdict: 0 FINDINGS in every measured file, UNMEASURED = YB1l / YB1m only" $? 0
import re, sys
t = open(sys.argv[1]).read()
meas = re.findall(r'^(Y\w+\.v) .* (\d+) FINDINGS', t, re.M)
unm = re.findall(r'^(Y\w+\.v)\s+UNMEASURED', t, re.M)
bad = [(f, n) for f, n in meas if n != '0']
print('  measured files %d, with findings %s; UNMEASURED %s' % (len(meas), bad or 'none', unm))
sys.exit(0 if not bad and sorted(unm) == ['YB1l.v', 'YB1m.v'] and len(meas) == 17 else 1)
EOF
}

G3() {  # port_addr_check FROZEN 16f8a030c869, cb0e067e3bae, e165063a0081 and efa19b81e92b (the newer version of record,
        # --fail-on-flags on both e165 and efa1); moved rows (cb0e -> e165 and e165 -> efa1); GENERATOR-FILL triage
  [ -d "$X/pac" ] && chmod -R u+w "$X/pac"; rm -rf "$X/pac"; mkdir -p "$X/pac/cgifA" "$X/pac/cgifB" "$X/pac/cache"
  cp -r "${PAC_CACHE:?set PAC_CACHE in env.sh}/." "$X/pac/cache/"; chmod -R u+w "$X/pac/cache"
  local inc=() cinc=() n
  for n in $ALL19; do cp "$X/in/cgif/A/A${n:1}.v" "$X/pac/cgifA/$n.v"; cp "$X/in/cgif/$n.v" "$X/pac/cgifB/$n.v"; cinc+=(--include "$n.v"); done
  for n in $(present); do inc+=(--include "$n.v"); done
  local v P PFX want
  for v in G3:pac G3b:pac-cb0e G3e:pac-e165 G3a:pac-efa1; do
    PFX=${v%%:*}; P="python3 $T/${v#*:}/port_addr_check.py --git $DON --donors-from ${DONOR_BINS:?set DONOR_BINS in env.sh} --cache $X/pac/cache --paired-only --summary"
    # efa19b81e92b (of record) and e165063a0081 with --fail-on-flags (FLAG-CLASSES 575d398c6022): flags fail, rc 4; the
    # flagged rows are triaged class by class by G3d / G3m / G3c / G3s. 16f8a030c869 and cb0e067e3bae report only (rc 0)
    want=0; case $PFX in G3e|G3a) P="$P --fail-on-flags"; want=4;; esac
    echo "=== $PFX CONTROL: port_addr_check $(sha256sum "$T/${v#*:}/port_addr_check.py" | cut -c1-12), cgif's own released A set (renamed to its Y twins) -> its B set, all 19 ==="
    lg $PFX.pac.cgifAB.log $P --src "$X/pac/cgifA" --src-image "B=$CA" --dst "$X/pac/cgifB" --dst-image "B=$CB" --out "$X/pac/$PFX.cgifAB.tsv" "${cinc[@]}"
    rc "$PFX port_addr_check CONTROL cgif A->B" $? $want; grep -v '^#' "$L/$PFX.pac.cgifAB.log" | grep -v '^ ' | grep -v '^INPUTS' | tail -30
    [ ${#inc[@]} -gt 0 ] || { echo "  no fuzz_wire file present"; continue; }
    echo "=== $PFX port_addr_check: cgif's released B set (source) -> the fuzz_wire B files present (port) ==="
    lg $PFX.pac.wireB.log $P --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$X/pac/$PFX.wireB.tsv" "${inc[@]}"
    rc "$PFX port_addr_check cgif B -> wire B" $? $want; grep -v '^#' "$L/$PFX.pac.wireB.log" | grep -v '^ ' | grep -v '^INPUTS' | tail -30
    lg $PFX.pac.table.md python3 "$G/pac_table.py" "$X/pac/$PFX.cgifAB.tsv" "$X/pac/$PFX.wireB.tsv"
    rc "$PFX pac_table" $?; cat "$L/$PFX.pac.table.md"
  done
  (cd "$X/pac" && sha256sum *.tsv) | klog > "$L/G3.tsv.sha256"
  echo "  TSVs (scratch, sha256 in logs/G3.tsv.sha256): $(cd "$X/pac" && ls *.tsv | tr '\n' ' ')"
  local gfc gfu REC=G3a        # the version of record: efa19b81e92b (G3a); e165063a0081 (G3e), cb0e067e3bae (G3b) and 16f8a030c869 (G3) beside it
  for v in G3e.pac.cgifAB.log G3e.pac.wireB.log G3a.pac.cgifAB.log G3a.pac.wireB.log; do echo "  $v: $(grep -E 'FLAGGED|FLAG-CLASSES' "$L/$v" | tr '\n' ' ' | cut -c1-300)"; done
  echo "=== G3d rows that MOVED between cb0e067e3bae and e165063a0081 (tools/pac_moved.py), control run first, then wire B ==="
  lg G3d.moved.cgifAB.log python3 "$T/pac_moved.py" "$X/pac/G3b.cgifAB.tsv" "$X/pac/G3e.cgifAB.tsv"; rc "G3d moved rows CONTROL cgif A->B" $?; sed -n '1,12p' "$L/G3d.moved.cgifAB.log" | cut -c1-300
  if [ -f "$X/pac/G3e.wireB.tsv" ]; then
    lg G3d.moved.wireB.log python3 "$T/pac_moved.py" "$X/pac/G3b.wireB.tsv" "$X/pac/G3e.wireB.tsv"; rc "G3d moved rows wire B" $?; cut -c1-400 "$L/G3d.moved.wireB.log" | head -60
  fi
  echo "=== G3m rows that MOVED between e165063a0081 and efa19b81e92b (the version change), control first, then wire B ==="
  lg G3m.moved.cgifAB.log python3 "$T/pac_moved.py" "$X/pac/G3e.cgifAB.tsv" "$X/pac/G3a.cgifAB.tsv"; rc "G3m moved rows CONTROL cgif A->B" $?; sed -n '1,12p' "$L/G3m.moved.cgifAB.log" | cut -c1-300
  if [ -f "$X/pac/G3a.wireB.tsv" ]; then
    lg G3m.moved.wireB.log python3 "$T/pac_moved.py" "$X/pac/G3e.wireB.tsv" "$X/pac/G3a.wireB.tsv"; rc "G3m moved rows wire B" $?; cut -c1-400 "$L/G3m.moved.wireB.log" | head -60
    echo "  G3m verdict counts, wire B: e165 $(awk -F'\t' 'NR>1 && !/^#/ {print $1}' "$X/pac/G3e.wireB.tsv" | sort | uniq -c | tr '\n' ' ')"
    echo "  G3m verdict counts, wire B: efa1 $(awk -F'\t' 'NR>1 && !/^#/ {print $1}' "$X/pac/G3a.wireB.tsv" | sort | uniq -c | tr '\n' ' ')"
  fi
  gfc=$(awk -F'\t' '$1=="GENERATOR-FILL"' "$X/pac/$REC.cgifAB.tsv" | wc -l)
  gfu=$( [ -f "$X/pac/$REC.wireB.tsv" ] && awk -F'\t' '$1=="GENERATOR-FILL"' "$X/pac/$REC.wireB.tsv" | wc -l || echo 0)
  echo "  GENERATOR-FILL rows ($REC, efa19b81e92b): control $gfc; wire B $gfu"
  if [ "$gfu" -gt 0 ]; then python3 - "$X/pac/$REC.wireB.tsv" <<'EOF'
import csv, collections, sys
rows = [r for r in csv.DictReader([l for l in open(sys.argv[1]) if not l.startswith('#')], delimiter='\t') if r['verdict'] == 'GENERATOR-FILL']
print('  wire B GENERATOR-FILL rows per file: %s; distinct ported lines %d' % (dict(collections.Counter(r['dst_file'] for r in rows)), len({(r['dst_file'], r['dst_line']) for r in rows})))
EOF
  fi
  echo "=== G3c GENERATOR-FILL triage: every row a measured reason. YF0m rows: tools/pac_fill.py; every other row: tools/pac_fill_states.py. CONTROLS first ==="
  lg G3c.fill.cgifAB.log python3 "$T/pac_fill.py" "$X/pac/$REC.cgifAB.tsv" "$X/pac/cgifB/YF0m.v" "$X/pac/cgifA/YF0m.v" "$CB" "$CBN" "$CA" "$S/syms/cgif_file_fuzzer.asan.nm"
  rc "G3c pac_fill CONTROL cgif A->B (its rows are cgif YCej rows, outside the YF0m rules: fails closed)" $? 1; cut -c1-400 "$L/G3c.fill.cgifAB.log" | tail -3
  lg G3c.fillstates.cgifAB.log python3 "$T/pac_fill_states.py" "$X/pac/$REC.cgifAB.tsv" "$X/pac/cgifB" "$X/pac/cgifA" "$CB" "$CA"
  rc "G3c pac_fill_states CONTROL cgif A->B (YCej rows are not state rows: fails closed)" $? 1; cut -c1-400 "$L/G3c.fillstates.cgifAB.log" | tail -2
  if has YB01 && awk -F'\t' '$1=="GENERATOR-FILL" && $6=="YB01.v"' "$X/pac/$REC.wireB.tsv" | grep -q .; then
    echo "=== G3c PLANTED control for rule S: a copy of WK/gen YB01 with one KFill 249 granule run planted in HS_tfib_0_kn's hull band must be refused ==="
    rm -rf "$X/pac/plantS"; mkdir -p "$X/pac/plantS"; cp "$X/in/gen"/*.v "$X/pac/plantS/"
    python3 - "$X/pac/plantS/YB01.v" <<'EOF'; rc "G3c rule-S plant" $?
import re, sys
t = open(sys.argv[1]).read()
i = t.index('Definition HS_tfib_0_kn')
m = re.compile(r'KZero \{\| a_base := ELit 0; a_off := 2147459072 \|\} \(ELit \d+\); ').search(t, i)
t = t[:m.start()] + 'KFill {| a_base := ELit 0; a_off := 2147459080 |} (ELit 2) 249; ' + t[m.start():]
open(sys.argv[1], 'w').write(t)
print('planted: KFill (0x7fffa008, 2) 249 before the band KZero of HS_tfib_0_kn')
EOF
    lg G3c.fillstates.planted.log python3 "$T/pac_fill_states.py" "$X/pac/$REC.wireB.tsv" "$X/pac/plantS" "$X/in/cgif" "$UB" "$CB"
    rc "G3c pac_fill_states PLANTED" $? 1; grep -E 'S1|UNEXPLAINED' "$L/G3c.fillstates.planted.log" | cut -c1-300 | tail -4
  fi
  echo "=== G3c triage of the wire B rows ==="
  if [ "$gfu" -gt 0 ]; then
    lg G3c.fillstates.wireB.log python3 "$T/pac_fill_states.py" "$X/pac/$REC.wireB.tsv" "$X/in/gen" "$X/in/cgif" "$UB" "$CB"
    rc "G3c pac_fill_states wire B (rows outside YF0m)" $?; cut -c1-500 "$L/G3c.fillstates.wireB.log"
  fi
  if has YF0m; then
    lg G3c.fill.wireB.log python3 "$T/pac_fill.py" "$X/pac/$REC.wireB.tsv" "$X/in/gen/YF0m.v" "$X/in/cgif/YF0m.v" "$UB" "$UNMS" "$CB" "$CBN"
    rc "G3c pac_fill wire B (YF0m rows; it prints every row outside YF0m as UNEXPLAINED, those are pac_fill_states'; the triage verdict below judges every row)" $? 1; cut -c1-500 "$L/G3c.fill.wireB.log"
    local ul; ul=$(grep -E '^  YF0m\.v:[0-9]+ row ' "$L/G3c.fill.wireB.log" | grep -v -- '-> ACCEPTED$' | sed -E 's/^  YF0m\.v:([0-9]+) .*/\1/' | tr '\n' ' ')
    echo "  YF0m lines pac_fill leaves UNEXPLAINED, given to pac_fill_n0: ${ul:-none}"
    lg G3c.filln0.wireB.log python3 "$T/pac_fill_n0.py" "$X/pac/$REC.wireB.tsv" "$X/in/gen/YF0m.v" "$X/in/cgif/YF0m.v" "$UB" "$UNMS" "$CB" "$CBN" "$X/in/gen/YB01.v" "$X/in/gen/YE37.v" ${ul:-0}
    rc "G3c pac_fill_n0 wire B (YF0m rows with no af0m FILL comment: rules N / Z)" $?; cut -c1-700 "$L/G3c.filln0.wireB.log"
  fi
  [ "$gfu" -gt 0 ] || echo "  wire B: 0 GENERATOR-FILL rows on the files present"
  if [ "$gfu" -gt 0 ]; then
    python3 - "$X/pac/$REC.wireB.tsv" "$L/G3c.fill.wireB.log" "$L/G3c.fillstates.wireB.log" "$L/G3c.filln0.wireB.log" <<'EOF'; rc "G3c GENERATOR-FILL triage, all rows (YF0m: pac_fill per line; others: pac_fill_states per row)" $?
import csv, os, re, sys
rows = [r for r in csv.DictReader([l for l in open(sys.argv[1]) if not l.startswith('#')], delimiter='\t') if r['verdict'] == 'GENERATOR-FILL']
yl = {int(r['dst_line']) for r in rows if r['dst_file'] == 'YF0m.v'}
fl = open(sys.argv[2]).read() if os.path.exists(sys.argv[2]) else ''
acc = {int(m.group(1)) for m in re.finditer(r'^  YF0m\.v:(\d+) row \d+ .*-> ACCEPTED$', fl, re.M)}
f0 = open(sys.argv[4]).read() if os.path.exists(sys.argv[4]) else ''
acc |= {int(m.group(1)) for m in re.finditer(r'^  YF0m\.v:(\d+) row \d+ .*-> ACCEPTED$', f0, re.M)}
uy = sorted(yl - acc)
fs = open(sys.argv[3]).read() if os.path.exists(sys.argv[3]) else ''
m = re.search(r'pac_fill_states: (\d+) of (\d+) GENERATOR-FILL rows UNEXPLAINED', fs)
uo, no = (int(m.group(1)), int(m.group(2))) if m else (None, None)
other = sum(1 for r in rows if r['dst_file'] not in ('YF0m.v', 'YE37.v'))
ye = sum(1 for r in rows if r['dst_file'] == 'YE37.v')
yea = len(re.findall(r'^  YE37\.v:\d+ .*-> ACCEPTED$', f0, re.M))
print('  GENERATOR-FILL rows %d: YF0m %d rows on %d lines, %d line(s) UNEXPLAINED %s; YE37 %d rows, %d ACCEPTED by pac_fill_n0; '
      'other files %d rows, pac_fill_states %s of %s UNEXPLAINED' % (len(rows), len(rows) - other - ye, len(yl), len(uy), uy,
                                                                   ye, yea, other, uo, no))
ok = not uy and yea == ye and (other == 0 or (no == other and uo == 0))
print('  TRIAGE: %s' % ('0 rows UNEXPLAINED' if ok else 'UNEXPLAINED rows remain'))
sys.exit(0 if ok else 1)
EOF
  fi
}

G3s() {  # every row of the stale / moved-object classes: a measured reason or UNTRIAGED (a candidate wrong pointer)
  local v
  echo "=== G3s CONTROL FIRST: a copy of the e165 wire B TSV with the ported value of each stale-class row of YB01 / YCej / YD2j moved by +4 (no longer a KImg bound / a return address / an owned bound) must be UNTRIAGED ==="
  python3 - "$X/pac/G3e.wireB.tsv" "$X/pac/G3e.wireB.planted.tsv" <<'EOF'; rc "G3s plant" $?
import sys
n = 0
out = []
for l in open(sys.argv[1]):
    f = l.rstrip('\n').split('\t')
    if not l.startswith('#') and len(f) > 11 and f[0] in ('STALE-DONOR-DATA-POINTER', 'SLID-TO-NEIGHBOUR', 'NO-COUNTERPART', 'IMAGE-EXTENT-CHANGED') and f[5] in ('YB01.v', 'YCej.v', 'YD2j.v'):
        f[11] = hex(int(f[11], 0) + 4); n += 1
        l = '\t'.join(f) + '\n'
    out.append(l)
open(sys.argv[2], 'w').write(''.join(out))
print('planted: %d row(s) moved by +4' % n)
EOF
  lg G3s.stale.planted.log python3 "$T/pac_stale.py" "$X/pac/G3e.wireB.planted.tsv" "$X/in/gen" "$UB" "$UNMS"
  rc "G3s pac_stale PLANTED (every planted row UNTRIAGED)" $? 1; grep -c UNTRIAGED: "$L/G3s.stale.planted.log" | sed 's/^/  UNTRIAGED rows: /'; tail -1 "$L/G3s.stale.planted.log"
  for v in G3e G3b G3; do
    echo "=== G3s stale-class rows of the wire B run $v ($( [ $v = G3e ] && echo 'e165063a0081, of record' || ([ $v = G3b ] && echo cb0e067e3bae || echo 16f8a030c869))) ==="
    lg G3s.stale.$v.wireB.log python3 "$T/pac_stale.py" "$X/pac/$v.wireB.tsv" "$X/in/gen" "$UB" "$UNMS" "$L/G3c.fill.wireB.log"
    rc "G3s pac_stale wire B $v" $?; cut -c1-400 "$L/G3s.stale.$v.wireB.log"
  done
}

G3f() {  # own control on symbol-NAMED cells (e165063a0081's NAMED_SYM rule judges them against the run's image)
  echo "=== G3f CONTROL FIRST: tools/symnamed.py on a planted file: src0_D_main := main (must be EQUAL) and src0_D_main := main + 4 (must be caught) ==="
  local mn; mn=$(awk '$NF == "main" {print $1; exit}' "$UNMS")
  printf 'Definition src0_D_main : Z := 0x%x.\n' "$((16#$mn))" > "$X/ctl/symnamed.ok.v"
  printf 'Definition src0_D_main : Z := 0x%x.\n' "$((16#$mn + 4))" > "$X/ctl/symnamed.bad.v"
  lg G3f.symnamed.control-ok.log python3 "$T/symnamed.py" "$UBs" "$X/ctl/symnamed.ok.v"; rc "G3f symnamed CONTROL correct cell" $? 0; head -1 "$L/G3f.symnamed.control-ok.log"
  lg G3f.symnamed.control-bad.log python3 "$T/symnamed.py" "$UBs" "$X/ctl/symnamed.bad.v"; rc "G3f symnamed CONTROL planted +4" $? 1; head -1 "$L/G3f.symnamed.control-bad.log"
  echo "=== G3f every symbol-named numeral cell of the files present vs the twin .symtab; YH03 / src0_D_ mentions ==="
  lg G3f.symnamed.wireB.log python3 "$T/symnamed.py" "$UBs" $(for n in $(present); do printf '%s ' "$X/in/gen/$n.v"; done)
  rc "G3f symnamed wire B" $?; cat "$L/G3f.symnamed.wireB.log"
  echo "=== G3r relocation tools of this lane: sha256 of port_core / the image address-map tool / the plan-relocation tool as used, and every mention of alreloc in the lane's text files ==="
  { (cd "$W/tools/pg-reloc/0e4e065eab9f" && sha256sum port_core.py) | sed 's#  #  W/tools/pg-reloc/0e4e065eab9f/#'
    (cd "$KIT" && sha256sum "${MAPTOOL#$KIT/}" "${RELOCTOOL#$KIT/}") | sed 's#  #  $KIT/#'
    echo "port_core version line: $(grep -h -m1 'port_core: versions' "$W/logs/port_core.B.log")"
    echo "map / relocation tool command lines of the collector and port_core: $(grep -l -I -E "${MAPTOOL##*/}|${RELOCTOOL##*/}" "$W"/logs/*.log 2>/dev/null | sed "s#$W/##" | tr '\n' ' ')"
    for f in "$(basename "$MAPTOOL" .py).B.log" "$(basename "$RELOCTOOL" .py).B.log"; do echo "logs/$f (the collector's map / relocation run): $(head -c 300 "$W/logs/$f" | tr '\n' ' ')"; done
    echo "mentions of alreloc in W/logs, W/tools, W/sub, W/work (text files, -I): $(grep -r -I -l 'alreloc' "$W/logs" "$W/tools" "$W/sub" "$W/work" 2>/dev/null | grep -v '/sub/gates/' | wc -l)"
  } > "$X/raw/G3r.reloc.log" 2>&1; klog < "$X/raw/G3r.reloc.log" > "$L/G3r.reloc.log"; cat "$L/G3r.reloc.log"
}

G4() {  # by-role code-address check: classify.py 8daec37298e7 + unit wireB (config only)
  rm -rf "$X/classify"; mkdir -p "$X/classify"
  echo "=== G4 CONTROL FIRST: planted copy (plant_wireB.py; P = .text end + 4 measured from the twin) in CODE cells must be flagged, in a DATA cell not ==="
  lg G4.plant.log python3 "$T/classify/plant_wireB.py" "$X/in/gen" "$X/classify/planted" "$UBs"; rc "G4 plant" $?; cat "$L/G4.plant.log"
  lg G4.classify.planted.log in_dir "$X/classify" python3 "$T/classify/classify.py" --unit wireB --files "$X/classify/planted" --out "$X/classify/out" --tag .planted
  rc "G4 classify PLANTED (a CODE plant exists)" $? 1; cat "$L/G4.classify.planted.log"
  python3 - "$L/G4.plant.log" "$L/G4.classify.planted.log" <<'EOF'; rc "G4 planted control verdict" $?
import re, sys
pl = [re.match(r'planted (\S+) (\S+):(\d+)', l).groups() for l in open(sys.argv[1]) if l.startswith('planted ')]
notp = [l.split()[2].rstrip(':') for l in open(sys.argv[1]) if l.startswith('not planted ')]
fl = {(m.group(1), int(m.group(2))) for m in re.finditer(r'FINDING (\S+):(\d+) ', open(sys.argv[2]).read())}
ok = True
for tag, f, ln in pl:
    hit = (f, int(ln)) in fl
    want = tag.endswith('CODE')
    print('  %-8s %s:%s flagged=%s want=%s %s' % (tag, f, ln, hit, want, 'ok' if hit == want else 'WRONG'))
    ok &= hit == want
extra = fl - {(f, int(ln)) for _, f, ln in pl}
print('  findings not at a plant: %d %s' % (len(extra), sorted(extra)))
v = 'FAIL' if not (ok and not extra) else ('PASS' if not notp else 'PARTIAL PASS (%d of 5 planted; not planted: %s)' % (len(pl), ' '.join(notp)))
print('  PLANTED CONTROL: %s' % v)
sys.exit(0 if ok and not extra else 1)
EOF
  echo "=== G4 classify.py on the fuzz_wire B files present ==="
  lg G4.classify.wireB.log in_dir "$X/classify" python3 "$T/classify/classify.py" --unit wireB --out "$X/classify/out"
  rc "G4 classify wireB" $?; cat "$L/G4.classify.wireB.log"
  [ -f "$X/classify/out/wireB.tsv" ] && klog < "$X/classify/out/wireB.tsv" > "$L/G4.classify.wireB.tsv"
  [ -f "$X/classify/out/wireB.summary.tsv" ] && klog < "$X/classify/out/wireB.summary.tsv" > "$L/G4.classify.wireB.summary.tsv"
  echo "=== G4 coverage: files classify.py reads (its own regex ^[AY](F0m|B\\w\\w)\\.v\$) and the literals its lemma reader skips ==="
  lg G4.coverage.log python3 - "$X/in/gen" "$L/G4.classify.wireB.tsv" "$UB" <<'EOF'; rc "G4 coverage report" $?; cat "$L/G4.coverage.log"
import collections, os, re, sys
from elftools.elf.elffile import ELFFile
gd, tsv, img = sys.argv[1:4]
e = ELFFile(open(img, 'rb'))
tx = e.get_section_by_name('.text'); tlo, thi = tx['sh_addr'], tx['sh_addr'] + tx['sh_size']
per = collections.Counter(l.split('\t')[0] for l in open(tsv).read().split('\n')[1:] if l) if os.path.exists(tsv) else {}
allf = sorted(f for f in os.listdir(gd) if f.endswith('.v'))
inside = [f for f in allf if re.match(r'^[AY](F0m|B\w\w)\.v$', f)]
print('  .text [%#x, %#x) (the pin)' % (tlo, thi))
print('  classify.py reads %d of %d files: %s' % (len(inside), len(allf), ', '.join('%s %d' % (f[:-2], per.get(f, 0)) for f in inside)))
print('  outside its scope (by design: AF0m / AB* only): %s' % ' '.join(f[:-2] for f in allf if f not in inside))
for f in inside:
    if f[1:4] in ('F0m', 'B01', 'B03', 'B05', 'B12'):
        continue
    for i, l in enumerate(open(os.path.join(gd, f)).read().split('\n'), 1):
        if l.lstrip().startswith('(*') or l.startswith('From') or l.startswith('Require'):
            continue
        for m in re.finditer(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)\.(?!\w)', l):
            v = int(m.group(1), 0)
            print('  NOT READ by the lemma reader: %s:%d %s (%s) %s' % (f, i, m.group(1), 'inside .text [%#x, %#x)' % (tlo, thi) if tlo <= v < thi else 'not in .text', l.strip()[:90]))
EOF
}

G5() {  # recount: recount_wire.py (IMG table measured from the twin; control row cgifB first)
  echo "=== G5 recount_wire.py (= recount_dec.py ce9e514496ac / recount_uci.py d64626ea9a6b, IMG table + paths + the n = 0 descriptor-array form) ==="
  lg G5.recount.log python3 "$T/recount_wire.py" "$X" "$UBs"; rc "G5 recount" $?; cat "$L/G5.recount.log"
}

G6() {  # keyed-table scan
  echo "=== G6 keyed-table scan (twin symbols; cgif AF0l / YF0l control first; the files present) ==="
  lg G6.keyed.log python3 "$T/keyed_scan_wire.py" "$UBs" "$X/in/cgif" $(for n in $(present); do printf '%s ' "$X/in/gen/$n.v"; done)
  rc "G6 keyed scan" $?; sed "s#\$LT/gates/in/##" "$L/G6.keyed.log" | cut -c1-400
}

G7() {  # pins.py 4778073f01be check / stamp (on copies) / emitcheck; the --pair check (image A's AF0m)
  rm -rf "$X/stamp"; mkdir -p "$X/stamp"; local n r d
  echo "=== G7a pins.py check (the pin + twin) ==="
  lg G7a.pins.check.log $FRT pins.py check "$UB" --twin "$UBs"; rc "G7a pins check" $?; grep -v '^frozen-run' "$L/G7a.pins.check.log"
  echo "=== G7b pins.py stamp per file (on a COPY in \$LT/gates/stamp, then the copy is compared with the file) ==="
  for n in $(present); do
    cp "$X/in/gen/$n.v" "$X/stamp/$n.v"
    lg G7b.stamp.$n.log $FRT pins.py stamp "$X/stamp/$n.v" "$UB" --twin "$UBs" --ns "$NS"; r=$?
    d=$(python3 - "$X/in/gen/$n.v" "$X/stamp/$n.v" <<'EOF'
import re, sys
a, b = (open(p).read().split('\n') for p in sys.argv[1:3])
fa = [(i + 1, l) for i, l in enumerate(a) if l.startswith('(* Read from: ')]
fb = [(i + 1, l) for i, l in enumerate(b) if l.startswith('(* Read from: ')]
rest = [l for l in a if not l.startswith('(* Read from: ')] == [l for l in b if not l.startswith('(* Read from: ')]
s = 'file Read-from line: %s; stamp writes it at line %s' % ('line %d' % fa[0][0] if fa else 'ABSENT', fb[0][0] if fb else '-')
if fa and fb:
    ha, hb = (re.findall(r'[0-9a-f]{64}', x[0][1]) for x in (fa, fb))
    s += ', text %s' % ('EQUAL' if fa[0][1] == fb[0][1] else 'DIFFERENT (%s)' % (
        'the same pin + twin sha256 %s / %s, other wording' % (hb[0][:12], hb[1][:12]) if ha == hb else 'sha256 DIFFER: file %s, pin %s' % (ha, hb)))
s += '; every other line %s' % ('EQUAL' if rest else 'DIFFERENT')
print(s + ('; copy BYTE-EQUAL' if a == b else ''))
EOF
)
    # YF0m's single-file stamp refuses by design (rc 2): its REAL rows are UNMEASURED without the other image's AF0m,
    # which is what G7d (`--pair`, want 0) measures on the same file
    rc "G7b stamp $n ($d)" $r "$([ "$n" = YF0m ] && echo 2 || echo 0)"; grep -v '^frozen-run' "$L/G7b.stamp.$n.log" | cut -c1-300
  done
  echo "=== G7c pins.py emitcheck --ns $NS on all files present ==="
  if [ -n "$(present)" ]; then
    lg G7c.emitcheck.log $FRT pins.py emitcheck --ns "$NS" $(for n in $(present); do printf '%s ' "$X/in/gen/$n.v"; done)
    rc "G7c emitcheck" $?; grep -v '^frozen-run' "$L/G7c.emitcheck.log" | sed "s#\$LT/gates/in/##"
  fi
  echo "=== G7d YF0m stamp --pair <image A's AF0m.v> (the realset pair check), donor cgif A/B ==="
  local cmd="\$FR3 pins.py stamp <copy of WK/gen/YF0m.v> \$UB --twin \$UBs --ns $NS --pair <image A's lib/A/AF0m.v> --pair-syms \$UAs --donor-a \$DLIBC/A/AF0m.v --donor-a-syms \$S/syms/cgif_file_fuzzer.asan.nm --donor-b \$DLIBC/YF0m.v --donor-b-syms \$S/syms/cgif_file_fuzzer.asan-ubsan.nm"
  if [ -n "${AF0M_A:-}" ] && [ -f "${AF0M_A:-}" ] && has YF0m; then
    cp "$X/in/gen/YF0m.v" "$X/stamp/YF0m.pair.v"
    lg G7d.stamp.YF0m.pair.log $FRT pins.py stamp "$X/stamp/YF0m.pair.v" "$UB" --twin "$UBs" --ns "$NS" --pair "$AF0M_A" --pair-syms "$UAs" \
      --donor-a "$X/in/cgif/A/AF0m.v" --donor-a-syms "$S/syms/cgif_file_fuzzer.asan.nm" \
      --donor-b "$X/in/cgif/YF0m.v" --donor-b-syms "$S/syms/cgif_file_fuzzer.asan-ubsan.nm"; r=$?
    rc "G7d stamp YF0m --pair (image A AF0m sha256 $(sha256sum "$AF0M_A" | cut -c1-12))" $r; grep -v '^frozen-run' "$L/G7d.stamp.YF0m.pair.log" | cut -c1-300
  else
    rc "G7d stamp YF0m --pair: image A's AF0m.v not given$(has YF0m || echo ' (and YF0m is not present)')" PENDING 0
    echo "  command: $cmd"
  fi
}

G8() {  # keyset.py f050b43e480e check, cgif controls first
  local c f r fs=()
  echo "=== G8 keyset.py check: CONTROL cgif's released YB12 / YF0m / YD2j / YB1k on cgif B (--record-names YB1w), one run per file ==="
  for c in YB12 YF0m YD2j YB1k; do
    lg G8.keyset.control.$c.log $FRT keyset.py check --image "$CB" --record-names "$X/in/cgif/YB1w.v" "$X/in/cgif/$c.v"; r=$?
    rc "G8 keyset CONTROL cgif released $c$( [ $c = YB12 ] && echo ' (known answer: REFUSED, the released YB12 lacks the 13th self-loop 0x6e21c that atable adds)')" $r "$([ $c = YB12 ] && echo 1 || echo 0)"; grep -v '^frozen-run' "$L/G8.keyset.control.$c.log" | sed "s#\$LT/gates/in/##" | cut -c1-300
  done
  echo "=== G8 CONTROL: cgif's YB12 as atable 42e18a7eef50 re-emits it on cgif B (WK/ctl/YB12.cgif.v, the generator's control output) ==="
  lg G8.keyset.control.YB12regen.log $FRT keyset.py check --image "$CB" --record-names "$X/in/cgif/YB1w.v" "$WK/ctl/YB12.cgif.v"
  rc "G8 keyset CONTROL cgif YB12 (atable re-emitted)" $?; grep -v '^frozen-run' "$L/G8.keyset.control.YB12regen.log" | cut -c1-300
  for f in YB12 YF0m YD2j YB1k; do has $f && fs+=("$X/in/gen/$f.v"); done
  if [ ${#fs[@]} -gt 0 ]; then
    lg G8.keyset.wireB.log $FRT keyset.py check --image "$UB" --twin "$UBs" "${fs[@]}"
    rc "G8 keyset wireB ($(for f in "${fs[@]}"; do basename "$f" .v; done | tr '\n' ' '))" $?; grep -v '^frozen-run' "$L/G8.keyset.wireB.log" | sed "s#\$LT/gates/in/##" | cut -c1-300
  else echo "  none of YB12 YF0m YD2j YB1k present"; fi
}

G9() {  # ifchk f5cde600cc18 (start-up set of commit dbb5a97ad14) YF0m x YB01
  local IF="$FRT ifchk.py" r cf
  echo "=== G9 CONTROL: cgif's released YF0m x YB01 on the cgif B image, --nholes 50 ==="
  lg G9.ifchk.control.log $IF --owned "$X/in/cgif/YF0m.v" --states "$X/in/cgif/YB01.v" --image "$CB" --nholes 50
  rc "G9 ifchk CONTROL cgif B" $?; grep -v '^frozen-run' "$L/G9.ifchk.control.log" | sed "s#\$LT/gates/in/##" | tail -8
  echo "=== G9 REFUSAL controls: no states (an empty states file), and --nholes 49 (must refuse, rc 2) ==="
  : > "$X/ctl/empty.YB01.v"
  local OW=$X/in/raw/YF0m.v ST=$X/in/raw/YB01.v IM=$UB AD=(--ad1g "$AD1G") lab=wireB
  if [ ! -f "$OW" ] || [ ! -f "$ST" ]; then OW=$X/in/cgif/YF0m.v; ST=$X/in/cgif/YB01.v; IM=$CB; AD=(); lab="cgif B (fuzz_wire raw YF0m / YB01 not present)"; fi
  lg G9.ifchk.nostates.log $IF --owned "$OW" --states "$X/ctl/empty.YB01.v" --image "$IM" --nholes 50 ${AD[@]+"${AD[@]}"}
  rc "G9 ifchk no-states on $lab" $? 2; grep -v '^frozen-run' "$L/G9.ifchk.nostates.log" | tail -3
  lg G9.ifchk.nholes49.log $IF --owned "$OW" --states "$ST" --image "$IM" --nholes 49 ${AD[@]+"${AD[@]}"}
  rc "G9 ifchk --nholes 49 on $lab" $? 2; grep -v '^frozen-run' "$L/G9.ifchk.nholes49.log" | tail -3
  if [ ! -f "$X/in/raw/YF0m.v" ] || [ ! -f "$X/in/raw/YB01.v" ]; then
    rc "G9 PLANTED control and the fuzz_wire B run: WK/raw YF0m.v / YB01.v not present" PENDING 0; return
  fi
  cf=$(awk '$NF == "_ZN11__sanitizer21common_flags_dont_useE" {print $1}' "$UNMS")
  echo "=== G9 PLANTED control: the Tfib_const_abs cell common_flags_dont_use+0 (twin .symtab 0x${cf#"${cf%%[!0]*}"}) of a copy of raw YF0m changed by +1, must be caught ==="
  python3 - "$X/in/raw/YF0m.v" "$X/ctl/YF0m.ifplant.v" "$((16#$cf))" <<'EOF'; rc "G9 plant" $?
import re, sys
t = open(sys.argv[1]).read()
m = list(re.finditer(r'z8 \(ANum %#x\) (0x[0-9a-f]+|\d+) ' % int(sys.argv[3]), t))
assert len(m) == 1, len(m)
v = int(m[0].group(1), 0)
open(sys.argv[2], 'w').write(t[:m[0].start(1)] + hex(v + 1) + t[m[0].end(1):])
print('planted: %r -> %s' % (m[0].group(0), hex(v + 1)))
EOF
  lg G9.ifchk.planted.log $IF --owned "$X/ctl/YF0m.ifplant.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$AD1G"
  rc "G9 ifchk PLANTED" $? 1; grep -v '^frozen-run' "$L/G9.ifchk.planted.log" | tail -6 | cut -c1-300
  echo "=== G9 ifchk on fuzz_wire B: --owned WK/raw/YF0m.v --states WK/raw/YB01.v --image UB --nholes 50 --ad1g port_core B YD1g (EXPECTED: 50 width-0 FALSE, rc 1: its xcell is cgif's, with no width-0 guard; G9p below is the gate of record) ==="
  lg G9.ifchk.wireB.log $IF --owned "$X/in/raw/YF0m.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$AD1G"
  rc "G9 ifchk wireB (port_core B YD1g: the EXPECTED width-0 result)" $? 1; grep -v '^frozen-run' "$L/G9.ifchk.wireB.log" | grep -v '^  state ' | sed "s#\$LT/gates/in/##"
  echo "  ($(grep -c '^  state ' "$L/G9.ifchk.wireB.log") per-state width-0 lines in logs/G9.ifchk.wireB.log)"
  python3 - "$L/G9.ifchk.wireB.log" "$X/in/raw/YF0m.v" <<'EOF'; rc "G9 ifchk wireB width-0 verdict (the expected form)" $? 0
import re, sys
t = open(sys.argv[1]).read()
m = re.search(r'ifchk: (\d+) cells \(sym (\d+), abs (\d+), shadow (\d+)\) x (\d+) states: (\d+) = stated, (\d+) different, '
              r'(\d+) undetermined \(None\), (\d+) inexpressible, (\d+) width-0 FALSE', t)
if not m:
    print('  ifchk summary line NOT FOUND'); sys.exit(1)
n, sy, ab, sh, st, ok_, diff, und, inex, w0 = map(int, m.groups())
z = re.findall(r'^ACell \(ANum (0x[0-9a-f]+)\) 0 \(AV \(ANum (\w+)\)\)', open(sys.argv[2]).read(), re.M)
print('  summary: %d cells (sym %d, abs %d, shadow %d) x %d states; stated %d = (%d - 1) x %d: %s; different %d, undetermined %d, '
      'inexpressible %d, width-0 FALSE %d' % (n, sy, ab, sh, st, ok_, n, st, ok_ == (n - 1) * st, diff, und, inex, w0))
print('  zero-width cells of raw YF0m Tfib_const_abs: %s' % z)
good = diff == 0 and und == 0 and inex == 0 and w0 == st == 50 and ok_ == (n - 1) * st and len(z) == 1
print('  WIDTH-0 VERDICT: %s' % ('EXPECTED: "50 width-0 FALSE" from the ONE zero-width cell %s, every other cell stated in all 50 '
                                 'states, 0 different (port_core B\'s YD1g xcell is cgif\'s, with no width-0 guard)' % z[0][0]
                                 if good else 'NOT the expected form'))
sys.exit(0 if good else 1)
EOF
  if [ -n "${AD1G_PATCHED:-}" ] && [ -f "${AD1G_PATCHED:-}" ]; then
    echo "=== G9p ifchk of record: the same run with --ad1g = the PATCHED YD1g (sha256 $(sha256sum "$AD1G_PATCHED" | cut -c1-12)); its controls first ==="
    lg G9p.ifchk.control.log $IF --owned "$X/in/cgif/YF0m.v" --states "$X/in/cgif/YB01.v" --image "$CB" --nholes 50
    rc "G9p ifchk CONTROL cgif B" $?; grep -E '^ifchk: [0-9]+ cells' "$L/G9p.ifchk.control.log"
    lg G9p.ifchk.planted.log $IF --owned "$X/ctl/YF0m.ifplant.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$AD1G_PATCHED"
    rc "G9p ifchk PLANTED with the patched YD1g" $? 1; grep -E '^ifchk: [0-9]+ cells' "$L/G9p.ifchk.planted.log"
    lg G9p.ifchk.nholes49.log $IF --owned "$X/in/raw/YF0m.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 49 --ad1g "$AD1G_PATCHED"
    rc "G9p ifchk --nholes 49" $? 2; tail -1 "$L/G9p.ifchk.nholes49.log"
    lg G9p.ifchk.wireB.log $IF --owned "$X/in/raw/YF0m.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$AD1G_PATCHED"
    rc "G9p ifchk wireB (patched YD1g, of record)" $?; grep -v '^frozen-run' "$L/G9p.ifchk.wireB.log" | sed "s#\$LT/gates/in/##" | head -12
  else rc "G9p ifchk of record (patched YD1g): AD1G_PATCHED not given (run: AD1G_PATCHED=<path> bash run_gates.sh G9)" PENDING 0; fi
}

G10() {  # ownedcheck 352fb92f567b / 4161c861b0d9, shadowcheck e04173f5a5a5 / 6dccc6f9e8ab / 542898b23954
  local d top ctop
  top=$(imgtop "$UB"); ctop=$(imgtop "$CB")
  echo "=== G10 IMG_TOP measured in this run (page-up of the last PT_LOAD end): fuzz_wire B pin $top, cgif B $ctop ==="
  echo "=== G10 self-test of the latest releases (selftest-d27dfffb.sh, cgif A AF0m on cgif A) ==="
  lg G10.selftest.log sh "$T/selftest-d27dfffb.sh" "$T/shadowcheck-542898b2" "$T/ownedcheck-4161c861" "$X/in/cgif/A/AF0m.v" "$CA"
  rc "G10 selftest 542898b2/4161c861" $?; cat "$L/G10.selftest.log"
  for d in ownedcheck-352fb92f ownedcheck-4161c861; do
    echo "=== G10 $d --elf: CONTROL cgif's released YF0m on cgif B, then fuzz_wire B YF0m on the twin ==="
    lg G10.$d.control.log in_dir "$T/$d" python3 ownedcheck.py "$X/in/cgif/YF0m.v" --elf "$CB"; rc "G10 $d CONTROL" $?; cat "$L/G10.$d.control.log"
    if has YF0m; then lg G10.$d.wireB.log in_dir "$T/$d" python3 ownedcheck.py "$X/in/gen/YF0m.v" --elf "$UBs"; rc "G10 $d wireB" $?; cat "$L/G10.$d.wireB.log"
    else echo "  YF0m not present"; fi
  done
  for d in shadowcheck-e04173f5 shadowcheck-6dccc6f9 shadowcheck-542898b2; do
    echo "=== G10 $d: CONTROL cgif YF0m on cgif B with IMG_TOP=$ctop, then fuzz_wire B with IMG_TOP=$top ==="
    lg G10.$d.control.log in_dir "$T/$d" env IMG_TOP="$ctop" python3 shadowcheck.py "$CB" "$X/in/cgif/YF0m.v"; rc "G10 $d CONTROL" $?; cat "$L/G10.$d.control.log"
    if has YF0m; then lg G10.$d.wireB.log in_dir "$T/$d" env IMG_TOP="$top" python3 shadowcheck.py "$UB" "$X/in/gen/YF0m.v"; rc "G10 $d wireB" $?; cat "$L/G10.$d.wireB.log"
    else echo "  YF0m not present"; fi
  done
}

G11() {  # gen_ad1k hull bound: lowbeg.py 8413f30bc6da (NO asan_globals on fuzz_wire B) + YD1k's bound = YImgTop.IMG_TOP
  local tg
  for tg in dbb5 8cd7; do
    echo "=== G11 lowbeg.py with gen_ad1k of bundle $tg ($(sha256sum "$X/bundle-$tg/gen_ad1k.py" | cut -c1-12)): CONTROL cgif B first, then fuzz_wire B pin ==="
    lg G11.lowbeg.$tg.log python3 "$T/lowbeg.py" "$DON" "$X/bundle-$tg" "$CB" "$UB"; rc "G11 lowbeg ($tg)" $?; cat "$L/G11.lowbeg.$tg.log"
  done
  echo "=== G11 hull-bound control: the bound YD1k states vs the MEASURED image top of the pin (same run) and YImgTop.IMG_TOP ==="
  lg G11.hull.log python3 - "$X/raw/G11.lowbeg.dbb5.log" "$X/in/cgif/YD1k.v" "$X/in/gen/YD1k.v" "$CB" "$UB" "$IMGTOPV" <<'EOF'
import hashlib, os, re, sys
from elftools.elf.elffile import ELFFile
log, fc, fu, ic, iu, itv = sys.argv[1:]
txt = open(log).read()
def top(p):
    e = ELFFile(open(p, 'rb'))
    ls = [s for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    end = max(s['p_vaddr'] + s['p_memsz'] for s in ls)
    last = max(ls, key=lambda s: s['p_vaddr'] + s['p_memsz'])
    return end, (end + 0xfff) & ~0xfff, last
ok = True
# cgif control: 3 descriptors, lowest beg 0x20dc0 aligned -> hull 0x20dc0; its YD1k states `p + n <= 0x20dc0`
hb = {m.group(1): (int(m.group(2)), int(m.group(3), 16)) for m in re.finditer(
    r'^(\S+) sha256=\S+ descriptors=(\d+) lowest_beg=\S+ mod64=\d+ hull_bound=(0x[0-9a-f]+)', txt, re.M)}
t = open(fc).read()
bs = sorted(set(re.findall(r'p \+ n <= (0x[0-9a-f]+)', t)))
lines = [i + 1 for i, l in enumerate(t.split('\n')) if re.search(r'p \+ n <= 0x', l)]
g = ic in hb and hb[ic][0] == 3 and bs == ['%#x' % hb[ic][1]] == ['0x20dc0']
ok &= g
print('CONTROL cgif B: lowbeg descriptors %s hull_bound %s; cgif YD1k `p + n <= ...` bounds %s at lines %s -> %s' % (
    hb.get(ic, ('?',))[0], '%#x' % hb[ic][1] if ic in hb else '?', bs, lines, 'EQUAL (3 descriptors, 0x20dc0)' if g else 'DIFFERENT'))
# fuzz_wire B: lowbeg must report NO asan_globals
no = re.search(r'^%s sha256=(\S+) NO asan_globals' % re.escape(iu), txt, re.M)
ok &= bool(no)
print('fuzz_wire B pin: lowbeg (gen_ad1k first_global + its own asan_globals parse): %s' % (
    'NO asan_globals (sha256 %s)' % no.group(1) if no else 'NOT "NO asan_globals" -> FAIL'))
end, pt, last = top(iu)
print('fuzz_wire B pin: MEASURED image top = page-up of the last PT_LOAD end: PT_LOAD vaddr %#x + memsz %#x = %#x -> %#x' % (
    last['p_vaddr'], last['p_memsz'], end, pt))
if not os.path.exists(fu):
    print('fuzz_wire B YD1k: NOT PRESENT -> the bound check is PENDING')
    sys.exit(0 if ok else 1)
u = open(fu).read()
ul = u.split('\n')
sym = [(i + 1, l.strip()[:150]) for i, l in enumerate(ul) if re.search(r'p \+ n <= YImgTop\.IMG_TOP\b', l)]
lit = [(i + 1, l.strip()[:150], int(m.group(1), 0)) for i, l in enumerate(ul)
       for m in [re.search(r'p \+ n <= (0x[0-9a-fA-F]+|\d+)', l)] if m]
req = [(i + 1, l.strip()[:200]) for i, l in enumerate(ul) if re.search(r'Require[^.]*\bYImgTop\b', l)]
print('fuzz_wire B YD1k: `p + n <= YImgTop.IMG_TOP` at lines %s; `p + n <= <numeral>` at lines %s, numerals %s' % (
    [a for a, _ in sym], [a for a, _, _ in lit], sorted({'%#x' % v for _, _, v in lit})))
for a, l in sym + [(a, l) for a, l, _ in lit]:
    print('   YD1k:%d %s' % (a, l))
v = re.search(r'Notation IMG_TOP := (0x[0-9a-fA-F]+)%Z', open(itv).read())
print('YImgTop.v (port_core B stage-out, sha256 %s): IMG_TOP := %s; YD1k Requires YImgTop: %s' % (
    hashlib.sha256(open(itv, 'rb').read()).hexdigest()[:12], v.group(1) if v else 'NOT FOUND', [a for a, _ in req] or 'no'))
if lit and not sym:   # the numeral form (accepted by the ruling): every stated bound = the measured top
    g = {x for _, _, x in lit} == {pt} and pt == 0x5f6000
    form = 'the NUMERAL form: YD1k states `p + n <= %s` at lines %s' % (sorted({'%#x' % x for _, _, x in lit}), [a for a, _, _ in lit])
elif sym and not lit:  # the symbolic form: the bound is YImgTop.IMG_TOP, whose value must be the measured top
    g = bool(req) and v is not None and int(v.group(1), 16) == pt == 0x5f6000
    form = 'the SYMBOLIC form: YD1k states `p + n <= YImgTop.IMG_TOP` at lines %s, IMG_TOP := %s' % ([a for a, _ in sym], v.group(1) if v else '?')
else:
    g, form = False, 'NEITHER one form (symbolic lines %s, numeral lines %s)' % ([a for a, _ in sym], [a for a, _, _ in lit])
ok &= g
print('HULL BOUND: %s; MEASURED pin image top (same run) %#x -> %s' % (form, pt, 'EQUAL (0x5f6000)' if g else 'FAIL'))
sys.exit(0 if ok else 1)
EOF
  rc "G11 hull-bound gate (cgif control 0x20dc0; fuzz_wire YD1k bound = measured pin image top)" $?; cat "$L/G11.hull.log"
}

G12_body() {  # the generators' own controls: collect their result lines (no re-run); the XW2 exit cross-gate
  echo "=== G12 control result lines of the generator runs (file:line), not re-run ==="
  local f
  for f in $(cd "$W" && ls logs/*.log logs/*/*.log sub/*/REPORT.md sub/*/logs/*.log sub/*/logs/*/*.log 2>/dev/null | grep -v '^sub/gates/'); do
    grep -n -i -E 'EQUAL|control|PASS|FAIL|caught|COk|differ|refus' "$W/$f" | grep -v '^[0-9]*:frozen-run' | sed "s#^#  $f:#" | cut -c1-300
  done
  for f in $(ls "$W/tools/af0mB/ctl" 2>/dev/null); do echo "  tools/af0mB/ctl/$f $(sha256sum "$W/tools/af0mB/ctl/$f" | cut -c1-12)"; done
  echo "=== G12b exit cross-gate: XW2 of YE23 = YE37's cellr cells + x2_shw windows. CONTROL cgif's released YE23/YE37 first ==="
  local pair
  for pair in "cgif:$X/in/cgif" "wireB:$X/in/gen"; do
    if [ ! -f "${pair#*:}/YE37.v" ] || [ ! -f "${pair#*:}/YE23.v" ]; then echo "  ${pair%%:*}: YE23 / YE37 not present"; continue; fi
    python3 - "${pair#*:}/YE37.v" "${pair#*:}/YE23.v" "${pair%%:*}" <<'EOF'; rc "G12b XW2 ${pair%%:*}" $?
import re, sys
t, x = open(sys.argv[1]).read(), open(sys.argv[2]).read()
m = re.search(r'Definition XW2 \(a : Z\) : Prop := (.*?)\.\n', x, re.S)
xw2 = sorted((int(a, 16), int(b, 16)) for a, b in re.findall(r'\((0x[0-9a-f]+) <= a < (0x[0-9a-f]+)\)', m.group(1))) if m else None
cell = [(int(a, 16), int(a, 16) + int(w)) for a, w in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit \d+\) true', t)]
sm = re.search(r'Definition x2_shw[^\n]*', t)
shw = [(int(a, 16), int(a, 16) + int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), ?(\d+)\)', sm.group(0))] if sm else []
mine = sorted(cell + shw)
print(sys.argv[3], 'XW2 (YE23.v)          ', [('%#x' % a, '%#x' % b) for a, b in xw2] if xw2 is not None else 'NO XW2 definition')
print(sys.argv[3], 'YE37 cellr + x2_shw   ', [('%#x' % a, '%#x' % b) for a, b in mine], '(x2_shw %s)' % ('found' if sm else 'NOT FOUND'))
print(sys.argv[3], 'EQUAL' if xw2 == mine else 'DIFFERENT')
sys.exit(0 if xw2 == mine else 1)
EOF
  done
}
G12() {
  G12_body 2>&1 | klog > "$L/G12.collected.log"
  echo "  logs/G12.collected.log: $(grep -c '' "$L/G12.collected.log") lines; per source file, the lines naming a control and the lines naming FAIL / REFUSED / differ:"
  grep -E '^  [^ ]+:[0-9]+:' "$L/G12.collected.log" | awk -F: '{f=$1; sub(/^  /, "", f); n[f]++; if ($0 ~ /[Cc][Oo][Nn][Tt][Rr][Oo][Ll]/) c[f]++; if ($0 ~ /FAIL|REFUSED|differ/) x[f]++} END {for (f in n) printf "    %-48s %4d lines, control %3d, FAIL/REFUSED/differ %3d\n", f, n[f], c[f]+0, x[f]+0}' | sort
  sed -n '/=== G12b/,$p' "$L/G12.collected.log"
}

G13() {  # nsW Require-set gate: nsW.py (the lane's module-path tool) on each file present, --grant-twin <same name>
  rm -rf "$X/nsW"; mkdir -p "$X/nsW/ctl"; local n r f
  echo "=== G13 CONTROL FIRST: a copy of the first file present with one module added to its first lib Require must DIFFER (rc 3) ==="
  f=$(present | awk '{print $1}')
  if [ -n "$f" ]; then
    python3 - "$X/in/gen/$f.v" "$X/nsW/ctl/$f.v" <<'EOF'; rc "G13 plant" $?
import re, sys
t = open(sys.argv[1]).read()
m = re.search(r'(From OssFuzzTheorems\.Proofs\.reac_repacer\.fuzz_wire\.lib\.(?:B|Reusable) Require(?: Import| Export)? )', t)
open(sys.argv[2], 'w').write(t[:m.end(1)] + 'YZZZ ' + t[m.end(1):])
print('planted: module YZZZ added after %r' % m.group(1))
EOF
    lg G13.nsW.control.log python3 "$LTOOLS/nsW.py" "$X/nsW/ctl/$f.v" "$X/nsW/ctl/$f.out.v" --grant-twin "$f"
    rc "G13 nsW PLANTED control on $f" $? 3; cat "$L/G13.nsW.control.log"
  fi
  echo "=== G13 nsW.py <WK/gen file> <scratch> --grant-twin <same name>: Require (dir, module) set vs fuzz_grant B 4f87de75d67; the rewrite must leave the file byte-equal ==="
  : > "$X/raw/G13.nsW.wireB.log"
  for n in $(present); do
    python3 "$LTOOLS/nsW.py" "$X/in/gen/$n.v" "$X/nsW/$n.v" --grant-twin "$n" >> "$X/raw/G13.nsW.wireB.log" 2>&1; r=$?
    echo "nsW $n rc=$r; rewrite of the file $(cmp -s "$X/in/gen/$n.v" "$X/nsW/$n.v" && echo BYTE-EQUAL '(nothing left to rename)' || echo DIFFERS)" >> "$X/raw/G13.nsW.wireB.log"
  done
  klog < "$X/raw/G13.nsW.wireB.log" > "$L/G13.nsW.wireB.log"
  local ne nd nb nf; ne=$(grep -c 'set EQUAL' "$L/G13.nsW.wireB.log"); nd=$(grep -c 'set DIFFERS' "$L/G13.nsW.wireB.log")
  nb=$(grep -c 'BYTE-EQUAL' "$L/G13.nsW.wireB.log"); nf=$(present | wc -w)
  echo "  nsW: $ne EQUAL, $nd DIFFER, $nb byte-equal rewrites, of $nf files"
  rc "G13 nsW Require set (EQUAL and byte-equal for every file)" "$( [ "$ne" = "$nf" ] && [ "$nd" = 0 ] && [ "$nb" = "$nf" ] && ! grep -q 'rc=[1-9]' "$L/G13.nsW.wireB.log" && echo 0 || echo 1)" 0
  grep -E 'EQUAL|DIFFER|rc=' "$L/G13.nsW.wireB.log" | cut -c1-300
  echo "=== G13b placement split (tools/placement.py): grant B's lib/B + lib/Reusable duplicates = PER-IMAGE (lib.B) + HELD (lib.B; measured at SHARED_REF) + SHARED (lib.Reusable); nsW's placement line must state the same split. CONTROLS first ==="
  grep -h 'placement' "$X/raw/G13.nsW.wireB.log" | sed 's/^nsW [^:]*: //' | sort | uniq -c | cut -c1-400
  : > "$X/nsW/pl.list"
  if [ -n "$f" ]; then
    sed "0,/^From OssFuzzTheorems\.Proofs\.reac_repacer\.fuzz_wire\.lib\./s//From OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.B Require YK09.\n&/" "$X/in/gen/$f.v" > "$X/nsW/ctl/$f.plB.v"
    sed "0,/^From OssFuzzTheorems\.Proofs\.reac_repacer\.fuzz_wire\.lib\./s//From OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YImgTop.\n&/" "$X/in/gen/$f.v" > "$X/nsW/ctl/$f.plR.v"
    sed "0,/^From OssFuzzTheorems\.Proofs\.reac_repacer\.fuzz_wire\.lib\./s//From OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.B Require YA0e.\n&/" "$X/in/gen/$f.v" > "$X/nsW/ctl/$f.plH.v"
    printf 'CONTROL-B %s\nCONTROL-R %s\n' "$X/nsW/ctl/$f.plB.v" "$X/nsW/ctl/$f.plR.v" >> "$X/nsW/pl.list"
    [ -n "${SHARED_REF:-}" ] && printf 'CONTROL-H %s\n' "$X/nsW/ctl/$f.plH.v" >> "$X/nsW/pl.list"   # YA0e from lib.B: must be caught once YA0e is SHARED
  fi
  for n in $(present); do echo "WIRE $X/in/gen/$n.v" >> "$X/nsW/pl.list"; done
  lg G13b.placement.log python3 "$T/placement.py" "$X/raw/G13.nsW.wireB.log" "$X/nsW/pl.list"
  rc "G13b placement split" $?; cut -c1-400 "$L/G13b.placement.log"
}

G14() {  # IDENTIFIER gate: idgate.py, every declared identifier vs fuzz_grant B's released lib/B/<same>.v (renamed)
  rm -rf "$X/idg"; mkdir -p "$X/idg/ctl" "$X/idg/grant"; local f n
  echo "=== G14 CONTROL 1: fuzz_grant B's own 19 files (record names renamed GrantB -> WireB ...) against themselves must be EQUAL ==="
  for n in $ALL19; do git -C "$HUB" show "4f87de75d67:proofs/libreac/fuzz_grant/lib/B/$n.v" | python3 -c '
import re, sys
t = sys.stdin.read()
for a, b in (("GrantB_syms", "WireB_syms"), ("GrantB_ok", "WireB_ok"), ("GrantSyms", "WireSyms"), ("GrantB", "WireB")):
    t = re.sub(r"(?<![\w\x27])%s(?![\w\x27])" % a, b, t)
sys.stdout.write(t)' > "$X/idg/grant/$n.v"; done
  lg G14.idgate.control-self.log python3 "$T/idgate.py" "$X/idg/grant" $ALL19; rc "G14 idgate CONTROL fuzz_grant self" $? 0; tail -1 "$L/G14.idgate.control-self.log"
  f=$(present | awk '{print $1}')
  if [ -n "$f" ]; then
    echo "=== G14 CONTROL 2: a copy of $f with its first declared identifier renamed (<name>_planted) must be DIFFERENT naming it (rc 1) ==="
    python3 - "$X/in/gen/$f.v" "$X/idg/ctl/$f.v" <<'EOF'; rc "G14 plant" $?
import re, sys
t = open(sys.argv[1]).read()
m = re.search(r'^(?:Definition|Lemma|Theorem) ([A-Za-z_][\w\']*)', t, re.M)
n = m.group(1)
t = re.sub(r'(?<![\w\'.])%s(?![\w\'])' % re.escape(n), n + '_planted', t)
open(sys.argv[2], 'w').write(t)
print('planted: %s -> %s_planted (every use)' % (n, n))
EOF
    lg G14.idgate.control-plant.log python3 "$T/idgate.py" "$X/idg/ctl" "$f"; rc "G14 idgate PLANTED control" $? 1; cat "$L/G14.idgate.control-plant.log" | cut -c1-400
  fi
  echo "=== G14 idgate.py on the fuzz_wire B files (all 19 named; a missing one is listed MISSING): 4 files differ from fuzz_grant B by known generator output ==="
  lg G14.idgate.wireB.log python3 "$T/idgate.py" "$X/in/gen" $ALL19; rc "G14 idgate wireB (4 known differences)" $? 1; cut -c1-600 "$L/G14.idgate.wireB.log"
  python3 - "$L/G14.idgate.wireB.log" <<'EOF'; rc "G14 the differences are exactly the known ones (a new one would be UNEXPECTED)" $? 0
import ast, re, sys
t = open(sys.argv[1]).read()
# known (GATES-wireB.md, IDENTIFIER gate): YCej = the functions on this image's own measured traces (check_copy, a
# fuzz_wire harness function); YD2j = this image's own read-only regions; YE37 = the n = 0 form (no descriptor cell
# lemmas); YF0m = af0m's fill list here, and no depot-hash rows (the image registers no descriptor)
KNOWN = {'YCej': ({'CTX_check_copy', 'TRACES_check_copy', 'TRACES_check_copy_U'},
                  {'CTX_emit_printf', 'CTX_target_alloc_count', 'CTX_target_alloc_init'}),
         'YD2j': ({'R_A1p'}, {'R_A1d', 'R_A1l', 'R_A1m', 'R_A1n'}),
         'YE37': (set(), {'MU0', 'zi8_14ea00', 'zi8_14f970'}),
         'YF0m': ({'Tfib_const_abs_filled'}, {'TFIB_HASH', 'TFIB_TR0', 'tfib_hash_buckets', 'ts_hash'})}
got = {}
for m in re.finditer(r'^(Y\w+): DIFFERENT .*\n   only here \(\d+\): (\[.*\])\n   only there \(\d+\): (\[.*\])', t, re.M):
    got[m.group(1)] = ({n for _, n in ast.literal_eval(m.group(2))}, {n for _, n in ast.literal_eval(m.group(3))})
for f in sorted(set(got) | set(KNOWN)):
    print('  %s: %s' % (f, 'as known' if got.get(f) == KNOWN.get(f) else 'NOT as known: got %s, known %s' % (got.get(f), KNOWN.get(f))))
sys.exit(0 if got == KNOWN else 1)
EOF
}

HDR() {  # header rule: hdrcheck.py on the scripts written here, REPORT.md and every kept log
  local mine=("$G/run_gates.sh" "$G/codeptr-decl.sh" "$G/pac_table.py" "$G/redact.py" "$T/recount_wire.py" "$T/keyed_scan_wire.py"
              "$T/idgate.py" "$T/placement.py" "$T/classify/plant_wireB.py" "$T/pac_fill_states.py" "$T/pac_fill_n0.py" "$T/pac_moved.py" "$T/symnamed.py" "$T/pac_stale.py" "$T/reqdiff.py"
              "$G/GD.expect" "$G/mk_results.py")
  [ -f "$T/decl_evidence_wire.py" ] && mine+=("$T/decl_evidence_wire.py")
  [ -f "$G/REPORT.md" ] && mine+=("$G/REPORT.md")
  echo "=== HDR hdrcheck.py on ${#mine[@]} scripts / REPORT and $(ls "$L" | wc -l) kept logs ==="
  python3 "$LTOOLS/hdrcheck.py" "${mine[@]}" "$L"/* 2>&1 | sed "s#$G/##" | tail -40; rc "HDR hdrcheck" ${PIPESTATUS[0]}
  echo "=== HDR (information) the copied tools: hits in their unchanged donor text, per file ==="
  python3 "$LTOOLS/hdrcheck.py" $(cd "$T" && find . -type f -name '*.py' -o -type f -name '*.sh' | grep -v -E 'recount_wire|keyed_scan_wire|idgate|placement|plant_wireB|decl_evidence_wire|pac_fill_states|pac_fill_n0|pac_moved|symnamed|pac_stale|reqdiff' | sed "s#^\.#$T#") 2>/dev/null \
    | awk -F: '/^\// {c[$1]++} END {for (f in c) print "  " c[f], f}' | sed "s#$T/##" | sort -k2
}

CTL() {  # the runner's own control (not in the default list; run: NOSNAP=1 bash run_gates.sh CTL): a planted step whose
         # rc 1 is wanted must be OK, and a planted failing step (want 0, rc 1) must be UNEXPECTED, so the run exits 1;
         # with CTL_PLANT=ok the failing step is left out, and the run must exit 0
  ( exit 1 ); rc "CTL planted step, rc 1 wanted" $? 1
  if [ "${CTL_PLANT:-fail}" = ok ]; then echo "  CTL_PLANT=ok: no failing step planted"
  else ( exit 1 ); rc "CTL planted failing step" $? 0; fi
}

GATES=("$@"); [ ${#GATES[@]} -eq 0 ] && GATES=(GD G1 G2 G3 G3s G3f G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 HDR)
sha() { [ -n "${1:-}" ] && [ -f "$1" ] && sha256sum "$1" | cut -c1-12 || echo 'not given'; }
echo "RUN run_gates.sh sha256 $(sha256sum "$GH/run_gates.sh" | cut -c1-64); gates: $([ "${NOSNAP:-0}" = 1 ] || echo 'G0 ')${GATES[*]}; AF0M_A sha256 $(sha "${AF0M_A:-}"); AD1G_PATCHED sha256 $(sha "${AD1G_PATCHED:-}"); GD.expect sha256 $(sha "$GDX"); trunk clone HEAD $(git -C "$TR" rev-parse HEAD)"
outs=()
if [ "${NOSNAP:-0}" != 1 ]; then G0 2>&1 | klog | tee "$L/G0.log"; outs+=("$L/G0.log"); fi
for g in "${GATES[@]}"; do [ "$g" = G0 ] && continue; echo "######## $g"; $g 2>&1 | klog | tee "$L/$g.out"; outs+=("$L/$g.out"); done
# the run's own status: every RESULT line of THIS run's logs must state a want and be OK
nres=$(cat "${outs[@]}" | grep -c '^RESULT ' || true)
nok=$(cat "${outs[@]}" | grep -cE '^RESULT .* \(want [0-9]+\) OK$' || true)
nbad=$((nres - nok)); st=0; [ "$nbad" = 0 ] || st=1
{ echo "######## SUMMARY"
  echo "SUMMARY: RESULT lines $nres in this run's logs (${outs[*]##*/}); OK (rc = the stated want) $nok; UNEXPECTED or no want stated $nbad"
  cat "${outs[@]}" | grep '^RESULT ' | grep -vE ' \(want [0-9]+\) OK$' | sed 's/^/  /'
} | tee "$L/SUMMARY.out"
# the kept logs: LT/gates/logs -> logs/ here (replaced as a set)
if mkdir -p "$GH/logs" && find "$GH/logs" -maxdepth 1 -type f -delete && cp "$L"/* "$GH/logs/"; then echo "logs copied: $(ls "$GH/logs" | wc -l) files"
else echo "logs copy FAILED"; st=1; fi
echo "run_gates.sh exit status: $st"
exit $st
