#!/usr/bin/env bash
# run.sh REPO IMAGE DONOR_IMAGE TOOLS OUT -- re-derive fuzz_disco's image-A start-up data from the files of this
# directory and the tools it cites, and compare every result with what ships.
#
#   REPO         a checkout of the tree that ships proofs/libreac/fuzz_disco (it also holds the donor's released
#                proofs/cgif/cgif_file_fuzzer and index/binaries.tsv)
#   IMAGE        fuzz_disco.asan, the pinned image (sha256 5e39150dd810..., index/binaries.tsv)
#   DONOR_IMAGE  cgif_file_fuzzer.asan, the donor's pinned image (sha256 7093581aab04..., index/binaries.tsv)
#   TOOLS        a directory holding the tools, unchanged, at the paths tools.sha256 names; run.sh checks
#                every one's sha256 before it runs anything:
#                  startup-set/{af0m,atable,gen_ad1k,gen_ad2,hsform,jtsites,keyset,pins,plantail,wh8}.py (startup-set
#                    2026-10-30d, sha256 f8201f503394, e88affcf0526, 2a6885e5c27f, 3665ff2a7926, 9747a6731b7e,
#                    5ff0133afe20, 38b229c6ad08, 4778073f01be, f8aa639d5cc7, fe8327d6bb7e; internal record)
#                  plan/itabranges.py (indexed as found, not of record: tools/startup-cited/itabranges/563d9c175a38/ at
#                    registry commit 5fd6732f0003, sha256 563d9c175a38) and the module it imports,
#                    plan/pautrlen/rvdis.py (startup-set 2026-10-30d, sha256 acc3b31392a5; internal record)
#                  plan/binmatch_plan.py and the module it imports, plan/imgref.py (copy as found, not of record: the
#                    tools that produced the AB05 plan body, tools/startup-cited/binmatch_plan/7f058fcb8e4a/ at registry
#                    commit 5fd6732f0003, sha256 7f058fcb8e4a, 064874159929)
#                  traces/gen_traces.py (indexed as found, not of record: tools/startup-cited/gen_traces/59966c883510/
#                    at registry commit 5fd6732f0003, sha256 59966c883510), traces/resolve_code.py (indexed as found,
#                    not of record: tools/startup-cited/resolve_code/81803218fe79/ at registry commit 5fd6732f0003,
#                    sha256 81803218fe79), traces/rvelf.py (pg-reloc-portcore e0e94a04094b, sha256 23152d9ca11c;
#                    internal record)
#                Every tool above is kept byte-equal at its former path in this directory on the internal records
#                ref records/libreac-fuzz_disco-1031-tool-copies.
#   OUT          an empty directory for the results
#
# Optional, to re-run the two extracts as well (their inputs are not shipped):
#   TWIN=<the unstripped twin of IMAGE>        twin/twin_symbols.py -> twin/fuzz_disco.asan.syms
#   COLLECTOR_LOG=<pass 1 + 2 build log>       collector/extract_dumps.py -> collector/pass12.dumps.1, .2
#   PROBE_LOG=<tail probe build log>           collector/extract_dumps.py -> collector/probe.dumps
#
# Needs python3 with pyelftools and capstone, and sha256sum.
#
# Each step writes into OUT and compares: a regenerated table with its copy under tables/ (cmp), a regenerated .v
# with the shipped file (compare.py's record, itself compared with its copy under tables/). Exit 0 when every
# comparison holds; the first one that does not stops the run.
#
# No tool is shipped here or edited. A tool that read the unstripped twin or a host-path constant runs through
# its driver under drivers/, which imports it unchanged from TOOLS, gives it the twin listing or the input as an argument,
# and runs its own __main__ block (drivers/twinlist.py).
set -euo pipefail
[ $# -eq 5 ] || { echo "usage: run.sh REPO IMAGE DONOR_IMAGE TOOLS OUT" >&2; exit 2; }
EV=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$1" && pwd); IMAGE=$(readlink -f "$2"); DONOR=$(readlink -f "$3"); TOOLS=$(cd "$4" && pwd); OUT=$5
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
check_sha() { [ "$(sha256sum "$1" | cut -c1-64)" = "$2" ] || { echo "run.sh: $1 is not sha256 $2" >&2; exit 1; }; }
check_sha "$IMAGE" 5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46
check_sha "$DONOR" 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0
(cd "$TOOLS" && sha256sum --quiet --strict -c "$EV/tools.sha256") \
  || { echo "run.sh: $TOOLS does not hold the tools tools.sha256 names" >&2; exit 1; }
# Every tool runs in OUT on relative paths (repo/, ev/, tools/, img/), so the reports it writes name no host path.
cd "$OUT"
ln -sfn "$REPO" repo; ln -sfn "$EV" ev; ln -sfn "$TOOLS" tools; mkdir -p img
ln -sfn "$IMAGE" img/fuzz_disco.asan; ln -sfn "$DONOR" img/cgif_file_fuzzer.asan
export OSSV_BINARIES_TSV=repo/index/binaries.tsv PYTHONDONTWRITEBYTECODE=1 STARTUP_TOOLS=tools
S=tools/startup-set; T=ev/tables; X=ev/twin/fuzz_disco.asan.syms; IMG=img/fuzz_disco.asan; CG=img/cgif_file_fuzzer.asan
D=repo/proofs/cgif/cgif_file_fuzzer/lib/A; U=repo/proofs/libreac/fuzz_disco/lib
NSA=OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A=OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.A
NSL=OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib=OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable
NSI=OssFuzzTheorems.cgif.cgif_file_fuzzer.images=OssFuzzTheorems.libreac.fuzz_disco.images
same() { cmp "$1" "$2" && echo "run.sh: $1 = $2"; }
record() {  # record NAME OUT SHIPPED: compare.py's record of OUT vs SHIPPED must be the shipped record tables/NAME.cmp.tsv
  python3 ev/compare.py "$2" "$3" > "$1.cmp.tsv"; same "$1.cmp.tsv" "$T/$1.cmp.tsv"; }

# 0. the extracts, when their inputs are given
if [ -n "${TWIN:-}" ]; then
  python3 ev/twin/twin_symbols.py "$TWIN" "$IMG" fuzz_disco.asan.syms; same fuzz_disco.asan.syms "$X"; fi
if [ -n "${COLLECTOR_LOG:-}" ]; then
  python3 ev/collector/extract_dumps.py "$COLLECTOR_LOG" pass12.dumps JSDUMP HSDUMPHOLES HSDUMP --split 4000000
  same pass12.dumps.1 ev/collector/pass12.dumps.1; same pass12.dumps.2 ev/collector/pass12.dumps.2; fi
if [ -n "${PROBE_LOG:-}" ]; then
  python3 ev/collector/extract_dumps.py "$PROBE_LOG" probe.dumps TAILDUMP; same probe.dumps ev/collector/probe.dumps; fi

# 1. AB03 (join state, pass 1) and AB01 (50 hand-off states, pass 2) from the collector's dumps (two parts: the
#    file size cap)
cat ev/collector/pass12.dumps.1 ev/collector/pass12.dumps.2 > pass12.dumps
python3 $S/hsform.py js pass12.dumps AB03.v --pass Pass1 --header $D/AB03.v --qualify-kinds APC \
  --image $IMG --names $X --ns "$NSA" --ns "$NSL" --month 2026-10
python3 $S/hsform.py hs pass12.dumps AB01.v --pass Pass2 --header $D/AB01.v --nholes 50 \
  --image $IMG --names $X --ns "$NSA" --ns "$NSL" --month 2026-10 --report-json AB01.hs.json
same AB01.hs.json $T/AB01.hs.json
record AB03 AB03.v $U/A/AB03.v
record AB01 AB01.v $U/A/AB01.v

# 2. AB05 (the start-up plan): body by the binary match, code range by the text rule, the measured tail
python3 ev/drivers/run_binmatch_plan.py $D/AB05.v AB05.v --binmatch ev/plan/binmatch.cgif.asan.json --cgif $CG \
  --disco $IMG --funcs ev/plan/funcs.asan.tsv --names $X
python3 tools/plan/itabranges.py --rule text --new $IMG --plan $D/AB05.v --out-plan AB05.v
# the tail: the probe's dump is one arm of N memset stops (0x99b74) and main (0x80aa4); N is the --count
N=$(python3 -c "import re,sys; v=[int(x) for x in re.findall(r'\d+', open(sys.argv[1]).read().split('TAILDUMP = 0')[1].split('     : list')[0])]; assert v[-1] == 0x80aa4 and set(v[:-1]) == {0x99b74}, v; print(len(v) - 1)" ev/collector/probe.dumps)
python3 $S/plantail.py insert --plan AB05.v --main 0x80aa4 --nodes XMemset --count "$N"
record AB05 AB05.v $U/A/AB05.v

# 3. AB12 (the address table) and its field table; the row-set gate on the shipped AB12 and AD2j
python3 ev/drivers/run_atable.py $IMG $X --side A --prefix OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib --reusable .Reusable \
  --img-names YImgTop.IMG_LO,YImgTop.IMG_TOP --donor-image $CG --donor-atable $D/AB12.v --cells $U/A/AF0m.v > AB12.v
python3 ev/drivers/run_atable.py $IMG $X --side A --prefix OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib --reusable .Reusable \
  --img-names YImgTop.IMG_LO,YImgTop.IMG_TOP --donor-image $CG --donor-atable $D/AB12.v --fields > AB12.fields.json
same AB12.fields.json $T/AB12.fields.json
record AB12 AB12.v $U/A/AB12.v
python3 $S/keyset.py check --image $IMG --twin $X --stops-exclude 0x6eca0 $U/A/AB12.v $U/A/AD2j.v > keyset.txt
same keyset.txt $T/keyset.txt

# 4. AD2i, AD2j (image regions, main-entry facts) from the hand-off states, the address table, the segments and the
#    owned cells; then the provenance stamp
MOD='the start-up data of this file is generated from fuzz_disco'"'"'s own asan image and its own collected hand-off states.'
python3 $S/gen_ad2.py --side A --states AB01.v --atable AB12.v --tsegs $U/A/AB1h.v --owned $U/A/AF0m.v --image $IMG --twin $X \
  --tmpl-ad2i $D/AD2i.v --tmpl-ad2j $D/AD2j.v --tmpl-image $CG --ns "$NSA" --ns "$NSL" --ns "$NSI" --modified "$MOD" \
  --month 2026-10 --world-core $U/Reusable/YA0n.v --wh8 --imgtop $U/Reusable/YImgTop.v \
  --out-ad2i AD2i.v --out-ad2j AD2j.v --report A.report --gate-table A.gate.md
# gen_ad2's report (A.report, sha256 below; internal record): two of its notes name the sources of the w_H8 rules as the
# tool's own text has them, so what ships is the report without those two lines (tables/A.report.record)
check_sha A.report e56c1151d7c225ff76b2e4e90d9760605eca1294cbd3285f206ce8e52d1f925b && echo "run.sh: A.report is sha256 e56c1151d7c2..."
awk '!/^NOTE w_H8: |^NOTE W_H8 PRECHECK /' A.report > A.report.record
same A.report.record $T/A.report.record
same A.gate.md $T/A.gate.md

# 5. AD1k: its chunk literals restated from the generated AD2j (the owned cells with YImgTop's numerals: resolve_imgtop.py)
python3 ev/resolve_imgtop.py $U/A/AF0m.v $U/Reusable/YImgTop.v AF0m.resolved.v
python3 ev/drivers/run_gen_ad1k.py --tmpl-ad1k $D/AD1k.v --tmpl-ad2j $D/AD2j.v --tmpl-owned $D/AF0m.v --tmpl-image $CG \
  --ad2j AD2j.v --owned AF0m.resolved.v --image $IMG --twin $X --ns "$NSA" --ns "$NSL" --ns "$NSI" --modified "$MOD" \
  --month 2026-10 --out AD1k.v --sites AD1k.sites.md --label A/AD1k.v
same AD1k.sites.md $T/AD1k.sites.md
for f in AD2i AD2j AD1k; do python3 ev/drivers/run_pins.py stamp $f.v $IMG --twin $X; done
record AD2i AD2i.v $U/A/AD2i.v
record AD2j AD2j.v $U/A/AD2j.v
record AD1k AD1k.v $U/A/AD1k.v

# 6. ACej's allocation traces: every call of the malloc / free interceptors, by function
python3 ev/drivers/run_gen_traces.py $IMG $X --ipc malloc=0x53680 --ipc free=0x53520 --fp LLVMFuzzerTestOneInput=0x80e40 \
  --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm \
  --module OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib > ACej.v
record ACej ACej.v $U/A/ACej.v
# ... and the return addresses ACej's harness contexts and gen_traces' --fp / --ipc arguments are: the direct calls
G=_ZN11__sanitizer10StackTrace12GetCurrentPcEv
# (call_sites.py imports rvelf.py; PYTHONPATH gives it TOOLS/traces/rvelf.py)
PYTHONPATH=tools/traces python3 ev/traces/call_sites.py $IMG $X target_alloc_init target_alloc_count emit_printf LLVMFuzzerTestOneInput \
  $G@__interceptor_malloc $G@__interceptor_free > call_sites.tsv
same call_sites.tsv $T/call_sites.tsv

echo "run.sh: every comparison holds"
