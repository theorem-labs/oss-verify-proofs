# ACej (lib/A/ACej.v): commands and results

This statement replaces the scripts and the universe report of `acej/`. Each is kept, unchanged, in an internal
record, cited below by path and sha256. `acej_check.final.out`, `negctl.out`, `decide.link.json` and
`added.fmemopen.json` stay in this directory.

- Image: fuzz_link.asan sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d (unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f).
- Tools: universe.py 9b10ff83f64b and the composer pautrlen/compose.py 7bf620a82573 of the start-up set 2026-10-30b
  (tool sha256 values: `../startup-set-2026-10-30b.sha256`), run with CTXALL=1 and PYTHONHASHSEED=0.

## Records

- regen.sh, every command of record: internal record, path startgen/acej/regen.sh, sha256 d0037d1838236e5eb140d2d9ae1a3d2e0812701598dee85cfd6a4fe2e910253b
- acej_check.py, the check of lib/A/ACej.v against the image: internal record, path startgen/acej/acej_check.py, sha256 b85758905e5b50a8134d886abe96c4c8a17a3e27554017ce91af5c5b81e2ca34
- compose_jt.py, the composer run with the two switch tables and the extra function start: internal record, path startgen/acej/compose_jt.py, sha256 63c9af0ab01492f2f4780793c6393291dc4230bc0a72594c9dbf26f283c29117
- universe.py's report for the `univ` carrier: internal record, path startgen/acej/universe.univ.report.txt, sha256 a112c9e6bcff9d092aac6acf8f2d61b3577e4d138e95c056b1fb63ee862c4caa

## Commands

The commands of record, with the host paths given as parameters: `STARTUP_SCRATCH` is the start-up scratch directory
(it holds `img/link.asan`, `startup/link.asan.nm.txt`, `startup/set/` and `startup/donor/ACej.v`), `PCAP_NM` the nm
text of libreac v1.9.0 `fuzz_pcap.asan`. The recorded scripts give the same paths as literals, and the two Python
scripts read the same directory from `STARTUP_SCRATCH`.

```sh
#!/bin/bash
# regen.sh -- rebuild acej/ACej.v of reac-pw/fuzz_link (image A) and run its checks; every command of record is here.
# Outputs: ctl/ACej.tool.v (universe.py's file), ACej.v (= ctl/ACej.tool.v + the two hand comments, see provenance.py).
set -euo pipefail
A=$(dirname "$(readlink -f "$0")")
S=${STARTUP_SCRATCH:?set STARTUP_SCRATCH to the start-up scratch directory (img/, startup/)}
export STARTUP_SCRATCH        # acej_check.py and compose_jt.py read it too
SET=$S/startup/set/tools/startup-set/2026-10-30b
IMG=$S/img/link.asan
NM=$S/startup/link.asan.nm.txt
DONOR=$S/startup/donor/ACej.v
PCAP_NM=${PCAP_NM:?set PCAP_NM to the nm text of libreac v1.9.0 fuzz_pcap.asan}
export PT_NAMES=$NM
export PYTHONHASHSEED=0      # the composer iterates sets: a fixed seed makes its JSON byte-stable (the .v files are anyway)
U() { (cd "$SET" && bash frozen-run.sh startup-set-2026-10-30b.tsv universe.py "$@"); }

# 1. pcap control (the tool of record on pcap's composer output) and its comparison with the donor
U "$A/compose.pcap.json" --names "$PCAP_NM" --top 0x80634 \
  --main-ra 0x88234 --lo 0x80298 --hi 0x81efc --out "$A/ctl/pcap.ACej.v" --report "$A/ctl/pcap.report.txt" \
  --json "$A/ctl/pcap.json"
python3 "$A/vdefs.py" "$A/ctl/pcap.ACej.v" "$DONOR" > "$A/ctl/pcap-vs-donor.txt" || true

# 2. link, the tool of record alone (acej/compose.link.json as made by the parent)
U "$A/compose.link.json" --names "$NM" --top 0x820c8 --main-ra 0x90688 --lo 0x81d2c --hi 0x8a350 \
  --out "$A/ctl/ACej.tor.v" --report "$A/ctl/link.tor.report.txt"

# 3. the composer, unchanged, run by compose_jt.py: control (no additions) = compose.link.json, then with the two switch
#    tables and the reac_served_mark start supplied
python3 "$A/compose_jt.py" "$IMG" --out "$A/ctl/compose.link.nojt.json"
python3 "$A/ctl/normcmp.py" "$A/compose.link.json" "$A/ctl/compose.link.nojt.json"
python3 "$A/compose_jt.py" "$IMG" --jt 82dd8:82cc4:82d10:82dbc --jt 843fc:843e0:843ec:843e4 --start 0x895a8 \
  --out "$A/compose.link.jt.json"
U "$A/compose.link.jt.json" --names "$NM" --top 0x820c8 --main-ra 0x90688 --lo 0x81d2c --hi 0x8a350 \
  --decide "$A/decide.link.json" --out "$A/ctl/ACej.jt.v" --report "$A/ctl/link.jt.report.txt"

# 4. plus the hand records of musl fmemopen's two calls; the file with the donor's header
python3 "$A/merge_added.py" "$A/compose.link.jt.json" "$A/added.fmemopen.json" "$A/compose.link.full.json"
M1="ported to reac-pw/fuzz_link: the call contexts and allocation traces are fuzz_link's, read from fuzz_link.asan (sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d) with the names of its unstripped twin (sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f; nm text sha256 889f1840021e1d295d705ecfc706292fab5a21bb2c42e5a46aa1ffb1c0877f43), by the start-up set's composer (pautrlen/compose.py, CTXALL=1) and universe.py 9b10ff83f64b. The composer was given what it does not read itself: the switch tables of LLVMFuzzerTestOneInput (jr at 0x82dd8, table 0x20f64, 5 entries, base reloaded from 0xb8(s1)) and kernel (jr at 0x843fc, table 0x20f78, 8 entries), and the start of reac_served_mark (0x895a8, entered only by the tail jump at 0x88444); two walks are decided: text_of's malloc call 0x87fec and the call 0x8841c in mark_quietly."
M2="added by analysis: musl fmemopen's two malloc calls (comment at TRACES_fmemopen). Excluded: libunwind's DwarfFDECache::add (malloc at +0x7c, 0x8ad54; free at +0xa0, 0x8ad78), for the donor's reason: it is reached only through BufferedStackTrace::UnwindSlow -> _Unwind_Backtrace -> __unw_init_local, and __asan_default_options (0x81d20) returns allocator_may_return_null=1 only, so fast_unwind_on_malloc keeps its default and malloc and free never take the slow unwinder. TRACES_text_of holds only the trace whose walk ends at the first record (comment at TRACES_text_of)."
U "$A/compose.link.full.json" --names "$NM" --top 0x820c8 --main-ra 0x90688 --lo 0x81d2c --hi 0x8a350 \
  --decide "$A/decide.link.json" --header "$DONOR" \
  --ns OssFuzzTheorems.Proofs.libreac.fuzz_pcap.lib=OssFuzzTheorems.Proofs.reac_pw.fuzz_link.lib \
  --modified "$M1" --modified "$M2" --out "$A/ctl/ACej.tool.v" --report "$A/ctl/link.report.txt" --json "$A/ctl/link.full.json"

# 5. checks (ACej.v itself is ctl/ACej.tool.v with the two comments inserted; provenance.py proves that)
python3 "$A/provenance.py" "$A/ACej.v" "$A/ctl/ACej.tool.v" "$A/ctl/ACej.tor.v" "$A/ctl/ACej.jt.v"
python3 "$A/acej_check.py" "$A/ACej.v"
python3 "$A/ctl/negctl.py" "$A/ACej.v"
```

## Results

- Composer input (compose.link.full.json): 22 allocation-site results; interceptor pc0s 0x5420c, 0x5436c, 0x545a0
  (0x540d4 -> 0x5420c, 0x542a4 -> 0x5436c, 0x544cc -> 0x545a0).
- 19 allocator calls; 19 distinct full traces; maximum depth 3; prefix-closed list 32. The donor-form universe has 32
  traces = 19 full + 10 RA_TOP copies + 3 [pc0]. Decided WILD sites: 0x87fec (text_of sets s0 = a1 at 0x87e04) and
  0x8841c (mark_quietly sets s0 = a1 at 0x883e8); neither has a frame record of its own.
- The 19 full traces: [0x5420c; 0x81df8]; [0x5420c; 0x81f28]; [0x5420c; 0x820f4]; [0x5420c; 0x82e70; 0x820c8]; [0x5420c; 0x82e78; 0x820c8]; [0x5420c; 0x83758; 0x820c8]; [0x5420c; 0x83760; 0x820c8]; [0x5420c; 0x838dc; 0x820c8]; [0x5420c; 0x83b8c; 0x820c8]; [0x5420c; 0x83b94; 0x820c8]; [0x5436c; 0x81d80]; [0x5436c; 0x81dd4]; [0x5436c; 0x82060]; [0x5436c; 0x863f0; 0x820c8]; [0x5436c; 0x87ff0]; [0x5436c; 0x96ab8]; [0x5436c; 0x96ac8]; [0x545a0; 0x82c78; 0x820c8]; [0x545a0; 0x82c88; 0x820c8].
- acej_check.py on lib/A/ACej.v (`acej_check.final.out`): sites 24: COVERED 19, EXCLUDED 5, MISSING 0; rules failed 0;
  Tfib_universe 32 traces; RESULT: PASS.
- Negative controls (`negctl.out`): the file passes; each of three copies with one trace removed FAILS (rc=1).
