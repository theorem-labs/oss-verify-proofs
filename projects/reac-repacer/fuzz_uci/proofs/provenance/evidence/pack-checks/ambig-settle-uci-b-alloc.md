# uci-b-alloc: the ambiscan AMBIG rows, settled by address

Written by PackKitScan, Fri Oct 30 19:41:43 UTC 2026. rule 24: no function proved.
Inputs: pack slice uci-b-alloc at 769e2b95876 (= f75c58498e6); X = fuzz_uci.asan-ubsan 8d07ffcf5948; Y = fuzz_grant.asan-ubsan
5a5ee7c02b4e (paircl Y bytes: pin fde52226dc48); for the two planted controls Y = the planted copies, rebuilt with run.sh's
bytes (grantB-S/U-call 1c85bde94bdb / 4aabaada3a62, grantB-S/U-rodata d4c374587adc / 7a86001f9ee0; each sha256 equals the
slice's images.sha256 row).

## 1. The 96 rows in the current (cmpkit 4bbd3a74be89) paircl outputs: 96 MATCH, 0 MISMATCH

All 96 rows name `_ZN6__asanL11MemToShadowEm` (none names `dummy`); they are the CSTR lines of 6 files
(paircl-{malloc,free,tmalloc,tfree}-grant.out, ctl-planted-{call,rodata}-paircl.out), 8 lines per file, each reported once
for X and once for Y. A CSTR line prints no function address, so each line was attributed to its function pair by
re-running paircl's own loop (tools/paircl_acc.py: paircl.py lines 23-75 of cmpkit 4bbd3a74be89, printing the pair before
each acceptance block). Its ACCEPT / CSTR lines are identical, line for line and in order, to each of the 6 record outputs
(3737 / 3737 / 3737 / 3737 / 3668 / 3737 lines), so every record line number maps to one (X address, Y address).

Per row (ambig-settle.tsv): the X copy and the Y copy as symbol + offset with st_value and the STT_FILE that precedes it in
each image's .symtab; every call site of that copy in that image (jal / j / auipc+jalr, all functions scanned); and the
callers paircl paired (paircl-pairs-*.tsv from tools/paircl_pairs.py) that call the X copy and the Y copy at the SAME offset.
MATCH = same function name, the same STT_FILE on both sides, at least one paired caller calling both copies at the same
offset, and no paired caller whose X call reaches the X copy while its Y counterpart at that offset calls something else.

The 4 copies the closures reach and their pairs (X : Y), each with its paired call sites:
- asan_errors.cpp 0x3aafc : 0x3b890, asan_linux.cpp 0x514dc : 0x52c30, asan_poisoning.cpp 0x52b24 : 0x54278,
  asan_thread.cpp 0x5ba10 : 0x5d164 (24 rows each). The asan_fake_stack.cpp copy (X 0x3c348) is not in these closures.

## 2. earlier/ (300 rows, grant run; 60 rows, identity control run): not cited

All 360 rows are in pairtable outputs under earlier/ (pairs-*-grant.tsv, ctl-pairs-*-identity.tsv, ctl-planted-*-pairs.tsv of
va88c2822a0f2, v7daa0e2a03d9, v9cbc3553c09e). Citation check over every file under earlier/ (159 files): tools/cite_check.py,
a fixed-string search equal to `grep -nF -f PATTERNS RECORD.md ACCEPTANCES.tsv settle.tsv MANIFEST.md` in the slice, with the
patterns `earlier/vX/name`, `vX/name` and (when no current file has the same name) `name`:

    $ cd <path> && python3 tools/cite_check.py pack/proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-alloc > uci-b-alloc/cite-check.out
    # 159 files under earlier/, 345 patterns; documents RECORD.md ACCEPTANCES.tsv settle.tsv MANIFEST.md
    TOTAL hits 0	RECORD.md
    TOTAL hits 0	ACCEPTANCES.tsv
    TOTAL hits 0	settle.tsv
    TOTAL hits 159	MANIFEST.md

RECORD.md, ACCEPTANCES.tsv, settle.tsv: not cited (0 hits; the check's output for them is empty apart from the TOTAL lines
above). MANIFEST.md: 159 hits, every one a row of its file table (`| `earlier/...` | earlier run (previous tool version ...) |
sha256 |`), i.e. the files are listed as shipped, not cited by the verdict. RECORD.md names the directory only ("Earlier
versions of record are kept unchanged in `earlier/`" ... "They are archived unchanged and are not shipped with this slice")
and rests its verdict on the cmpkit 4bbd3a74be89 outputs. So the earlier/ rows were not checked row by row.
Note: RECORD.md says earlier/ is "not shipped with this slice", but the pack's MANIFEST.md lists all 159 earlier/ files and
they are in the pack tree.

Commands (cwd kitscan, PYTHONPATH=<path>):

    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan img/fuzz_grant.asan-ubsan.pin ___interceptor_malloc 0x530b0 img/fuzz_grant.asan-ubsan > uci-b-alloc/paircl-acc-malloc.txt
    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan img/fuzz_grant.asan-ubsan.pin ___interceptor_free 0x52ee0 img/fuzz_grant.asan-ubsan > uci-b-alloc/paircl-acc-free.txt
    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan img/fuzz_grant.asan-ubsan.pin __interceptor_trampoline_malloc 0x52edc img/fuzz_grant.asan-ubsan > uci-b-alloc/paircl-acc-tmalloc.txt
    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan img/fuzz_grant.asan-ubsan.pin __interceptor_trampoline_free 0x52ed8 img/fuzz_grant.asan-ubsan > uci-b-alloc/paircl-acc-tfree.txt
    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan uci-b-alloc/planted/grantB-S-call.elf ___interceptor_malloc 0x530b0 uci-b-alloc/planted/grantB-U-call.elf > uci-b-alloc/paircl-acc-ctl-call.txt
    python3 tools/paircl_acc.py oldkit4bbd img/fuzz_uci.asan-ubsan uci-b-alloc/planted/grantB-S-rodata.elf ___interceptor_malloc 0x530b0 uci-b-alloc/planted/grantB-U-rodata.elf > uci-b-alloc/paircl-acc-ctl-rodata.txt
    python3 tools/paircl_pairs.py oldkit4bbd img/fuzz_uci.asan-ubsan uci-b-alloc/planted/grantB-S-call.elf ___interceptor_malloc 0x530b0 uci-b-alloc/planted/grantB-U-call.elf > uci-b-alloc/paircl-pairs-ctl-call.tsv
    python3 tools/paircl_pairs.py oldkit4bbd img/fuzz_uci.asan-ubsan uci-b-alloc/planted/grantB-S-rodata.elf ___interceptor_malloc 0x530b0 uci-b-alloc/planted/grantB-U-rodata.elf > uci-b-alloc/paircl-pairs-ctl-rodata.tsv
    planted copies: copy of the pin / twin with bytes ef f0 9d cd at file offset 0x421e0 (call) or 93 8a 05 46 at 0x850cc (rodata), as run.sh
    call sites, STT_FILE, line attribution and the MATCH test: the session's Python over these files (ambig-settle.tsv columns)
