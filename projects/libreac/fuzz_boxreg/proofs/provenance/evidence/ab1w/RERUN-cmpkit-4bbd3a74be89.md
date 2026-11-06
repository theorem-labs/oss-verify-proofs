# ab1w code comparison (NOTES.md lines 40-44), re-run on the comparison kits

`NOTES.md` lines 40-44 gave the instruction-compare result of the 518 kept rows from the `port_verdict` column of the
function-pairing table: a mnemonic + register compare with every immediate masked. That compare also masks the
pc-relative fields, so it cannot see a re-pointed target, and it compared only the rows its pairing gave a same-size
target. This record re-runs the comparison for every kept row on the comparison kits, settles every target the kits
leave open by a named measurement, and lists the rows that are not compared, with the reason for each.

## Result

Every kept row is compared: the cgif row `[tfib_A, tfib_E)` of `proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v` in
cgif_file_fuzzer.asan against its row in `proofs/libreac/fuzz_boxreg/lib/A/AB1w.v` in fuzz_boxreg.asan, as byte ranges,
by address. A merged cgif row is compared against the two boxreg rows that split it, which are adjacent (one byte
range of the same length). The two size-0 asm rows (`start`, `set_thread_area`) are compared over their row ranges.

| | rows |
|---|---|
| kept rows (cgif row with a boxreg row; `NOTES.md` "Counts") | 518 |
| compared | 518 (513 rows 1:1, 5 merged rows against their 2 split rows) |
| NOT COMPARED among the kept rows | 0 |
| cgif rows with no boxreg row: NOT COMPARED (listed below with the reason) | 27 |
| boxreg row with no cgif row (`asan_stack_malloc_3`, a new instance): not compared, no cgif twin | 1 |

The counts below count compared rows only; a row that was not compared is in no count.

| cmpkit 4bbd3a74be89 (`strictcmp2.tcmp`, by address) | rows | settled verdict |
|---|---|---|
| `EQUAL`, 0 target differences | 141 | same code |
| `EQUAL-mod-pcrel`, 0 target differences | 356 | same code past pc-relative fields |
| `EQUAL-mod-pcrel` with fail-closed target differences | 21 (23 targets) | same code past pc-relative fields: every target settled by a named measurement (section "The rows the kit does not certify") |
| REAL word difference, length difference, unmeasured word | 0 | |

On cmpkit 86da41d3ef68 (`strictcmp3.tcmp`, by address, combined verdict): `EQUAL` 141, `EQUAL-mod-pcrel` 335,
`DIFFERENT-target` 42. The `DIFFERENT-target` rows are the same 21 rows and 23 targets, and 39 `lui-in-section`
targets in 23 rows; strictcmp3 also accepts 20 `lui` values in 18 rows only by its fail-open `lui-const (dataflow)`
label. All 59 `lui` values are traced in both images: 57 certified, 2 NOT CERTIFIED: REAL 0 (`InitializeShadowMemory` +0x1b0, `SizeClassAllocator64_PopulateFreeArray` +0xb0). No value is a
different number in the two images and no use differs between them; no row moves toward a real difference.
The kit's `EQUAL` verdicts are audited independently against the fail-open shapes (a)-(h) of cmpkit 86da41d3ef68
(section "Address-shape audit against cmpkit 86da41d3ef68's fail-open list (a)-(h)"): every static base and every
jump target of the 518 rows names the same symbol + offset in both images (7466 bases, 8502 targets; 0 DIFFERENT,
0 UNRESOLVED).

## What the verdicts rest on

The old commands in `NOTES.md` named elfdis.py (sha256 ed45f6bea2e5, `217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py`).
That tool is fail-open on the comparison-tool registry's false-equal plant set (23 plants, manifest sha256
`31c4dfb2053aacc591d627bcc3a94a97415cb0b58778172df0bef374ce10b2b2`): it printed EQUAL on 23 of the 23 plants and caught none; its
`--diff` verdict compares mnemonic sequences only. elfdis is not cited as evidence anywhere in this record. Every
verdict here rests on the independent decoder `rvdis.py` (sha256 `dc4e137a1a22b4307d370543b8991b68dd4adc77c1743421e12a950978e3d565`) and the
cmpkit 86da41d3ef68 `strictcmp3` runs shown, row by row; the cmpkit 4bbd3a74be89 `strictcmp2` result is shown beside
each row. `strictcmp3` gives the result shown for each row.

## Line 127 (split boundary) and line 228 (16 `j` stubs), re-run on cmpkit 86da41d3ef68

`NOTES.md` line 127 compares cgif `0x80418+0x30` with boxreg `oft_exit_guard`, and lines 228-236 pair 16 one-instruction
`j` stubs by jump target; both rested on elfdis. Both are re-run here by address and by name (`strictcmp3.py cmp`, every
name 1 copy in each image), with the 86da `jtcheck.py`, planted re-points (file copies of fuzz_boxreg.asan) and their
baselines.

| claim | cmpkit 86da41d3ef68 (`strictcmp3`) | cmpkit 4bbd3a74be89 (`strictcmp2`) | jtcheck (86da) | controls |
|---|---|---|---|---|
| line 127: cgif 0x80418+0x30 vs `oft_exit_guard` 0x7fed4+0x30 | by address `EQUAL-mod-pcrel`, 0 target differences (pcrel 6, real 0, unmeasured 0); by name `EQUAL-mod-pcrel`, 0 target differences | `EQUAL-mod-pcrel`, 0 target differences | target differs 0, target unmeasured 0 | P127-jal CAUGHT; P127-lbu CAUGHT; baseline clean |

| stub (cgif row) | cgif / boxreg | name | `strictcmp3` by address | copies | jump target (cgif / boxreg) |
|---|---|---|---|---|---|
| `thunk_417cc` | 0x41940 / 0x41440 | `__interceptor_trampoline_strerror` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_strerror 1 / 1, __wrap_strerror 1 / 1 | ___interceptor_strerror/__interceptor_strerror+0x0 / ___interceptor_strerror/__interceptor_strerror+0x0 |
| `thunk_417dc` | 0x41954 / 0x41450 | `__interceptor_trampoline_fflush` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_fflush 1 / 1, __wrap_fflush 1 / 1 | ___interceptor_fflush/__interceptor_fflush+0x0 / ___interceptor_fflush/__interceptor_fflush+0x0 |
| `thunk_417e4` | 0x4195c / 0x41454 | `__interceptor_trampoline_sem_init` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sem_init 1 / 1, __wrap_sem_init 1 / 1 | ___interceptor_sem_init/__interceptor_sem_init+0x0 / ___interceptor_sem_init/__interceptor_sem_init+0x0 |
| `thunk_417e8` | 0x41960 / 0x41458 | `__interceptor_trampoline_sem_destroy` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sem_destroy 1 / 1, __wrap_sem_destroy 1 / 1 | ___interceptor_sem_destroy/__interceptor_sem_destroy+0x0 / ___interceptor_sem_destroy/__interceptor_sem_destroy+0x0 |
| `thunk_417ec` | 0x41964 / 0x4145c | `__interceptor_trampoline_sem_wait` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sem_wait 1 / 1, __wrap_sem_wait 1 / 1 | ___interceptor_sem_wait/__interceptor_sem_wait+0x0 / ___interceptor_sem_wait/__interceptor_sem_wait+0x0 |
| `thunk_417f0` | 0x41968 / 0x41460 | `__interceptor_trampoline_sem_trywait` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sem_trywait 1 / 1, __wrap_sem_trywait 1 / 1 | ___interceptor_sem_trywait/__interceptor_sem_trywait+0x0 / ___interceptor_sem_trywait/__interceptor_sem_trywait+0x0 |
| `thunk_417f8` | 0x41970 / 0x41468 | `__interceptor_trampoline_sem_post` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sem_post 1 / 1, __wrap_sem_post 1 / 1 | ___interceptor_sem_post/__interceptor_sem_post+0x0 / ___interceptor_sem_post/__interceptor_sem_post+0x0 |
| `thunk_4180c` | 0x41984 / 0x4147c | `__interceptor_trampoline_sigaction` | EQUAL-mod-pcrel N=0 | __interceptor_trampoline_sigaction 1 / 1, __wrap_sigaction 1 / 1 | ___interceptor_sigaction/__interceptor_sigaction+0x0 / ___interceptor_sigaction/__interceptor_sigaction+0x0 |
| `thunk_59674` | 0x59854 / 0x59310 | `__asan_set_death_callback` | EQUAL N=0 | __asan_set_death_callback 1 / 1 | _ZN11__sanitizer18SetUserDieCallbackEPFvvE+0x0 / _ZN11__sanitizer18SetUserDieCallbackEPFvvE+0x0 |
| `thunk_653ec` | 0x655d4 / 0x65090 | `_ZN11__sanitizer23InitializePlatformEarlyEv` | EQUAL N=0 | _ZN11__sanitizer23InitializePlatformEarlyEv 1 / 1 | _ZN11__sanitizer11InitTlsSizeEv+0x0 / _ZN11__sanitizer11InitTlsSizeEv+0x0 |
| `thunk_66008` | 0x661f0 / 0x65cac | `_ZN11__sanitizer9CloseFileEi` | EQUAL N=0 | _ZN11__sanitizer9CloseFileEi 1 / 1 | _ZN11__sanitizer14internal_closeEi+0x0 / _ZN11__sanitizer14internal_closeEi+0x0 |
| `thunk_6d37c` | 0x6d564 / 0x6d020 | `_ZN11__sanitizer13GetThreadSelfEv` | EQUAL-mod-pcrel N=0 | _ZN11__sanitizer13GetThreadSelfEv 1 / 1 | __pthread_self_internal/pthread_self/thrd_current+0x0 / __pthread_self_internal/pthread_self/thrd_current+0x0 |
| `thunk_762d8` | 0x765fc / 0x760b8 | `_ZN11__sanitizer17SymbolizerProcess7GetEnvPEv` | EQUAL N=0 | _ZN11__sanitizer17SymbolizerProcess7GetEnvPEv 1 / 1 | _ZN11__sanitizer10GetEnvironEv+0x0 / _ZN11__sanitizer10GetEnvironEv+0x0 |
| `thunk_77ab0` | 0x77dd4 / 0x77890 | `_ZN11__sanitizer18InternalSymbolizer5FlushEv` | EQUAL N=0 | _ZN11__sanitizer18InternalSymbolizer5FlushEv 1 / 1 | _ZN11__sanitizer18InternalSymbolizer5FlushEv+0x0 / _ZN11__sanitizer18InternalSymbolizer5FlushEv+0x0 |
| `thunk_7b6f8` | 0x7ba28 / 0x7b4e4 | `_ZN6__lsan26DoRecoverableLeakCheckVoidEv` | EQUAL N=0 | _ZN6__lsan26DoRecoverableLeakCheckVoidEv 1 / 1 | _ZN6__lsanL22DoRecoverableLeakCheckEv+0x0 / _ZN6__lsanL22DoRecoverableLeakCheckEv+0x0 |
| `thunk_931e0` | 0x8dd54 / 0x890bc | `__lctrans` | EQUAL N=0 | __lctrans 1 / 1 | __lctrans_impl+0x0 / __lctrans_impl+0x0 |

By name (`strictcmp3.py cmp`): 16 of 16 `EQUAL` / `EQUAL-mod-pcrel` with 0 target differences. 86da `jtcheck.py`: 16 of 16 with "target differs 0", "target unmeasured 0". The 4bbd `strictcmp2` result of the same 16 is 16 of 16 with 0 target differences.
- P228-semwait: DIFFERENT-target N=1 [('0x0', '___interceptor_sem_wait/__interceptor_sem_wait+0x0', '___interceptor_sem_trywait/__interceptor_sem_trywait+0x0', 'names')] -> CAUGHT; baseline EQUAL-mod-pcrel N=0
- P228-flush: DIFFERENT-target N=1 [('0x0', '_ZN11__sanitizer18InternalSymbolizer5FlushEv+0x0', '_ZN11__sanitizer18InternalSymbolizer8DemangleEPKc+0x0', 'names')] -> CAUGHT; baseline EQUAL N=0
- P228-close4: DIFFERENT-target N=1 [('0x0', '_ZN11__sanitizer14internal_closeEi+0x0', '_ZN11__sanitizer14internal_closeEi+0x4', 'names')] -> CAUGHT; baseline EQUAL N=0

## Address-shape audit against cmpkit 86da41d3ef68's fail-open list (a)-(h)

cmpkit 86da41d3ef68's README lists the shapes (a)-(h) in which a static address can reach a load / store / jump base
without the kit seeing it (an immediate on a formed value, addi chains, logical / shift ops, a stack / FP / CSR round
trip, a table edge into a shared arm, a callee, `c.lui`, an address built without lui / auipc). For those shapes the
kit's `EQUAL` alone is not evidence. An independent audit checked every row of both comparisons against all eight
shapes with its own RV64GC decoder and dataflow (not the kit, not `rvdis.py`, not elfdis): every load / store / jalr /
AMO / LR / SC base that an address-capable value reaches, and every jal / branch target, must name the same symbol +
offset in both images.

The independent audit's report: `REPORT.md`, sha256 `5b7718b7ba250ed19854bb610e3f453634f3e28cee8cb3347f1115149123644e`, git blob `fa8129f4b97fd63d3f505f2d8ef58de86f7e0646`.
Its tool list: `tools.sha256`, sha256 `be28c70da3655a290f48848a9e8803089bec71eff103683b10aca37ff2ca584b`, git blob `c53738b442e987267865624853df60e72d2755a0`
(13 tools, Python 3.12.3, pyelftools 0.33 for ELF parsing only); its output list: `outputs.sha256`, sha256
`6096615e63827078e189699e8a577bccd21ed7b7346b8cb179d7d5dbdf5e1625`, git blob `3d07cffe7447da1b7edb251f9f6fe1e2684db94c` (165 files).

| audit tool | sha256 |
|---|---|
| `ab1w.py` | `3524f9886ddfcb0742c5ef8550e6de5f3933f9567f12d1e5c1057bb2d892e2f6` |
| `audit.py` | `d995bec8505bb53dd0b069294fc70cde20bd46d1d39fbeed4519dbc469267c86` |
| `flow.py` | `1dd311c3eedf76ae36ed7dae4a454d9ad3ee431ab70debceb9a9d30481b84e64` |
| `img.py` | `c010fd6d145005fdadecdeff60460d63e626b0c558ae08290d34ad47ca79aa41` |
| `mkreport.py` | `0d669efa631d7727d63f01242ac4428fac7e1e792d99dedfbe282cdf2c43feeb` |
| `noret.py` | `b6cba001ad55d129c894c35e1659a174c185b76ff7bad66c05a7f73a86bf2718` |
| `plants.py` | `fbc7d8b4333c68f37655748b1df1e1097d6f528aedd177c1ed6aac094f5f5423` |
| `rdtrace.py` | `9aec0a7b83eb5d330a08041a228bbae6b5188eb18c43e4fff27f21ae2dbe931c` |
| `rv.py` | `f43ab8de6d44ab636a082205d5dcd45986426359a80da702073242c665527cdf` |
| `scope2.py` | `2b56d0cf3f23dff9e76a11b6422d7fc1a3e26a1c4de4a611875e093f9b774035` |
| `validate.py` | `682a082803016d282b097ca1ef1dbf2c8427317edcaf0f30569675b7dfaae988` |
| `xfun.py` | `6702871f0e2011609ace58c08175302dad34fc7ab6b8c51eb97788493a08c064` |
| `run_all.sh` | `93ed39906bee515fa1d55a402d929a5d2e1518aacbe0ff3a75e0287478dbb30f` |

Per-row results, committed as provenance inputs (byte-identical to the audit's tables): `SHAPE-AUDIT-rows.tsv` in this
directory (518 rows, sha256 `b428ae5878ec7d89a77bd5a4a7a4277bded6886bb6d1a8cc8c57296cff89cc86`) and `../ab1wB/SHAPE-AUDIT-rows.tsv` (524 rows, sha256
`25ab32cb84c920afce3e4816c93a49752466d65b626537ac11ad45d7f2804c9c`). Columns: row, A and B start, words, accesses, static_bases, EQUAL, DIFFERENT,
UNRESOLVED, unreached_words, tables, ft_arms, notes. In each table the row `target_run` counts one static base more
than its verdicts: its call +0xc8 to `LLVMFuzzerTestOneInput`, the fuzz target, which is not a row and is not compared
(by design; its static argument a0 is `oft_aligned_copy.empty#0+0x0` or a dynamic buffer in all three images).

### Result

0 DIFFERENT and 0 UNRESOLVED in all four comparisons; 0 unreached words; 0 unresolved indirect jumps.

| comparison | rows | words / image | accesses | static bases (in-row + cross-function) | EQUAL | DIFFERENT | UNRESOLVED | jump targets EQUAL |
|---|---|---|---|---|---|---|---|---|
| ab1wB: fuzz_boxreg.asan vs fuzz_boxreg.asan-ubsan (`../ab1wB/RERUN-cmpkit-4bbd3a74be89.md`) | 524 | 47319 | 12721 | 7462 (4316 + 3146) | 7462 | 0 | 0 | 8519 / 8519 |
| ab1w (this record): cgif_file_fuzzer.asan vs fuzz_boxreg.asan | 518 | 47212 | 12722 | 7466 (4322 + 3144) | 7466 | 0 | 0 | 8502 / 8502 |
| line 127: cgif 0x80418+0x30 vs boxreg `oft_exit_guard` 0x7fed4+0x30 | 1 | 12 | 5 | 3 (+ 2 call arguments) | 3 | 0 | 0 | 3 / 3 |
| line 228: the 16 one-word `j` stubs | 16 | 1 each | - | - | - | - | - | 16 / 16 same target symbol + offset |

Line 127: 12 / 12 words with opcode and registers equal, 0 REAL; the 3 bases and 3 targets name the same symbol +
offset (`oft_in_callback`, the `.got` cell of `stdout` and its content `__stdout_FILE`, `__interceptor_trampoline_fflush`,
`__interceptor_trampoline__exit`). Line 228: all 16 stubs have the same target symbol + offset; 13 pair by callee, and
7 are byte-identical, among them Flush (`j .`), DoRecoverableLeakCheckVoid and __lctrans (`j .+4`). The 42 ab1w rows
that `strictcmp3` calls `DIFFERENT-target` are among the 518 and give no difference here. For the ab1w pair (two
programs) unnamed read-only data is compared by content: 840 `.got` cells by the name of their content, 717 C strings,
110 data loads by their bytes, 11 De Bruijn reads by the 64 / 32 bytes their index reaches, 10 table reads by their
entries, 5 jump tables by their targets.

"Kit-only" below: no lui root of the base is among the lui values a record traces by hand (55 in
`../ab1wB/RERUN-cmpkit-4bbd3a74be89.md`, 59 here); for those bases the kit's `EQUAL` was the only evidence before the
audit. A base can count under several shapes.

**ab1wB (524 rows), per shape:**

| shape | how this method covers it | static bases in-row | of which kit-only | cross-function (f) | DIFFERENT | UNRESOLVED |
|---|---|---|---|---|---|---|
| (a) load / store / jalr / AMO immediate on a formed value (V+imm) | combined target = value + imm, named | 1274 | 1258 | 1349 | 0 | 0 |
| (b) addi / addiw chain | each addi / addiw folded exactly | 192 | 184 | 0 | 0 | 0 |
| (c) ori / xori / andi / slli / srli / sll / or / xor / and / add-x0 on a static value | constant ops computed exactly; a non-linear op keeps its static operand | 55 | 40 | 0 | 0 | 0 |
| (d) stack spill + reload, FP move, CSR round trip | sp-relative slots, FP registers and CSRs carry the value | 41 | 34 | 0 | 0 | 0 |
| (e) jump-table edge into an arm that fall-through also reaches | tables decoded with their bound; every target is an edge; unreached words entered with the dispatch state | 1 | 1 | 0 | 0 | 0 |
| (f) in-function callee (caller a0-a7 in, a0/a1 back) | in-row call strings; plus callee summaries 3 calls deep for calls out of the row | 16 | 16 | 3146 | 0 | 0 |
| (g) c.lui | RVC decoded; c.lui is a lui root | 0 | 0 | 0 | 0 | 0 |
| (h) address built without lui / auipc | li roots; a constant in a section (or + imm) is static | 0 | 0 | 0 | 0 | 0 |

**ab1w (518 rows, cgif vs boxreg), per shape:**

| shape | in-row | kit-only | cross-function | DIFFERENT | UNRESOLVED |
|---|---|---|---|---|---|
| (a) | 1274 | 1258 | 1348 | 0 | 0 |
| (b) | 192 | 184 | 0 | 0 | 0 |
| (c) | 55 | 40 | 0 | 0 | 0 |
| (d) | 42 | 35 | 0 | 0 | 0 |
| (e) | 1 | 1 | 0 | 0 | 0 |
| (f) | 17 | 17 | 3144 | 0 | 0 |
| (g) | 0 | 0 | 0 | 0 | 0 |
| (h) | 0 | 0 | 0 | 0 | 0 |

**The five `Allocator::Allocate` words that the fail-open list names for shape (a)** (in fuzz_boxreg; the only caller,
`asan_malloc` +0x28, passes `this` = `_ZN6__asanL8instanceE` in both images):

| word | instruction | base on every path (both images, `rdtrace.py`) | combined target via the caller (`asan_malloc` +0x28, both images) |
|---|---|---|---|
| +0x16c | `lh a0,1577(s10)` | s10 = +0x8c `addi s10,s6,2047`, s6 = +0x4c `mv s6,a0` (a0 = `this`) | `_ZN6__asanL8instanceE#0+0xe28` |
| +0x188 | `lh a0,1579(s10)` | same | `instance#0+0xe2a` |
| +0x21c | `ld a0,1569(s10)` | same | `instance#0+0xe20` |
| +0x25c | `ld a2,1569(s10)` | same | `instance#0+0xe20` |
| +0x368 | `sb zero,984(s6)` | s6 = +0x4c `mv s6,a0` | `instance#0+0x3d8` |

No lui and no constant root reaches these bases on any executable path: the base is `this + 0x7ff + imm`.

### Method (summary)

- Decoder: written from the RISC-V encodings; RV64I, M, A, F, D, Zicsr, Zifencei and all of C. Zba / Zbb / Zbs / V / Q
  words decode as `ext` (a row holding one would be UNRESOLVED; none does).
- Dataflow, per row and per image: every register (x and f) holds `constant + sum(k * atom)` with root markers and
  shape tags; roots are auipc, lui, c.lui, li, gp, read-only cell contents, bounded table entries, in-row return
  addresses and static callee returns. Both edges of every branch; integer ops folded exactly on constants; sp-relative
  stack slots, FP moves and CSR writes carry values; jump tables read entry by entry under their bound; in-row calls
  followed with a call string; callees measured to not return have no successor; words no entry path reaches are
  analysed with every dispatch state (none remained unreached).
- A base is static if an address-kind root reaches it, or a lui / c.lui / li root whose value or the base's constant
  part lies in an image section. The pair is EQUAL iff the whole canonical text (names, offsets, atoms, phi seeds,
  table entries) is the same in both images. Cross-function (f): a static value passed in a0-a7 to a function outside
  the row that uses it as a base, followed up to 3 calls deep.

### Decoder validation

GNU objdump 2.42 (`riscv64-alpine-linux-musl-objdump -d -M no-aliases,numeric`, from the toolchain image
`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b`),
compared field by field with the audit's decoder:

| set | compared | equal | not equal |
|---|---|---|---|
| every `.text` word of fuzz_boxreg.asan | 106097 | 106097 | 0 |
| every `.text` word of fuzz_boxreg.asan-ubsan | 106338 | 106338 | 0 |
| every 2-byte parcel (49152 values, quadrants 0-2) | 46745 decoded by objdump (+2407 both refuse) | 46743 | 2: 0x0000 (c.unimp) and 0x6101 (c.addi16sp with imm 0, reserved): the audit's decoder refuses both |
| 400000 random 32-bit words over every major opcode (seed 20261030) | 211130 decoded by both (+183326 both refuse) | 211130 | 5544 objdump refuses, the audit's decoder decodes: fence / fence.i with non-zero reserved fields (the spec says to ignore them) and fcvt.d.s / .d.w / .d.wu with rm != 0 (valid encodings) |

### Controls

Planted copies compared with the same audit as the rows (host row `Allocator_Allocate`; synthetic plants write the same
words in both images at the row start and `ebreak` to the row end, then change one constant in one image). Every plant
is caught at the planted access (exactly 1 DIFFERENT); every baseline has 0.

| id | shape | plant (planted change) | baseline DIFFERENT | planted DIFFERENT | caught as (A'' vs B') |
|---|---|---|---|---|---|
| P-a-real | (a) | real code: Allocator_Allocate +0x530 `lbu rd,85(rs)` -> 120 (word 0555c583 -> 0785c583) | 0 | 1 | `asan_flags_dont_use_directly#0+0x55` -> `allow_after_dynamic_init#0+0x0` |
| P-a-M01 | (a) | `lui t0,0x10; add t0,t0,a0; ld t1,0x398 (-> 0x3a0)(t0)` | 0 | 1 | `OFF 0x103a0 + E10` / `OFF 0x10398 + E10` |
| P-b-C1 | (b) | `lui t0,0x10; addi t0,t0,0x298; addi t0,t0,0x100 (-> 0x108); ld t1,0(t0)` | 0 | 1 | `§.rodata+0xc0` / `§.rodata+0xb8` |
| P-b-C2 | (b) | the same with addiw | 0 | 1 | `§.rodata+0xc0` / `§.rodata+0xb8` |
| P-c-C3 | (c) | `lui t0,0x10; ori t0,t0,0x398 (-> 0x3a0); ld t1,0(t0)` | 0 | 1 | `§.rodata+0xc0` / `§.rodata+0xb8` |
| P-c-C4 | (c) | `lui t0,0x1; slli t0,t0,4 (-> 5); addi t0,t0,0x398; ld t1,0(t0)` | 0 | 1 | `~__global_pointer$#0+0xfb98` / `§.rodata+0xb8` |
| P-d-M03 | (d) | `lui t0,0x10 (-> 0x11); sd t0,0(sp); ld t1,0(sp); ld t2,0x398(t1)` | 0 | 1 | `~__global_pointer$#0+0xb98` / `§.rodata+0xb8` |
| P-d-M07 | (d) | `lui t0,0x10 (-> 0x11); fmv.d.x ft0,t0; fmv.x.d t1,ft0; ld t2,0x398(t1)` | 0 | 1 | same |
| P-d-M08 | (d) | `lui t0,0x10 (-> 0x11); csrw sscratch,t0; csrr t1,sscratch; ld t2,0x398(t1)` | 0 | 1 | same |
| P-e-FT1 | (e) | `lui t0,0x10 (-> 0x11); jr a1; li t0,0; ld t1,0x398(t0)` (arm reached by the jr and by fall-through) | 0 | 1 | at +0xc in the dispatch context: seed `~__global_pointer$#0+0xb98` / `§.rodata+0xb8` |
| P-f-CA1 | (f) | `lui a0,0x10 (-> 0x11); jal ra,+0x40`; callee +0x40 `ld t1,0x398(a0); ret` | 0 | 1 | at +0x40 in call string [4] |
| P-g-M06b | (g) | `c.lui t0,0x10 (-> 0x11); c.nop; ld t1,0x398(t0)` (62c1 -> 62c5) | 0 | 1 | `~__global_pointer$#0+0xb98` / `§.rodata+0xb8` |
| P-h-NL1 | (h) | `addi t0,zero,1 (-> 2); slli t0,t0,16; ld t1,0x398(t0)` | 0 | 1 | `~__global_pointer$#0+0xfb98` / `§.rodata+0xb8` |

### Not verified by the audit

- Memory other than the stack frame is not modelled: a static address stored to a global or heap object and loaded
  back is a dynamic value after the load. No shape of the fail-open list needs this, but such a path is not traced.
- Calls: the in-row call string is at most 4 deep and does not re-enter a call site already on it; the
  cross-function step follows direct `jal` callees only, 3 calls deep; an indirect call's callee is not followed.
- Stack slots whose address may have escaped are dropped at calls and unknown stores; other threads are not modelled.
- Table bounds come only from `bltu` / `bgeu` against a constant; all 10 tables had one (an unbounded table would be
  UNRESOLVED; none).
- The 17 indirect tail calls are classified by rule (sp equals sp at entry and the target is not a table read).
- The noreturn set (25 functions per image) is measured on the binary; `ecall` with a7 = 93 / 94 is taken as not
  returning.
- The callee of `target_run` +0xc8 (`LLVMFuzzerTestOneInput`) is not compared.
- ab1w content naming: a C string is compared up to its NUL plus the bytes the access reads; a pointer passed to a
  callee that reads past the NUL is compared only through the callee's own recorded uses.
- Zba / Zbb / V words are decoded for the census only; none is in a row, so their dataflow is not exercised.
- The audit did not re-run the kit and did not re-check the records' other claims (lui classes, citations, C-string
  audit).

## The ab1wB generator scripts and the values of lib/A/AB1w.v and lib/B/AB1w.v

`../ab1wB/NOTES.md` (Commands) regenerates `lib/B/AB1w.v` with the scripts in `../ab1wB/work/` (commit
`0ec8bd3fae71ca36acb3467a84b0dd52f3cf3893`; `check.py` differs from that commit's only in its docstring). A byte-for-byte
regeneration shows only that the generator is deterministic, so the scripts' use of elfdis and the values themselves are checked here.

**How the scripts use elfdis** (elfdis.py = `217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py`):

- elfdis.py:81-84: `disasm()` returns capstone's full `(address, mnemonic, op_str)` for every instruction; `func()`
  (:87-91) calls it. elfdis.py:107-109: the operand drop (`ma = [m for _, m, _ in ia]`) and the mnemonic-only compare
  are only inside `main()`'s `--diff` branch (:100-120), downstream of every script read below.
- No script calls `--diff`, `main()` or `difflib`. The four scripts that import elfdis use it in decode mode only:
  `interior.py` :9 import, :16 `elfdis.load`, :38-39 and :50 `elfdis.disasm`, :43 compares mnemonics only, :51 reads
  op_str to print the MemToShadow literals (output only); `map.py` :11 import, :22 `elfdis.load`, :33 `elfdis.disasm`,
  :29 `shape()` reads the registers from op_str for `cmp_code()` (:32-38); `resolve.py` :9 import, :21 `elfdis.load`,
  :34 `elfdis.disasm`, :26 `shape()` (registers from op_str) and :30 `full()` (the whole op_str); `tail.py` :13 import,
  :23 `elfdis.load` only (the result is not used further).
- `map.py`'s `cmp_code()` (:32-38) is defined but never called, and the `rows.json` that `map.py` writes is read by no
  script. The pairing that `gen.py` uses is `resolve.py`'s (`resolved.json`): a row's symbol name, or, where the name
  has several copies, the copy of the same ordinal (`resolve.py`:80-90; 4 rows, checked by address below).
- `resolve.py`'s `SAME` / `IMM` / `SHAPE` verdicts (`resolved.json`) are superseded by the `strictcmp3` re-run in
  `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md` and are not evidence.

**The values, checked independently** (`bcheck.py`, pyelftools and `rvdis.py`; `lib/A/AB1w.v` against fuzz_boxreg.asan,
`lib/B/AB1w.v` against the fuzz_boxreg.asan-ubsan twin, which `drvcmp.py twins` proves equal to the pin in every
loadable byte except the ELF header and `.note.gnu.build-id`):

| check | file / image | checked | equal | wrong |
|---|---|---|---|---|
| (i) every `tfib_A_*` / `tfib_E_*` = one FUNC symbol's st_value / st_value + st_size (the 2 size-0 asm rows by their rule) | lib/A | 524 | 524 | 0 |
| (i) every `tfib_A_*` / `tfib_E_*` = one FUNC symbol's st_value / st_value + st_size (the 2 size-0 asm rows by their rule) | lib/B | 524 | 524 | 0 |
| (ii) every `tfib_D_*` / `tfib_at_*` re-read by its stated meaning (symbol, `.got` slot content, section start, ELF header field, instruction at function + offset, constant built in the code) | lib/A | 51 | 51 | 0 |
| (ii) every `tfib_D_*` / `tfib_at_*` re-read by its stated meaning (symbol, `.got` slot content, section start, ELF header field, instruction at function + offset, constant built in the code) | lib/B | 51 | 51 | 0 |
| the header constants (`tfib_*_lo` / `_hi`, `tfib_entry`, `tfib_gp`) = section table / e_entry / `__global_pointer$` | lib/A | 26 | 26 | 0 |
| the header constants (`tfib_*_lo` / `_hi`, `tfib_entry`, `tfib_gp`) = section table / e_entry / `__global_pointer$` | lib/B | 26 | 26 | 0 |
| (iii) the rows paired where a name has several copies (MemToShadow, 5 copies), re-checked by address: the same instructions, every pc-relative target the same symbol + offset | lib/A vs lib/B | 4 | 4 | 0 |
| (iii) the rows paired where a name has several copies (MemToShadow, 5 copies), re-checked by address: the same instructions, every pc-relative target the same symbol + offset | cgif vs lib/A | 4 | 4 | 0 |

Controls, one planted cell per check (a copy of `lib/B/AB1w.v` with one value off by 4), each caught:

- Pv-i (i): tfib_E_ReportGenericError 0x57a6c -> 0x57a70 in a copy of lib/B/AB1w.v: CAUGHT: ReportGenericError WRONG no FUNC symbol 0x571b0..0x57a70
- Pv-ii (ii): tfib_D_GOT_flags 0x992d0 -> 0x992d4 in a copy of lib/B/AB1w.v: CAUGHT: tfib_D_GOT_flags WRONG .got cells holding _ZN6__asan28asan_flags_dont_use_directlyE (0x9ebb8): ['0x992d0']
- Pv-iv (iv): tfib_got_lo 0x99278 -> 0x9927c in a copy of lib/B/AB1w.v: CAUGHT: tfib_got_lo WRONG .got lo 0x99278
- Pv-iii (iii): tfib_A_MemToShadow_checked 0x537e8 -> 0x537ec in a copy of lib/B/AB1w.v: CAUGHT: MemToShadow_checked WRONG lengths 0x13c / 0x138
- Pv-iii-shift (iii, extra): tfib_A_ and tfib_E_MemToShadow_checked both +4 in a copy of lib/B/AB1w.v: CAUGHT: asan 0x53788 / asan-ubsan 0x537ec +0x13c: at +0x4: `ld a1,1840(a1)` / `ld a1,0(a1)`

Per value (`bcheck.py` output), the tail and header values of `lib/B/AB1w.v`:

| check | name | result | read in fuzz_boxreg.asan-ubsan |
|---|---|---|---|
| ii | `tfib_D_str_sealed` | OK | bytes b'<sealed>\x00' occur in .rodata at ['0x117fe'] |
| ii | `tfib_D_init_array_0_3` | OK | .init_array starts at 0x98d40 |
| ii | `tfib_D_fini_array_0_1` | OK | .fini_array starts at 0x98d60 |
| ii | `tfib_D_GOT_common_flags` | OK | .got cells holding _ZN11__sanitizer21common_flags_dont_useE (0x132ee8): ['0x992c8'] |
| ii | `tfib_D_GOT_flags` | OK | .got cells holding _ZN6__asan28asan_flags_dont_use_directlyE (0x9ebb8): ['0x992d0'] |
| ii | `tfib_D_GOT_asan_shadow_memory_dynamic_address` | OK | .got cells holding __asan_shadow_memory_dynamic_address (0xa13b8): ['0x992d8'] |
| ii | `tfib_D_GOT_kMidMemBeg` | OK | .got cells holding _ZN6__asan10kMidMemBegE (0xa20a8): ['0x992e0'] |
| ii | `tfib_D_GOT_kMidMemEnd` | OK | .got cells holding _ZN6__asan10kMidMemEndE (0xa20b0): ['0x992e8'] |
| ii | `tfib_D_GOT_kHighMemEnd` | OK | .got cells holding _ZN6__asan11kHighMemEndE (0xa20a0): ['0x992f0'] |
| ii | `tfib_D_GOT_replace_intrin_cached` | OK | .got cells holding _ZN6__asan21replace_intrin_cachedE (0xa2099): ['0x99e40'] |
| ii | `tfib_D_environ_musl` | OK | .got cells holding ___environ (0x5d4280): ['0x99f68'] |
| ii | `tfib_D_REAL_read` | OK | symbol [('_ZN14__interception9real_readE', '0x9b018')] |
| ii | `tfib_D_REAL_memcpy` | OK | symbol [('_ZN14__interception11real_memcpyE', '0x9b140')] |
| ii | `tfib_D_REAL_memset` | OK | symbol [('_ZN14__interception11real_memsetE', '0x9b148')] |
| ii | `tfib_D_asan_allocator_instance_asan_allocator_cpp_insta` | OK | symbol [('_ZN6__asanL8instanceE', '0x9dd58')] |
| ii | `tfib_D_asan_flags_Flags_struct_flags` | OK | symbol [('_ZN6__asan28asan_flags_dont_use_directlyE', '0x9ebb8')] |
| ii | `tfib_D_asan_shadow_memory_dynamic_address` | OK | symbol [('__asan_shadow_memory_dynamic_address', '0xa13b8')] |
| ii | `tfib_D_asan_inited` | OK | symbol [('_ZN6__asanL11asan_initedE', '0xa2098')] |
| ii | `tfib_D_replace_intrin_cached` | OK | symbol [('_ZN6__asan21replace_intrin_cachedE', '0xa2099')] |
| ii | `tfib_D_kHighMemEnd` | OK | symbol [('_ZN6__asan11kHighMemEndE', '0xa20a0')] |
| ii | `tfib_D_kMidMemBeg` | OK | symbol [('_ZN6__asan10kMidMemBegE', '0xa20a8')] |
| ii | `tfib_D_kMidMemEnd` | OK | symbol [('_ZN6__asan10kMidMemEndE', '0xa20b0')] |
| ii | `tfib_D_malloc_context_size` | OK | symbol [('_ZN6__asanL19malloc_context_sizeE', '0xa20bc')] |
| ii | `tfib_D_common_flags_dont_use_CommonFlags_struct_common` | OK | symbol [('_ZN11__sanitizer21common_flags_dont_useE', '0x132ee8')] |
| ii | `tfib_D_libc_progname_area_musl_bss` | OK | symbol [('__libc', '0x5f45e0')] |
| ii | `tfib_at_img_lo` | OK | img_lo = 0x10000 |
| ii | `tfib_at_img_hi` | OK | img_top = 0x5f6000 |
| ii | `tfib_at_n_res` | OK | n_load = 0x4 |
| ii | `tfib_at_shadow_off` | OK | built by _ZN6__asan22FindDynamicShadowStartEv+0xc `lui a0,0x7fff8`; _ZN6__asan19SealedReserveShadowEv+0x30 `lui s1,0x7fff8` |
| ii | `tfib_at_a_entry` | OK | e_entry = 0x2ffb8 |
| ii | `tfib_at_rw_lo` | OK | rw_lo = 0x9a000 |
| ii | `tfib_at_rw_len` | OK | rw_len = 0x55c000 |
| ii | `tfib_at_ph_addr_z` | OK | ph_addr = 0x10040 |
| ii | `tfib_at_ph_ent_z` | OK | e_phentsize = 0x38 |
| ii | `tfib_at_ph_num_z` | OK | e_phnum = 0xb |
| ii | `tfib_at_x_imemset` | OK | symbol [('__sanitizer_internal_memset', '0x63484')] |
| ii | `tfib_at_x_imemcpy` | OK | symbol [('__sanitizer_internal_memcpy', '0x63408')] |
| ii | `tfib_at_x_memset` | OK | symbol [('memset', '0x929ac')] |
| ii | `tfib_at_x_memcpy` | OK | symbol [('memcpy', '0x925a8')] |
| ii | `tfib_at_x_memiszero` | OK | symbol [('_ZN11__sanitizer11mem_is_zeroEPKcm', '0x639b4')] |
| ii | `tfib_at_x_istrncpy` | OK | symbol [('_ZN11__sanitizer16internal_strncpyEPcPKcm', '0x638b0')] |
| ii | `tfib_at_x_sealed` | OK | bytes b'<sealed>\x00' occur in .rodata at ['0x117fe'] |
| ii | `tfib_at_x_popfree` | OK | _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0x1bc = insn 111/220 `srli a4,a2,0x4` |
| ii | `tfib_at_x_sniff` | OK | not an address; 0 |
| ii | `tfib_at_sniff_tab` | OK | not an address; 0 |
| ii | `tfib_at_sniff_cell` | OK | not an address; 0 |
| ii | `tfib_at_x_envscan` | OK | __init_libc+0x38 = insn 14/139 `ld a0,0(s1)` |
| ii | `tfib_at_x_envscan_k` | OK | __init_libc+0x44 = insn 17/139 `auipc a0,0x56c` |
| ii | `tfib_at_x_pnscan` | OK | __init_libc+0xfc = insn 63/139 `lbu a3,-1(a1)` |
| ii | `tfib_at_x_pnscan_k` | OK | __init_libc+0x108 = insn 66/139 `addi a0,sp,48` |
| ii | `tfib_at_stops_more` | OK | _ZN11__sanitizer29SealedHangOnAllocationFailureEv+0x24 = insn 9/14 `j 0x34018`; _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm+0x190 = insn 100/121 `j 0x3563c`; _ZN6__asan12PoisonShadowEmmh+0x4a4 = insn 297/319 `j 0x53790`; _ZN6__asan19SealedReserveShadowEv+0x1b0 = insn 108/120 `j 0x59b48`; _ZN6__asan19SealedReserveShadowEv+0x1c4 = insn 113/120 `j 0x59b5c`; _ZN6__asan19SealedReserveShadowEv+0x1d8 = insn 118/120 `j 0x59b70`; _ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib+0x30 = insn 12/54 `j 0x5f500`; _ZN11__sanitizer25ReportMunmapFailureAndDieEPvmib+0x28 = insn 10/39 `j 0x5f5d0`; _ZN11__sanitizer16MapDynamicShadowEmmmRmm+0x158 = insn 86/147 `j 0x6cafc`; _ZN11__sanitizer18MmapFixedNoReserveEmmPKc+0xc4 = insn 49/76 `j 0x6da08`; _ZN11__sanitizer20ReservedAddressRange4InitEmPKcm+0xc4 = insn 49/51 `j 0x6db98`; _ZN11__sanitizer18InternalSymbolizer5FlushEv+0x0 = insn 0/1 `j 0x778f0` |
| iv | `tfib_rodata_lo` | OK | .rodata lo 0x102e0 |
| iv | `tfib_rodata_hi` | OK | .rodata hi 0x2268c |
| iv | `tfib_text_lo` | OK | .text lo 0x2ffb8 |
| iv | `tfib_text_hi` | OK | .tbss start 0x97d40 (the convention; .text ends 0x97d40) |
| iv | `tfib_init_array_lo` | OK | .init_array lo 0x98d40 |
| iv | `tfib_init_array_hi` | OK | .init_array hi 0x98d60 |
| iv | `tfib_fini_array_lo` | OK | .fini_array lo 0x98d60 |
| iv | `tfib_fini_array_hi` | OK | .fini_array hi 0x98d70 |
| iv | `tfib_preinit_array_lo` | OK | .preinit_array lo 0x98d70 |
| iv | `tfib_preinit_array_hi` | OK | .preinit_array hi 0x98d78 |
| iv | `tfib_data_rel_ro_lo` | OK | .data.rel.ro lo 0x98d78 |
| iv | `tfib_data_rel_ro_hi` | OK | .data.rel.ro hi 0x99278 |
| iv | `tfib_got_lo` | OK | .got lo 0x99278 |
| iv | `tfib_got_hi` | OK | .got hi 0x99fd0 |
| iv | `tfib_data_lo` | OK | .data lo 0x9afd0 |
| iv | `tfib_data_hi` | OK | .data hi 0x9db90 |
| iv | `tfib_asan_globals_lo` | OK | asan_globals lo 0x9db90 |
| iv | `tfib_asan_globals_hi` | OK | asan_globals hi 0x9dcd0 |
| iv | `tfib_bss_lo` | OK | .bss lo 0x9dd00 |
| iv | `tfib_bss_hi` | OK | .bss hi 0x5f5c30 |
| iv | `tfib_tbss_lo` | OK | .tbss lo 0x97d40 |
| iv | `tfib_tbss_hi` | OK | .tbss hi 0x97d54 |
| iv | `tfib_img_lo` | OK | image lo 0x10000 |
| iv | `tfib_img_hi` | OK | image hi 0x5f6000 |
| iv | `tfib_entry` | OK | e_entry 0x2ffb8 |
| iv | `tfib_gp` | OK | __global_pointer$ ['0x10800'] |
| iii (lib/A vs lib/B) | `MemToShadow_3c6cc` | OK | asan 0x3c6cc / asan-ubsan 0x3c72c +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (lib/A vs lib/B) | `MemToShadow_CHECK_AddrIsInMem_instance` | OK | asan 0x52140 / asan-ubsan 0x521a0 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (lib/A vs lib/B) | `MemToShadow_checked` | OK | asan 0x53788 / asan-ubsan 0x537e8 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (lib/A vs lib/B) | `MemToShadow_checked_instance_3` | OK | asan 0x5c674 / asan-ubsan 0x5c6d4 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (cgif vs lib/A) | `MemToShadow_3c6cc` | OK | cgif row FakeStack_SetShadow 0x3cbd0 / asan 0x3c6cc +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (cgif vs lib/A) | `MemToShadow_CHECK_AddrIsInMem_instance` | OK | cgif row MemToShadow_CHECK_AddrIsInMem_instance 0x52684 / asan 0x52140 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (cgif vs lib/A) | `MemToShadow_checked` | OK | cgif row MemToShadow_checked 0x53ccc / asan 0x53788 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |
| iii (cgif vs lib/A) | `MemToShadow_checked_instance_3` | OK | cgif row MemToShadow_checked_instance_3 0x5cbb8 / asan 0x5c674 +0x13c: 79 instructions, 31 pc-relative targets the same symbol + offset, every other word equal |

The same checks of `lib/A/AB1w.v` against fuzz_boxreg.asan give the counts above (every value equal). The four
MemToShadow rows are also the copy of the same file in each image: the qualified-name compare (`NAME{FILE}`) of
cmpkit 86da41d3ef68 lands on the row addresses in both pairs (section "Names with more than one copy").

## Inputs

| image | pin (stripped) sha256 | twin with `.symtab` and DWARF (read here) sha256 |
|---|---|---|
| cgif_file_fuzzer.asan | `7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0` | `488e39500746294ebe16fb1333e50c52e2339671de22f7768a37232aaeb05ad1` |
| fuzz_boxreg.asan | `eacfa20547ad7dc0d24164010513fcc8af4ba5e557ff3f391a07559e3e34a6df` | `4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3` |

Twin proof (`drvcmp.py twins`, kit member): for both pairs the PT_LOAD layout is equal and the only differing loadable
bytes are in the ELF header and `.note.gnu.build-id`.

Row tables: `proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v` (git blob `4dead8b1cff4cc7af784e200ee7644eb50002411`, 545 rows)
and `proofs/libreac/fuzz_boxreg/lib/A/AB1w.v` (git blob `68d907a2306868af462cff22e74fb9e3b9c467c2`, 524 rows; its rows are
the same as those of `AB1w.v` in this directory, git blob `af7ca2343672e320f7db73d41d1efc140a6e2153`, which differs only in
the image top: two values written as the number 0x5f6000 where `lib/A/AB1w.v` has `YImgTop.IMG_TOP`, and no `YImgTop`
Require line). Pairing: the two tables are walked in order. A boxreg row pairs 1:1 with the cgif row at its
place; a `(* cgif merged row X (A+S) ... *)` line is followed by the two rows that split X; a `(* cgif ... *)` line
that marks a dropped row stands at that cgif row's place, and its `(A+S)` equals the cgif row's range (checked for
every such line). The walk ends at the last token of both tables. 64 of the 513 1:1 rows carry a boxreg name other than
the cgif name; every pair has the same length.

Tools, by sha256:

| tool | sha256 |
|---|---|
| cmpkit 4bbd3a74be89 (sha256 of its `SHA256SUMS`) | `4bbd3a74be8994d014875952efdb79ef6516680988de43e95a3e217194f0ec33` |
| kit member `strictcmp2.py` | `16982e3ef42b8773ae979f587eebc32ad365a4012e874047f194779412d1a57c` |
| kit member `jtcheck.py` | `824905e2621161bc7e85cd99db6e724f496e493ee3dae0868d10854b6d8be4c2` |
| kit member `drvcmp.py` | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` |
| cmpkit 86da41d3ef68 (sha256 of its `SHA256SUMS`) | `86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60` |
| kit member `strictcmp3.py` | `65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7` |
| kit member `luiscan.py` | `9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad` |
| `rvdis.py`: independent RV64GC decoder over pyelftools 0.33 (not the kit, not capstone, not elfdis) | `dc4e137a1a22b4307d370543b8991b68dd4adc77c1743421e12a950978e3d565` |
| `ab1w_rerun.py`: pairing and both kit runs, by address and by name | `99cdd1b76aa296ff7d19a310f7bd7dd69bf88f5aa9ba4c61756c0de1d50bcef4` |
| `settle_ab1w.py`: named measurements of the fail-closed targets | `6bcfb98e0d774dd665e0a30dcca1fcb416ce1e413e8633a9eca4293c93aab467` |
| `luitrace.py`: lui value tracer (dataflow over the CFG, both images) | `d1b1a391cc09d999fde252ad9a30072f93ce0dde56a4cdbf268a05e694db8826` |
| `lui_ab1w.py`: class of every lui value of this pair | `4d4352e4fe8b943c2e425684004ebaf8866a5efba96870816358133e1c641b8a` |
| `lui_classes.py`: classes and citations shared with the ab1wB record | `003df38d0948d645ad0fd03ad5d38d02a6fa2a762e8d950decde858a9a22c097` |
| `rootcheck.py`: pointer-root check of load / store bases | `58b86013d2a3916552019b76d20a42b4e809f5f479689d6c2ca4807aae83a381` |
| `dwarfcite.py`: DWARF call sites and .debug_line rows | `4c25390bc1b8089dabfbfbceb85b42c5ee06bfd647747890e40553ae20b3159e` |
| `cites_ab1w.py`: binary citations of every lui use in both images | `bd4910c36b09792fd4b270ef950581786aeb6317a99e5db301b1ee8268c6bf24` |
| `plants_ab1w.py`: one planted re-point per settlement class | `f06d13ce1d20950a6ce79567f55fccce7a4e94be2fda9294448a6cda471e4e62` |
| `ab1w_extra.py`: kit controls, qualified-name compares, C-string audit | `82f30e2d61196d263ee401b2cb0f406b2de5aea7b6bcc029ba48671b484655fc` |
| `samecode.py`: kit calls, plants | `d0d308cef431255b723023a331a255f0050d370850056bd909d1d0a8092a68db` |
| `rerun127_228.py`: lines 127 and 228 on cmpkit 86da41d3ef68 | `aa571d6642f72cdd2e86e6bae10b8e85a6541aa8736cbadfe52a5d607e93d206` |
| `bcheck.py`: the values of lib/A/AB1w.v and lib/B/AB1w.v | `362933834ea36acc06a41da9bab931400206bd0935f67833b88c3bb4967f0fe0` |
| `ab1wB_fix.py`: the correction of `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md` lines 188 and 191 | `74ccbbb86894b1b4177763e5fd8f2a365b21882bb7efff028e0445b5f99a7cf1` |

Two tools changed after `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md` was committed (commit `a4891bbedbebe479e3e795c3119e111545a2cf4b`),
and that record keeps the versions it was made with: `luitrace.py` `12eda0ad0e63f06c2e7943eb953f6f4931063d6c90249606f5592fc606baa0d3` ->
`d1b1a391cc09d999fde252ad9a30072f93ce0dde56a4cdbf268a05e694db8826` (adds the cgif / boxreg image pair and finds each value's containing function), and
`rootcheck.py` `3fdb7676cbace31308006e7843317fd55ca039c79ae22203c05b5996d52c30a4` -> `58b86013d2a3916552019b76d20a42b4e809f5f479689d6c2ca4807aae83a381` (takes its
image list from the environment). Re-run with the new versions on the ab1wB pair: the lui trace output
(`luitrace-regress.out`, sha256 `0674996381da83aed953e0e93f494f64e655c677ccddcadd239004465f183060`) is the output of the
run recorded with `a4891bbedbeb` plus one new first line that names the two images; without that line it is
byte-identical to that run's output (both `9a1e364c498127103de0ef5b2cb978d0557bf6a17e2ec7a9e60c8565b6fd2cfc`). The
fmt_fp frame-base check output (`fmtfp-roots-regress.out`) is byte-identical to that run's output (both
`f266b836e65a9cc07678a9cbe36911e409e7c54e806a9770d98be9a6aaf189b9`).

Lines 188 and 191 of `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md` are corrected in this commit (measurement text only, verdict
unchanged). Their tool is `settle_ab1w.py` (sha256 `6bcfb98e0d774dd665e0a30dcca1fcb416ce1e413e8633a9eca4293c93aab467`), whose `EMPTY_CONSUMER` override holds
the two corrected texts; `ab1wB_fix.py` (sha256 `74ccbbb86894b1b4177763e5fd8f2a365b21882bb7efff028e0445b5f99a7cf1`) re-runs the ab1wB measurements of
`settle.py` (sha256 `ec1daa7d89ca40d347a10e50e6c545bdfda526603136d82832172ba8ca522139`, unchanged, still holding the old texts) with
that override and replaces exactly those two lines. A full regeneration of the ab1wB record from the corrected
measurements differs from the record committed at `a4891bbedbeb` only at lines 63-64 (the two tool versions above),
188 and 191.

Runtime source of record: as in `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md`, section "Runtime source of record"
(the toolchain's private source repository at the commit that section names, patches 0001-0023 on llvm-project
`87f0227cb60147a26a1eeb4fb06e3b505e9c7261` = llvmorg-20.1.8; musl `f21a9653` with patches 0001 and 0003, which change
only `src/env/__init_tls.c`). **P** = the file as the patch series leaves it, **U** = llvmorg-20.1.8 for a file the
series does not change, **M** = musl `f21a9653`, **P(musl)** = musl `f21a9653` + its patches 0001 and 0003. Both images
come from that toolchain (clang 20.1.8 in `.comment` of both).

## Rows not compared

### cgif rows with no boxreg row (NOT COMPARED)

| cgif row | cgif range | reason (the boxreg table's line at that place) |
|---|---|---|
| `asan_stack_malloc_A` | 0x3c8a4+0x190 | no boxreg row: replaced: cgif __asan_stack_malloc class 1 (0x3c8a4+0x190) has no twin; fuzz_boxreg.asan has only __asan_stack_malloc_3 0x3c520+0x1ac (107 insns), a new instance (CORE-PREP 1(a)) |
| `asan_stack_malloc_B` | 0x3ca34+0x19c | no boxreg row: cgif __asan_stack_malloc class 2 (0x3ca34+0x19c): fuzz_boxreg.asan has no __asan_stack_malloc_2; dropped (CORE-PREP 1(a)) |
| `fopen` | 0x41950+0x4 | no boxreg row: cgif fopen trampoline (0x41950+0x4): fuzz_boxreg.asan has no fopen; dropped |
| `fclose` | 0x41958+0x4 | no boxreg row: cgif fclose trampoline (0x41958+0x4): fuzz_boxreg.asan has no fclose; dropped |
| `icpt_fopen` | 0x462f0+0x46c | no boxreg row: cgif __interceptor_fopen (0x462f0+0x46c): fuzz_boxreg.asan has no fopen interceptor; dropped |
| `icpt_fclose` | 0x46868+0x1ac | no boxreg row: cgif __interceptor_fclose (0x46868+0x1ac): fuzz_boxreg.asan has no fclose interceptor; dropped |
| `LLVMFuzzerTestOneInput` | 0x80490+0x6a8 | no boxreg row: cgif program function LLVMFuzzerTestOneInput (0x80490+0x6a8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `read_frameconfig` | 0x80b38+0x864 | no boxreg row: cgif program function read_frameconfig (0x80b38+0x864): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_newgif` | 0x81404+0x614 | no boxreg row: cgif program function cgif_newgif (0x81404+0x614): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_writecb_or_freeCGIF` | 0x81a18+0xd0 | no boxreg row: cgif program function cgif_writecb_or_freeCGIF (0x81a18+0xd0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `freeFrame_or_freeCGIF` | 0x81ae8+0x80 | no boxreg row: cgif program function freeFrame_or_freeCGIF (0x81ae8+0x80): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_addframe` | 0x81b68+0xdb4 | no boxreg row: cgif program function cgif_addframe (0x81b68+0xdb4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cmpPixel` | 0x8291c+0x1e4 | no boxreg row: cgif program function cmpPixel (0x8291c+0x1e4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `flushFrame` | 0x82b00+0x1394 | no boxreg row: cgif program function flushFrame (0x82b00+0x1394): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `freeFrame` | 0x83e94+0xc0 | no boxreg row: cgif program function freeFrame (0x83e94+0xc0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_close` | 0x83f54+0x224 | no boxreg row: cgif program function cgif_close (0x83f54+0x224): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_raw_newgif` | 0x84178+0x71c | no boxreg row: cgif program function cgif_raw_newgif (0x84178+0x71c): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_raw_addframe` | 0x84894+0xd28 | no boxreg row: cgif program function cgif_raw_addframe (0x84894+0xd28): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `LZW_GenerateStream` | 0x855bc+0x10c8 | no boxreg row: cgif program function LZW_GenerateStream (0x855bc+0x10c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `cgif_raw_close` | 0x86684+0xe0 | no boxreg row: cgif program function cgif_raw_close (0x86684+0xe0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `create_byte_list` | 0x86764+0x2c8 | no boxreg row: cgif program function create_byte_list (0x86764+0x2c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `create_byte_list_block` | 0x86a2c+0x1a0 | no boxreg row: cgif program function create_byte_list_block (0x86a2c+0x1a0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md) |
| `musl_fclose` | 0x92ee4+0xcc | no boxreg row: cgif musl fclose (0x92ee4+0xcc): not linked into fuzz_boxreg.asan; dropped |
| `musl_fopen` | 0x93540+0xdc | no boxreg row: cgif musl fopen (0x93540+0xdc): not linked into fuzz_boxreg.asan; dropped |
| `fmodeflags` | 0x9361c+0xb4 | no boxreg row: cgif musl __fmodeflags (0x9361c+0xb4): not linked into fuzz_boxreg.asan; dropped |
| `fdopen` | 0x929c4+0x1d8 | no boxreg row: cgif musl __fdopen (0x929c4+0x1d8): not linked into fuzz_boxreg.asan; dropped |
| `ofl_add` | 0x93950+0x40 | no boxreg row: cgif musl __ofl_add (0x93950+0x40): not linked into fuzz_boxreg.asan; dropped |

### The 34 rows the earlier pairing could not compare

The pairing table behind the old counts gave no same-size target for 34 of the 545 cgif rows (its `port_target` was
missing, refused, of a different size, or split). Where each one went in this re-run:

| cgif row | earlier `port_verdict` | earlier reason | this re-run |
|---|---|---|---|
| `start` | NOSYM | no symbol / no target | compared (1:1, 0x302dc+0x48 vs 0x2ff58+0x48): 4bbd EQUAL-mod-pcrel, 1 target differences (settled) |
| `asan_stack_malloc_A` | SHAPE | size differs (0x190 vs 0x1ac) | NOT COMPARED: no boxreg row (replaced: cgif __asan_stack_malloc class 1 (0x3c8a4+0x190) has no twin; fuzz_boxreg.asan has only __asan_stack_malloc_3 0x3c520+0x1ac (107 insns), a new instance (CORE-PREP 1(a))) |
| `asan_stack_malloc_B` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif __asan_stack_malloc class 2 (0x3ca34+0x19c): fuzz_boxreg.asan has no __asan_stack_malloc_2; dropped (CORE-PREP 1(a))) |
| `thunk_417cc` | SHAPE | size differs (0x8 vs 0x4) | compared (merged, 0x41940+0x8 vs 0x41440+0x8): 4bbd EQUAL-mod-pcrel, 0 target differences |
| `fopen` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif fopen trampoline (0x41950+0x4): fuzz_boxreg.asan has no fopen; dropped) |
| `fclose` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif fclose trampoline (0x41958+0x4): fuzz_boxreg.asan has no fclose; dropped) |
| `icpt_fopen` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif __interceptor_fopen (0x462f0+0x46c): fuzz_boxreg.asan has no fopen interceptor; dropped) |
| `icpt_fclose` | SHAPE | size differs (0x1ac vs 0x30) | NOT COMPARED: no boxreg row (cgif __interceptor_fclose (0x46868+0x1ac): fuzz_boxreg.asan has no fclose interceptor; dropped) |
| `MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` | SHAPE | size differs (0x14c vs 0x74) | compared (merged, 0x6e0b8+0x14c vs 0x6db74+0x14c): 4bbd EQUAL-mod-pcrel, 0 target differences |
| `target_run` | SHAPE | size differs (0x188 vs 0x158) | compared (merged, 0x802c0+0x188 vs 0x7fd7c+0x188): 4bbd EQUAL-mod-pcrel, 0 target differences |
| `LLVMFuzzerTestOneInput` | SHAPE | size differs (0x6a8 vs 0x10a4) | NOT COMPARED: no boxreg row (cgif program function LLVMFuzzerTestOneInput (0x80490+0x6a8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `read_frameconfig` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function read_frameconfig (0x80b38+0x864): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_newgif` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_newgif (0x81404+0x614): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_writecb_or_freeCGIF` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_writecb_or_freeCGIF (0x81a18+0xd0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `freeFrame_or_freeCGIF` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function freeFrame_or_freeCGIF (0x81ae8+0x80): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_addframe` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_addframe (0x81b68+0xdb4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cmpPixel` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cmpPixel (0x8291c+0x1e4): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `flushFrame` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function flushFrame (0x82b00+0x1394): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `freeFrame` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function freeFrame (0x83e94+0xc0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_close` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_close (0x83f54+0x224): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_raw_newgif` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_raw_newgif (0x84178+0x71c): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_raw_addframe` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_raw_addframe (0x84894+0xd28): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `LZW_GenerateStream` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function LZW_GenerateStream (0x855bc+0x10c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `cgif_raw_close` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function cgif_raw_close (0x86684+0xe0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `create_byte_list` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function create_byte_list (0x86764+0x2c8): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `create_byte_list_block` | REFUSED | no symbol / no target | NOT COMPARED: no boxreg row (cgif program function create_byte_list_block (0x86a2c+0x1a0): fuzz_boxreg.asan is a different program; dropped (boxreg program lane listed in NOTES.md)) |
| `fdopen` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif musl __fdopen (0x929c4+0x1d8): not linked into fuzz_boxreg.asan; dropped) |
| `musl_fclose` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif musl fclose (0x92ee4+0xcc): not linked into fuzz_boxreg.asan; dropped) |
| `musl_fopen` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif musl fopen (0x93540+0xdc): not linked into fuzz_boxreg.asan; dropped) |
| `fmodeflags` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif musl __fmodeflags (0x9361c+0xb4): not linked into fuzz_boxreg.asan; dropped) |
| `ofl_add` | NOSYM | no symbol / no target | NOT COMPARED: no boxreg row (cgif musl __ofl_add (0x93950+0x40): not linked into fuzz_boxreg.asan; dropped) |
| `pthread_key_create_body_tsd_init` | SHAPE | size differs (0x11c vs 0x8) | compared (merged, 0x99700+0x11c vs 0x94650+0x11c): 4bbd EQUAL, 0 target differences |
| `thunk_96f9c` | SHAPE | size differs (0x8 vs 0x4) | compared (merged, 0x998b4+0x8 vs 0x94804+0x8): 4bbd EQUAL, 0 target differences |
| `set_thread_area` | NOSYM | no symbol / no target | compared (1:1, 0x998bc+0xc vs 0x9480c+0xc): 4bbd EQUAL, 0 target differences |

7 of the 34 are kept rows and are compared here; the other 27 are the cgif rows with no boxreg row.

## The rows the kit does not certify: kit verdict and settled verdict

21 rows, 23 target differences on cmpkit 4bbd3a74be89, all of fail-closed kinds; none is a REAL word. Each is settled
by the measurement its kind needs, read with the independent decoder in both images. A consumer is shown to be the same
code in both images by the kit's own compare of the consumer function, by address.

| row | function | word | kit target kind | kit verdict (by address) | settled verdict |
|---|---|---|---|---|---|
| `start` | `_start` | +0x10 | writable-unnamed | `EQUAL-mod-pcrel` | same (settled) |
| `Allocator_Deallocate` | `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE` | +0x20c | data-differs (De Bruijn table) | `EQUAL-mod-pcrel` | same (settled) |
| `Allocator_Allocate` | `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb` | +0xdc | data-differs (De Bruijn table) | `EQUAL-mod-pcrel` | same (settled) |
| `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` | `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_` | +0x190 | data-differs (De Bruijn table) | `EQUAL-mod-pcrel` | same (settled) |
| `Allocator_ComputeRZLog` | `_ZN6__asanL10RZSize2LogEj` | +0x44 | data-differs (De Bruijn table) | `EQUAL-mod-pcrel` | same (settled) |
| `asan_InitializeFlags` | `_ZN6__asan15InitializeFlagsEv` | +0x104 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `force_interface_symbols_dead_volatile_switch` | `_ZN6__asanL23force_interface_symbolsEv` | +0x20 | data-differs (jump table) | `EQUAL-mod-pcrel` | same (settled) |
| `asan_suppression_kinds_getter_3_insns` | `__asan_default_suppressions` | +0x4 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `ReportFile_SetReportPath` | `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | +0x48 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `FlagParser_ParseString_parse_flags` | `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | +0x1218 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `internal_sigaction_syscall_wrapper_selector` | `_ZN11__sanitizer19GetHandleSignalModeEi` | +0x24 | data-differs (pointer table) | `EQUAL-mod-pcrel` | same (settled) |
| `lsan_flags_init_helper` | `_ZN6__lsan5Flags11SetDefaultsEv` | +0xc | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `lsan_ubsan_default_options_weak_stub` | `__lsan_default_options` | +0x4 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `ubsan_MaybeCallUbsanDefaultOptions` | `_ZN7__ubsan5Flags11SetDefaultsEv` | +0x4 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `ubsan_default_options_weak_returns` | `__ubsan_default_options` | +0x4 | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `asan_module_ctor` | `asan.module_ctor` | +0x1c | got-value (cell holds a section-end address) | `EQUAL-mod-pcrel` | same (settled) |
| `asan_module_dtor` | `asan.module_dtor` | +0x14 | got-value (cell holds a section-end address) | `EQUAL-mod-pcrel` | same (settled) |
| `sysconf` | `sysconf` | +0xdc | data-differs (jump table) | `EQUAL-mod-pcrel` | same (settled) |
| `init_libc` | `__init_libc` | +0xcc | data-differs (unnamed empty string) | `EQUAL-mod-pcrel` | same (settled) |
| `printf_core` | `printf_core` | +0x534 | data-differs (jump table) | `EQUAL-mod-pcrel` | same (settled) |
| `printf_core` | `printf_core` | +0x6ac | data-differs (jump table) | `EQUAL-mod-pcrel` | same (settled) |
| `printf_core` | `printf_core` | +0x890 | unmeasured (I/S-type word on an auipc register) | `EQUAL-mod-pcrel` | same (settled) |
| `pop_arg` | `pop_arg` | +0x14 | data-differs (jump table) | `EQUAL-mod-pcrel` | same (settled) |

### The measurements

- `start` +0x10 (writable-unnamed): auipc a1 / addi a1 (+0xc / +0x10) form 0 (cgif) and 0 (boxreg): address 0 (undefined weak _DYNAMIC); _start ends `j _start_c` (True / True) and _start_c +0 is `lw a1,0(a0)` / `lw a1,0(a0)`, which overwrites a1 before any read
- `Allocator_Deallocate` +0x20c (data-differs (De Bruijn table)): index = (x & -x) * C >> 58 (neg, mul, srli 0x3a, lbu present in both images: True / True), so 64 bytes are read; table cgif 0x103e8 / boxreg 0x103e0: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C 0x0218a392cd3d5dbf / 0x0218a392cd3d5dbf
- `Allocator_Allocate` +0xdc (data-differs (De Bruijn table)): index = (x & -x) * C >> 58 (neg, mul, srli 0x3a, lbu present in both images: True / True), so 64 bytes are read; table cgif 0x10428 / boxreg 0x10420: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C 0x0218a392cd3d5dbf / 0x0218a392cd3d5dbf
- `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` +0x190 (data-differs (De Bruijn table)): index = (x & -x) * C >> 58 (neg, mul, srli 0x3a, lbu present in both images: True / True), so 64 bytes are read; table cgif 0x104e8 / boxreg 0x104e0: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C 0x0218a392cd3d5dbf / 0x0218a392cd3d5dbf
- `Allocator_ComputeRZLog` +0x44 (data-differs (De Bruijn table)): index = (x & -x) * C >> 58 (neg, mul, srli 0x3a, lbu present in both images: True / True), so 64 bytes are read; table cgif 0x10528 / boxreg 0x10520: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C 0x0218a392cd3d5dbf / 0x0218a392cd3d5dbf
- `asan_InitializeFlags` +0x104 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi t5 (+0x104), then two stores: sd t5,288(sp) (+0x108), whose only other 288(sp) access is ld a1,288(sp) at +0xc94 -> jal FlagParser::ParseString (+0xc9c); and sd t5,104(s3) (+0x220), s3 = __asan::asan_flags_dont_use_directly (set at +0xe8), so the asan `suppressions` flag (Flags +104); consumer (read in fuzz_boxreg.asan): FlagParser::ParseString: lbu a2,0(s) (+0x5c); byte 0 is no whitespace (mask 0x400100100002600 bit 0 = 0); beqz a2 (+0x88) -> exit (+0xb0) without parse_flag: reads s[0] only; asan::InitializeSuppressions +0x40 ld a1,104(a0) (a0 = the flags object, from its .got cell) -> jal SuppressionContext::ParseFromFile (+0x4c): lbu a1,0(a1) (+0x1c), beqz -> return: reads byte 0 only; the consumer code is the same in both images (kit, by address): _ZN11__sanitizer10FlagParser11ParseStringEPKcS2_ EQUAL-mod-pcrel N=0; _ZN6__asan22InitializeSuppressionsEv EQUAL-mod-pcrel N=0; _ZN11__sanitizer18SuppressionContext13ParseFromFileEPKc EQUAL-mod-pcrel N=0
- `force_interface_symbols_dead_volatile_switch` +0x20 (data-differs (jump table)): relative jump table: bound `li 51; bltu` -> 52 entries in both; base cgif 0x2096c / boxreg 0x20840; every entry as function + offset: equal in both images; every entry on an instruction boundary of _ZN6__asanL23force_interface_symbolsEv in both: True; entries: +0x34 +0x1c8 +0x160 +0x23c +0x258 +0x188 +0x1d4 +0x1e0 +0x27c +0x270 +0x104 +0x198 +0x140 +0xd0 +0x1fc +0x20c +0x2ac +0x288 +0xb0 +0x150 +0x2cc +0xc0 +0x130 +0xf0 +0x1a8 +0xe0 +0x2f0 +0x2e4 +0x118 +0x16c +0x22c +0x178 +0x2dc +0x30c +0x110 +0x29c +0x2fc +0x90 +0x264 +0x80 +0x70 +0x120 +0x1b8 +0x2bc +0x40 +0xa0 +0x1ec +0x248 +0x318 +0x21c +0x60 +0x50
- `asan_suppression_kinds_getter_3_insns` +0x4 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): returns a0 = ""; only caller asan::InitializeSuppressions jal at +0x50, mv a1,a0, tail j SuppressionContext::Parse (+0x6c); consumer (read in fuzz_boxreg.asan): SuppressionContext::Parse: lbu str[0] (+0xcc), not 32 / 9; internal_strchr(str,10) (C string) = 0; internal_strlen(str) = 0 -> end == str (+0xfc); lbu end[0] (+0xac) beqz -> exit: reads to the NUL only; the consumer code is the same in both images (kit, by address): _ZN6__asan22InitializeSuppressionsEv EQUAL-mod-pcrel N=0; _ZN11__sanitizer18SuppressionContext5ParseEPKc EQUAL-mod-pcrel N=0
- `ReportFile_SetReportPath` +0x48 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi a4 (+0x48) -> sd a4 to CommonFlags +24 / +200 / +208 = strip_path_prefix / cov_8bit_counters_out / cov_pcs_out (RegisterCommonFlags handlers +0x104 / +0x9a4 / +0x9d8); consumer (read in fuzz_boxreg.asan): readers found (value-tracking scan): strip_path_prefix: ProcessAddressFrames +0xbc / ReportErrorSummary +0xc4 load it into a7, the strip_path_prefix argument of the virtual RenderFrame; StripPathPrefix (callers: FormattedStackTracePrinter::RenderFrame x2, RenderSourceLocation, RenderModuleLocation, RenderData) reads it only through internal_strstr and internal_strlen (C string); cov_8bit_counters_out / cov_pcs_out: no reader found; FlagHandler<const char*>::Format (0x37204): ld *t_, internal_snprintf "%s" (C string); the consumer code is the same in both images (kit, by address): _ZN11__sanitizer12_GLOBAL__N_121StackTraceTextPrinter20ProcessAddressFramesEm EQUAL-mod-pcrel N=0; _ZN11__sanitizer18ReportErrorSummaryEPKcS1_ EQUAL-mod-pcrel N=0; _ZN11__sanitizer15StripPathPrefixEPKcS1_ EQUAL N=0; _ZN11__sanitizer11FlagHandlerIPKcE6FormatEPcm EQUAL-mod-pcrel N=0
- `FlagParser_ParseString_parse_flags` +0x1218 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi s2 (+0x1218), then two stores sd s2,24(a2) (+0x1228 and +0x1274): the original_path field of the two FlagHandlerInclude objects, `include` and `include_if_exists`, each from LowLevelAllocator::Allocate(32) (vtable +0, parser +8, ignore_missing +16, path +24); consumer (read in fuzz_boxreg.asan): FlagHandlerInclude::Format (0x62594): ld a3,24(a0) -> internal_snprintf(buf, size, "%s", path) (C string); FlagHandlerInclude::Parse (0x624d8) first does sd a1,24(a0) (overwrites the field, never reads the old value); both objects use these two methods; the consumer code is the same in both images (kit, by address): _ZN11__sanitizer18FlagHandlerInclude6FormatEPcm EQUAL-mod-pcrel N=0; _ZN11__sanitizer18FlagHandlerInclude5ParseEPKc EQUAL-mod-pcrel N=0
- `internal_sigaction_syscall_wrapper_selector` +0x24 (data-differs (pointer table)): pointer table (.data.rel.ro): 8 entries at cgif 0x9db58 / boxreg 0x98a78, read as `ld` after the mask 0x9f test (`li 159` present in both: True / True); entries read (0-4, 7): 0 _ZN11__sanitizer21common_flags_dont_useE+0x64; 1 _ZN11__sanitizer21common_flags_dont_useE+0x68; 2 _ZN11__sanitizer21common_flags_dont_useE+0x60; 3 _ZN11__sanitizer21common_flags_dont_useE+0x5c; 4 _ZN11__sanitizer21common_flags_dont_useE+0x6c; 7 _ZN11__sanitizer21common_flags_dont_useE+0x58; entries 5 and 6: 0,0 / 0,0 (never read)
- `lsan_flags_init_helper` +0xc (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi a3 (+0xc) -> sd a3,32(a0): lsan Flags +32 = suppressions (RegisterLsanFlags handler +0x378); consumer (read in fuzz_boxreg.asan): reader: LeakSuppressionContext::Suppress +0x44 ld a1,96(s5) (= lsan_flags+32) -> SuppressionContext::ParseFromFile: lbu a1,0(a1) (+0x1c), beqz -> return: reads byte 0 only; FlagHandler<const char*>::Format "%s"; the consumer code is the same in both images (kit, by address): _ZN6__lsan22LeakSuppressionContext8SuppressEjmm EQUAL-mod-pcrel N=0; _ZN11__sanitizer18SuppressionContext13ParseFromFileEPKc EQUAL-mod-pcrel N=0; _ZN11__sanitizer11FlagHandlerIPKcE6FormatEPcm EQUAL-mod-pcrel N=0
- `lsan_ubsan_default_options_weak_stub` +0x4 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): returns a0 = ""; only caller asan::InitializeFlags jal +0xcc8, mv a1,a0 -> jal FlagParser::ParseString +0xcd8; consumer (read in fuzz_boxreg.asan): FlagParser::ParseString (as for InitializeFlags +0x104): reads s[0] only; the consumer code is the same in both images (kit, by address): _ZN6__asan15InitializeFlagsEv EQUAL-mod-pcrel N=1, every target settled here (+0x104); _ZN11__sanitizer10FlagParser11ParseStringEPKcS2_ EQUAL-mod-pcrel N=0
- `ubsan_MaybeCallUbsanDefaultOptions` +0x4 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi a1 (+0x4) -> sd a1,8(a0): ubsan Flags +8 = suppressions (RegisterUbsanFlags handler +0xc4); consumer (read in fuzz_boxreg.asan): reader: ubsan::InitializeSuppressions +0x40 ld a1,8(a0) -> tail j SuppressionContext::ParseFromFile: lbu a1,0(a1), beqz -> return: byte 0 only; FlagHandler<const char*>::Format "%s"; the consumer code is the same in both images (kit, by address): _ZN7__ubsan22InitializeSuppressionsEv EQUAL-mod-pcrel N=0; _ZN11__sanitizer18SuppressionContext13ParseFromFileEPKc EQUAL-mod-pcrel N=0; _ZN11__sanitizer11FlagHandlerIPKcE6FormatEPcm EQUAL-mod-pcrel N=0
- `ubsan_default_options_weak_returns` +0x4 (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): returns a0 = ""; only caller asan::InitializeFlags jal +0xcb4, mv a1,a0 -> jal FlagParser::ParseString +0xcc4; consumer (read in fuzz_boxreg.asan): FlagParser::ParseString: reads s[0] only; the consumer code is the same in both images (kit, by address): _ZN6__asan15InitializeFlagsEv EQUAL-mod-pcrel N=1, every target settled here (+0x104); _ZN11__sanitizer10FlagParser11ParseStringEPKcS2_ EQUAL-mod-pcrel N=0
- `asan_module_ctor` +0x1c (got-value (cell holds a section-end address)): .got cell cgif 0x9ec30 (.got) holds 0xa2930 / boxreg 0x99b38 (.got) holds 0x9d8b0; every symbol at that value: __stop_asan_globals / __stop_asan_globals, the end of asan_globals (cgif 0xa2870+0xc0, boxreg 0x9d770+0x140); consumer __asan_register_elf_globals: the same code in both images (kit, by address: EQUAL-mod-pcrel N=0), which uses the value only as the loop bound (beq a1,a2; sub a2,a2,a1 -> count). The enclosed arrays are each program's own globals: 3 entries in cgif, 5 in boxreg
- `asan_module_dtor` +0x14 (got-value (cell holds a section-end address)): .got cell cgif 0x9ec30 (.got) holds 0xa2930 / boxreg 0x99b38 (.got) holds 0x9d8b0; every symbol at that value: __stop_asan_globals / __stop_asan_globals, the end of asan_globals (cgif 0xa2870+0xc0, boxreg 0x9d770+0x140); consumer __asan_unregister_elf_globals: the same code in both images (kit, by address: EQUAL-mod-pcrel N=0), which uses the value only as the loop bound (beq a1,a2; sub a2,a2,a1 -> count). The enclosed arrays are each program's own globals: 3 entries in cgif, 5 in boxreg
- `sysconf` +0xdc (data-differs (jump table)): relative jump table: bound `li 12; bltu` -> 13 entries in both; base cgif 0x2143c / boxreg 0x212f8; every entry as function + offset: equal in both images; every entry on an instruction boundary of sysconf in both: True; entries: +0xa4 +0x214 +0x200 +0x208 +0xf8 +0x164 +0x164 +0x138 +0x138 +0x21c +0xf8 +0x104 +0x104
- `init_libc` +0xcc (data-differs (unnamed empty string)): target cgif 0x13ed0 (.rodata) / boxreg 0x13e6c (.rodata); byte 0 = 00 / 00; how it leaves the function (boxreg): addi s0 (+0xcc) when argv[0] is NULL -> sd s0 to __progname_full and __progname (GOT cells 0x99b50 / 0x99b58 in asan); consumer (read in fuzz_boxreg.asan): in-function scan for "/": lbu a3,-1(a1) from pn[0] (+0xfc), bnez continue -> stops at the NUL; no other reader of __progname / __progname_full found by the value-tracking scan; the consumer code is the same in both images (kit, by address): the read loop is inside this function, which is this row
- `printf_core` +0x534 (data-differs (jump table)): relative jump table: bound `li 55; bltu` -> 56 entries in both; base cgif 0x22078 / boxreg 0x21f38; every entry as function + offset: equal in both images; every entry on an instruction boundary of printf_core in both: True; entries: +0x548 +0x5c8 +0x6e8 +0x5c8 +0x548 +0x548 +0x548 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x7ac +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x748 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x5c8 +0x548 +0x5c8 +0x708 +0x598 +0x548 +0x548 +0x548 +0x5c8 +0x598 +0x5c8 +0x5c8 +0x5c8 +0x5f4 +0x694 +0x640 +0x734 +0x5c8 +0x5c8 +0x5e0 +0x5c8 +0x6d0 +0x5c8 +0x5c8 +0x748
- `printf_core` +0x6ac (data-differs (jump table)): relative jump table: bound `li 7; bltu` -> 8 entries in both; base cgif 0x22158 / boxreg 0x22018; every entry as function + offset: equal in both images; every entry on an instruction boundary of printf_core in both: True; entries: +0xc48 +0x6c0 +0x6c0 +0xc58 +0xc68 +0xb0 +0x6c0 +0x6c0
- `printf_core` +0x890 (unmeasured (I/S-type word on an auipc register)): word 00158893 (addi a7,a1,1) in both; jump-table targets as successors of each jr (cgif 18 / boxreg 18); the value of a1 there: a1 = 0x10b5c / 0x10b54, so the word forms 0x10b5d / 0x10b55, C string b'+   0X0x\x00' / b'+   0X0x\x00'
- `pop_arg` +0x14 (data-differs (jump table)): relative jump table: bound `li 17; bltu` -> 18 entries in both; base cgif 0x22178 / boxreg 0x22038; every entry as function + offset: equal in both images; every entry on an instruction boundary of pop_arg in both: True; entries: +0x28 +0x11c +0x94 +0x28 +0x28 +0x28 +0xac +0x104 +0x7c +0xc4 +0x28 +0x28 +0x28 +0x28 +0x28 +0x28 +0x40 +0xdc

The two `.got` cells hold `__stop_asan_globals` in both images, and the consumer uses it only as a bound, so the
reference is the same symbol. The `asan_globals` arrays they bound are each program's own globals and differ by
program; the rows compare the code, not that data.

## The 59 lui values: trace, class and citation

Ops the tracer follows (luitrace.py): every RV64GC integer instruction the decoder knows (lui, auipc, li, mv, addi(w), add(w), sub(w), sh1add, sh2add, sh3add, and, or, xor, andi, ori, xori, sll(i)(w), srl(i)(w), sra(i)(w), mul(w), mulh*, div(u)(w), rem(u)(w), slt(i)(u), seqz, snez, sign / zero extension, the Zbb ops), loads and stores (a stack slot at a known sp offset carries the value to its reload), and the A-extension lr / sc / amo* as bases and as data, from the value's word to each register's or slot's next write, over every path of the function's control-flow graph.

The rules are those of `../ab1wB/RERUN-cmpkit-4bbd3a74be89.md` ("Settlement rules applied"): (i) a call argument whose
parameter the source contract states is a byte count / length / count / size / flags / mode / prot / alignment (an
address parameter never settles); (ii) a returned integer that is not an address; (iii) an offset added to an object
pointer from a load, an argument or an allocator return, or an absolute address compared by symbol + offset in both
images; store into an integer, non-address field; (c) CheckFailed v1 / v2, which CheckFailed formats only with a
numeric conversion and uses nowhere else; (d) a value whose every use on every path up to its next write is a branch /
compare operand; (e) a frame base: the base's only pointer root is sp on every path, integer constants added to it
(a lui-built frame offset included) are offsets, and no auipc / lui / section-built pointer appears in the base chain.

fuzz_boxreg.asan is the same image as in the ab1wB record, so a value at the same fuzz_boxreg.asan word has the same
uses there. For each of the 59 values the trace shows the same number and the same uses in cgif_file_fuzzer.asan
(59 of 59), and the DWARF call sites and `.debug_line` rows of every target word and every use are the same in
both images (240 of 240 citation rows). 55 values sit at a word the ab1wB record classes, and carry that class and
citation; 4 are new to this pair (the asan / asan-ubsan pair accepted them as C strings with the same bytes in
both images) and are classed and cited here.

Counts (values): (c) 1, (d) 22, (e)+(ii)+(i) 1, (i) 10, (i)+(store)+(c) 1, (ii) 3, (iii) 14, (store) 4, (store)+(c) 1, NOT CERTIFIED 2; total 57 certified, 2 NOT CERTIFIED: REAL 0, of 59.

**NOT CERTIFIED: REAL 0** (no real difference is shown; not settled under the rules):

- `InitializeShadowMemory` +0x1b0: an address parameter (`uptr zero_base_max_shadow_start`) never settles
- `SizeClassAllocator64_PopulateFreeArray` +0xb0: the value enters the store base at +0x1d0 non-linearly (its CheckFailed `v1` use alone would settle by (c))

| row | word | value (both images) | kind | class | what it is | binary evidence | source of record | class from |
|---|---|---|---|---|---|---|---|---|
| `QuarantineCache_MergeBatches_Transfer` | +0x74 | 0x190000 | lui-in-section | CERTIFIED (d) compare only | every use on every path is a compare operand (ruling (d)) | binary: the only use is `mul a4,a6,a4` (+0x7c); the product's only use is `bgeu a5,a4` (+0x84); a4 is live at `jal MergeBatches` (+0xa4) but MergeBatches takes this, from (a0, a1: `MergeBatchesEPS3_`), so it is not passed; next write of a4 ends the chain | U sanitizer_quarantine.h:163-166 (`overhead_size * (100 + kOverheadThresholdPercents) > cache_size * kOverheadThresholdPercents`) | ab1wB `Quarantine_Recycle +0x74` |
| `SizeClassAllocator64_EnsureFreeArraySpace` | +0x2c | 0x3ffff | lui-in-section | CERTIFIED (i) call argument + CERTIFIED (store) + CERTIFIED (c) CheckFailed v1 / v2 | Map `size` and PoisonShadow `size` (uptr, used only as lengths, ruling (b)), stores into `uptr mmaped` and `uptr mapped_free_array`, CheckFailed v1 (ruling (c)) | binary: a2 of `jal ReservedAddressRange::Map` (+0x9c; `MapEmmPKc`, 3rd incl. this = unsigned long), a1 of `jal PoisonShadow` (+0xb8; DWARF asan_poisoning.h:27), `sd` at +0xd4 (.debug_line asan_allocator.cpp:296) and +0xdc (.debug_line sanitizer_allocator_primary64.h:758), a3 of `jal CheckFailed` (+0x120; DWARF sanitizer_common.h:333). binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | P sanitizer_allocator_primary64.h:750-751 `RoundUpTo(needed_space, kFreeArrayMapSize)`, `CHECK_LE(new_mapped_free_array, kFreeArraySize)` (llvmorg-20.1.8: 745-746), :758, :679 `uptr mapped_free_array`; P sanitizer_posix_libcdep.cpp:492-499 (Map: size goes only to MmapFixedOrDieOnFatalError(fixed_addr, size, name) and SealedRepairReservation(fixed_addr, size)); P asan_poisoning.cpp:37-51 (size only in addr + size bounds and FastPoisonShadow(addr, size, value)); P asan_allocator.cpp:296 `thread_stats.mmaped += size`, U asan_stats.h:37 `uptr mmaped` | ab1wB `SizeClassAllocator64_EnsureFreeArraySpace +0x2c` |
| `LargeMmapAllocator_Allocate` | +0x430 | 0x100000 | lui-in-section | CERTIFIED (c) CheckFailed v1 / v2 | CheckFailed v2 = kMaxNumChunks (ruling (c)) | binary: a4 of `jal CheckFailed` (+0x434; DWARF sanitizer_common.h:333); .debug_line at the word: sanitizer_allocator_secondary.h:42. binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | U sanitizer_allocator_secondary.h:42 `CHECK_LT(n, kMaxNumChunks)` | ab1wB `LargeMmapAllocator_Allocate +0x430` |
| `LargeMmapAllocator_Allocate` | +0x448 | 0x20000 | lui-in-section | CERTIFIED (i) call argument | ReservedAddressRange::MapOrDie `size` (uptr), used only as a length (ruling (b)) | binary: `lui a2,0x20` (+0x448) is a2 of `jal ReservedAddressRange::MapOrDie` (+0x458) in both images; `MapOrDieEmmPKc` = (this, uptr fixed_addr, uptr size, const char *name), so a2 is `size`; DWARF call site: see the citations table | U sanitizer_allocator_secondary.h:45-48 (`address_range_.MapOrDie(base + n_reserved_ * sizeof(uptr), kChunksBlockCount * sizeof(uptr))`, :55 `kChunksBlockCount = 1 << 14`: 0x20000 bytes); P sanitizer_posix_libcdep.cpp:504-506 (MapOrDie passes size only to MmapFixedOrDie); P sanitizer_posix.cpp:124-145 (MmapFixedImpl: size only in RoundUpTo, MmapNamed length, ReportMmapFailureAndDie, IncreaseTotalMmap) | new here |
| `SizeClassAllocator64_PopulateFreeArray` | +0xb0 | 0x40000 | lui-in-section | NOT CERTIFIED: REAL 0 | the value enters the store base at +0x1d0 non-linearly (its CheckFailed `v1` use alone would settle by (c)) | binary: store base at +0x1d0 (.debug_line sanitizer_allocator_primary64.h:843) takes the value through non-linear ops; CheckFailed a3 = v1 (+0x2ac); .debug_line at the word: sanitizer_common.h:471 (RoundUpTo) | P sanitizer_allocator_primary64.h:843, :852 (llvmorg-20.1.8: 838, 847); U sanitizer_common.h:471 | ab1wB `SizeClassAllocator64_PopulateFreeArray +0xb0` |
| `AsanDeactivate_activation_CHECK_helper` | +0x8c | 0x100010 | lui-in-section | CERTIFIED (store) | store into integer fields u16 min_redzone, u16 max_redzone of a local AllocatorOptions | binary: `sw a0,8(sp)` (+0x90) of 0x00100010 = two u16 values 16; .debug_line +0x90: asan_activation.cpp:115; then `mv a0,sp; jal ReInitializeAllocator` (+0x98/+0x9c; `ReInitializeAllocatorERKNS_16AllocatorOptionsE`, a const reference; DWARF call site asan_allocator.h:48) | U asan_allocator.h:34-38 (`u32 quarantine_size_mb; u32 thread_local_quarantine_size_kb; u16 min_redzone; u16 max_redzone;` -> +8, +10); U asan_activation.cpp:115-116, :119 | ab1wB `AsanDeactivate_activation_CHECK_helper +0x8c` |
| `InitializeAsanInterceptors` | +0x44 | 0x38db28 | lui-in-section | CERTIFIED (i) call argument | MmapOrDie `size` (uptr), used only as a length (ruling (b)) | binary: a0 of `jal MmapOrDie` (+0x4c; `MmapOrDieEmPKcb`, 1st = unsigned long; DWARF call site sanitizer_common.h:90); .debug_line at the word: sanitizer_addrhashmap.h:200 | U sanitizer_common.h:90 `void *MmapOrDie(uptr size, const char *mem_type, bool raw_report = false)`; P sanitizer_posix.cpp:48-56 (size only in RoundUpTo, MmapNamed(nullptr, size, ...), ReportMmapFailureAndDie(size, ...), IncreaseTotalMmap(size)); U sanitizer_addrhashmap.h:200 `MmapOrDie(kSize * sizeof(table_[0]), "AddrHashMap")` | ab1wB `InitializeAsanInterceptors +0x44` |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | +0x74 | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int) | binary: a3 of `jal internal_mmap` (+0x88; `internal_mmapEPvmiiiy`, 4th = int; DWARF call site sanitizer_posix.h:40); .debug_line at the word: asan_shadow_setup.cpp:70 | U sanitizer_posix.h:40-41 `uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd, u64 offset)`; P asan_shadow_setup.cpp:68-72 (SealedReserveRange, patch 0019, not upstream) `MAP_PRIVATE \| MAP_ANONYMOUS \| MAP_NORESERVE \| MAP_FIXED_NOREPLACE` = 0x104022 | ab1wB `ReserveShadowMemoryRanges_sealed_early_shadow_re +0x74` |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | +0xfc | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int), two calls | binary: a3 of `jal internal_mmap` (+0x118, +0x164; DWARF call site sanitizer_posix.h:40); .debug_line at the word: asan_shadow_setup.cpp:69 | U sanitizer_posix.h:40-41; P asan_shadow_setup.cpp:68-72 (patch 0019) | ab1wB `ReserveShadowMemoryRanges_sealed_early_shadow_re +0xfc` |
| `InitializeShadowMemory` | +0x1b0 | 0x40000 | lui-in-section | NOT CERTIFIED: REAL 0 | an address parameter (`uptr zero_base_max_shadow_start`) never settles | binary: a3 of `jal ProtectGap` (+0x1c0; `ProtectGapEmmmm`, 4th = unsigned long; DWARF call site sanitizer_common.h:160); .debug_line at the word: asan_shadow_setup.cpp:49 | U sanitizer_common.h:160-161 `void ProtectGap(uptr addr, uptr size, uptr zero_base_shadow_start, uptr zero_base_max_shadow_start)`; P asan_shadow_setup.cpp:49-50 (`kZeroBaseMaxShadowStart`) | ab1wB `InitializeShadowMemory +0x1b0` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0x88 | 0x81008 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x81008 | binary: a0 of `jal __sanitizer_internal_memset` (+0x98; DWARF call site sanitizer_libc.h:35) = auipc base + the value: internal_alloc_placeholder+0x81008 in both images | P sanitizer_allocator.cpp:29 `static char internal_alloc_placeholder[sizeof(InternalAllocator)]`, :36-47 | ab1wB `internal_allocator +0x88` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0xa4 | 0x40000 | lui-in-section | CERTIFIED (i) call argument | memset `n` (uptr): a byte count (ruling (a)) | binary: a2 of `jal __sanitizer_internal_memset` (+0xb0; DWARF call site sanitizer_libc.h:35); .debug_line at the word: sanitizer_libc.h:52 | U sanitizer_libc.h:35-36 `void *__sanitizer_internal_memset(void *s, int c, uptr n)`, :51 `internal_memset(void *s, int c, uptr n)`; contract: M include/string.h:29 `void *memset (void *, int, size_t);` (C memset: n is the byte count) | ab1wB `internal_allocator +0xa4` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0xb4 | 0x40040 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x40040 | binary: a0 of `jal __sanitizer_internal_memset` (+0xc8) = internal_alloc_placeholder+0x40040 in both images | P sanitizer_allocator.cpp:29 | ab1wB `internal_allocator +0xb4` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0xcc | 0x41000 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s`, two store bases and one stored address, all internal_alloc_placeholder + an offset | binary: memset a0 (+0xe0) = placeholder+0x40dc0; `sd` bases (+0x10c, +0x110; .debug_line sanitizer_allocator_secondary.h:76-77) = placeholder+0x40dc0, +0x40dc8; stored datum (+0x110) = placeholder+0x40dd0; the same in both images. a1 at `ret` (+0x144) is not a return value: internal_allocator returns one pointer, in a0 | P sanitizer_allocator.cpp:29, :36 `InternalAllocator *internal_allocator()`; U sanitizer_allocator_secondary.h:75-77 | ab1wB `internal_allocator +0xcc` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0xd0 | 0x40dc0 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x40dc0 | binary: a0 of `jal __sanitizer_internal_memset` (+0xe0) = placeholder+0x40dc0 in both images | P sanitizer_allocator.cpp:29 | ab1wB `internal_allocator +0xd0` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0xd8 | 0x40248 | lui-in-section | CERTIFIED (i) call argument | memset `n` (uptr): a byte count (ruling (a)) | binary: a2 of `jal __sanitizer_internal_memset` (+0xe0; DWARF call site sanitizer_libc.h:35); .debug_line at the word: sanitizer_libc.h:52 | U sanitizer_libc.h:35-36 `void *__sanitizer_internal_memset(void *s, int c, uptr n)`, :51 `internal_memset(void *s, int c, uptr n)`; contract: M include/string.h:29 `void *memset (void *, int, size_t);` (C memset: n is the byte count) | ab1wB `internal_allocator +0xd8` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | +0x100 | 0x40dd0 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | stored datum internal_alloc_placeholder+0x40dd0 | binary: stored by `sd a2,-568(a1)` (+0x110) at placeholder+0x40dc8 (.debug_line sanitizer_allocator_secondary.h:77); the same in both images | P sanitizer_allocator.cpp:29; U sanitizer_allocator_secondary.h:77 `chunks_ = reinterpret_cast<Header**>(ptr_array_.Init())` | ab1wB `internal_allocator +0x100` |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0xa8 | 0x40dc0 | lui-in-section | CERTIFIED (iii) offset from an argument base | `this` of LargeMmapAllocator::Allocate = incoming a0 (CombinedAllocator `this`, an argument) + 0x40dc0 = &secondary_ | binary: a0 of `jal ...LargeMmapAllocator...8AllocateEPNS_14AllocatorStatsEmm` (+0xc0) = incoming a0 + 0x40dc0 in both images; a4 is live but not a parameter | U sanitizer_allocator_combined.h:71 `secondary_.Allocate(&stats_, original_size, alignment)`, :196-198; U sanitizer_allocator_secondary.h:85 | ab1wB `InternalAllocator_CombinedAllocator_Allocate_int +0xa8` |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0xac | 0x81008 | lui-in-section | CERTIFIED (iii) offset from an argument base | `AllocatorStats *stat` = incoming a0 + 0x81008 = &stats_ | binary: a1 of the same call (+0xc0; 2nd parameter `PNS_14AllocatorStatsE`) = incoming a0 + 0x81008 in both images; a5 is live but not a parameter | U sanitizer_allocator_combined.h:71, :198; U sanitizer_allocator_secondary.h:85 `void *Allocate(AllocatorStats *stat, const uptr size, uptr alignment)` | ab1wB `InternalAllocator_CombinedAllocator_Allocate_int +0xac` |
| `InternalAllocator_LargeMmapAllocator_Allocate` | +0x118 | 0x40010 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offsets from `this` (incoming a0): +0x40010 (n_chunks_, chunks_sorted_, stats.*), +0x40240 (mutex_) | binary: 13 load / store bases = incoming a0 + 0x40010 (.debug_line sanitizer_allocator_secondary.h:119-127), `lr.w.aq` / `sc.w` bases (+0x12c, +0x140) and a0 of `jal StaticSpinMutex::LockSlow` (+0x390) = incoming a0 + 0x40240, in both images | U sanitizer_allocator_secondary.h:313-321 (page_size_, chunks_, n_chunks_, chunks_sorted_, struct Stats, mutex_), :118-127 | ab1wB `InternalAllocator_LargeMmapAllocator_Allocate +0x118` |
| `InternalAllocator_LargeMmapAllocator_Allocate` | +0x24c | 0x40000 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offset +0x40000 from `this` + a runtime index: stats.by_size_log[size_log] | binary: `ld` / `sd` bases (+0x258, +0x268; .debug_line sanitizer_allocator_secondary.h:127) = incoming a0 + index + 0x40000 in both images | U sanitizer_allocator_secondary.h:127 `stats.by_size_log[size_log]++`, :319 | ab1wB `InternalAllocator_LargeMmapAllocator_Allocate +0x24c` |
| `internal_usleep_internal_sleep_nanosleep` | +0x14 | 0xf4240 | lui-in-section | CERTIFIED (store) | store into the integer field `long tv_nsec` of a local timespec | binary: `sd a0,8(sp)` (+0x38; .debug_line sanitizer_linux.cpp:641) of (us - q*1000000)*1000; then a0 = a1 = sp, a7 = 101 (nanosleep), `ecall` | P sanitizer_linux.cpp:638-642 `ts.tv_nsec = (useconds % 1000000) * 1000`; M include/alltypes.h.in:44 `struct timespec { time_t tv_sec; ...; long tv_nsec; ... }` | ab1wB `internal_usleep_internal_sleep_nanosleep +0x14` |
| `ReadLongProcessName_proc_self_cmdline` | +0x40 | 0x100000 | lui-in-section | CERTIFIED (i) call argument | ReadFileToBuffer `max_len` (uptr), used only as a length (ruling (b)) | binary: a4 of `jal ReadFileToBuffer` (+0x48; `ReadFileToBufferEPKcPPcPmS4_mPi`, 5th = unsigned long; DWARF call site sanitizer_common.h:781); .debug_line at the word: sanitizer_linux.cpp:1397 | U sanitizer_common.h:781-783 `bool ReadFileToBuffer(const char *file_name, char **buff, uptr *buff_size, uptr *read_len, uptr max_len = ..., error_t *errno_p = nullptr)`; P sanitizer_file.cpp:140, :143, :146, :167 (max_len only in `!max_len`, `Min(PageSize, max_len)`, `Min(size * 2, max_len)`, `*read_len == max_len`); P sanitizer_linux.cpp:1397-1398 (`1024 * 1024`) | ab1wB `ReadLongProcessName_proc_self_cmdline +0x40` |
| `GetNamedMappingFd_MmapNamed` | +0x90 | 0x80242 | lui-in-section | CERTIFIED (i) call argument | internal_open `flags` (int) | binary: a1 of `jal internal_open` (+0x98; `internal_openEPKcij`, 2nd = int; DWARF call site sanitizer_posix.h:30); .debug_line at the word: sanitizer_posix.cpp:397 | U sanitizer_posix.h:30 `uptr internal_open(const char *filename, int flags, u32 mode)`; P sanitizer_posix.cpp:397 `O_RDWR \| O_CREAT \| O_TRUNC \| o_cloexec` = 0x2 \| 0x40 \| 0x200 \| 0x80000 = 0x80242 | ab1wB `GetNamedMappingFd_MmapNamed +0x90` |
| `MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` | +0xec | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int) | binary: a3 of `jal internal_mmap` (row +0x104 = SealedRepairReservation +0x90; DWARF call site sanitizer_posix.h:40) | U sanitizer_posix.h:40-41; P sanitizer_posix_libcdep.cpp:475-484 (SealedRepairReservation, patch 0022, not upstream) `MAP_PRIVATE \| MAP_ANON \| MAP_NORESERVE \| MAP_FIXED_NOREPLACE` | ab1wB `SealedRepairReservation +0x78` |
| `StackStore_Alloc` | +0x78 | 0x100000 | lui-in-section | CERTIFIED (store) + CERTIFIED (c) CheckFailed v1 / v2 | amo add into `atomic_uint32_t stored_`, `*pack` (uptr), and CheckFailed v2 = kBlockSizeFrames (ruling (c)) | binary: `amoadd.w.rl` data (+0x9c, +0xd0) and `sd` into *pack (+0xcc, +0xf0) as for +0x84; a4 of `jal CheckFailed` (+0x130; DWARF call site sanitizer_common.h:333) = 0x100000 = v2. binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | U sanitizer_stack_store.cpp:91 `CHECK_LE(count, kBlockSizeFrames)`, :92-96, :374-376; U sanitizer_stack_store.h:21 `kBlockSizeFrames = 0x100000`, :91 | ab1wB `StackStore_Alloc +0x78` |
| `StackStore_Alloc` | +0x84 | 0xfffff | lui-in-section | CERTIFIED (store) | stores into integers: amo add into `atomic_uint32_t stored_`, and `*pack` (uptr) | binary: `amoadd.w.rl` data (+0x9c, +0xd0; .debug_line sanitizer_atomic_clang.h:58, inside Stored()) into blocks_[i] + 8; `sd` into *pack (+0xcc, +0xf0; .debug_line sanitizer_stack_store.cpp:95-96; pack = 3rd parameter of `AllocEmPmS1_`, unsigned long*); a7 at `jal BlockInfo::Create` is not a parameter | U sanitizer_stack_store.h:88-91 (`atomic_uintptr_t data_; ...; atomic_uint32_t stored_;`), :76; U sanitizer_stack_store.cpp:92-96, :374-376 | ab1wB `StackStore_Alloc +0x84` |
| `StackDepotBase_Put` | +0x104 | 0x400010 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offset +0x400010 (nodes.map1_) from `this` (incoming a0) + a runtime index | binary: `ld` bases (+0x134, +0x1e0; .debug_line sanitizer_atomic_clang.h:43, atomic_load) = incoming a0 + index + 0x400010 in both images | U sanitizer_stackdepotbase.h:73 `TwoLevelMap<Node, kNodesSize1, kNodesSize2> nodes`; U sanitizer_flat_map.h:121-124, :155 `atomic_uintptr_t map1_[kSize1]` | ab1wB `StackDepotBase_Put +0x104` |
| `StackDepotBase_Put` | +0x114 | 0x400008 | lui-in-section | CERTIFIED (iii) offset from an argument base | `this` of TwoLevelMap::Create = incoming a0 + 0x400008 = &nodes | binary: a0 of `jal ...TwoLevelMap...6CreateEm` (+0x168, +0x27c) = incoming a0 + 0x400008 in both images; a3 at `jal lock` (+0x17c) is not a parameter (static `lock(atomic_uint32_t *p)`) | U sanitizer_stackdepotbase.h:67, :73; U sanitizer_flat_map.h:143 | ab1wB `StackDepotBase_Put +0x114` |
| `StackDepotBase_Put` | +0x1b0 | 0x400000 | lui-in-section | CERTIFIED (iii) offset from an argument base | amo base = incoming a0 + 0x400000 = &n_uniq_ids | binary: `amoadd.w a0,a1,(a0)` (+0x1bc; .debug_line sanitizer_atomic_clang.h:58) base = incoming a0 + 0x400000 in both images | U sanitizer_stackdepotbase.h:71 `atomic_uint32_t n_uniq_ids`, :139 | ab1wB `StackDepotBase_Put +0x1b0` |
| `StackDepotBase_Get` | +0x30 | 0x400010 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | load base theDepot+0x400010 + a runtime index (nodes.map1_[i]) | binary: `ld` bases (+0x3c, +0x48) = auipc theDepot + 0x400010 + index in both images | U sanitizer_stackdepot.cpp:58 `static StackDepot theDepot`, :214-215 | ab1wB `StackDepotGet +0x30` |
| `StackDepotBase_Get` | +0xc8 | 0x400008 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | `this` of TwoLevelMap::Create = theDepot+0x400008 | binary: a0 of `jal ...TwoLevelMap...6CreateEm` (+0xd0) = theDepot+0x400008 in both images | U sanitizer_stackdepot.cpp:58; U sanitizer_flat_map.h:143 | ab1wB `StackDepotGet +0xc8` |
| `StackDepotBase_lock_bucket_spin_lock` | +0x84 | 0xfffff | lui-in-section | CERTIFIED (i) call argument | MmapOrDie `size` (uptr), used only as a length (ruling (b)) | binary: a0 of `jal MmapOrDie` (+0xa0; DWARF call site sanitizer_common.h:90); the value is the round-up mask of RoundUpTo | U sanitizer_common.h:90; P sanitizer_posix.cpp:48-56 (as InitializeAsanInterceptors +0x44); U sanitizer_flat_map.h:117-118, :147 `MmapOrDie(MmapSize(), "TwoLevelMap")` | ab1wB `TwoLevelMap_StackDepotNode_Create +0x84` |
| `sysconf` | +0xe8 | 0x31000 | lui-in-section | CERTIFIED (ii) return value | returned by `long sysconf(int)`: 200809, an integer, not an address | binary: `addiw a0,a2,105` -> a0 = 0x31069, then the jump table (0x212f8, 13 entries) reaches `ret` (+0xc0) with it; a2 at `jal getauxval` / `jal sysinfo` is not a parameter; DWARF: the call site of sysconf in the runtime declares it in the toolchain image's musl sysroot (usr/include/unistd.h:133) | M include/unistd.h:133 `long sysconf(int);`, :217 `#define _POSIX_VERSION 200809L`; M src/conf/sysconf.c:190-191 `case VER & 255: return _POSIX_VERSION;` | ab1wB `sysconf +0xe8` |
| `sysconf` | +0xf0 | 0x31069 | lui-in-section | CERTIFIED (ii) return value | as +0xe8 (this word builds the returned 0x31069) | binary: as +0xe8 | M as +0xe8 | ab1wB `sysconf +0xf0` |
| `sysconf` | +0x214 | 0x20000 | lui-in-section | CERTIFIED (ii) return value | returned by `long sysconf(int)`: ARG_MAX 131072, an integer, not an address | binary: `lui a0,0x20` (+0x214) reaches `ret` (+0xc0) in a0 in both images; a0 at `jal __stack_chk_fail` is not a parameter (void) | M include/unistd.h:133 `long sysconf(int);`; M src/conf/sysconf.c:31 `[_SC_ARG_MAX] = JT_ARG_MAX`, :192-193 `case JT_ARG_MAX & 255: return ARG_MAX;`; M include/limits.h:49 `#define ARG_MAX 131072` | new here |
| `init_tls` | +0x158 | 0x200d1 | lui-in-section | CERTIFIED (d) compare only | every use on every path is a compare: `bltu a1,a3` (+0x16c), the TLS-size check | binary: `lui a1,0x20; addiw a3,a1,209` = 0x200d1 in both images; the only use is `bltu a1,a3` (size < 0x200d1, i.e. size <= sizeof builtin_tls = 0x200d0) | P(musl) src/env/__init_tls.c:154 `if (libc.tls_size > sizeof builtin_tls) {` (musl f21a9653 + patches 0001, 0003; :47 `BUILTIN_TLS_SPACE 131072`, :51-55 struct builtin_tls) | new here |
| `printf_core` | +0x84 | 0x12889 | lui-in-section | CERTIFIED (d) compare only | every use on every path is a compare: FLAGMASK, spilled to the frame; every reload feeds `and` and then `beqz` / `bnez`; registers live at calls are beyond the callees' parameters | binary: `lui a1,0x13; addiw a1,a1,-1911` = 0x12889 in both images; `sd a1,80(sp)` (+0x88); `and` (+0x1a8, +0x1d4) -> `beqz` / `bnez`; a4 / a5 live at __fwritex (3 parameters), pop_arg (3), __errno_location (0), strnlen (2), wctomb (2), memset (3), __stack_chk_fail (0): not passed | M src/stdio/vfprintf.c:22-29 (`FLAGMASK (ALT_FORM\|ZERO_PAD\|LEFT_ADJ\|PAD_POS\|MARK_POS\|GROUPED)` = 0x12889), :474 `for (fl=0; (unsigned)*s-' '<32 && (FLAGMASK&(1U<<*s-' ')); s++)` | new here |
| `fmt_fp` | +0x670 | 0x24000 | lui-in-section | CERTIFIED (e) frame base + CERTIFIED (ii) return value + CERTIFIED (i) call argument | the 9 load / store bases it enters are frame bases (ruling (e): the base's only pointer root is sp on every path; integer constants added to it, including a lui-built frame offset, are offsets, not pointers; no auipc / lui / section-built pointer appears anywhere in the base chain); also the returned int, memset `n`, __fwritex `l` and pad `w` (lengths) | binary: rootcheck.py (fmt_fp prototype: a1-a7 integers) finds that every value reaching the bases at +0xa90, +0xb04, +0xde0, +0xe0c, +0xe30, +0xe38, +0xe44, +0xec4, +0xf24 has the single pointer root sp, on every path, in both images (the VLA: `sub s6,sp,a0` at +0x94, stack probe, `mv sp,s6`); the integer constants in the chains (frame offsets from sp, e.g. -0x25c ... -0x1f0c, and the index from this 0x24000 after its division by 9) are offsets; the lui values of fmt_fp that lie in a section (0x24000; 0x12000 at +0x398 / +0xa20 / +0x10f8) never reach a base as a pointer, and no auipc pointer does (no `saddr` / `pc` root, no `mix`). Other uses: a0 at `ret` (+0x474, int), a2 of `jal memset` (+0x1138, +0x11f0, +0x1660), a1 of `jal __fwritex` (+0x1194 ... +0x16b0), a2 of `jal pad` (+0x14e0, +0x1624); spills to its own frame (reloads traced); registers live at __floatsitf(int) / __stack_chk_fail(void) beyond their parameters | M src/stdio/vfprintf.c:181 `static int fmt_fp(FILE *f, long double y, int w, int p, int fl, int t, int ps)`, :190 `uint32_t big[bufsize]`, :314-315 `((j+9*LDBL_MAX_EXP)/9 - LDBL_MAX_EXP)`, `j += 9*LDBL_MAX_EXP` (0x24000 = 9 * 16384); :138-146 pad (w only in `l >= w`, `l = w - l`); M src/internal/stdio_impl.h:78 `size_t __fwritex(const unsigned char *, size_t, FILE *)`; M include/string.h:29 memset | ab1wB `fmt_fp +0x670` |
| `SizeClassAllocator64_GetFromAllocator` | +0x1b4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `SizeClassAllocator64_GetFromAllocator +0x1b4` |
| `asan_register_globals_impl_RegisterGlobal_loop` | +0xb2c | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `asan_register_globals_impl_RegisterGlobal_loop +0xb2c` |
| `asan_unregister_globals_impl` | +0x3fc | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `asan_unregister_globals_impl +0x3fc` |
| `asan_UnpoisonBeforeMain_ctor` | +0x134 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `asan_UnpoisonBeforeMain_ctor +0x134` |
| `asan_before_dynamic_init_asan_after_dynamic_init` | +0x1d4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `asan_before_dynamic_init_asan_after_dynamic_init +0x1d4` |
| `AsanStats_Clear_ctor` | +0x170 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `AsanStats_Clear_ctor +0x170` |
| `InternalAlloc_RawInternalAlloc` | +0x150 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `GetAsanThreadContext +0x150` |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0x80 | 0x20000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use is `bltu` (a size limit) | binary: uses listed below | - | ab1wB `InternalAllocator_CombinedAllocator_Allocate_int +0x80` |
| `ThreadRegistry_CreateThread` | +0x21c | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `ThreadRegistry_CreateThread +0x21c` |
| `ThreadRegistry_StartThread` | +0x1a4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `ThreadRegistry_StartThread +0x1a4` |
| `StackStore_Store_BlockInfo_helper` | +0xb0 | 0x100000 | lui-const (dataflow) | CERTIFIED (store) | store into the integer `*pack` (uptr) | binary: `xor` with 0x100000, `seqz`, `add` to *pack, `sd a0,0(s0)` (+0xd4; .debug_line sanitizer_stack_store.cpp:52; pack = 2nd parameter of `StoreERKNS_10StackTraceEPm`, unsigned long*) | U sanitizer_stack_store.cpp:40, :52 `*pack += blocks_[GetBlockIdx(idx)].Stored(h.size + 1)`, :374-376 | ab1wB `StackStore_Store_BlockInfo_helper +0xb0` |
| `lsan_register_root_region` | +0x1dc | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `lsan_register_root_region +0x1dc` |
| `lsan_unregister_root_region` | +0x248 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - | ab1wB `lsan_unregister_root_region +0x248` |
| `open` | +0x48 | 0x410000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - | ab1wB `open +0x48` |
| `libc_malloc_impl` | +0x64 | 0x1ffec | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - | ab1wB `libc_malloc_impl +0x64` |
| `printf_core` | +0x994 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`); it is also spilled to its own frame slot, and every reload is used only by compares | binary: uses listed below | - | ab1wB `printf_core +0x994` |
| `pad` | +0x30 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - | ab1wB `pad +0x30` |
| `fmt_fp` | +0x398 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - | ab1wB `fmt_fp +0x398` |
| `fmt_fp` | +0xa20 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - | ab1wB `fmt_fp +0xa20` |
| `fmt_fp` | +0x10f8 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`); it is also spilled to its own frame slot, and every reload is used only by compares | binary: uses listed below | - | ab1wB `fmt_fp +0x10f8` |

### Every use of every value (the same in both images)

One line per use site (offset in the row, instruction, role, linear / non-linear). A register live at a call is
marked with the parameter it is, or "not a parameter". Each use's `.debug_line` row and each call's DWARF callee is
the same in both images.

**`QuarantineCache_MergeBatches_Transfer` +0x74** (lui-in-section; `_ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_`; word lui a4,0x190):

- +0x7c `mul a4,a6,a4` alu mul [linear]
- +0x84 `bgeu a5,a4,0x33188` branch [non-linear]
- +0xa4 `jal 0x332b0` live-in-a4-at-call [non-linear]: _ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE12MergeBatchesEPS3_, not a parameter

**`SizeClassAllocator64_EnsureFreeArraySpace` +0x2c** (lui-in-section; `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm`; word addiw a3,a3,-1):

- +0x30 `add a3,a5,a3` add [linear]
- +0x38 `and s0,a3,s0` alu and [linear]
- +0x44 `bgeu s0,a3,0x342d4` branch [non-linear]
- +0x6c `add a2,s0,a2` add [non-linear]
- +0x7c `bgeu a0,a2,0x342ac` branch [non-linear]
- +0x88 `sub s2,s0,a4` sub [non-linear]
- +0x9c `jal 0x6e0b8` live-in-a2-at-call [non-linear]: _ZN11__sanitizer20ReservedAddressRange3MapEmmPKc, parameter `size`
- +0xb8 `jal 0x537d0` live-in-a1-at-call [non-linear]: _ZN6__asan12PoisonShadowEmmh, parameter `size`
- +0xc8 `add a1,a1,s2` add [non-linear]
- +0xd4 `sd a1,80(a0)` store-data [non-linear]
- +0xdc `sd s0,24(a1)` store-data [non-linear]
- +0x120 `jal 0x6b670` live-in-a3-at-call [non-linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, parameter `v1`

**`LargeMmapAllocator_Allocate` +0x430** (lui-in-section; `_ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`; word lui a4,0x100):

- +0x434 `jal 0x6b670` live-in-a4-at-call [linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, parameter `v2`

**`LargeMmapAllocator_Allocate` +0x448** (lui-in-section; `_ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`; word lui a2,0x20):

- +0x458 `jal 0x6e204` live-in-a2-at-call [linear]: _ZN11__sanitizer20ReservedAddressRange8MapOrDieEmmPKc, parameter `size`

**`SizeClassAllocator64_PopulateFreeArray` +0xb0** (lui-in-section; `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm`; word lui s3,0x40):

- +0xbc `add s3,a1,s3` add [linear]
- +0xcc `add a3,a3,s3` add [linear]
- +0xd4 `bgeu a3,a1,0x36794` branch [linear]
- +0xf0 `add s4,s4,s3` add [linear]
- +0x100 `bgeu a2,s4,0x36668` branch [linear]
- +0x11c `jal 0x6e0b8` live-in-a2-at-call [linear]: _ZN11__sanitizer20ReservedAddressRange3MapEmmPKc, parameter `size`
- +0x138 `jal 0x537d0` live-in-a1-at-call [linear]: _ZN6__asan12PoisonShadowEmmh, parameter `size`
- +0x14c `add a2,a2,s3` add [linear]
- +0x154 `sd a2,80(a0)` store-data [linear]
- +0x160 `amoadd.d zero,s3,(s1)` amo-data(amoadd.d) [linear]
- +0x16c `add s4,s4,s3` add [linear]
- +0x170 `sd s4,48(s0)` store-data [linear]
- +0x178 `sub s4,s4,a3` sub [linear]
- +0x17c `divu s3,s4,s5` alu divu [linear]
- +0x180 `add s1,s1,s3` add [non-linear]
- +0x190 `jal 0x341d0` live-in-a3-at-call [non-linear]: _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm, parameter `num_freed_chunks`
- +0x19c `bltu s4,s5,0x366e8` branch [linear]
- +0x1b0 `slli s1,s1,0x2` alu slli [non-linear]
- +0x1b4 `add a1,a1,s1` add [non-linear]
- +0x1cc `add a5,a1,a5` add [non-linear]
- +0x1d0 `sw a4,0(a5)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly
- +0x1d8 `bltu a0,s3,0x366c8` branch [non-linear]
- +0x1e0 `mul a1,s3,s5` alu mul [non-linear]
- +0x1e8 `add a3,a3,a1` add [non-linear]
- +0x1ec `add a0,a0,s3` add [non-linear]
- +0x1f0 `sd a0,16(s0)` store-data [non-linear]
- +0x1f4 `sd a3,32(s0)` store-data [non-linear]
- +0x1f8 `bltu a4,a3,0x367a4` branch [non-linear]
- +0x2ac `jal 0x6b670` live-in-a3-at-call [non-linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, parameter `v1`
- +0x2ac `jal 0x6b670` live-in-a5-at-call [non-linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, not a parameter
- +0x2c4 `jal 0x6b670` live-in-a5-at-call [non-linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, not a parameter
- +0x2e8 `jal 0x66ce8` live-in-a3-at-call [linear]: _ZN11__sanitizer6PrintfEPKcz, Printf variadic slot 3

**`AsanDeactivate_activation_CHECK_helper` +0x8c** (lui-in-section; `_ZN6__asan14AsanDeactivateEv`; word addi a0,a0,16):

- +0x90 `sw a0,8(sp)` spill to sp-40 [linear]

**`InitializeAsanInterceptors` +0x44** (lui-in-section; `_ZN6__asan26InitializeAsanInterceptorsEv`; word addiw a0,a2,-1240):

- +0x4c `jal 0x65838` live-in-a0-at-call [linear]: _ZN11__sanitizer9MmapOrDieEmPKcb, parameter `size`

**`ReserveShadowMemoryRanges_sealed_early_shadow_re` +0x74** (lui-in-section; `_ZN6__asan19SealedReserveShadowEv`; word addiw a3,a0,34):

- +0x88 `jal 0x64168` live-in-a3-at-call [linear]: _ZN11__sanitizer13internal_mmapEPvmiiiy, parameter `flags`

**`ReserveShadowMemoryRanges_sealed_early_shadow_re` +0xfc** (lui-in-section; `_ZN6__asan19SealedReserveShadowEv`; word addiw s0,a0,34):

- +0x118 `jal 0x64168` live-in-a3-at-call [linear]: _ZN11__sanitizer13internal_mmapEPvmiiiy, parameter `flags`
- +0x164 `jal 0x64168` live-in-a3-at-call [linear]: _ZN11__sanitizer13internal_mmapEPvmiiiy, parameter `flags`

**`InitializeShadowMemory` +0x1b0** (lui-in-section; `_ZN6__asan22InitializeShadowMemoryEv`; word lui a3,0x40):

- +0x1c0 `jal 0x6bfa4` live-in-a3-at-call [linear]: _ZN11__sanitizer10ProtectGapEmmmm, parameter `zero_base_max_shadow_start`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0x88** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word addiw a0,a1,8):

- +0x8c `add a0,s1,a0` add [linear]
- +0x98 `jal 0x63968` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0xa4** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word lui a2,0x40):

- +0xb0 `jal 0x63968` live-in-a2-at-call [linear]: __sanitizer_internal_memset, parameter `n`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0xb4** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word addiw a0,s3,64):

- +0xb8 `add a0,s1,a0` add [linear]
- +0xc8 `jal 0x63968` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0xcc** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word lui s2,0x41):

- +0xd0 `addiw a0,s2,-576` alu addiw [linear]
- +0xd4 `add a0,s1,a0` add [linear]
- +0xe0 `jal 0x63968` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`
- +0xfc `add a1,s1,s2` add [linear]
- +0x100 `addiw a2,s2,-560` alu addiw [linear]
- +0x104 `add a2,s1,a2` add [linear]
- +0x10c `sd a0,-576(a1)` BASE [linear]: absolute: abs:_ZN11__sanitizerL26internal_alloc_placeholderE+0x40dc0
- +0x110 `sd a2,-568(a1)` BASE [linear]: absolute: abs:_ZN11__sanitizerL26internal_alloc_placeholderE+0x40dc8
- +0x110 `sd a2,-568(a1)` store-data [linear]
- +0x144 `ret` return a1 [linear]

**`InternalFree_LowLevelAllocator_free_to_freelist` +0xd0** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word addiw a0,s2,-576):

- +0xd4 `add a0,s1,a0` add [linear]
- +0xe0 `jal 0x63968` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0xd8** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word addiw a2,s3,584):

- +0xe0 `jal 0x63968` live-in-a2-at-call [linear]: __sanitizer_internal_memset, parameter `n`

**`InternalFree_LowLevelAllocator_free_to_freelist` +0x100** (lui-in-section; `_ZN11__sanitizer18internal_allocatorEv`; word addiw a2,s2,-560):

- +0x104 `add a2,s1,a2` add [linear]
- +0x110 `sd a2,-568(a1)` store-data [linear]

**`InternalAllocator_CombinedAllocator_Allocate_int` +0xa8** (lui-in-section; `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE8AllocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEmm`; word addiw a1,a1,-576):

- +0xb0 `add a4,a0,a1` add [linear]
- +0xc0 `jal 0x5e68c` live-in-a0-at-call [linear]: _ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm, parameter `this`
- +0xc0 `jal 0x5e68c` live-in-a4-at-call [linear]: _ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm, not a parameter

**`InternalAllocator_CombinedAllocator_Allocate_int` +0xac** (lui-in-section; `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE8AllocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEmm`; word addiw a5,a4,8):

- +0xb4 `add a1,a0,a5` add [linear]
- +0xc0 `jal 0x5e68c` live-in-a1-at-call [linear]: _ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm, parameter `stat`
- +0xc0 `jal 0x5e68c` live-in-a5-at-call [linear]: _ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm, not a parameter

**`InternalAllocator_LargeMmapAllocator_Allocate` +0x118** (lui-in-section; `_ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`; word addiw a1,a1,16):

- +0x11c `add s3,s1,a1` add [linear]
- +0x120 `addi a1,s3,560` addi [linear]
- +0x124 `andi a3,a1,-4` align andi -4 [linear]
- +0x12c `lr.w.aq a5,zero,(a3)` BASE(lr.w.aq) [linear]: object base in:a0, offset 0x40240
- +0x140 `sc.w a6,a6,(a3)` BASE(sc.w) [linear]: object base in:a0, offset 0x40240
- +0x150 `ld a3,0(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x160 `ld a4,16(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x164 `ld a5,32(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x168 `ld a1,40(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x230 `sd a7,0(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x234 `sb zero,8(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x238 `sd a4,16(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x23c `sd a3,32(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x264 `sd a1,40(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x27c `sb zero,560(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x390 `jal 0x656e4` live-in-a0-at-call [linear]: _ZN11__sanitizer15StaticSpinMutex8LockSlowEv, parameter `this`
- +0x390 `jal 0x656e4` live-in-a1-at-call [linear]: _ZN11__sanitizer15StaticSpinMutex8LockSlowEv, not a parameter
- +0x390 `jal 0x656e4` live-in-a3-at-call [linear]: _ZN11__sanitizer15StaticSpinMutex8LockSlowEv, not a parameter
- +0x398 `ld a3,0(s3)` BASE [linear]: object base in:a0, offset 0x40010

**`InternalAllocator_LargeMmapAllocator_Allocate` +0x24c** (lui-in-section; `_ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`; word lui a3,0x40):

- +0x250 `add a3,s1,a3` add [linear]
- +0x254 `add a2,a3,a2` add [linear]
- +0x258 `ld a3,64(a2)` BASE [linear]: object base in:a0+op:+0x248, offset 0x40000
- +0x268 `sd a3,64(a2)` BASE [linear]: object base in:a0+op:+0x248, offset 0x40000

**`internal_usleep_internal_sleep_nanosleep` +0x14** (lui-in-section; `_ZN11__sanitizer15internal_usleepEy`; word addiw a2,a2,576):

- +0x20 `mul a1,a4,a2` alu mul [linear]
- +0x24 `sub a0,a0,a1` sub [non-linear]
- +0x2c `mul a0,a0,a3` alu mul [non-linear]
- +0x38 `sd a0,8(sp)` spill to sp-8 [non-linear]

**`ReadLongProcessName_proc_self_cmdline` +0x40** (lui-in-section; `_ZN11__sanitizer19ReadLongProcessNameEPcm`; word lui a4,0x100):

- +0x48 `jal 0x60cac` live-in-a4-at-call [linear]: _ZN11__sanitizer16ReadFileToBufferEPKcPPcPmS4_mPi, parameter `max_len`

**`GetNamedMappingFd_MmapNamed` +0x90** (lui-in-section; `_ZN11__sanitizer17GetNamedMappingFdEPKcmPi`; word addiw a1,a1,578):

- +0x98 `jal 0x641c8` live-in-a1-at-call [linear]: _ZN11__sanitizer13internal_openEPKcij, parameter `flags`

**`MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` +0xec** (lui-in-section; `_ZN11__sanitizerL23SealedRepairReservationEmm` at row +0x74; word addiw a3,a0,34):

- +0x104 `jal 0x64168` live-in-a3-at-call [linear]: _ZN11__sanitizer13internal_mmapEPvmiiiy, parameter `flags`

**`StackStore_Alloc` +0x78** (lui-in-section; `_ZN11__sanitizer10StackStore5AllocEmPmS1_`; word lui a4,0x100):

- +0x7c `bltu a4,a5,0x700f0` branch [linear]
- +0x84 `addiw a7,a4,-1` alu addiw [linear]
- +0x88 `and t2,s0,a7` alu and [linear]
- +0x90 `sub t2,a4,t2` sub [non-linear]
- +0x90 `sub t2,a4,t2` sub [linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [non-linear]
- +0xa8 `sub t3,a5,t2` sub [linear]
- +0xa8 `sub t3,a5,t2` sub [non-linear]
- +0xb4 `add t0,t2,t0` add [linear]
- +0xb4 `add t0,t2,t0` add [non-linear]
- +0xc0 `xor t0,t0,a4` alu xor [linear]
- +0xc0 `xor t0,t0,a4` alu xor [non-linear]
- +0xc4 `seqz t0,t0` alu seqz [non-linear]
- +0xc8 `add t0,t2,t0` add [non-linear]
- +0xcc `sd t0,0(a3)` store-data [non-linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [non-linear]
- +0xe0 `add t0,t3,t0` add [linear]
- +0xe0 `add t0,t3,t0` add [non-linear]
- +0xe4 `xor t0,t0,a4` alu xor [linear]
- +0xe4 `xor t0,t0,a4` alu xor [non-linear]
- +0xe8 `seqz t0,t0` alu seqz [non-linear]
- +0xec `add t0,t1,t0` add [non-linear]
- +0xf0 `sd t0,0(a3)` store-data [non-linear]
- +0x110 `jal 0x709c0` live-in-a4-at-call [linear]: _ZN11__sanitizer10StackStore9BlockInfo6CreateEPS0_, not a parameter
- +0x110 `jal 0x709c0` live-in-a7-at-call [linear]: _ZN11__sanitizer10StackStore9BlockInfo6CreateEPS0_, not a parameter
- +0x130 `jal 0x6b670` live-in-a4-at-call [linear]: _ZN11__sanitizer11CheckFailedEPKciS1_yy, parameter `v2`

**`StackStore_Alloc` +0x84** (lui-in-section; `_ZN11__sanitizer10StackStore5AllocEmPmS1_`; word addiw a7,a4,-1):

- +0x88 `and t2,s0,a7` alu and [linear]
- +0x90 `sub t2,a4,t2` sub [non-linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [non-linear]
- +0xa8 `sub t3,a5,t2` sub [non-linear]
- +0xb4 `add t0,t2,t0` add [non-linear]
- +0xc0 `xor t0,t0,a4` alu xor [non-linear]
- +0xc4 `seqz t0,t0` alu seqz [non-linear]
- +0xc8 `add t0,t2,t0` add [non-linear]
- +0xcc `sd t0,0(a3)` store-data [non-linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [non-linear]
- +0xe0 `add t0,t3,t0` add [non-linear]
- +0xe4 `xor t0,t0,a4` alu xor [non-linear]
- +0xe8 `seqz t0,t0` alu seqz [non-linear]
- +0xec `add t0,t1,t0` add [non-linear]
- +0xf0 `sd t0,0(a3)` store-data [non-linear]
- +0x110 `jal 0x709c0` live-in-a7-at-call [linear]: _ZN11__sanitizer10StackStore9BlockInfo6CreateEPS0_, not a parameter

**`StackDepotBase_Put` +0x104** (lui-in-section; `_ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb`; word addiw s8,a3,16):

- +0x108 `add s8,s1,s8` add [linear]
- +0x130 `add a2,s8,a2` add [linear]
- +0x134 `ld a2,0(a2)` BASE [linear]: object base in:a0+op:+0x12c, offset 0x400010
- +0x1dc `add a0,s8,a0` add [linear]
- +0x1e0 `ld a0,0(a0)` BASE [linear]: object base in:a0+op:+0x1d8, offset 0x400010

**`StackDepotBase_Put` +0x114** (lui-in-section; `_ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb`; word addiw a3,a3,8):

- +0x118 `add s4,s1,a3` add [linear]
- +0x168 `jal 0x72cd4` live-in-a0-at-call [linear]: _ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm, parameter `this`
- +0x168 `jal 0x72cd4` live-in-a3-at-call [linear]: _ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm, not a parameter
- +0x17c `jal 0x72c44` live-in-a3-at-call [linear]: _ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE4lockEPNS_15atomic_uint32_tE, not a parameter
- +0x27c `jal 0x72cd4` live-in-a0-at-call [linear]: _ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm, parameter `this`

**`StackDepotBase_Put` +0x1b0** (lui-in-section; `_ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb`; word lui a0,0x400):

- +0x1b4 `add a0,s1,a0` add [linear]
- +0x1bc `amoadd.w a0,a1,(a0)` BASE(amoadd.w) [linear]: object base in:a0, offset 0x400000

**`StackDepotBase_Get` +0x30** (lui-in-section; `_ZN11__sanitizer13StackDepotGetEj`; word addiw a3,a3,16):

- +0x34 `add a0,a2,a3` add [linear]
- +0x38 `add a0,a0,a4` add [linear]
- +0x3c `ld a3,0(a0)` BASE [linear]: absolute: abs:_ZN11__sanitizerL8theDepotE+0x400010 + runtime op:+0x28
- +0x48 `ld a0,0(a0)` BASE [linear]: absolute: abs:_ZN11__sanitizerL8theDepotE+0x400010 + runtime op:+0x28

**`StackDepotBase_Get` +0xc8** (lui-in-section; `_ZN11__sanitizer13StackDepotGetEj`; word addiw a0,a0,8):

- +0xcc `add a0,a2,a0` add [linear]
- +0xd0 `jal 0x72cd4` live-in-a0-at-call [linear]: _ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm, parameter `this`

**`StackDepotBase_lock_bucket_spin_lock` +0x84** (lui-in-section; `_ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm`; word addiw a1,a1,-1):

- +0x88 `add a1,a0,a1` add [linear]
- +0x90 `and a0,a1,a0` alu and [linear]
- +0xa0 `jal 0x65838` live-in-a0-at-call [non-linear]: _ZN11__sanitizer9MmapOrDieEmPKcb, parameter `size`

**`sysconf` +0xe8** (lui-in-section; `sysconf`; word lui a2,0x31):

- +0xc0 `ret` return a0 [non-linear]
- +0xc0 `ret` return a0 [linear]
- +0xf0 `addiw a0,a2,105` alu addiw [linear]
- +0x108 `jal 0x916ec` live-in-a2-at-call [linear]: __getauxval, not a parameter
- +0x13c `jal 0x8dd30` live-in-a2-at-call [linear]: __lsysinfo, not a parameter
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [non-linear]: __stack_chk_fail, not a parameter
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [linear]: __stack_chk_fail, not a parameter

**`sysconf` +0xf0** (lui-in-section; `sysconf`; word addiw a0,a2,105):

- +0xc0 `ret` return a0 [non-linear]
- +0xc0 `ret` return a0 [linear]
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [non-linear]: __stack_chk_fail, not a parameter
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [linear]: __stack_chk_fail, not a parameter

**`sysconf` +0x214** (lui-in-section; `sysconf`; word lui a0,0x20):

- +0xc0 `ret` return a0 [non-linear]
- +0xc0 `ret` return a0 [linear]
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [non-linear]: __stack_chk_fail, not a parameter
- +0x224 `jal 0x8d2f0` live-in-a0-at-call [linear]: __stack_chk_fail, not a parameter

**`init_tls` +0x158** (lui-in-section; `__init_tls`; word addiw a3,a1,209):

- +0x16c `bltu a1,a3,0x8d180` branch [linear]

**`printf_core` +0x84** (lui-in-section; `printf_core`; word addiw a1,a1,-1911):

- +0x88 `sd a1,80(sp)` spill to sp-464 [linear]
- +0x144 `jal 0x936d0` live-in-a4-at-call [non-linear]: __fwritex, not a parameter
- +0x1a8 `and a4,a3,t0` alu and [linear]
- +0x1b4 `beqz a4,0x93e60` branch [non-linear]
- +0x1d4 `and a5,a3,t0` alu and [linear]
- +0x1dc `bnez a5,0x93e3c` branch [non-linear]
- +0x4d8 `jal 0x94ab0` live-in-a4-at-call [non-linear]: pop_arg, not a parameter
- +0x5f4 `jal 0x8d2f8` live-in-a4-at-call [non-linear]: ___errno_location, not a parameter
- +0x614 `jal 0x418f4` live-in-a4-at-call [non-linear]: __interceptor_trampoline_strnlen, not a parameter
- +0x7c8 `jal 0x4193c` live-in-a4-at-call [non-linear]: __interceptor_trampoline_wctomb, not a parameter
- +0x9cc `jal 0x515d4` live-in-a4-at-call [non-linear]: __interceptor_trampoline_memset, not a parameter
- +0xa3c `jal 0x936d0` live-in-a4-at-call [non-linear]: __fwritex, not a parameter
- +0xa70 `jal 0x515d4` live-in-a4-at-call [non-linear]: __interceptor_trampoline_memset, not a parameter
- +0xaf4 `jal 0x515d4` live-in-a4-at-call [non-linear]: __interceptor_trampoline_memset, not a parameter
- +0xb64 `jal 0x936d0` live-in-a4-at-call [non-linear]: __fwritex, not a parameter
- +0xb98 `jal 0x515d4` live-in-a4-at-call [non-linear]: __interceptor_trampoline_memset, not a parameter
- +0xc78 `jal 0x8d2f8` live-in-a4-at-call [non-linear]: ___errno_location, not a parameter
- +0xc78 `jal 0x8d2f8` live-in-a5-at-call [non-linear]: ___errno_location, not a parameter
- +0xcac `jal 0x94ab0` live-in-a4-at-call [non-linear]: pop_arg, not a parameter
- +0xdcc `jal 0x8d2f8` live-in-a4-at-call [non-linear]: ___errno_location, not a parameter
- +0xdcc `jal 0x8d2f8` live-in-a5-at-call [non-linear]: ___errno_location, not a parameter
- +0xe2c `jal 0x8d2f0` live-in-a4-at-call [non-linear]: __stack_chk_fail, not a parameter

**`fmt_fp` +0x670** (lui-in-section; `fmt_fp`; word lui a1,0x24):

- +0x474 `ret` return a0 [non-linear]; +0x67c `addw a0,a0,a1` alu addw [linear]; +0x688 `mul a1,a0,a1` alu mul [non-linear]; +0x68c `srli a2,a1,0x3f` alu srli [non-linear]; +0x690 `srai a1,a1,0x21` alu srai [non-linear]; +0x694 `add a1,a1,a2` add [non-linear]; +0x698 `slli a2,a1,0x2` alu slli [non-linear]; +0x69c `slli a3,a1,0x3` alu slli [non-linear]; +0x6a0 `add a4,s6,a2` add [non-linear]; +0x6a4 `add a1,a3,a1` add [non-linear]; +0x6a8 `addi s2,a4,4` addi [non-linear]; +0x6ac `subw a0,a0,a1` alu subw [non-linear]; +0x6b4 `add a2,a4,s10` add [non-linear]; +0x6b8 `blt a1,a0,0x95740` branch [non-linear]; +0x6bc `addi a0,a0,-8` addi [non-linear]; +0x6c8 `addiw a0,a0,1` alu addiw [non-linear]; +0x6d0 `bnez a0,0x95380` branch [non-linear]; +0xa8c `sd a2,-504(s0)` spill to sp-504 [non-linear]; +0xa90 `lw s8,0(a2)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xaa0 `add s10,s2,s10` add [non-linear]; +0xaa8 `bne s10,s11,0x95774` branch [non-linear]; +0xabc `sd a4,-520(s0)` spill to sp-520 [non-linear]; +0xac4 `jal 0x90ba0` live-in-a2-at-call [non-linear]: __floatsitf, not a parameter; +0xac4 `jal 0x90ba0` live-in-a3-at-call [non-linear]: __floatsitf, not a parameter; +0xac4 `jal 0x90ba0` live-in-a4-at-call [non-linear]: __floatsitf, not a parameter; +0xaf8 `bgeu s1,a0,0x957ec` branch [non-linear]; +0xb00 `add a0,s2,a0` add [non-linear]; +0xb04 `lbu a0,-4(a0)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xd48 `bne s10,s11,0x95a10` branch [non-linear]; +0xde0 `sw s2,0(s7)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xe0c `sw a0,0(s7)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xe1c `add a0,a2,a0` add [non-linear]; +0xe30 `lw a2,0(a0)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xe38 `sw a2,0(a0)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xe3c `addi a0,a0,-4` addi [non-linear]; +0xe44 `sw zero,4(a0)` BASE [non-linear]: REFUSE: the lui value enters this address non-linearly; +0xe48 `bgeu a0,s1,0x95ae8` branch [non-linear]; +0xe74 `addi s7,a0,4` addi [non-linear]; +0xea4 `addi a0,s7,4` addi [non-linear]; +0xea8 `bltu a0,s11,0x95b68` branch [non-linear]; ... (106 more sites of the same kinds)

**`SizeClassAllocator64_GetFromAllocator` +0x1b4** (lui-const (dataflow); `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16GetFromAllocatorEPNS_14AllocatorStatsEmPjm`; word addi a1,a1,-1):

- +0x1c0 `slli a6,a1,0x28` alu slli [linear]
- +0x1f8 `and a1,a2,a6` alu and [linear]
- +0x1fc `beqz a1,0x36424` branch [non-linear]
- +0x25c `jal 0x657f4` live-in-a6-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`asan_register_globals_impl_RegisterGlobal_loop` +0xb2c** (lui-const (dataflow); `__asan_register_globals`; word addi a1,a1,-1):

- +0xb38 `slli a5,a1,0x28` alu slli [linear]
- +0xb6c `and a1,a0,a5` alu and [linear]
- +0xb70 `beqz a1,0x3efd8` branch [non-linear]
- +0xbdc `jal 0x657f4` live-in-a5-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`asan_unregister_globals_impl` +0x3fc** (lui-const (dataflow); `__asan_unregister_globals`; word addi a1,a1,-1):

- +0x408 `slli a5,a1,0x28` alu slli [linear]
- +0x43c `and a1,a0,a5` alu and [linear]
- +0x440 `beqz a1,0x3f6c4` branch [non-linear]
- +0x510 `j 0x657f4` live-in-a5-at-tailcall [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`asan_UnpoisonBeforeMain_ctor` +0x134** (lui-const (dataflow); `_ZL18UnpoisonBeforeMainv`; word addi a1,a1,-1):

- +0x140 `slli a6,a1,0x28` alu slli [linear]
- +0x178 `and a1,a2,a6` alu and [linear]
- +0x17c `beqz a1,0x40120` branch [non-linear]
- +0x208 `jal 0x657f4` live-in-a6-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter
- +0x22c `jal 0x66ce8` live-in-a6-at-call [linear]: _ZN11__sanitizer6PrintfEPKcz, Printf variadic slot 6
- +0x25c `j 0x401f0` live-in-a6-at-tailcall [linear]: __asan_after_dynamic_init, not a parameter
- +0x264 `jal 0x657f4` live-in-a6-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`asan_before_dynamic_init_asan_after_dynamic_init` +0x1d4** (lui-const (dataflow); `__asan_after_dynamic_init`; word addi a1,a1,-1):

- +0x1e0 `slli a5,a1,0x28` alu slli [linear]
- +0x218 `and a1,a0,a5` alu and [linear]
- +0x21c `beqz a1,0x40430` branch [non-linear]
- +0x2dc `j 0x657f4` live-in-a5-at-tailcall [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`AsanStats_Clear_ctor` +0x170** (lui-const (dataflow); `_ZN6__asan22FlushToDeadThreadStatsEPNS_9AsanStatsE`; word addi a1,a1,-1):

- +0x17c `slli a5,a1,0x28` alu slli [linear]
- +0x1b4 `and a1,a0,a5` alu and [linear]
- +0x1b8 `beqz a1,0x5aa90` branch [non-linear]
- +0x278 `j 0x657f4` live-in-a5-at-tailcall [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`InternalAlloc_RawInternalAlloc` +0x150** (lui-const (dataflow); `_ZN6__asanL20GetAsanThreadContextEj`; word addi a3,a3,-1):

- +0x15c `slli a3,a3,0x28` alu slli [linear]
- +0x19c `and a1,a7,a3` alu and [linear]
- +0x1a0 `beqz a1,0x5db98` branch [non-linear]
- +0x204 `jal 0x657f4` live-in-a3-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`InternalAllocator_CombinedAllocator_Allocate_int` +0x80** (lui-const (dataflow); `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE8AllocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEmm`; word lui a5,0x20):

- +0x84 `bltu a5,a3,0x5e460` branch [linear]
- +0x88 `bltu a5,a4,0x5e460` branch [linear]

**`ThreadRegistry_CreateThread` +0x21c** (lui-const (dataflow); `_ZN11__sanitizer14ThreadRegistry12CreateThreadEmbjjPv`; word addi a1,a1,-1):

- +0x228 `slli a5,a1,0x28` alu slli [linear]
- +0x25c `and a1,a0,a5` alu and [linear]
- +0x260 `beqz a1,0x69dc4` branch [non-linear]
- +0x2c4 `jal 0x657f4` live-in-a5-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`ThreadRegistry_StartThread` +0x1a4** (lui-const (dataflow); `_ZN11__sanitizer14ThreadRegistry11StartThreadEjyNS_10ThreadTypeEPv`; word addi a1,a1,-1):

- +0x1b0 `slli a5,a1,0x28` alu slli [linear]
- +0x1e4 `and a1,a0,a5` alu and [linear]
- +0x1e8 `beqz a1,0x6aa84` branch [non-linear]
- +0x2b8 `j 0x657f4` live-in-a5-at-tailcall [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`StackStore_Store_BlockInfo_helper` +0xb0** (lui-const (dataflow); `_ZN11__sanitizer10StackStore5StoreERKNS_10StackTraceEPm`; word lui a1,0x100):

- +0xc4 `xor a0,a0,a1` alu xor [linear]
- +0xcc `seqz a0,a0` alu seqz [non-linear]
- +0xd0 `add a0,a2,a0` add [non-linear]
- +0xd4 `sd a0,0(s0)` store-data [non-linear]

**`lsan_register_root_region` +0x1dc** (lui-const (dataflow); `__lsan_register_root_region`; word addi a1,a1,-1):

- +0x1e8 `slli a4,a1,0x28` alu slli [linear]
- +0x220 `and a1,a5,a4` alu and [linear]
- +0x224 `beqz a1,0x7c87c` branch [non-linear]
- +0x288 `jal 0x657f4` live-in-a4-at-call [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`lsan_unregister_root_region` +0x248** (lui-const (dataflow); `__lsan_unregister_root_region`; word addi a1,a1,-1):

- +0x250 `slli a4,a1,0x28` alu slli [linear]
- +0x290 `and a1,t0,a4` alu and [linear]
- +0x294 `beqz a1,0x7cc1c` branch [non-linear]
- +0x364 `j 0x657f4` live-in-a4-at-tailcall [linear]: _ZN11__sanitizer9Semaphore4PostEj, not a parameter

**`open` +0x48** (lui-const (dataflow); `open`; word lui a0,0x410):

- +0x4c `and a1,s0,a0` alu and [linear]
- +0x50 `beq a1,a0,0x8d8d4` branch [non-linear]
- +0x50 `beq a1,a0,0x8d8d4` branch [linear]

**`libc_malloc_impl` +0x64** (lui-const (dataflow); `__libc_malloc_impl`; word addiw a0,a0,-20):

- +0x70 `bltu s0,a0,0x8eca4` branch [linear]

**`printf_core` +0x994** (lui-const (dataflow); `printf_core`; word lui a0,0x12):

- +0x998 `and s2,s8,a0` alu and [linear]
- +0x99c `sd s2,8(sp)` spill to sp-536 [non-linear]
- +0x99c `sd s2,8(sp)` spill to sp-536 [linear]
- +0x9a0 `bnez s2,0x946a4` branch [non-linear]
- +0x9a0 `bnez s2,0x946a4` branch [linear]
- +0xa44 `bne s2,a0,0x94748` branch [non-linear]
- +0xa44 `bne s2,a0,0x94748` branch [linear]
- +0xb6c `bne s2,a0,0x93d30` branch [non-linear]
- +0xb6c `bne s2,a0,0x93d30` branch [linear]

**`pad` +0x30** (lui-const (dataflow); `pad`; word lui a0,0x12):

- +0x34 `and a0,a4,a0` alu and [linear]
- +0x38 `bnez a0,0x94c8c` branch [non-linear]

**`fmt_fp` +0x398** (lui-const (dataflow); `fmt_fp`; word lui a0,0x12):

- +0x39c `and a0,s11,a0` alu and [linear]
- +0x3a4 `bne a0,a1,0x950d4` branch [non-linear]

**`fmt_fp` +0xa20** (lui-const (dataflow); `fmt_fp`; word lui a0,0x12):

- +0xa24 `and s7,a1,a0` alu and [linear]
- +0xa2c `bnez s7,0x95820` branch [non-linear]
- +0xb88 `bne s7,a0,0x958b8` branch [non-linear]
- +0xcbc `bne s7,a0,0x959ec` branch [non-linear]

**`fmt_fp` +0x10f8** (lui-const (dataflow); `fmt_fp`; word lui a0,0x12):

- +0x10fc `and a0,t3,a0` alu and [linear]
- +0x1104 `sd a0,-472(s0)` spill to sp-472 [non-linear]
- +0x1108 `bnez a0,0x95e50` branch [non-linear]
- +0x11c0 `bne a1,a0,0x95f08` branch [non-linear]
- +0x163c `bne a1,a0,0x9636c` branch [non-linear]

### fmt_fp +0x670: the frame-base check in both images

    # incoming registers typed as integers by the prototype: ['a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7']
    cgif_file_fuzzer.asan fmt_fp: lui words whose value lies in an image section (static-address candidates): +0x398 lui 0x12000 (.rodata), +0x670 lui 0x24000 (.eh_frame_hdr), +0xa20 lui 0x12000 (.rodata), +0x10f8 lui 0x12000 (.rodata)
    cgif_file_fuzzer.asan fmt_fp +0xa90 `lw s8,0(a2)`: base a2 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xb04 `lbu a0,-4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xde0 `sw s2,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xe0c `sw a0,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xe30 `lw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xe38 `sw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xe44 `sw zero,4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xec4 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    cgif_file_fuzzer.asan fmt_fp +0xf24 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp: lui words whose value lies in an image section (static-address candidates): +0x398 lui 0x12000 (.rodata), +0x670 lui 0x24000 (.eh_frame_hdr), +0xa20 lui 0x12000 (.rodata), +0x10f8 lui 0x12000 (.rodata)
    fuzz_boxreg.asan fmt_fp +0xa90 `lw s8,0(a2)`: base a2 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xb04 `lbu a0,-4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xde0 `sw s2,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe0c `sw a0,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe30 `lw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe38 `sw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe44 `sw zero,4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xec4 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xf24 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    # every value reaching every base has root sp, in both images: True

## Names with more than one copy

| row | name | copies (cgif / boxreg) | by address | by name (`Img.fsym`: lowest-address copy) |
|---|---|---|---|---|
| `FakeStack_SetShadow` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | `EQUAL-mod-pcrel` N=0 (0x3cbd0 / 0x3c6cc) | `EQUAL-mod-pcrel` N=0 (0x3b1e8 / 0x3ae64) |
| `MemToShadow_CHECK_AddrIsInMem_instance` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | `EQUAL-mod-pcrel` N=0 (0x52684 / 0x52140) | `EQUAL-mod-pcrel` N=0 (0x3b1e8 / 0x3ae64) |
| `MemToShadow_checked` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | `EQUAL-mod-pcrel` N=0 (0x53ccc / 0x53788) | `EQUAL-mod-pcrel` N=0 (0x3b1e8 / 0x3ae64) |
| `MemToShadow_checked_instance_3` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | `EQUAL-mod-pcrel` N=0 (0x5cbb8 / 0x5c674) | `EQUAL-mod-pcrel` N=0 (0x3b1e8 / 0x3ae64) |
| `init` | `dummy` | 6 / 5 | `EQUAL` N=0 (0x8cbe4 / 0x87f4c) | `EQUAL` N=0 (0x8cbe4 / 0x87f4c) |
| `musl_exit_helper_stub` | `dummy` | 6 / 5 | `EQUAL` N=0 (0x8d5b4 / 0x8891c) | `EQUAL` N=0 (0x8cbe4 / 0x87f4c) |
| `aio_close_stub_j_ret_used_by_close_stdio_close` | `dummy` | 6 / 5 | `EQUAL` N=0 (0x92b9c / 0x8dd2c) | `EQUAL` N=0 (0x8cbe4 / 0x87f4c) |

The by-address verdict covers the row. For the MemToShadow rows the by-name compare takes copy 1 in both images,
not the row's copy; the qualified-name compare below takes the row's copy. Each `dummy` row also carries a unique name
(`_init`, `_fini`, `__aio_close`), compared `EQUAL` by name at the row address.

`start` and `set_thread_area` are size-0 symbols, so a by-name compare has no symbol length (`ABSENT`); they are
compared by address over their row ranges.

### Controls and qualified names (ab1w_extra.py)


**(1) kit controls (plants in file copies of fuzz_boxreg.asan)**

    Pab1w-kit-jal: row ReportGenericError, boxreg 0x577ac jal 0x78994 (_ZN11__sanitizer21ScopedErrorReportLock4LockEv+0x0) -> 0x78a90 (_ZN11__sanitizer21ScopedErrorReportLock6UnlockEv+0x0): 4bbd by address EQUAL-mod-pcrel N=1, 86da DIFFERENT-target N=1 -> CAUGHT; baseline 4bbd EQUAL-mod-pcrel N=0, 86da EQUAL-mod-pcrel N=0
    Pab1w-kit-m2s: row MemToShadow_CHECK_AddrIsInMem_instance, boxreg 0x52278 jal 0x6b12c (_ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0) -> 0x6b1e4 (_ZN11__sanitizer16BackgroundThreadEPv+0x0): 4bbd by address EQUAL-mod-pcrel N=1, 86da DIFFERENT-target N=1 -> CAUGHT; baseline 4bbd EQUAL-mod-pcrel N=0, 86da EQUAL-mod-pcrel N=0; by name (Img.fsym: copy 1, cgif 0x3b1e8 / boxreg 0x3ae64) on the plant: EQUAL-mod-pcrel N=0, so the by-name compare does not see it

**(2) rows whose name has several copies, by qualified name on cmpkit 86da41d3ef68 (strictcmp3.py cmp NAME{FILE})**

        # A = cgif_file_fuzzer.asan sha256 488e39500746
        # B = fuzz_boxreg.asan sha256 4532568b621d
        # C-string rule ON (default)
        fn	pair	addr1	addr2	size1	size2	verdict	pcrel	real	unmeasured	targets(full-bytes-eq,got-value-or-tls-index-eq,cstr-eq)	target-differ	value/full-bytes/NAME-ONLY acceptances	C-string acceptances (also one CSTR row each)	differing targets printed (in target-differ, this row)	words-only
        _ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}	A:B	0x3cbd0	0x3c6cc	316	316	EQUAL-mod-pcrel	13	0	0	(0, 0, 2)	0		0x124@0x1f9fa|0x1f8e7=b'/llvm-project/compiler-rt/lib/asan/asan_mapping.h\x00' 0x128@0x16fa4|0x16f4d=b'((AddrIsInMem(p))) != (0)\x00'	printed 0 of 0 targets	EQUAL-mod-pcrel
        _ZN6__asanL11MemToShadowEm{asan_linux.cpp}	A:B	0x52684	0x52140	316	316	EQUAL-mod-pcrel	12	0	0	(0, 0, 2)	0		0x124@0x1f9fa|0x1f8e7=b'/llvm-project/compiler-rt/lib/asan/asan_mapping.h\x00' 0x128@0x16fa4|0x16f4d=b'((AddrIsInMem(p))) != (0)\x00'	printed 0 of 0 targets	EQUAL-mod-pcrel
        _ZN6__asanL11MemToShadowEm{asan_poisoning.cpp}	A:B	0x53ccc	0x53788	316	316	EQUAL-mod-pcrel	12	0	0	(0, 0, 2)	0		0x124@0x1f9fa|0x1f8e7=b'/llvm-project/compiler-rt/lib/asan/asan_mapping.h\x00' 0x128@0x16fa4|0x16f4d=b'((AddrIsInMem(p))) != (0)\x00'	printed 0 of 0 targets	EQUAL-mod-pcrel
        _ZN6__asanL11MemToShadowEm{asan_thread.cpp}	A:B	0x5cbb8	0x5c674	316	316	EQUAL-mod-pcrel	12	0	0	(0, 0, 2)	0		0x124@0x1f9fa|0x1f8e7=b'/llvm-project/compiler-rt/lib/asan/asan_mapping.h\x00' 0x128@0x16fa4|0x16f4d=b'((AddrIsInMem(p))) != (0)\x00'	printed 0 of 0 targets	EQUAL-mod-pcrel
        _init	A:B	0x8cbe4	0x87f4c	4	4	EQUAL	0	0	0	(0, 0, 0)	0			printed 0 of 0 targets	EQUAL
        _fini	A:B	0x8d5b4	0x8891c	4	4	EQUAL	0	0	0	(0, 0, 0)	0			printed 0 of 0 targets	EQUAL
        __aio_close	A:B	0x92b9c	0x8dd2c	4	4	EQUAL	0	0	0	(0, 0, 0)	0			printed 0 of 0 targets	EQUAL
        row addresses (boxreg): FakeStack_SetShadow 0x3c6cc, MemToShadow_CHECK_AddrIsInMem_instance 0x52140, MemToShadow_checked 0x53788, MemToShadow_checked_instance_3 0x5c674

**(3) C-string and full-data acceptances of strictcmp3 over the 518 pairs, re-read with the independent decoder**

        acceptances by kind: {'gotval': 34, 'full': 124, 'cstr': 2053, 'lui-const': 20, 'tlsindex': 1}
        C-string and full-data acceptances: 2177; the accepted bytes are equal in both images (C string through its NUL, full data over its length): 2177; not equal: 0 []

## Controls: one planted re-point per settlement class

Each plant is a file copy of fuzz_boxreg.asan with one instruction word changed, compared with cgif_file_fuzzer.asan
like the pairs. It must be refused by the measurement that settles its class; the unplanted baseline must settle.

| plant | class | row | planted word | kit on the row | class measurement | result | baseline |
|---|---|---|---|---|---|---|---|
| Pab1w-empty | empty string | asan_InitializeFlags +0x104 | 0x3c90c `addi t5,t3,1412` (584e0f13) -> `addi t5,t3,1413` (585e0f13) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=1 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-debruijn | De Bruijn table | Allocator_Deallocate +0x20c | 0x31094 `addi a4,a4,852` (35470713) -> `addi a4,a4,853` (35570713) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=1 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-rel4 | jump table | sysconf +0xdc | 0x87e00 `addi a0,a0,1276` (4fc50513) -> `addi a0,a0,1280` (50050513) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=4 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-ptrtab | pointer table | internal_sigaction_syscall_wrapper_selector +0x24 | 0x64e90 `addi a1,a1,-1044` (bec58593) -> `addi a1,a1,-1036` (bf458593) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=1 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-got | .got section-bound value | asan_module_ctor +0x1c | 0x815d0 `ld a2,1392(a2)` (57063603) -> `ld a2,1400(a2)` (57863603) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=1 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-printf890 | unmeasured auipc-register word | printf_core +0x890 | 0x8f400 `addi a7,a1,1` (00158893) -> `addi a7,a1,2` (00258893) | 4bbd DIFFERENT N=3 REAL=1; 86da DIFFERENT N=4 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-start | writable-unnamed (value 0, dead) | start +0x10 | 0x2ff68 `addi a1,a1,156` (09c58593) -> `addi a1,a1,164` (0a458593) | 4bbd EQUAL-mod-pcrel N=1 REAL=0; 86da DIFFERENT-target N=1 | measurement: refuses | REFUSED | settles; measurement: settles |
| Pab1w-lui-i | (i) call argument | InitializeAsanInterceptors +0x44 | 0x473a4 `lui a2,0x38e` (0038e637) -> `lui a2,0x38f` (0038f637) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=1 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-ii | (ii) return value | sysconf +0xe8 | 0x87e0c `lui a2,0x31` (00031637) -> `lui a2,0x32` (00032637) | 4bbd DIFFERENT N=1 REAL=1; 86da DIFFERENT N=4 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-iii-arg | (iii) offset from an argument base | StackDepotBase_Put +0x1b0 | 0x7213c `lui a0,0x400` (00400537) -> `lui a0,0x401` (00401537) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=3 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-iii-abs | (iii) absolute address | InternalFree_LowLevelAllocator_free_to_freelist +0xcc | 0x5d9f0 `lui s2,0x41` (00041937) -> `lui s2,0x42` (00042937) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=7 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-store | store into an integer field | AsanDeactivate_activation_CHECK_helper +0x8c | 0x36a9c `lui a0,0x100` (00100537) -> `lui a0,0x101` (00101537) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=1 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-c | (c) CheckFailed v1 / v2 | LargeMmapAllocator_Allocate +0x430 | 0x35d38 `lui a4,0x100` (00100737) -> `lui a4,0x101` (00101737) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=2 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-d | (d) compare only | init_tls +0x158 | 0x88498 `lui a1,0x20` (000205b7) -> `lui a1,0x21` (000215b7) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=1 | tracer: value equal False, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |
| Pab1w-lui-e | (e) frame base: sp root replaced by gp | fmt_fp +0x670 | 0x8fc3c `sub s6,sp,a0` (40a10b33) -> `sub s6,gp,a0` (40a18b33) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=1 | rootcheck: every value reaching every base has root sp, in both images: False (plant roots: ['in:3']) | REFUSED | settles; rootcheck: every value reaching every base has root sp, in both images: True |
| Pab1w-lui-or | linear-only rule: add -> or before a store base | InternalFree_LowLevelAllocator_free_to_freelist +0xcc | 0x5da20 `add a1,s1,s2` (012485b3) -> `or a1,s1,s2` (0124e5b3) | 4bbd DIFFERENT N=0 REAL=1; 86da DIFFERENT N=7 | tracer: value equal True, every use the same False | REFUSED | settles; tracer: value equal True, every use the same True |

16 plants, 16 refused; every baseline settles.

## Appendix: all 518 kept rows

| cgif row | cgif A | boxreg row(s) | boxreg A | size | 4bbd3a74be89 verdict (by address) | N | 86da41d3ef68 verdict (by address) | N | settled verdict |
|---|---|---|---|---|---|---|---|---|---|
| `start` | 0x302dc | `start` | 0x2ff58 | 0x48 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `do_init` | 0x30324 | `do_init` | 0x2ffa0 | 0x74 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `do_fini` | 0x30398 | `do_fini` | 0x30014 | 0x90 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AllocatorOptions_SetFrom` | 0x30428 | `AllocatorOptions_SetFrom` | 0x300a4 | 0x3c | EQUAL | 0 | EQUAL | 0 | same |
| `InitializeAllocator` | 0x305d4 | `InitializeAllocator` | 0x30250 | 0x18 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_InitLinkerInitialized` | 0x305ec | `Allocator_InitLinkerInitialized` | 0x30268 | 0x16c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_FindHeapChunkByAddress_helper` | 0x30cb4 | `Allocator_FindHeapChunkByAddress_helper` | 0x30930 | 0x15c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_free` | 0x311e4 | `asan_free` | 0x30e60 | 0x28 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_Deallocate` | 0x3120c | `Allocator_Deallocate` | 0x30e88 | 0x2b8 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_malloc` | 0x314c4 | `asan_malloc` | 0x31140 | 0x5c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_Allocate` | 0x31520 | `Allocator_Allocate` | 0x3119c | 0x988 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `AsanChunkView_GetAsanChunk_ptr_helper` | 0x325e0 | `AsanChunkView_GetAsanChunk_ptr_helper` | 0x3225c | 0x144 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_get_allocated_begin_size_style_query` | 0x32810 | `sanitizer_get_allocated_begin_size_style_query` | 0x3248c | 0x5c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_Init` | 0x3286c | `SizeClassAllocator64_Init` | 0x324e8 | 0x250 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_MapWithCallbackOrDie` | 0x32abc | `SizeClassAllocator64_MapWithCallbackOrDie` | 0x32738 | 0xf4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_SharedInitCode` | 0x32bb0 | `Allocator_SharedInitCode` | 0x3282c | 0xe8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `QuarantineCache_MergeBatches_Transfer` | 0x330cc | `Quarantine_Recycle` | 0x32d48 | 0x1e4 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `QuarantineCache_DequeueBatch` | 0x332b0 | `QuarantineCache_DequeueBatch` | 0x32f2c | 0x184 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `QuarantineCallback_Recycle` | 0x3356c | `QuarantineCallback_Recycle` | 0x331e8 | 0x284 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_GetBlockBegin` | 0x337f0 | `LargeMmapAllocator_GetBlockBegin` | 0x3346c | 0x180 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64LocalCache_Deallocate` | 0x33970 | `SizeClassAllocator64LocalCache_Deallocate` | 0x335ec | 0x1c8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_Deallocate` | 0x33b38 | `LargeMmapAllocator_Deallocate` | 0x337b4 | 0x1cc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_ReturnToAllocator_helper` | 0x33d04 | `SizeClassAllocator64_ReturnToAllocator_helper` | 0x33980 | 0xa0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalMmapVector_Realloc` | 0x33da4 | `InternalMmapVector_Realloc` | 0x33a20 | 0x104 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_EnsureFreeArraySpace` | 0x341d0 | `SizeClassAllocator64_EnsureFreeArraySpace` | 0x33e4c | 0x148 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `DieOnMapFailure_sealed` | 0x34318 | `DieOnMapFailure_sealed` | 0x33f94 | 0x38 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` | 0x34ae8 | `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` | 0x34764 | 0x2e8 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `Allocator_QuarantineChunk` | 0x354a8 | `Allocator_QuarantineChunk` | 0x35124 | 0x178 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_QuarantineChunk_tail_quarantine_Put` | 0x35620 | `Allocator_QuarantineChunk_tail_quarantine_Put` | 0x3529c | 0x1b0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `QuarantineCache_Enqueue` | 0x357d0 | `QuarantineCache_Enqueue` | 0x3544c | 0x1e4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CombinedAllocator_Allocate` | 0x359b4 | `CombinedAllocator_Allocate` | 0x35630 | 0x2d8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_Allocate` | 0x35c8c | `LargeMmapAllocator_Allocate` | 0x35908 | 0x478 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `SizeClassAllocator64LocalCache_Refill` | 0x36104 | `SizeClassAllocator64LocalCache_Refill` | 0x35d80 | 0x100 | EQUAL | 0 | EQUAL | 0 | same |
| `SizeClassAllocator64_GetFromAllocator` | 0x36204 | `SizeClassAllocator64_GetFromAllocator` | 0x35e80 | 0x308 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `SizeClassAllocator64_PopulateFreeArray` | 0x3650c | `SizeClassAllocator64_PopulateFreeArray` | 0x36188 | 0x370 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | NOT CERTIFIED: REAL 0 |
| `Allocator_ComputeRZLog` | 0x3687c | `RZSize2Log` | 0x364f8 | 0x118 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `LargeMmapAllocator_EnsureSortedChunks` | 0x36c9c | `LargeMmapAllocator_EnsureSortedChunks` | 0x36918 | 0xfc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanDeactivate_activation_CHECK_helper` | 0x36d98 | `AsanDeactivate_activation_CHECK_helper` | 0x36a14 | 0xe8 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `AsanActivate` | 0x36e80 | `AsanActivate` | 0x36afc | 0xdc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_activation_flag_parse_helper_0_no` | 0x37438 | `asan_activation_flag_parse_helper_0_no` | 0x370b4 | 0xe8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_AddrIsInFakeStack` | 0x3bfd8 | `FakeStack_AddrIsInFakeStack` | 0x3bc54 | 0xd8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_Create` | 0x3c0b0 | `FakeStack_Create` | 0x3bd2c | 0xec | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_Allocate` | 0x3c458 | `FakeStack_Allocate` | 0x3c0d4 | 0x2e8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetTLSFakeStack` | 0x3c874 | `SetTLSFakeStack` | 0x3c4f0 | 0x30 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_SetShadow` | 0x3cbd0 | `MemToShadow_3c6cc` | 0x3c6cc | 0x13c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_InitializeFlags` | 0x3cd0c | `asan_InitializeFlags` | 0x3c808 | 0x102c | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_register_globals_impl_RegisterGlobal_loop` | 0x3e444 | `asan_register_globals_impl_RegisterGlobal_loop` | 0x3df40 | 0xe1c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_unregister_globals_impl` | 0x3f260 | `asan_unregister_globals_impl` | 0x3ed5c | 0x5cc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_register_globals` | 0x3f82c | `asan_register_globals` | 0x3f328 | 0x6c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_unregister_globals` | 0x3f898 | `asan_unregister_globals` | 0x3f394 | 0x68 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_UnpoisonBeforeMain_ctor` | 0x3ff80 | `asan_UnpoisonBeforeMain_ctor` | 0x3fa7c | 0x270 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_before_dynamic_init_asan_after_dynamic_init` | 0x401f0 | `asan_before_dynamic_init_asan_after_dynamic_init` | 0x3fcec | 0x308 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | 0x40c6c | `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | 0x40768 | 0x150 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_globals_RegisterGlobal_vector_push_back` | 0x417d8 | `asan_globals_RegisterGlobal_vector_push_back` | 0x412d4 | 0x118 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `strlen` | 0x418f0 | `strlen` | 0x413ec | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `strnlen` | 0x418f4 | `strnlen` | 0x413f0 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `strcmp` | 0x418f8 | `strcmp` | 0x413f4 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `strchr` | 0x418fc | `strchr` | 0x413fc | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `memcmp` | 0x41900 | `memcmp` | 0x41400 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `memcmp_2` | 0x41904 | `interceptor_trampoline_bcmp` | 0x41404 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `memchr` | 0x41908 | `memchr` | 0x41408 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `frexpl` | 0x4190c | `frexpl` | 0x4140c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `read` | 0x41910 | `read` | 0x41410 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `fwrite` | 0x41914 | `fwrite` | 0x41414 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `time` | 0x41918 | `time` | 0x41418 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `gmtime_r` | 0x4191c | `gmtime_r` | 0x4141c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `vprintf` | 0x41920 | `vprintf` | 0x41420 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `vfprintf` | 0x41924 | `vfprintf` | 0x41424 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `vsnprintf` | 0x41928 | `vsnprintf` | 0x41428 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `vfprintf_2` | 0x4192c | `interceptor_trampoline_fprintf` | 0x4142c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417bc` | 0x41930 | `interceptor_trampoline_snprintf` | 0x41430 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `clock_gettime` | 0x41934 | `clock_gettime` | 0x41434 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `wcrtomb` | 0x41938 | `wcrtomb` | 0x41438 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `wctomb` | 0x4193c | `wctomb` | 0x4143c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417cc` | 0x41940 | `interceptor_trampoline_strerror` + `interceptor_trampoline__exit` | 0x41440 | 0x8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `pthread_attr_getstack` | 0x41948 | `pthread_attr_getstack` | 0x41448 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `tls_get_addr_thunk` | 0x4194c | `tls_get_addr_thunk` | 0x4144c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417dc` | 0x41954 | `interceptor_trampoline_fflush` | 0x41450 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417e4` | 0x4195c | `interceptor_trampoline_sem_init` | 0x41454 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417e8` | 0x41960 | `interceptor_trampoline_sem_destroy` | 0x41458 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417ec` | 0x41964 | `interceptor_trampoline_sem_wait` | 0x4145c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417f0` | 0x41968 | `interceptor_trampoline_sem_trywait` | 0x41460 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sem_timedwait` | 0x4196c | `sem_timedwait` | 0x41464 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_417f8` | 0x41970 | `interceptor_trampoline_sem_post` | 0x41468 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `pthread_setcancelstate` | 0x41974 | `pthread_setcancelstate` | 0x4146c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `send` | 0x41978 | `send` | 0x41470 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sendto` | 0x4197c | `sendto` | 0x41474 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sigaltstack` | 0x41980 | `sigaltstack` | 0x41478 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_4180c` | 0x41984 | `interceptor_trampoline_sigaction` | 0x4147c | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strlen` | 0x41988 | `icpt_strlen` | 0x41480 | 0x294 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strnlen` | 0x41c1c | `icpt_strnlen` | 0x41714 | 0x294 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strcmp` | 0x41eb4 | `icpt_strcmp` | 0x419ac | 0x530 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strchr` | 0x423e4 | `icpt_strchr` | 0x424b8 | 0x2e0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcmp` | 0x42f5c | `icpt_memcmp` | 0x43030 | 0xbc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m` | 0x43018 | `icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m` | 0x430ec | 0xbc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memchr` | 0x430d4 | `icpt_memchr` | 0x431a8 | 0x2d0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_frexpl` | 0x433a4 | `icpt_frexpl` | 0x43478 | 0x278 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_read` | 0x4361c | `icpt_read` | 0x436f0 | 0x270 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_fwrite` | 0x4388c | `icpt_fwrite` | 0x43960 | 0x274 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_time` | 0x43b00 | `icpt_time` | 0x43bd4 | 0x29c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_gmtime_r` | 0x43fa4 | `icpt_gmtime_r` | 0x44078 | 0x240 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vprintf` | 0x441e4 | `icpt_vprintf` | 0x442b8 | 0x9c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `printf_common_format_interceptor` | 0x44280 | `printf_common_format_interceptor` | 0x44354 | 0xac8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vfprintf` | 0x44d48 | `icpt_vfprintf` | 0x44e1c | 0xb4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vsnprintf` | 0x44dfc | `icpt_vsnprintf` | 0x44ed0 | 0x318 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vfprintf_2` | 0x45114 | `interceptor_fprintf` | 0x451e8 | 0xd8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_clock_gettime` | 0x45290 | `icpt_clock_gettime` | 0x45364 | 0x258 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_wcrtomb` | 0x454e8 | `icpt_wcrtomb` | 0x455bc | 0x570 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_wctomb` | 0x45a58 | `icpt_wctomb` | 0x45b2c | 0x35c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_pthread_attr_getstack` | 0x45e80 | `icpt_pthread_attr_getstack` | 0x45f54 | 0x3e8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_tls_get_addr_DTLS_on_tls_get_addr_hook` | 0x46274 | `icpt_tls_get_addr_DTLS_on_tls_get_addr_hook` | 0x46348 | 0x7c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sem_timedwait` | 0x46b14 | `icpt_sem_timedwait` | 0x465d0 | 0x298 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_pthread_setcancelstate` | 0x46ddc | `icpt_pthread_setcancelstate` | 0x46898 | 0x228 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_send` | 0x47004 | `icpt_send` | 0x46ac0 | 0x2b4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sendto` | 0x472b8 | `icpt_sendto` | 0x46d74 | 0x2c4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sigaltstack` | 0x4757c | `icpt_sigaltstack` | 0x47038 | 0x25c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeAsanInterceptors` | 0x478ac | `InitializeAsanInterceptors` | 0x47368 | 0x1b0 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `icpt_diouxXn` | 0x47a5c | `format_get_value_size` | 0x47518 | 0x198 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeCommonInterceptors` | 0x487a0 | `ioctl_table_fill` | 0x4825c | 0x8cd8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeSignalInterceptors_or_syscall_hooks` | 0x51478 | `Sort_ioctl_desc` | 0x50f34 | 0x15c | EQUAL | 0 | EQUAL | 0 | same |
| `memset` | 0x515d4 | `memset` | 0x51090 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `memcpy` | 0x515d8 | `memcpy` | 0x51094 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `asan_memcpy` | 0x515dc | `asan_memcpy` | 0x51098 | 0x49c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_memset` | 0x51a78 | `asan_memset` | 0x51534 | 0x240 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memset` | 0x51cb8 | `icpt_memset` | 0x51774 | 0x2f0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcpy` | 0x51fa8 | `icpt_memcpy` | 0x51a64 | 0x5f0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeMemintrinsicInterceptors_tail_CHECK` | 0x52598 | `InitializeMemintrinsicInterceptors_tail_CHECK` | 0x52054 | 0x38 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializePlatformInterceptors` | 0x525d0 | `InitializePlatformInterceptors` | 0x5208c | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `InitializePlatformExceptionHandlers` | 0x525d4 | `InitializePlatformExceptionHandlers` | 0x52090 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `asan_linux_PlatformShadowSetup_helper_CheckForEx` | 0x525d8 | `asan_linux_PlatformShadowSetup_helper_CheckForEx` | 0x52094 | 0x60 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_CHECK_AddrIsInMem_instance` | 0x52684 | `MemToShadow_CHECK_AddrIsInMem_instance` | 0x52140 | 0x13c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanCheckIncompatibleRT` | 0x527c0 | `AsanCheckDynamicRTPrereqs` | 0x5227c | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `AsanCheckDynamicRTPrereqs` | 0x527c4 | `AsanCheckIncompatibleRT` | 0x52280 | 0x168 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `free` | 0x5292c | `free` | 0x523e8 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `malloc` | 0x52930 | `malloc` | 0x523ec | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `icpt_free` | 0x52934 | `icpt_free` | 0x523f0 | 0x1d0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_malloc` | 0x52b04 | `icpt_malloc` | 0x525c0 | 0x15c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_cfree_or_DlsymFree` | 0x52c60 | `DlSymAllocator_Allocate` | 0x5271c | 0xcc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReplaceSystemMalloc` | 0x52d2c | `ReplaceSystemMalloc` | 0x527e8 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `DlsymAlloc_PointerIsMine_internal_allocator_From` | 0x52d30 | `TwoLevelMap_u8_Create` | 0x527ec | 0x100 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `HeapProfile_Insert_asan_memory_profile` | 0x53158 | `HeapProfile_Insert_asan_memory_profile` | 0x52c14 | 0x16c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCanPoisonMemory` | 0x537ac | `SetCanPoisonMemory` | 0x53268 | 0x10 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CanPoisonMemory` | 0x537bc | `CanPoisonMemory` | 0x53278 | 0x14 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PoisonShadow` | 0x537d0 | `PoisonShadow` | 0x5328c | 0x4fc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_checked` | 0x53ccc | `MemToShadow_checked` | 0x53788 | 0x13c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_poison_stack_memory_PoisonAlignedStackMemor` | 0x53e08 | `asan_poison_stack_memory_PoisonAlignedStackMemor` | 0x538c4 | 0x1a0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_unpoison_stack_memory` | 0x53fa8 | `asan_unpoison_stack_memory` | 0x53a64 | 0x180 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_region_is_poisoned` | 0x54158 | `asan_region_is_poisoned` | 0x53c14 | 0x344 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDInit` | 0x548bc | `AsanTSDInit` | 0x54378 | 0x7c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDGet` | 0x54938 | `AsanTSDGet` | 0x543f4 | 0x40 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDSet` | 0x54978 | `AsanTSDSet` | 0x54434 | 0x40 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PlatformTSDDtor` | 0x549b8 | `PlatformTSDDtor` | 0x54474 | 0x84 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallAtForkHandler` | 0x54a3c | `InstallAtForkHandler` | 0x544f8 | 0x1c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallAtExitCheckLeaks` | 0x54ab8 | `InstallAtExitCheckLeaks` | 0x54574 | 0x44 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ScopedInErrorReport_ReportError_helper` | 0x55214 | `ReportDeadlySignal` | 0x54cd0 | 0x20c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportDoubleFree` | 0x55b28 | `ReportDoubleFree` | 0x555e4 | 0x290 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportGenericError` | 0x57694 | `ReportGenericError` | 0x57150 | 0x8bc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInited` | 0x586dc | `AsanInited` | 0x58198 | 0x18 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load1` | 0x586f4 | `asan_report_load1` | 0x581b0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load1` | 0x58744 | `asan_report_exp_load1` | 0x58200 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load2` | 0x58794 | `asan_report_load2` | 0x58250 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load2` | 0x587e4 | `asan_report_exp_load2` | 0x582a0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load4` | 0x58834 | `asan_report_load4` | 0x582f0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load4` | 0x58884 | `asan_report_exp_load4` | 0x58340 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load8` | 0x588d4 | `asan_report_load8` | 0x58390 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load8` | 0x58924 | `asan_report_exp_load8` | 0x583e0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load16` | 0x58974 | `asan_report_load16` | 0x58430 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load16` | 0x589c4 | `asan_report_exp_load16` | 0x58480 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store1` | 0x58a14 | `asan_report_store1` | 0x584d0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store1` | 0x58a64 | `asan_report_exp_store1` | 0x58520 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store2` | 0x58ab4 | `asan_report_store2` | 0x58570 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store2` | 0x58b04 | `asan_report_exp_store2` | 0x585c0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store4` | 0x58b54 | `asan_report_store4` | 0x58610 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store4` | 0x58ba4 | `asan_report_exp_store4` | 0x58660 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store8` | 0x58bf4 | `asan_report_store8` | 0x586b0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store8` | 0x58c44 | `asan_report_exp_store8` | 0x58700 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store16` | 0x58c94 | `asan_report_store16` | 0x58750 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store16` | 0x58ce4 | `asan_report_exp_store16` | 0x587a0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load_n` | 0x58d34 | `asan_report_load_n` | 0x587f0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load_n` | 0x58d84 | `asan_report_exp_load_n` | 0x58840 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store_n` | 0x58dd4 | `asan_report_store_n` | 0x58890 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store_n` | 0x58e24 | `asan_report_exp_store_n` | 0x588e0 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeHighMemEnd` | 0x58e74 | `InitializeHighMemEnd` | 0x58930 | 0x80 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PrintAddressSpaceLayout` | 0x58ef4 | `PrintAddressSpaceLayout` | 0x589b0 | 0x3b4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInitInternal` | 0x59338 | `AsanInitInternal` | 0x58df4 | 0x2b4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInitFromRtl_ENSURE_ASAN_INITED` | 0x595ec | `AsanInitFromRtl_ENSURE_ASAN_INITED` | 0x590a8 | 0xa0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_59674` | 0x59854 | `asan_set_death_callback` | 0x59310 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `asan_init` | 0x59858 | `asan_init` | 0x59314 | 0x94 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_version_mismatch_check_v8` | 0x598ec | `asan_version_mismatch_check_v8` | 0x593a8 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `SealedTopOfMemory_check` | 0x598f0 | `SealedTopOfMemory_check` | 0x593ac | 0x64 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_handle_no_return_tiny_rtl_stub_2_insns` | 0x59ac8 | `asan_handle_no_return_tiny_rtl_stub_2_insns` | 0x59584 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `force_interface_symbols_dead_volatile_switch` | 0x59b54 | `force_interface_symbols_dead_volatile_switch` | 0x59610 | 0x328 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | 0x59e7c | `ReserveShadowMemoryRanges_sealed_early_shadow_re` | 0x59938 | 0x1e0 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `InitializeShadowMemory` | 0x5a05c | `InitializeShadowMemory` | 0x59b18 | 0x308 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | NOT CERTIFIED: REAL 0 |
| `SetMallocContextSize` | 0x5a364 | `SetMallocContextSize` | 0x59e20 | 0x10 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetMallocContextSize` | 0x5a374 | `GetMallocContextSize` | 0x59e30 | 0x10 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `BufferedStackTrace_UnwindImpl_asan` | 0x5a384 | `BufferedStackTrace_UnwindImpl_asan` | 0x59e40 | 0x150 | EQUAL | 0 | EQUAL | 0 | same |
| `AsanStats_Clear_ctor` | 0x5a8b4 | `AsanStats_Clear_ctor` | 0x5a370 | 0x2a0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `GetCurrentThreadStats` | 0x5afb8 | `GetCurrentThreadStats` | 0x5aa74 | 0x38 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_suppression_kinds_getter_3_insns` | 0x5b298 | `asan_suppression_kinds_getter_3_insns` | 0x5ad54 | 0xc | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_InitializeSuppressions` | 0x5b2a4 | `asan_InitializeSuppressions` | 0x5ad60 | 0x8c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsInterceptorSuppressed` | 0x5b330 | `IsInterceptorSuppressed` | 0x5adec | 0x68 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `HaveStackTraceBasedSuppressions` | 0x5b398 | `HaveStackTraceBasedSuppressions` | 0x5ae54 | 0x78 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsODRViolationSuppressed` | 0x5b410 | `IsODRViolationSuppressed` | 0x5aecc | 0x68 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsStackTraceSuppressed` | 0x5b478 | `IsAddrSuppressed` | 0x5af34 | 0x14c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_thread_tiny_getter_3_insns` | 0x5b850 | `asan_thread_tiny_getter_3_insns` | 0x5b30c | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_Create` | 0x5b9dc | `AsanThread_Create` | 0x5b498 | 0x19c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_Destroy_TSDDtor` | 0x5bbd4 | `AsanThread_Destroy_TSDDtor` | 0x5b690 | 0x218 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetCurrentThread` | 0x5bdec | `GetCurrentThread` | 0x5b8a8 | 0x20 | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_SetThreadStackAndTls` | 0x5be0c | `AsanThread_SetThreadStackAndTls` | 0x5b8c8 | 0x1a4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_stack_top` | 0x5bfb0 | `AsanThread_stack_top` | 0x5ba6c | 0x58 | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_stack_bottom` | 0x5c008 | `AsanThread_stack_bottom` | 0x5bac4 | 0x58 | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_AsyncSignalSafeLazyInitFakeStack` | 0x5c060 | `AsanThread_AsyncSignalSafeLazyInitFakeStack` | 0x5bb1c | 0x230 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_Init` | 0x5c290 | `AsanThread_Init` | 0x5bd4c | 0x3f4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_ClearShadowForThreadStackAndTLS` | 0x5c684 | `AsanThread_ClearShadowForThreadStackAndTLS` | 0x5c140 | 0x10c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CreateMainThread` | 0x5c7c4 | `CreateMainThread` | 0x5c280 | 0x110 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCurrentThread` | 0x5c8d4 | `SetCurrentThread` | 0x5c390 | 0xe0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_checked_instance_3` | 0x5cbb8 | `MemToShadow_checked_instance_3` | 0x5c674 | 0x13c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `weak_default_hook_ret` | 0x5d9c8 | `ThreadContextBase_OnStarted` | 0x5d484 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `InternalAlloc_RawInternalAlloc` | 0x5d9d4 | `GetAsanThreadContext` | 0x5d490 | 0x240 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `InternalFree_LowLevelAllocator_free_to_freelist` | 0x5de68 | `internal_allocator` | 0x5d924 | 0x158 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 7 | same (lui certified) |
| `internal_allocator_getter` | 0x5e1ac | `internal_allocator_getter` | 0x5dc68 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LowLevelAllocator_InternalAlloc_bump_allocator` | 0x5e1b8 | `LowLevelAllocator_InternalAlloc_bump_allocator` | 0x5dc74 | 0x14c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetLowLevelAllocateMinAlignment` | 0x5e304 | `SetLowLevelAllocateMinAlignment` | 0x5ddc0 | 0x4c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetLowLevelAllocateCallback` | 0x5e350 | `SetLowLevelAllocateCallback` | 0x5de0c | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetAllocatorMayReturnNull` | 0x5e38c | `SetAllocatorMayReturnNull` | 0x5de48 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PrintHintAllocatorCannotReturnNull` | 0x5e398 | `PrintHintAllocatorCannotReturnNull` | 0x5de54 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AllocatorMayReturnNull` | 0x5e3a4 | `IsRssLimitExceeded` | 0x5de60 | 0x10 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalAllocator_CombinedAllocator_Allocate_int` | 0x5e3c0 | `InternalAllocator_CombinedAllocator_Allocate_int` | 0x5de7c | 0x2cc | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `InternalAllocator_LargeMmapAllocator_Allocate` | 0x5e68c | `InternalAllocator_LargeMmapAllocator_Allocate` | 0x5e148 | 0x3c0 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `SetSealedStartFrame_sealed_patch` | 0x5f9a8 | `SetSealedStartFrame_sealed_patch` | 0x5f464 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportMmapFailureAndDie` | 0x5f9b4 | `ReportMmapFailureAndDie` | 0x5f470 | 0xd8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportMunmapFailureAndDie` | 0x5fa8c | `ReportMunmapFailureAndDie` | 0x5f548 | 0x9c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check` | 0x6004c | `IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check` | 0x5fb08 | 0x44 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IncreaseTotalMmap` | 0x60090 | `DecreaseTotalMmap` | 0x5fb4c | 0x24 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadBinaryNameCached_CacheBinaryName_body` | 0x60308 | `ReadBinaryNameCached_CacheBinaryName_body` | 0x5fdc4 | 0x114 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `RunMallocHooks` | 0x605c0 | `RunMallocHooks` | 0x6007c | 0xb8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_malloc_hook_weak_default_ret` | 0x60678 | `sanitizer_malloc_hook_weak_default_ret` | 0x60134 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `RunFreeHooks` | 0x6067c | `RunFreeHooks` | 0x60138 | 0xac | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_free_hook_weak_default` | 0x60728 | `sanitizer_free_hook_weak_default` | 0x601e4 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `sanitizer_ignore_free_hook_weak_default_ret_0` | 0x60730 | `sanitizer_ignore_free_hook_weak_default_ret_0` | 0x601ec | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `SleepForSeconds_WaitForDebugger` | 0x6075c | `SleepForSeconds_WaitForDebugger` | 0x60218 | 0x4c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportFile_SetReportPath_body_stderr_stdout_keyw` | 0x60a6c | `ReportFile_SetReportPath_body_stderr_stdout_keyw` | 0x60528 | 0x240 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_set_report_path` | 0x612a8 | `sanitizer_set_report_path` | 0x60d64 | 0x18 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportFile_SetReportPath` | 0x612c0 | `CommonFlags_SetDefaults` | 0x60d7c | 0x144 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `OverrideCommonFlags_no_op_flag_hook_2_insns` | 0x61404 | `OverrideCommonFlags_no_op_flag_hook_2_insns` | 0x60ec0 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `FlagParser_ParseString_parse_flags` | 0x61754 | `FlagParser_ParseString_parse_flags` | 0x61210 | 0x12a4 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `FlagParser_PrintFlagDescriptions_gate_Verbosity` | 0x629f8 | `InitializeCommonFlags` | 0x624b4 | 0x24 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_parse_flag_ParseString_core` | 0x62ed0 | `FlagParser_parse_flag_ParseString_core` | 0x6298c | 0x310 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_ParseStringFromEnv` | 0x631e0 | `FlagParser_ParseStringFromEnv` | 0x62c9c | 0x144 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_ParseString` | 0x63324 | `FlagParser_ParseString` | 0x62de0 | 0xf4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `RegisterFlag_T_FlagParser_RegisterHandler` | 0x635ac | `RegisterFlag_T_FlagParser_RegisterHandler` | 0x63068 | 0x60 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_alloc_helper_LowLevelAlloc` | 0x6360c | `FlagParser_alloc_helper_LowLevelAlloc` | 0x630c8 | 0x40 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_atoll` | 0x6364c | `internal_atoll` | 0x63108 | 0xec | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_simple_strtoll` | 0x63738 | `internal_simple_strtoll` | 0x631f4 | 0x15c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_memchr` | 0x63894 | `internal_memchr` | 0x63350 | 0x20 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memcmp` | 0x638b4 | `internal_memcmp` | 0x63370 | 0x38 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memcpy` | 0x638ec | `internal_memcpy` | 0x633a8 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memmove` | 0x63910 | `internal_memmove` | 0x633cc | 0x58 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memset` | 0x63968 | `internal_memset` | 0x63424 | 0x60 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strcspn` | 0x639c8 | `internal_strcspn` | 0x63484 | 0x54 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strcmp` | 0x63a1c | `internal_strcmp` | 0x634d8 | 0x34 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strdup` | 0x63a50 | `internal_strdup` | 0x6350c | 0x6c | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strlen` | 0x63abc | `internal_strlen` | 0x63578 | 0x1c | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strncmp` | 0x63ad8 | `internal_strncmp` | 0x63594 | 0x44 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strchr` | 0x63b1c | `internal_strchr` | 0x635d8 | 0x4c | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strchrnul` | 0x63b68 | `internal_strchrnul` | 0x63624 | 0x48 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strrchr` | 0x63bb0 | `internal_strrchr` | 0x6366c | 0x40 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strnlen` | 0x63d20 | `internal_strnlen` | 0x637dc | 0x30 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strncpy` | 0x63d94 | `internal_strncpy` | 0x63850 | 0x70 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strstr` | 0x63e04 | `internal_strstr` | 0x638c0 | 0x94 | EQUAL | 0 | EQUAL | 0 | same |
| `mem_is_zero` | 0x63e98 | `mem_is_zero` | 0x63954 | 0xb4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_sigprocmask_raw_rt_sigprocmask` | 0x63f4c | `internal_sigprocmask_raw_rt_sigprocmask` | 0x63a08 | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `BlockSignals_ScopedBlockSignals_ctor_CHECK_inter` | 0x63f5c | `BlockSignals_ScopedBlockSignals_ctor_CHECK_inter` | 0x63a18 | 0x1e0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_iserror` | 0x64148 | `internal_iserror` | 0x63c04 | 0x20 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_mmap` | 0x64168 | `internal_mmap` | 0x63c24 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_munmap` | 0x64174 | `internal_munmap` | 0x63c30 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_mprotect` | 0x64180 | `internal_mprotect` | 0x63c3c | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_madvise` | 0x64190 | `internal_madvise` | 0x63c4c | 0x2c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_close` | 0x641bc | `internal_close` | 0x63c78 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_open_openat_AT_FDCWD` | 0x641c8 | `internal_open_openat_AT_FDCWD` | 0x63c84 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_read` | 0x641ec | `internal_read` | 0x63ca8 | 0x38 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_write` | 0x64224 | `internal_write` | 0x63ce0 | 0x38 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_ftruncate` | 0x6425c | `internal_ftruncate` | 0x63d18 | 0x38 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_dup` | 0x64294 | `internal_dup` | 0x63d50 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_dup2_dup3` | 0x642a0 | `internal_dup2_dup3` | 0x63d5c | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_unlink_unlinkat` | 0x642b0 | `internal_unlink_unlinkat` | 0x63d6c | 0x18 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sched_yield` | 0x642c8 | `internal_sched_yield` | 0x63d84 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_usleep_internal_sleep_nanosleep` | 0x642d4 | `internal_usleep_internal_sleep_nanosleep` | 0x63d90 | 0x4c | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `internal_execve` | 0x64320 | `internal_execve` | 0x63ddc | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_exit_exit_group` | 0x6432c | `internal_exit_exit_group` | 0x63de8 | 0x14 | EQUAL | 0 | EQUAL | 0 | same |
| `FileExists_newfstatat` | 0x64340 | `FileExists_newfstatat` | 0x63dfc | 0x80 | EQUAL | 0 | EQUAL | 0 | same |
| `DirExists_newfstatat` | 0x643c0 | `DirExists_newfstatat` | 0x63e7c | 0x64 | EQUAL | 0 | EQUAL | 0 | same |
| `GetTid_gettid` | 0x64424 | `GetTid_gettid` | 0x63ee0 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `GetEnv` | 0x64430 | `GetEnv` | 0x63eec | 0x130 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FutexWait` | 0x64664 | `FutexWait` | 0x64120 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `FutexWake` | 0x64688 | `FutexWake` | 0x64144 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_ptrace` | 0x646ac | `internal_ptrace` | 0x64168 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_waitpid_wait4` | 0x646b8 | `internal_waitpid_wait4` | 0x64174 | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_getpid` | 0x646c8 | `internal_getpid` | 0x64184 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_getppid` | 0x646d4 | `internal_getppid` | 0x64190 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_prctl` | 0x646e0 | `internal_prctl` | 0x6419c | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sigaltstack` | 0x646ec | `internal_sigaltstack` | 0x641a8 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `internal_fork_clone` | 0x646f8 | `internal_fork_clone` | 0x641b4 | 0x18 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sigaction_norestorer_rt_sigaction` | 0x64710 | `internal_sigaction_norestorer_rt_sigaction` | 0x641cc | 0x12c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetNamedMappingFd_ReadProcess_openat_getdents64` | 0x64a14 | `ThreadLister_ListThreads` | 0x644d0 | 0x3fc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetMaxUserVirtualAddress_sealed_from_the_start_f` | 0x64f7c | `GetMaxUserVirtualAddress_sealed_from_the_start_f` | 0x64a38 | 0x118 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetPageSizeCached` | 0x65094 | `GetPageSize` | 0x64b50 | 0x8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadBinaryName_readlinkat_proc_self_exe` | 0x6509c | `ReadBinaryName_readlinkat_proc_self_exe` | 0x64b58 | 0xac | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadLongProcessName_proc_self_cmdline` | 0x65148 | `ReadLongProcessName_proc_self_cmdline` | 0x64c04 | 0x120 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `internal_clone_CHECK_child_stack_16` | 0x65330 | `internal_clone_CHECK_child_stack_16` | 0x64dec | 0x80 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_sigaction_syscall_wrapper_selector` | 0x653b0 | `GetHandleSignalMode` | 0x64e6c | 0x5c | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `internal_start_thread_BlockSignals_variant_rt_si` | 0x6540c | `internal_start_thread_BlockSignals_variant_rt_si` | 0x64ec8 | 0xcc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_653ec` | 0x655d4 | `InitializePlatformEarly` | 0x65090 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `CheckASLR` | 0x655d8 | `CheckASLR` | 0x65094 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `GetMmapGranularity_thunk` | 0x65828 | `GetMmapGranularity_thunk` | 0x652e4 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `internal_errno_mapping_helper` | 0x6582c | `ErrorIsOOM` | 0x652e8 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `MmapOrDie` | 0x65838 | `MmapOrDie` | 0x652f4 | 0x10c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNamed_internal_mmap_name_helper` | 0x65944 | `MmapNamed_internal_mmap_name_helper` | 0x65400 | 0x74 | EQUAL | 0 | EQUAL | 0 | same |
| `UnmapOrDie` | 0x659b8 | `UnmapOrDie` | 0x65474 | 0x7c | EQUAL | 0 | EQUAL | 0 | same |
| `MmapOrDieOnFatalError` | 0x65a34 | `MmapOrDieOnFatalError` | 0x654f0 | 0x110 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNoReserveOrDie` | 0x65d70 | `MmapNoReserveOrDie` | 0x6582c | 0x104 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedNoAccess_3_insn_arg_shim_0x65c98` | 0x65e74 | `MmapFixedOrDie` | 0x65930 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `MmapFixed_named_may_die_core_MmapNamed_IncreaseT` | 0x65e80 | `MmapFixed_named_may_die_core_MmapNamed_IncreaseT` | 0x6593c | 0x178 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | 0x65ff8 | `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | 0x65ab4 | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `thunk_66008` | 0x661f0 | `CloseFile` | 0x65cac | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `GetNamedMappingFd_MmapNamed` | 0x66514 | `GetNamedMappingFd_MmapNamed` | 0x65fd0 | 0x20c | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `SetPrintfAndReportCallback` | 0x66cd8 | `SetPrintfAndReportCallback` | 0x66794 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Printf` | 0x66ce8 | `Printf` | 0x667a4 | 0x4c | EQUAL | 0 | EQUAL | 0 | same |
| `SharedPrintfCode` | 0x66d34 | `SharedPrintfCode` | 0x667f0 | 0x5c | EQUAL | 0 | EQUAL | 0 | same |
| `Report` | 0x66d90 | `Report` | 0x6684c | 0x4c | EQUAL | 0 | EQUAL | 0 | same |
| `SuppressionContext_ctor` | 0x688d4 | `SuppressionContext_ctor` | 0x68390 | 0x5c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SuppressionContext_ParseFromFile` | 0x68930 | `SuppressionContext_ParseFromFile` | 0x683ec | 0x23c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SuppressionContext_Parse` | 0x68b6c | `SuppressionContext_Parse` | 0x68628 | 0x324 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob` | 0x69430 | `GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob` | 0x68eec | 0xd0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a` | 0x69500 | `sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a` | 0x68fbc | 0x350 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `DTLS_Destroy_ForEachDVT_no_op_4_insns` | 0x69850 | `DTLS_Destroy_ForEachDVT_no_op_4_insns` | 0x6930c | 0x10 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalAllocatorLock_Unlock_or_stats_add_17_ins` | 0x69a9c | `ThreadContextBase_ctor` | 0x69558 | 0x44 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | 0x69ae0 | `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | 0x6959c | 0x60 | EQUAL | 0 | EQUAL | 0 | same |
| `ThreadRegistry_CreateThread` | 0x69b40 | `ThreadRegistry_CreateThread` | 0x695fc | 0x478 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `ThreadRegistry_StartThread` | 0x6a878 | `ThreadRegistry_StartThread` | 0x6a334 | 0x324 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `ThreadRegistry_ThreadArgRetval_vector_growth` | 0x6aba4 | `ThreadRegistry_ThreadArgRetval_vector_growth` | 0x6a660 | 0x104 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AddDieCallback` | 0x6b458 | `AddDieCallback` | 0x6af14 | 0x88 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Die` | 0x6b5a4 | `Die` | 0x6b060 | 0xc0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCheckUnwindCallback` | 0x6b664 | `SetCheckUnwindCallback` | 0x6b120 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CheckFailed` | 0x6b670 | `CheckFailed` | 0x6b12c | 0xb8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReservedAddressRange_InitAligned` | 0x6bd80 | `ReservedAddressRange_InitAligned` | 0x6b83c | 0xf8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReserveShadowMemoryRange` | 0x6be78 | `ReserveShadowMemoryRange` | 0x6b934 | 0x12c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_common_libcdep_static_ctor_background` | 0x6c1cc | `sanitizer_common_libcdep_static_ctor_background` | 0x6bc88 | 0x7c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetThreadStackTopAndBottom` | 0x6c27c | `GetThreadStackTopAndBottom` | 0x6bd38 | 0x2e8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `weak_default_hook_ret_2` | 0x6c564 | `InitTlsSize` | 0x6c020 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `GetThreadStackAndTls` | 0x6c568 | `GetTls` | 0x6c024 | 0x3f0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetThreadStackTopAndBottom_caller_ClearShadowFor` | 0x6c958 | `GetThreadStackAndTls` | 0x6c414 | 0xd0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AndroidLogInit` | 0x6ce0c | `AndroidLogInit` | 0x6c8c8 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `MonotonicNanoTime_NanoTime` | 0x6ce40 | `MonotonicNanoTime_NanoTime` | 0x6c8fc | 0x48 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MapDynamicShadow_MmapAlignedOrDieOnFatalError` | 0x6ce88 | `MapDynamicShadow_MmapAlignedOrDieOnFatalError` | 0x6c944 | 0x24c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `weak_default_hook_ret_3` | 0x6d0d4 | `InitializePlatformCommonFlags` | 0x6cb90 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `InternalMmapVector_push_back` | 0x6d0d8 | `CollectStaticTlsBlocks` | 0x6cb94 | 0x10c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalMmapVector_Realloc_2` | 0x6d1e4 | `InternalMmapVector_Realloc_2` | 0x6cca0 | 0x104 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_6d37c` | 0x6d564 | `GetThreadSelf` | 0x6d020 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetShadowRegionHugePageMode_DontDumpShadow_madvi` | 0x6d60c | `SetShadowRegionHugePageMode_DontDumpShadow_madvi` | 0x6d0c8 | 0x20 | EQUAL | 0 | EQUAL | 0 | same |
| `DisableCoreDumperIfNecessary` | 0x6d62c | `DisableCoreDumperIfNecessary` | 0x6d0e8 | 0xa0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_pthread_weak_stub_ret` | 0x6d718 | `Atexit` | 0x6d1d4 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetAlternateSignalStack` | 0x6d758 | `SetAlternateSignalStack` | 0x6d214 | 0xc4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `UnsetAlternateSignalStack` | 0x6d81c | `UnsetAlternateSignalStack` | 0x6d2d8 | 0x88 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallDeadlySignalHandlers` | 0x6d8a4 | `InstallDeadlySignalHandlers` | 0x6d360 | 0x78 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MaybeInstallSigaction` | 0x6d91c | `MaybeInstallSigaction` | 0x6d3d8 | 0xe4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsAccessibleMemoryRange` | 0x6dabc | `IsAccessibleMemoryRange` | 0x6d578 | 0x134 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve` | 0x6de28 | `MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve` | 0x6d8e4 | 0x130 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedNoReserve` | 0x6df58 | `MmapFixedSuperNoReserve` | 0x6da14 | 0x60 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNoAccess_ReservedAddressRange_Init` | 0x6dfb8 | `MmapNoAccess_ReservedAddressRange_Init` | 0x6da74 | 0xcc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MprotectNoAccess` | 0x6e098 | `MmapNoAccess` | 0x6db54 | 0x20 | EQUAL | 0 | EQUAL | 0 | same |
| `MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` | 0x6e0b8 | `ReservedAddressRange_Map` + `SealedRepairReservation` | 0x6db74 | 0x14c | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `MmapFixedOrDie` | 0x6e204 | `ReservedAddressRange_MapOrDie` | 0x6dcc0 | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `MaybeStartBackgroudThread` | 0x6fa0c | `InitializeCoverage` | 0x6f4c8 | 0x44 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Atexit_internal_exit_hook_runner_12_insns_execut` | 0x6fa50 | `sanitizer_cov_dump` | 0x6f50c | 0x30 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackStore_Store_BlockInfo_helper` | 0x6feb4 | `StackStore_Store_BlockInfo_helper` | 0x6f970 | 0x124 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `StackStore_Alloc` | 0x6ffd8 | `StackStore_Alloc` | 0x6fa94 | 0x134 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `StackStore_BlockInfo_Create_Map` | 0x709c0 | `StackStore_BlockInfo_Create_Map` | 0x7047c | 0xb4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotNode_store_hash_helper` | 0x721c8 | `StackDepotNode_store_hash_helper` | 0x71c84 | 0x5c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotPut` | 0x724b0 | `StackDepotPut` | 0x71f6c | 0x20 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotBase_Put` | 0x724d0 | `StackDepotBase_Put` | 0x71f8c | 0x284 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 3 | same (lui certified) |
| `StackDepotBase_Get` | 0x72754 | `StackDepotGet` | 0x72210 | 0x110 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `StackDepotBase_find_bucket_chain_walk` | 0x72c44 | `StackDepotBase_find_bucket_chain_walk` | 0x72700 | 0x90 | EQUAL | 0 | EQUAL | 0 | same |
| `StackDepotBase_lock_bucket_spin_lock` | 0x72cd4 | `TwoLevelMap_StackDepotNode_Create` | 0x72790 | 0x100 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `StackTrace_GetCurrentPc` | 0x72e34 | `StackTrace_GetCurrentPc` | 0x728f0 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `BufferedStackTrace_Init_UnwindFast_frame_pointer` | 0x72e3c | `BufferedStackTrace_Init_UnwindFast_frame_pointer` | 0x728f8 | 0x160 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackTrace_PopStackFrames` | 0x72f9c | `StackTrace_PopStackFrames` | 0x72a58 | 0x74 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `BufferedStackTrace_Unwind_FAST_frame_pointer_wal` | 0x73498 | `BufferedStackTrace_Unwind_FAST_frame_pointer_wal` | 0x72f54 | 0x118 | EQUAL | 0 | EQUAL | 0 | same |
| `thunk_762d8` | 0x765fc | `SymbolizerProcess_GetEnvP` | 0x760b8 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `thunk_77ab0` | 0x77dd4 | `InternalSymbolizer_Flush` | 0x77890 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `BufferedStackTrace_UnwindSlow` | 0x79800 | `BufferedStackTrace_UnwindSlow` | 0x792bc | 0xbc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Unwind_Trace_callback` | 0x798bc | `Unwind_Trace_callback` | 0x79378 | 0xd8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Unwind_GetIP_slow_unwind_helper` | 0x79994 | `Unwind_GetIP_slow_unwind_helper` | 0x79450 | 0x274 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lsan_flags_init_helper` | 0x79f34 | `lsan_flags_init_helper` | 0x799f0 | 0x44 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re` | 0x79f78 | `lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re` | 0x79a34 | 0x3d0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lsan_InitCommonLsan` | 0x7a618 | `lsan_InitCommonLsan` | 0x7a0d4 | 0xb8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_7b6f8` | 0x7ba28 | `DoRecoverableLeakCheckVoid` | 0x7b4e4 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `lsan_register_root_region` | 0x7c634 | `lsan_register_root_region` | 0x7c0f0 | 0x330 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `lsan_unregister_root_region` | 0x7c964 | `lsan_unregister_root_region` | 0x7c420 | 0x488 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `lsan_ubsan_default_options_weak_stub` | 0x7cdec | `lsan_ubsan_default_options_weak_stub` | 0x7c8a8 | 0xc | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_malloc_hook_RunMallocHooks_target_sanitizer` | 0x7f9b0 | `DisabledInThisThread` | 0x7f46c | 0x18 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_InitializeSuppressions` | 0x7fd4c | `ubsan_InitializeSuppressions` | 0x7f808 | 0x7c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_InitAsPlugin` | 0x7fdc8 | `ubsan_InitAsPlugin` | 0x7f884 | 0xb0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_MaybeCallUbsanDefaultOptions` | 0x7fe78 | `ubsan_MaybeCallUbsanDefaultOptions` | 0x7f934 | 0x18 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `ubsan_RegisterUbsanFlags_InitializeFlags_part` | 0x7fe90 | `ubsan_RegisterUbsanFlags_InitializeFlags_part` | 0x7f94c | 0x148 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_default_options_weak_returns` | 0x7ffd8 | `ubsan_default_options_weak_returns` | 0x7fa94 | 0xc | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_default_options_cli_c` | 0x7ffe4 | `asan_default_options_cli_c` | 0x7faa0 | 0xc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `main` | 0x7fff0 | `main` | 0x7faac | 0x2c4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `target_alloc_init` | 0x802b4 | `target_alloc_init` | 0x7fd70 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `target_alloc_count` | 0x802b8 | `target_alloc_count` | 0x7fd74 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `target_run` | 0x802c0 | `target_run` + `oft_exit_guard` | 0x7fd7c | 0x188 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `emit_printf` | 0x80448 | `emit_printf` | 0x7ff04 | 0x48 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_module_ctor` | 0x8139c | `asan_module_ctor` | 0x815b4 | 0x38 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_module_dtor` | 0x813d4 | `asan_module_dtor` | 0x815ec | 0x30 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `extenddftf2` | 0x86bdc | `extenddftf2` | 0x81f44 | 0x190 | EQUAL | 0 | EQUAL | 0 | same |
| `sysconf` | 0x8c9bc | `sysconf` | 0x87d24 | 0x228 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 4 | same (settled; lui certified) |
| `init` | 0x8cbe4 | `init` | 0x87f4c | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `init_libc` | 0x8cbe8 | `init_libc` | 0x87f50 | 0x22c | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `libc_start_init` | 0x8ce14 | `libc_start_init` | 0x8817c | 0x4c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_start_main` | 0x8ce60 | `libc_start_main` | 0x881c8 | 0x60 | EQUAL | 0 | EQUAL | 0 | same |
| `libc_start_main_stage2` | 0x8cec0 | `libc_start_main_stage2` | 0x88228 | 0x48 | EQUAL | 0 | EQUAL | 0 | same |
| `init_tls` | 0x8cfe0 | `init_tls` | 0x88348 | 0x2b0 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `init_ssp` | 0x8d290 | `init_ssp` | 0x885f8 | 0x60 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stack_chk_fail` | 0x8d2f0 | `stack_chk_fail` | 0x88658 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_sigaction_abort_area_fn_rt_sigaction_tkill` | 0x8d340 | `musl_sigaction_abort_area_fn_rt_sigaction_tkill` | 0x886a8 | 0x94 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Exit` | 0x8d3d4 | `Exit` | 0x8873c | 0x1c | EQUAL | 0 | EQUAL | 0 | same |
| `funcs_on_exit` | 0x8d420 | `funcs_on_exit` | 0x88788 | 0xc8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `fini_stub_ret` | 0x8d4e8 | `cxa_finalize` | 0x88850 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `cxa_atexit_atexit` | 0x8d4ec | `cxa_atexit_atexit` | 0x88854 | 0xc4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_exit_fini_array_walker_stub` | 0x8d5b0 | `call` | 0x88918 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_exit_helper_stub` | 0x8d5b4 | `fini` | 0x8891c | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `libc_exit_fini` | 0x8d5b8 | `libc_exit_fini` | 0x88920 | 0x4c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `exit` | 0x8d604 | `exit` | 0x8896c | 0x74 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `open` | 0x8d878 | `open` | 0x88be0 | 0xe4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `syscall_ret` | 0x8d95c | `syscall_ret` | 0x88cc4 | 0x38 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_dl_iterate_phdr_static` | 0x8d994 | `musl_dl_iterate_phdr_static` | 0x88cfc | 0x1a8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `calloc` | 0x8e100 | `calloc` | 0x89468 | 0x138 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_malloc_j_libc_malloc_impl` | 0x8e238 | `libc_malloc_j_libc_malloc_impl` | 0x895a0 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `libc_free` | 0x8e23c | `libc_free` | 0x895a4 | 0x1cc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `get_meta` | 0x8e408 | `get_meta` | 0x89770 | 0x110 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `alloc_meta` | 0x8e8f0 | `alloc_meta` | 0x89c58 | 0x2d8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_malloc_impl` | 0x8ebc8 | `libc_malloc_impl` | 0x89f30 | 0x370 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `alloc_slot` | 0x8ef38 | `alloc_slot` | 0x8a2a0 | 0x8a4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `enframe` | 0x8f7dc | `enframe` | 0x8ab44 | 0x150 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `malloc_allzerop` | 0x8f92c | `malloc_allzerop` | 0x8ac94 | 0x178 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `getrlimit` | 0x91754 | `getrlimit` | 0x8cabc | 0xf8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `getrusage` | 0x9184c | `getrusage` | 0x8cbb4 | 0x28 | EQUAL | 0 | EQUAL | 0 | same |
| `setrlimit` | 0x91874 | `setrlimit` | 0x8cbdc | 0xc8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `mmap` | 0x91d64 | `mmap` | 0x8d0cc | 0xec | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `mprotect` | 0x91e50 | `mprotect` | 0x8d1b8 | 0x48 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `munmap` | 0x91f6c | `munmap` | 0x8d2d4 | 0x48 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sched_yield` | 0x92278 | `sched_yield` | 0x8d5e0 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `raise_tkill_path` | 0x922f8 | `raise_tkill_path` | 0x8d660 | 0x78 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sigaction_libc_sigaction` | 0x92370 | `sigaction_libc_sigaction` | 0x8d6d8 | 0x1d4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_sigaltstack` | 0x9263c | `musl_sigaltstack` | 0x8d9a4 | 0x8c | EQUAL | 0 | EQUAL | 0 | same |
| `fprintf` | 0x92e7c | `dprintf` | 0x8e00c | 0x64 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lockfile` | 0x92fb0 | `lockfile` | 0x8e070 | 0xfc | EQUAL | 0 | EQUAL | 0 | same |
| `unlockfile` | 0x930ac | `unlockfile` | 0x8e16c | 0x60 | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_read` | 0x92bcc | `stdio_read` | 0x8dd5c | 0x118 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stdio_write` | 0x92cec | `stdio_write` | 0x8de7c | 0x190 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `aio_close_stub_j_ret_used_by_close_stdio_close` | 0x92b9c | `aio_close_stub_j_ret_used_by_close_stdio_close` | 0x8dd2c | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_close` | 0x92ba0 | `stdio_close` | 0x8dd30 | 0x2c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `fwritex` | 0x936d0 | `fwritex` | 0x8e600 | 0x138 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_fwrite` | 0x93808 | `musl_fwrite` | 0x8e738 | 0xb8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `towrite` | 0x938c0 | `towrite` | 0x8e7f0 | 0x54 | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_exit` | 0x9339c | `stdio_exit` | 0x8e45c | 0x1a4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ofl_lock` | 0x93914 | `ofl_lock` | 0x8e844 | 0x30 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_vfprintf` | 0x93ad0 | `musl_vfprintf` | 0x8e9c0 | 0x1b0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `printf_core` | 0x93c80 | `printf_core` | 0x8eb70 | 0xe30 | EQUAL-mod-pcrel | 3 | DIFFERENT-target | 4 | same (settled; lui certified) |
| `pop_arg` | 0x94ab0 | `pop_arg` | 0x8f9a0 | 0x134 | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `pad` | 0x94be4 | `pad` | 0x8fad4 | 0xd4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `fmt_fp` | 0x94cb8 | `fmt_fp` | 0x8fba8 | 0x16c8 | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `thunk_931e0` | 0x8dd54 | `lctrans` | 0x890bc | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_wctomb` | 0x920e0 | `musl_wctomb` | 0x8d448 | 0x24 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_wcrtomb` | 0x91fb4 | `musl_wcrtomb` | 0x8d31c | 0x12c | EQUAL | 0 | EQUAL | 0 | same |
| `fpclassifyl` | 0x90344 | `fpclassifyl` | 0x8b6ac | 0x44 | EQUAL | 0 | EQUAL | 0 | same |
| `letf2` | 0x8fb7c | `letf2` | 0x8aee4 | 0xc8 | EQUAL | 0 | EQUAL | 0 | same |
| `multf3` | 0x8fc44 | `multf3` | 0x8afac | 0x700 | EQUAL | 0 | EQUAL | 0 | same |
| `floatsitf` | 0x90ba0 | `floatsitf` | 0x8bf08 | 0x108 | EQUAL | 0 | EQUAL | 0 | same |
| `scalbn` | 0x915ac | `scalbn` | 0x8c914 | 0x98 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `subtf3` | 0x90b90 | `subtf3` | 0x8bef8 | 0x10 | EQUAL | 0 | EQUAL | 0 | same |
| `addtf3` | 0x90388 | `addtf3` | 0x8b6f0 | 0x7cc | EQUAL | 0 | EQUAL | 0 | same |
| `fe_getround` | 0x90b54 | `fe_getround` | 0x8bebc | 0x30 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `fixunstfsi` | 0x96388 | `fixunstfsi` | 0x91278 | 0x94 | EQUAL | 0 | EQUAL | 0 | same |
| `floatunsitf` | 0x9641c | `floatunsitf` | 0x9130c | 0xec | EQUAL | 0 | EQUAL | 0 | same |
| `fixtfsi` | 0x91644 | `fixtfsi` | 0x8c9ac | 0xa8 | EQUAL | 0 | EQUAL | 0 | same |
| `divtf3` | 0x90ca8 | `divtf3` | 0x8c010 | 0x904 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_vprintf` | 0x96be0 | `musl_vprintf` | 0x91ad0 | 0x1c | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stdout_write` | 0x93990 | `stdout_write` | 0x8e880 | 0xa0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `thunk_95368` | 0x97194 | `bcmp` | 0x92084 | 0x4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_memcmp` | 0x97264 | `musl_memcmp` | 0x92154 | 0x30 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_memcpy` | 0x97294 | `musl_memcpy` | 0x92184 | 0x404 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_memset` | 0x97698 | `musl_memset` | 0x92588 | 0xf8 | EQUAL | 0 | EQUAL | 0 | same |
| `musl_strchr` | 0x97790 | `musl_strchr` | 0x92680 | 0x3c | EQUAL | 0 | EQUAL | 0 | same |
| `strchrnul` | 0x977cc | `strchrnul` | 0x926bc | 0xe0 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_strlen` | 0x978e4 | `musl_strlen` | 0x927d4 | 0x90 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_strnlen` | 0x97b20 | `musl_strnlen` | 0x92a70 | 0x44 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_memchr` | 0x97198 | `musl_memchr` | 0x92088 | 0xcc | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lock` | 0x97b64 | `lock` | 0x92ab4 | 0x288 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `unlock` | 0x97dec | `unlock` | 0x92d3c | 0x74 | EQUAL | 0 | EQUAL | 0 | same |
| `syscall_cp_c` | 0x97e60 | `syscall_cp_c` | 0x92db0 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `syscall_cp_sccp` | 0x97e84 | `syscall_cp_sccp` | 0x92dd4 | 0x4 | EQUAL | 0 | EQUAL | 0 | same |
| `syscall_cp_c_tail_sccp_9_insns` | 0x97e88 | `tls_get_addr` | 0x92dd8 | 0x24 | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_atfork` | 0x97ec4 | `pthread_atfork` | 0x92e14 | 0xa4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `mremap` | 0x91e98 | `mremap` | 0x8d200 | 0xd4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `pthread_getspecific_tss_get` | 0x98f3c | `pthread_getspecific_tss_get` | 0x93e8c | 0x1c | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_key_create` | 0x992e4 | `pthread_key_create` | 0x94234 | 0xd4 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lock_unlock_pair_user_futex` | 0x9965c | `lock_unlock_pair_user_futex` | 0x945ac | 0xa4 | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_key_create_body_tsd_init` | 0x99700 | `pthread_rwlock_wrlock` + `pthread_rwlock_timedwrlock` | 0x94650 | 0x11c | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_key_atfork_tsd_table_init_11_insns` | 0x9981c | `pthread_key_atfork_tsd_table_init_11_insns` | 0x9476c | 0x2c | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_setspecific` | 0x99880 | `pthread_setspecific` | 0x947d0 | 0x34 | EQUAL | 0 | EQUAL | 0 | same |
| `set_thread_area` | 0x998bc | `set_thread_area` | 0x9480c | 0xc | EQUAL | 0 | EQUAL | 0 | same |
| `thunk_96f9c` | 0x998b4 | `pthread_testcancel` + `testcancel` | 0x94804 | 0x8 | EQUAL | 0 | EQUAL | 0 | same |
| `clock_gettime_113_vdso_fallback_169_gettimeofday` | 0x9a1e8 | `clock_gettime_113_vdso_fallback_169_gettimeofday` | 0x95138 | 0xb8 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `close` | 0x9c8b8 | `close` | 0x97808 | 0x54 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_read` | 0x9c998 | `musl_read` | 0x978e8 | 0x34 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `vm_wait` | 0x99ef8 | `vm_wait` | 0x94e48 | 0x50 | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
