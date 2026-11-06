# Decode image B Allocate relocation, cmpkit 86da41d3ef68: ADDENDUM over the call closure (the full re-run)

## 0. What this addendum is, and how it relates to the two other records
- **This directory** is the full re-run of the decode addendum on cmpkit 86da41d3ef68, over its WHOLE compare set: strictcmp3
  `cmp` on the 8 paired functions, closure_strict3 on their call closure, the kit's jtcheck on every reported member, and every
  differing target settled by hand. It supersedes, as the current version, the earlier run on cmpkit 4bbd3a74be89, which stays
  beside it unchanged (`../fncmp-cmpkit-4bbd3a74be89/`, its own RECORD.md).
- **The re-run of record of the 8-function claim** is `alloc-reloc/B/fncmp.cmpkit-4bbd3a74be89.log` and
  `alloc-reloc/cmpkit-4bbd3a74be89/` on this branch. It compares the 8 functions on two donor inputs against decode B's
  unstripped twin: S (the record's symtwin) and T (the donor's unstripped twin). This record uses C = T and D = that twin.
- **Every row where this record and that re-run disagree** (`tools/rerun8cmp.py`, `out/rerun8cmp.out`, 2 disagreements; the
  same 2 as in the 4bbd version):

  | pair | row | this record (C:D) | the re-run | why |
  |---|---|---|---|---|
  | T:E | all 8 functions, every field | - | - | **0 disagreements** |
  | S:E | PoisonShadow, accepted targets | (0, 1, 11) | (0, 0, 11) | input only: S has no STT_TLS symbol, so the kit cannot name the .got cell's TLS value and reports it (got-tls) instead of accepting it |
  | S:E | PoisonShadow, target differences | 0 | 0x48c | the same .got cell 0x9e248 / 0x99328; the re-run settles it as got-value-zero-test; both cells hold 0x1 in the images here |

  Allocator::Allocate +0xdc: the same table (0x10428 / 0x10440, 64 bytes) and the same bytes as the re-run's
  bounded-byte-table settlement (section 2).

Scope: the functions that the relocation of the closed primary-size Allocate (lib/B, 65 files; blob-identical in release
88154566652a) pairs between cgif_file_fuzzer.asan-ubsan (image "cgif B") and fuzz_decode.asan-ubsan (image "decode B"),
and their call closure. No proof file changes; rule 24: no function proved (a measurement record).

Inputs (`out/twins.out`, `drvcmp.py twins`: each pin and its twin have an equal PT_LOAD layout, and their only differing
loadable bytes are in the ELF header [0x10000, 0x10040) and `.note.gnu.build-id`):
- `<cgif-B-pin>` cgif_file_fuzzer.asan-ubsan, sha256 1c29845fe6058de6..., and `<cgif-B-twin>`, its unstripped rebuild,
  sha256 ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7.
- `<decode-B-pin>` fuzz_decode.asan-ubsan, sha256 5d05689fd5b19697..., and `<decode-B-twin>`, its unstripped twin, sha256
  6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4.
- Functions (`out/FNLIST8.txt`): Allocator::Allocate, CombinedAllocator::Allocate, SizeClassAllocator64LocalCache::Refill,
  memset, internal_mmap, StackDepotPut, PoisonShadow, TryMemCpy (the same 8 as the earlier version).

Kit: cmpkit 86da41d3ef68 (hub commit 98e50c029045, `tools/cmpkit/86da41d3ef68/`); `sha256sum -c SHA256SUMS`: 9 of 9 OK before
the run; sha256(SHA256SUMS)[:12] = 86da41d3ef68. Members: strictcmp3 65688e94214a (THE compare), closure_strict3 a98d2b3e8857,
jtcheck 8b0ea3862423, repin_check e6883477399d, drvcmp 4d70e90bc1fa, paircl 926a9a88afcd, bytecmp 1480ca2faea0, and the two
exposure scans luiscan 9ae61e4a0e01 and ambiscan 9f61b4cee422. The kit files are NOT copied here: `git archive 98e50c029045
tools/cmpkit/86da41d3ef68` gives them (`tools/run.sh` takes that directory).

## 1. Kit verdict (strictcmp3, `out/strictcmp3-cmp.out`)

`strictcmp3.py cmp <8 functions> C=<cgif-B-twin> D=<decode-B-twin> C:D`, C-string rule ON (default):

| function | cgif B | decode B | size | verdict | pcrel / real / unmeasured | accepted targets (full-bytes, got / tls, C string) | target differences |
|---|---|---|---|---|---|---|---|
| __asan::Allocator::Allocate | 0x31550 | 0x31298 | 2440 | DIFFERENT-target | 81 / 0 / 0 | (2, 0, 20) | **1: +0xdc (.rodata) data-differs** |
| CombinedAllocator::Allocate | 0x359e4 | 0x3580c | 728 | EQUAL-mod-pcrel | 16 / 0 / 0 | (0, 0, 8) | 0 |
| SizeClassAllocator64LocalCache::Refill | 0x36134 | 0x35f5c | 256 | EQUAL | 0 / 0 / 0 | (0, 0, 0) | 0 |
| memset | 0x9790c | 0x92a1c | 248 | EQUAL | 0 / 0 / 0 | (0, 0, 0) | 0 |
| internal_mmap | 0x64198 | 0x63d88 | 12 | EQUAL | 0 / 0 / 0 | (0, 0, 0) | 0 |
| StackDepotPut | 0x724e0 | 0x720d0 | 32 | EQUAL-mod-pcrel | 2 / 0 / 0 | (0, 0, 0) | 0 |
| __asan::PoisonShadow | 0x53800 | 0x5308c | 1276 | EQUAL-mod-pcrel | 61 / 0 / 0 | (0, 1, 11) | 0 |
| TryMemCpy | 0x6dcc8 | 0x6d8b8 | 400 | EQUAL-mod-pcrel | 12 / 0 / 0 | (0, 0, 6) | 0 |

Against the 4bbd version: every field of every row is the same; strictcmp3 prints the +0xdc row as DIFFERENT-target where
strictcmp2 printed EQUAL-mod-pcrel with a target difference (the same difference, a different verdict word). 45 C-string
acceptances (CSTR rows), as before.

## 2. Allocator::Allocate +0xdc: the 64-byte De Bruijn ctz table (settled, DEBRUIJN)
- +0xd8 `srli a1, a1, 0x3a`: the index is the top 6 bits of a 64-bit product, so 0 <= index <= 63;
- +0xd4 / +0xdc `auipc a2 ; addi a2, a2, lo12`: the table base, cgif B 0x10428, decode B 0x10440;
- +0xe0 `add a1, a2, a1`, +0xe4 `lbu a1, 0(a1)`: one byte read at base + index;
- so only [base, base + 64) is read, and those 64 bytes are EQUAL in both images (00 01 02 07 03 0d 08 13 ...).
- Planted control (`tools/plant_ctz.py`, `out/plant_ctz.out`): an untouched copy of the cgif-B twin gives EQUAL; a copy
  with ONE byte changed inside the table (0x10439: 0x11 -> 0xee) gives **DIFFERS**. strictcmp3 reports the row on both copies.

## 3. The call closure (closure_strict3, `out/closure_strict3.out`)
784 functions reached from the 8 roots (786 members of the union closure, `out/dupaddr.out`): EQUAL 162, EQUAL-mod-pcrel
with every target equal 522, **reported 100** (`out/closure-reported.txt`); 426 members carry value / full-bytes /
C-string acceptances. The kit's NAME-ONLY acceptances in the whole compare set: **0** (`tools/nameonly.py`,
`out/nameonly.out`: none to re-measure).

## 4. Every differing target of the 100 reported members (`out/fulldiff.tsv`, `out/certify.tsv`)
The FULL differing-target list of each reported member, from the kit's own tcmp (`tools/fulldiff.py`; never the printed
lines): **164 targets** (kit kinds: data-differs 90, lui-in-section 74). The kit's jtcheck (8b0ea3862423) was run on the
100 (`out/jtcheck.out`): it accepted 14 targets itself (tables / initializer) and left 150 open.

| settlement | targets | by |
|---|---|---|
| CSTR-EMPTY (an empty C string: a NUL byte in both images; who reads it, section 7) | 67 | settle.py |
| DEBRUIJN (64-byte bit-count tables, as section 2) | 6 | settle.py |
| INDEXED (OpenFile's 3-entry `open()` flag table: K = 2, 12 bytes equal) | 1 | settle.py |
| RELJUMP / RELSTR (a jump table / a string-offset table settled entry by entry) | 1 / 1 | settle.py |
| TABLE-REL4-JUMP (10), TABLE-ABS8-PTR (1), INITIALIZER (1): each entry measured by address | 12 | tables.py |
| RELJUMP (data-flow bound): VSNPrintf +0x1c0 (33 entries) and CFI_Parser::parseFDEInstructions +0x140 (48 entries), the two tables jtcheck 8b0ea3862423 refuses | 2 | switchbound.py (`out/switchbound.tsv`) |
| LUI: a `lui-in-section` target, settled by its use class (section 5) | 58 | luiclass.py |
| **NOT CERTIFIED: REAL 0** (a `lui-in-section` target whose uses are not all settled; section 5 lists them) | **16** | - |

No differing target is a real difference: every measurement by address found the two images' bytes or names equal. The 16
NOT CERTIFIED targets are not measured differences; they are uses the classes below do not cover.

## 5. The lui rows: one settlement class per row (`tools/luitrace.py`, `tools/luiclass.py`)
The rows: the 74 `lui-in-section` targets of section 4 (`scans/lui-targets.tsv`) and the 35 `lui-const` acceptances
closure_strict3 printed (`scans/luiconst-targets.tsv`); both lists are regenerated from the kit's output
(`tools/luitargets.py`). Exposure scans (the kit README, "Using the scans"): luiscan over both twins gives 41 of 786 members
EXPOSED, 745 exposure 0 (`scans/exposure.out`); the traced rows are the lui words of those members' targets.

**The trace.** From the lui word, the register holding V is followed over the member's control-flow graph (both arms of every
branch, the measured jump-table cases) up to every write that ends it, in BOTH images. The ops followed: add / addw / sub /
subw / sh1add / sh2add / sh3add / add.uw / and / or / xor / andi / ori / xori / slli / srli / srai / slliw / srliw / sraiw /
addi / addiw / mul / div / rem, plus mv / sext.w. A call argument is followed INTO its callee (unless a parameter contract
settles it), a value handed back is followed INTO each direct caller, 4 levels (`IN-CALLEE` / `IN-CALLER` lines,
`followups`); a register left live at a call is checked dead in the callee to its return, every path (`tools/deadreg.py`).
The two images' follow-ups are compared by header path; a caller only one program has is classed on its own.

**The stack-slot rule** (`tools/spslot.py`). A store to an sp slot is a SPILL (not a use, followed to its reloads) only when the
slot is PRIVATE: no pointer to the slot is passed to a call or ecall, stored or returned, and no sp-derived pointer reads or
writes it (whole function; stricter than "before the slot is overwritten"). Any other stack store is a STORE-DATA use. Example:
internal_usleep +0x38 stores tv_nsec to 8(sp), and `mv a0, sp ; ecall` hands the slot to the kernel: a STORE, cited below.

**The classes** (<agent> 18:5xZ and the 20:12Z addendum). Every use in both images gets one:
- (i) CALL ARGUMENT: an integer parameter whose pinned-source contract says byte count / length / count / size / flags / mode /
  prot / alignment; the declaration and the contract line are cited (`tools/contracts.py` CONTRACT; syscalls
  SYSCALL_CONTRACT). (i-b) CheckFailed v1 / v2: the CHECK line (the call's DWARF line in each image) and the CheckFailed body,
  sanitizer_termination.cpp:67-89, where v1 / v2 appear only in the Printf of lines 70-72 (`0x%zx`, cast to uptr).
- (ii) RETURN: an integer that is not an address by its meaning (RETURNS: sysconf, __tm_to_secs, __year_to_secs).
- (iii) DISPLACEMENT: a load / store / AMO base or a pointer passed / stored, onto an object pointer (argument, load,
  allocator return: luitrace OFFSET-RUNTIME-OBJECT), or onto an image address with the FULL address compared as symbol +
  offset in both images (OFFSET-SAME-SYMBOL).
- (iv) STORE into an integer, non-address field: the struct line is cited (STORES: BlockInfo::stored_, Mutex::state_,
  StaticSpinMutex::state_, AllocatorStats::stats_[Mapped], AsanStats::mmaped, RegionInfo fields, AllocatorOptions
  min_redzone / max_redzone, timespec tv_nsec).
- (c) COMPARE: a branch / compare operand. A row classed (c) alone shows only compares, private spills / reloads and
  overwrites in its trace.
- (d) FRAME: an sp-derived frame base.
- (e) DEAD-AT-CALL: the callee never reads the register on any path to its return; or a caller-saved register handed back
  and traced on in each caller. At an INDIRECT call: t0-t6 are never read (RISC-V psABI, riscv-non-isa/riscv-elf-psabi-doc
  at master 9b2767e2a885 (2026-10-27; riscv-cc.adoc last changed at riscv-non-isa/riscv-elf-psabi-doc 1ac24703c0a6, blob 9d7a7b69f2f6), riscv-cc.adoc section
  "Integer Register Convention" lines 21-25 and section "Integer Calling Convention" lines 178-179),
  nor an argument register at or beyond the pointer type's arity (REAL(x): the INTERCEPTOR declaration, interception.h:255-262;
  callbacks: DieCallbackType, the malloc hook, FindThreadCallback; `contracts.py` REAL_ARITY / CALLBACK_ARITY).

A row settles when every use in both images has a class, the traces both images have are the same, no follow-up was cut at
the depth limit, and every address use compared equal. Its class is the set of its use classes.

**Result** (`scans/luiclass.tsv`: every classed use with its citation, every unsettled use; `scans/luiclass-summary.md`:
the tables below and the 39 NOT CERTIFIED rows one by one, `tools/luisummary.py`):

| rows | settled | NOT CERTIFIED: REAL 0 |
|---|---|---|
| 74 `lui-in-section` (section 4) | 58 | 16 |
| 35 `lui-const` | 12 | 23 |
| **109** | **70** | **39** |

Settled rows per class (a row counts in each class its uses have): (c) 27, (e) 40, (i) 17, (i-b) 3, (ii) 7, (iii) 28,
(iv) 5; (d) 0. A row classed (c) alone: 6 (only compares, private spills / reloads and overwrites in its trace).

Why the 39 rows stay NOT CERTIFIED (a row can have several reasons): an indirect call whose pointer type the record does not
name, with the register live (31 rows); a follow-up cut at the 4-level limit (17); a STORE into a field no citation names
(16, e.g. the variadic register save areas of Printf / Report and cgif's own structs); a callee that reads the register
beyond its signature, i.e. a variadic save (15); a value handed back to a function with no direct caller (11: callbacks,
module constructors, virtual methods); the dead-at-call analysis cut by depth / recursion (7); a variadic argument not
followed into its callee (5); a syscall argument with no contract (2); luitrace REVIEW (2); a V-derived base in a follow-up
only one image has (1). No unsettled use is a measured difference: each is a use the classes do not cover. Most of the 23
`lui-const` rows are the Mutex masks 0xfffff (kReaderLockMask) / 0x100000 (kWaitingReaderInc), inlined in many functions,
whose values reach the error-report paths (Printf / Report / CheckFailed) through registers the callees save as varargs.

**Planted controls** (`tools/plant_luiclass.py`, `scans/plant_luiclass.out`), each a FILE copy of the cgif-B twin:
- (a) a lui value that feeds a STORE BASE through `add` (InitializeAsanInterceptors +0x44 `add a0, a2, zero`, +0x48
  `sd zero, 0(a0)`): **NOT CERTIFIED** (luitrace REVIEW: the base is V itself, `ABSOLUTE V-derived`).
- (b) a lui call argument to a `void *addr` parameter (SealedReserveShadow +0x7c `mv a0, a3`, internal_mmap's addr):
  **NOT CERTIFIED** (internal_mmap's syscall argument a0 has no contract; no address parameter settles by type).

## 6. The kit's fail-opens
**FAIL-OPEN #3, two lui values in one base** (`tools/luilui.py`, `scans/luilui.out`). Every compared function with 2 or more
lui words in either image (101 functions), both images, its own data-flow over expression trees. lui+lui->base: **21 sites,
targets equal**: 19 OBJECT (the same base object and the same index expression in both images: SWAR popcount / clz size-class
indices and StackDepot hash masks onto an allocator, stats or depot object) and 2 TABLE (a 64-byte De Bruijn table read
through a lui-built index; the 64 bytes equal in both images). Planted controls (`tools/plant_luilui.py`,
`scans/plant_luilui.out`): (c) the displacement lui of LargeMmapAllocator::Allocate +0x24c changed 0x40 -> 0x41: **DIFFERS**;
(d) one byte of PackedCounterArray's table at 0x104e8 flipped: **DIFFERS**.

**The logical-op fail-open** (<agent> 19:20Z): the trace follows add / sub / sh*add / and / or / xor / andi / ori / xori /
slli / srli / srai, plus mv, up to the register's next write (section 5); the 35 `lui-const (dataflow)` rows are traced
(section 5).

**The fail-opens (a)-(h)** (<agent> 21:53Z; `tools/constbase.py`, `scans/constbase.out`): a whole-closure scan of EVERY
constant built without auipc, in all 786 members, both images.

| shape | how the scan covers it | sites showing it |
|---|---|---|
| (a) the load / store immediate | the full address is the value + the instruction's immediate | 413 with a non-zero immediate |
| (b) an addi / addiw chain | constants fold through addi / addiw; mixes keep the expression tree | (all) |
| (c) ori / xori / slli | the same, for every immediate and register ALU op | (all) |
| (d) a stack spill, FP move or CSR round trip | a spill to a PRIVATE slot (spslot.py) and its reload keep the value; fmv.* and csrrw / csrr are followed (0 fmv and 0 csr instructions in the closure); a store anywhere else is a STORED site | 88 reloads followed in each image |
| (e) a jump-table arm reached only by fall-through | objscan.Fn's graph keeps every fall-through edge and follows `jr` into the measured cases (all 13 switch `jr` of the closure have them); the other 32 `jr t1` jump through a loaded function pointer (interceptor trampolines, REAL(x)) in functions with no switch, and are tail calls | (all) |
| (f) an in-function callee (caller a0-a7) | a value in a0-a7 at a call or tail call (direct or through a pointer) that may form an address (an expression, or a number >= 0x10000) is a PASSED site, and in a0 / a1 at a return a RETURNED site, compared as a full address; every callee is analysed on its own | 2106 |
| (g) c.lui | cannot occur: every one of the closure's 70,756 instructions is 4 bytes in each image (ELF e_flags 0x4, the RVC bit clear) | 0 |
| (h) an address built WITHOUT lui | every `addi rd, zero, imm` (4226 in each image) is a tracked constant beside the 558 lui | 2036 with no lui among their constants |

**Result** (`scans/constbase.tsv`, kept as `scans/constbase.part-1.tsv` and `scans/constbase.part-2.tsv`;
`scans/constbase-summary.md`): 287 functions hold a site; **2934 sites, 0 DIFFERS**:
- 2787 EQUAL: the same symbol + offset, the same number outside both images, the same base + displacement + index
  expression, or the same table bytes;
- 24 NUMBER-IN-IMAGE settled: the same number in both images that falls inside an image section (a size or mask such as
  0x100000 or 0x40000: by value it names different symbols in the two images), settled by its lui row's class (section 5);
- 21 NOT CERTIFIED: REAL 0: such a number whose lui row is NOT CERTIFIED, or built with an `addi` from zero (no lui row);
- 102 REVIEW, counted NOT CERTIFIED: REAL 0: the expression was dropped, or a base summand has no provenance (a linear scan
  that crosses a call), in 21 functions (DenseMap lookups, LzwEncode, `__libc_malloc_impl`, `alloc_slot`, `__intscan`,
  `do_tzset`, parseCIE / parseFDEInstructions, StackDepotGet / Put, internal_allocator, and others; the list is in
  `scans/constbase-summary.md`).

**The 8 CLAIM functions**: 96 sites (Allocator::Allocate 71, CombinedAllocator::Allocate 23, Refill 2; the other 5 build no
tracked constant into a site), **every one EQUAL**.

Planted controls (`tools/plant_constbase.py`, `scans/plant_constbase.out`): (e) the lui displacement of
LargeMmapAllocator::Allocate +0x24c 0x40 -> 0x41: **DIFFERS**; (f) Refill +0x60 `addi a3, zero, 0x20` -> 0x21, a constant built
without lui that is the loop-entry value of what +0x98 stores: **DIFFERS**.

## 7. The C-string rows (`tools/escape.py`, `out/escape.tsv`)
67 C-string targets, all CSTR-EMPTY. PRIMARY settlement: the named readers of each row, found by following every pointer to
the string (the whole-image field scan `tools/objscan.py` / `tools/ptrfollow.py`, whose PTRSTORE rule now counts a store to a
non-private stack slot as an escape, spslot.py): 52 rows ARG-ONLY (the string only passed to named callees), 15 ESCAPES
(stored, with the field's readers named). 0 rows whose uses differ between the images, 0 whose primary settlement differs,
0 with an UNRESOLVED or NOT SCANNED part. Second measurement: 533 equal bytes past the NUL in both images for every row.

## 8. Functions looked up by name (`tools/dupnames.py`, `tools/dupaddr.py`)
Each of the 8 functions passed to `cmp` by name has exactly 1 symtab entry in each twin. Of the 786 closure members, 4 carry
a name with more than one symtab entry (`__asan::MemToShadow`, from asan_errors / asan_linux / asan_poisoning / asan_thread);
each was re-checked at the address its callers call, in both images: EQUAL-mod-pcrel (the union closure by address: EQUAL
163, EQUAL-mod-pcrel 523, reported 100).

## 9. Verdict
- The 8 paired functions: the same code (7 EQUAL / EQUAL-mod-pcrel; Allocator::Allocate's one target difference, +0xdc, is the
  settled De Bruijn table, its control caught). Their 96 constant sites (section 6) are all EQUAL.
- The closure: 164 differing targets; 148 settled by a measurement, 16 NOT CERTIFIED: REAL 0 (lui uses outside the classes);
  no measured difference. The lui rows: 70 of 109 settled, 39 NOT CERTIFIED: REAL 0 (section 5). Two lui values in one base:
  21 sites, all equal. The constant scan for the fail-opens (a)-(h): 2934 sites, 0 DIFFERS, 2811 equal or settled, 123 NOT
  CERTIFIED: REAL 0 (section 6). C strings: 67 rows, every reader named. NAME-ONLY acceptances: 0.
- 7 planted controls, each refused: plant_ctz (DIFFERS), (a) (b) lui classes (NOT CERTIFIED), (c) (d) lui+lui (DIFFERS),
  (e) (f) constant scan (DIFFERS); plus 1 untouched baseline copy (plant_ctz's), which is accepted (EQUAL). The kit's own
  controls (negctl.py and the 40-plant suite.py), run here: the same verdicts as the kit registered (section 11).
- No CLAIM row moved toward a real difference.
- The earlier version (`../fncmp-cmpkit-4bbd3a74be89/`) ran its field scan (its section 4f) before the stack-slot rule of
  section 5; this version's field scan (section 7) applies it.

## 10. Reproduce: `tools/run.sh`
`tools/run.sh KIT_DIR CGIF_B_PIN CGIF_B_TWIN DECODE_B_PIN DECODE_B_TWIN`, with KIT_DIR the kit as run (`git archive
98e50c029045 tools/cmpkit/86da41d3ef68`). It checks the kit's SHA256SUMS, then writes every `out/` and `scans/` file of this
record in order. Every script takes its paths from the environment (`tools/common.py`); the planted copies go to PLANTDIR,
never into the record; progress and timings go to stderr, never into the record. rerun8cmp.py reads the 8-function re-run
beside the record (`../fncmp.cmpkit-4bbd3a74be89.log`, `../../cmpkit-4bbd3a74be89/settled.tsv`).

**End-to-end runs.** run.sh was run as ONE command in two fresh copies of this directory, at the same time, each with its own
(random) Python hash seed. Each copy held only `tools/`, the input `out/FNLIST8.txt`, `kit/SHA256SUMS` and `RECORD.md`, beside
the two 8-function re-run files taken from the branch (`git show 6e74a7e62d4f:...`, sha256 eff9ccb831d8 / 41d7ccff1f7f), with
KIT_DIR a fresh `git archive` of the kit (`sha256sum -c SHA256SUMS`: 9 of 9 OK). Both exited 0 (51 min 39 s and 50 min 43 s).
- `diff -r` of the two copies after the run: **0 lines** (the whole directories).
- `diff -r` of the second copy against the record as it then stood (`out/`, `scans/`, `tools/`, `kit/`; 50 output files):
  **0 lines**.

After the review (section 12) changed the text of three citations in `tools/contracts.py`, the steps whose outputs carry
them were re-run in the record (luitrace.py twice, luiclass.py, luisummary.py, constbase.py, certify.py,
plant_luiclass.py), and run.sh was run once more as ONE command in a third fresh copy, built the same way with the fixed
`tools/` (exit 0). `diff -r` of that copy against this record (`out/`, `scans/`, `tools/`, `kit/`): **0 lines**. So the
`out/` and `scans/` files here are what run.sh writes from `tools/` as committed. `RECORD.md`, `REVIEW.md` and `controls/`
were written after the runs.

How the record got there (every count and every verdict stayed the same throughout: the constbase count lines, its 287
row verdicts, and the luitrace verdicts are equal in every run):
- The first end-to-end run (one copy) against the step-by-step outputs: 165 diff lines in 5 files. `out/closure_strict3.out`
  and `out/strictcmp3-cmp.out` carried the `time` lines of the step-by-step runs at their end. `tools/spslot.py` iterated a
  SET of argument registers, so the reason text of one refused spill (internal_usleep +0x38: the frame pointer given to the
  kernel "in a0" or "in a1") depended on the hash seed; it now iterates a0..a7 in order. `tools/constbase.py` picked a
  widened loop value's entry values by `str()` of tuples that hold frozensets, so REVIEW texts depended on the hash seed; the
  order is now canonical.
- The second pair of runs: the two copies still differed in `scans/constbase.out` / `.tsv` (the REVIEW texts of 10
  functions: a site's values were ordered by `str()` of a field that is the same for all of them). The order is now total;
  constbase.py then gave the same bytes under two hash seeds, and the third pair of runs is the one above.

## 11. The kit's own controls (`controls/`)
Run as the kit README prescribes ("CONTROLS (controls/)"), by `controls/run-controls.sh RUN_DIR REG_RUN_ROOT`: fresh copies of
the kit (`git archive 98e50c029045 tools/cmpkit/86da41d3ef68`, 9 of 9 sums OK) and of the old kit (`git archive 3c3e62ee278
tools/cmpkit/4bbd3a74be89`, 7 of 7 OK), the cross-check directory (the old kit plus the kit's `controls/xchk/jtcheck_strict2.py`),
the kit's `controls/oldtools/SHA256SUMS` (12 of 12 OK, checked by suite.py at start); `negctl.py kitrun`; `SUITE_OLD_KIT=<old
kit> SUITE_XCHK_JT=<cross-check>/jtcheck_strict2.py suite.py <kit> OUT PLANTED 16`. `controls/compare.py` compares the outputs
with the ones the kit registered in its `controls/` (`controls/compare.out`):

| control | output here | the kit's registered output | result |
|---|---|---|---|
| negctl.py (repin_check CONTROL (1)/(2)) | `controls/negctl.out` | `repin-negctl.out` | **byte-identical**: natural FA:DP 11 target differences, baseline FA:DA 0, planted main+0x50 `jal __wrap_malloc -> __wrap_free` caught, under the old and the kit repin_check |
| suite.py, 40 plants: SUMMARY.tsv | `controls/suite-SUMMARY.tsv` (473 rows) | `SUMMARY.tsv` (473 rows) | the seven verdict columns (plant, family, tool, sha12, version, baseline verdict, planted verdict) **identical in all 473 rows**; the evidence column identical once the five directories a run chooses are labelled, except in 3 rows (below) |
| suite.py: planted.sha256 | `controls/suite-planted.sha256` (106 lines) | `planted.sha256` | identical once the directories are labelled |
| suite.py: every raw tool output | (905 files; not kept here) | `suite-raw.tar.xz` (905 files) | **all 905 identical** once the directories are labelled |

The 3 rows: Q1, V1 and V2 under paircl-NEW. Their evidence is cut at 600 characters in both runs, and it holds an output
directory path, whose length differs between the runs, so the cut falls at another place: for V1 and V2 the shorter text is
a prefix of the longer; for Q1 the cut falls inside the path itself. Their raw outputs (above) are identical.
The kit-version cells (236): caught 196, caught-tsv 1, refused 4, equal-listed 24 (4 of them its own row with other closure
members reported), noteq-both 5, EQUAL 6: the same as the kit registered, row by row. The kit's other controls (regress3.py,
census_check.py) were not run here.
The shipped `controls/negctl.out` and `controls/suite-planted.sha256` are the relative-path re-run, equal to the first
run's outputs after the normaliser in `controls/RERUN-RELATIVE.md`; the first run's outputs are kept in the unit's internal
record by sha256 (negctl.out 314168a26e3bc507d72d001d8aaf2cbedf47d1dc50dc6bb0bbce497ccf984860, suite-planted.sha256
73bed249505318d687382bf5235f4c67cf506b965dee97b9021fd6de6b51a453).

## 12. Review (`REVIEW.md`)
A fresh reviewer read this record (sections 0-11, `tools/`, `out/`, `scans/`, `controls/`) and re-ran parts of it
independently: the 8-function compare and the closure from a pristine kit copy, its own tracer on all 70 settled lui rows,
the constant scan's counts, the lui+lui sites and the four plant scripts. Verdict: **APPROVE, 0 rejected rows, 3 doubtful
rows**. `REVIEW.md` is the review as written, scrubbed for publication; its line numbers refer to the record before the
fixes below. All three are fixed:
- **D1** (section 9 said "8 planted controls, each refused"): there are 7 refused plants and 1 untouched baseline copy that is
  accepted (EQUAL). Section 9 now says so. No measurement changes.
- **D2** (`tools/contracts.py` REAL_ARITY cited `sanitizer_common_interceptors.inc` 6407 / 6412 for fflush and 6426 / 6433
  for fclose): at compiler-rt 87f0227cb601 the INTERCEPTOR lines are **6408** and **6427** and the `REAL(..)(fp)` lines
  **6413** and **6434** (read again here). Fixed in contracts.py.
- **D3** (the RISC-V psABI citation had no pin): it now names riscv-non-isa/riscv-elf-psabi-doc at master 9b2767e2a885
  (2026-10-27), the commit current when the document was read; riscv-cc.adoc is byte-identical at riscv-non-isa/riscv-elf-psabi-doc 1ac24703c0a6 (its last
  change, 2026-10-08; blob 9d7a7b69f2f6). Lines 21-25 (section "Integer Register Convention") and 178-179 (section "Integer
  Calling Convention") were read again at that commit and hold the cited text. Fixed in contracts.py and section 5.

What the fixes changed (the record before the fixes against the record after them, every `out/` and `scans/` file):
- 47 of 50 files are byte-identical.
- `scans/luitrace.tsv` and `scans/luitrace-luiconst.tsv` are identical once the three old citations are replaced by the new
  ones (4 fflush, 4 fclose and 55 psABI citations).
- `scans/luiclass.tsv`: every cell outside the citation column (class, settled / NOT CERTIFIED, unsettled uses) is identical.
  The citation column differs only because luiclass.py cuts an (e) citation at 220 characters, and the longer new texts are
  cut at another place. luiclass.py was run without that cut on the old and on the new traces: the old output with the three
  replacements equals the new one. Of the 5644 citation entries, 355 are cut.
- No count, class or verdict changed.

## Publication scrub
Host paths of the four images are replaced by `<cgif-B-pin>`, `<cgif-B-twin>`, `<decode-B-pin>`, `<decode-B-twin>`; planted
copies by `<plantdir>`. `out/closure_strict3.out` is kept as text. `scans/constbase.tsv` (7,420,464 bytes, over the
repository's 5 MiB cap per file) is kept in two parts cut at a line boundary: `scans/constbase.part-1.tsv` (the header
line and rows 1-195) and `scans/constbase.part-2.tsv` (rows 196-287, no header: the columns are part 1's).
`cat scans/constbase.part-*.tsv` restores `scans/constbase.tsv` byte for byte (sha256
`343c44b803c2d23acc1dae29a4d6cdaac10c25026636198875675773e6308aff`).
