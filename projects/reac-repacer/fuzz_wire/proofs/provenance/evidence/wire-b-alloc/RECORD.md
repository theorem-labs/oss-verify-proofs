# WIRE-B-ALLOC bytecmp record: fuzz_wire image B malloc / free chain against fuzz_grant image B

Read-only on every input. Version of record: **cmpkit 86da41d3ef68** (strictcmp3 the one compare; closure_strict3 by
name; paircl 926a9a88afcd against the stripped grant pin; drvcmp twins; and the kit's two exposure scans, luiscan
and ambiscan), with **jtcheck 226254f48c97** (`tools/jtcheck.py`, from the original sha256 226254f48c97; `tools/DIFFS.md`), the jtcheck of record for table verdicts, in place of
the kit's jtcheck 8b0ea3862423, **plus this record's hand traces of every lui value of every compared
function** (`tools/luitrace.py`, settled by the classes of the unit owner's rulings).
The previous version of record, cmpkit 4bbd3a74be89, is kept in `earlier/v4bbd3a74be89/` (its tools, outputs, run.sh
and RECORD.md) as its run wrote it, except the rewrites `earlier/SCRUB.tsv` lists: the role rewrite, the dropped
times of day, the forbidden-word loader, the sha256 pin repair and the DIFFS.md note (each described under "Names"
below). `earlier/` ships `v4bbd3a74be89/` (with its own run.sh) and `va88c2822a0f2/` (with its own run.sh; it holds its own earlier versions `v9cbc3553c09e/`, which have no run.sh of their own: its run.sh runs them). `./run.sh` repeats every measurement. The
committed slice is `commit/` plus this file; the file names below are those in `commit/`.

**Verdict (cmpkit 86da41d3ef68 with jtcheck 226254f48c97 + hand traces): NO REAL DIFFERENCE: 0 DIFFERS anywhere.** fuzz_wire B's malloc / free
interceptor chain against fuzz_grant B's (pinned fde52226dc48). The 4 CLAIM rows, the roots, are EQUAL /
EQUAL-mod-pcrel with 0 differing targets, as under 4bbd3a74be89. The kit reports 107 closure rows (by name 100, paired 107):
62 settle in full by the settlement classes; the other 45 carry the kit's 76 `lui-in-section` targets or one of the
2 tables jtcheck 226254f48c97 refuses (settled by hand in `commit/handtable.out`, 2 of them, under the rule stated
below; part (4), a non-writer's read, confirmed both). The hand traces settle the lui-in-section targets
use by use: 18 targets in full (18 by class or measured non-row, 0 compare-only, 0 with no use),
58 with at least one use **NOT CERTIFIED: REAL 0**. Over every lui value of the 943 compared functions (633 lui words): 0 DIFFERS;
595 use rows settled ((i) 322, (ii) 7, (iii) 251, (iv) 7, STORE-UNREAD 8); **NOT CERTIFIED: REAL 0 on 1018 use rows**.
123 uses lie only beyond a call that never returns (`UNREACH` lines: on no feasible path; listed, not counted as rows).

**Ops followed (the unit owner's ruling), each up to the register's next write:** add, sub, sh1add, sh2add, sh3add, add.uw, and, or, xor, sll, srl, sra, slt, sltu, mul, div, rem and their -w forms; mv, addi, addiw, andi, ori, xori, slli, srli, srai, slti, sltiu; a store into a PRIVATE stack slot (no pointer to its frame object leaves the function) and every reload of it; jump-table arms, also those reached by fall-through; in-function callees; a caller-saved register across a call unless the call is measured to end it.

Every op on a traced value keeps the result TRACED (it stays a value derived from the lui, followed to its uses). add /
sub / sh*add keep its form (anchor + constant); every op is computed exactly on known numbers (div / rem and their
unsigned and -w forms included); on anything else the result is an unknown number, so a base built from it is NOT
CERTIFIED, never EQUAL. Plant (c) below checks this: a lui value reaches a store base only through `divuw` and `slli`.

**lui+lui->base (the unit owner's ruling, FAIL-OPEN #3):** 25 sites where two or more lui values reach one load / store / jalr /
AMO base: 17 settled (every base row there is (iii): an object-pointer displacement, or the same symbol + offset in X
and Y), 8 NOT CERTIFIED: REAL 0 (the base's constant is unknown on some path, so no target can be named), 0 DIFFERS.
Plant (a) below is this class: the kit reads it EQUAL, the hand trace reads it DIFFERS.

## The eight fail-open shapes of cmpkit 86da41d3ef68 (the unit owner's ruling): how this record covers each

One line per shape. "lui" counts are uses the lui traces met (`commit/luitrace.tsv`, its `# SHAPES` line); "present"
counts are occurrences in the 943 compared functions of X / Y (`commit/basescan.tsv`, its `PRESENT` lines).

- **(a) load / store immediate (V+imm):** covered. Every lui-derived base adds the instruction's immediate before it is
  named (`luitrace.py` trace(), 496 load and 310 store bases); every base of the compared set, lui or not, is named with
  its immediate in X and Y by `basescan.py` (23361 bases; present with a nonzero immediate: 17902 / 17901).
- **(b) addi / addiw chain:** covered. addi sums its immediate, addiw sums and sign-extends from 32 bits (luitrace: 1205
  addi and 850 addiw steps, 2055 in all; anchor() and basescan's val() follow the same chains backwards).
- **(c) ori / xori / slli:** covered, fail-closed. On a known number every OP-IMM and R-type op is computed exactly
  (luitrace imm_op / alu: 479 OP-IMM and 33 R-type steps); on an anchored or unknown value the result is an unknown
  number (1857 OP-IMM and 2590 R-type steps), so a base built from it is NOT CERTIFIED, never EQUAL.
- **(d) stack spill, FP move, CSR round trip:** spills covered, with the escape rule of the egress review: 53 stores
  into private slots followed into 140 reloads; the traces met a store into a slot of an escaping frame object 262
  times (the `# SHAPES` count: once per lui trace that meets the store, in X, in Y, and in X again with each noreturn
  call's fall-through put back); those stores are 90 STORE rows (`ROW` lines, one per lui value and store): 7 settle
  by class (iv), 8 as STORE-UNREAD and 75 are NOT CERTIFIED: REAL 0.
  FP moves: none present (integer -> FP 0 / 0, FP -> integer 0 / 0, FP loads / stores 0 / 0);
  CSR writes: none present (0 / 0; the one CSR instruction, in CheckFailed, only reads `cycle`). Either would be a
  NOT CERTIFIED row (luitrace kinds `fpmove`, `csr`).
- **(e) jump-table arm reached by fall-through:** covered. `arms_of` reads every table the function addresses and adds
  an edge from each indirect jump to each arm (204 / 204 arms, 17 / 17 of them also reached by fall-through or a branch;
  47 / 47 indirect jumps, every one without an arm is a tail call through t1 or musl `call`); the lui traces carried
  values into such an arm 10 times; anchor(), origin() and basescan use the same edges.
- **(f) in-function callee (caller's a0-a7):** covered. 8 / 8 in-function calls (recursion, and calls to an
  undefined weak symbol that the linker turned into a call to itself): the values are arg ROWs at the call AND are
  followed into the callee on the call edge (8 times); the edge carries the caller's registers into anchor() too.
- **(g) c.lui:** absent: 0 / 0 two-byte parcels in the compared set (c.lui 0 / 0). A function with any two-byte
  parcel is refused whole (`UNMEASURED`) by luitrace and basescan.
- **(h) addresses built without lui (auipc-only, gp-relative, loaded pointer + immediate):** covered by `basescan.py`:
  23361 bases: 20292 EQUAL (every form named by its symbol + offset, or by a stack / tp / object anchor, the same in X and
  Y), 2427 EQUAL+INDEX (the same named anchor plus an index), 199 EQUAL+BYTES and 30 EQUAL+TABLE, 413 NOT CERTIFIED: REAL 0,
  0 DIFFERS; 2002 of them auipc pairs the kit resolves; gp-relative bases 0 / 0;
  tp-relative bases 0 / 0. The 4 roots: 70 bases, 66 EQUAL and 4 EQUAL+INDEX (below).
  **Unnamed addresses (the egress re-review, RR1):** 231 bases hold an address inside a section that no symbol covers
  (`(.rodata)+offset`). They are never compared by that name: a constant address is EQUAL+BYTES when the bytes the
  instruction reads there are equal in X and Y (199 bases); an index into such an object, or a constant address whose
  bytes differ, is EQUAL+TABLE only when jtcheck 226254f48c97's `same_target` (over the table shape its proof gives on
  both images) or a settle.tsv
  ACCEPT row at the word that forms the address settles the target pair, and the row is cited (30 bases); anything
  else is NOT CERTIFIED. Of the ANON bases, 2 come out NOT CERTIFIED and 0 DIFFERS (the `unnamed:` column of
  `commit/basescan.tsv` gives each one's evidence).

## Every base of the 4 roots (shape h; `commit/basescan.tsv`, `ROOTBASE` lines)

- `__interceptor_trampoline_malloc`: 0 bases (a single `jal zero` to the interceptor).
- `___interceptor_malloc`: 33 bases: EQUAL 33.
- `__interceptor_trampoline_free`: 0 bases (a single `jal zero` to the interceptor).
- `___interceptor_free`: 37 bases: EQUAL 33, EQUAL+INDEX 4.

Every root base that is not a stack slot (the stack slots are the same `sp at entry +N` in X and Y):

| root | word | instruction | X | Y | verdict |
|---|---|---|---|---|---|
| `___interceptor_malloc` | +0xcc | `ld a1,1332(a1)` | ADDRESS: the .got cell of _ZN11__sanitizer21common_flags_dont_useE+0x0 | ADDRESS: the .got cell of _ZN11__sanitizer21common_flags_dont_useE+0x0 | EQUAL |
| `___interceptor_malloc` | +0xd0 | `lbu s3,34(a1)` | ADDRESS: _ZN11__sanitizer21common_flags_dont_useE+0x22 | ADDRESS: _ZN11__sanitizer21common_flags_dont_useE+0x22 | EQUAL |
| `___interceptor_free` | +0x48 | `ld a3,8(a2)` | INDEX: _ZN11__sanitizerL26internal_alloc_placeholderE+0x0 + an index +8 | INDEX: _ZN11__sanitizerL26internal_alloc_placeholderE+0x0 + an index +8 | EQUAL+INDEX |
| `___interceptor_free` | +0x54 | `ld a2,8(a2)` | INDEX: _ZN11__sanitizerL26internal_alloc_placeholderE+0x0 + an index +8 | INDEX: _ZN11__sanitizerL26internal_alloc_placeholderE+0x0 + an index +8 | EQUAL+INDEX |
| `___interceptor_free` | +0x6c | `lbu a0,0(a0)` | INDEX: a value loaded by `ld a2,8(a2)` at +0x54 + an index +0 | INDEX: a value loaded by `ld a2,8(a2)` at +0x54 + an index +0 | EQUAL+INDEX |
| `___interceptor_free` | +0xd0 | `lbu a0,0(a0)` | INDEX: the return of _ZNK11__sanitizer11TwoLevelMapIhLy32768ELy4096ENS_21LocalAddressSpaceViewEE6CreateEm + an index +0 | INDEX: the return of _ZNK11__sanitizer11TwoLevelMapIhLy32768ELy4096ENS_21LocalAddressSpaceViewEE6CreateEm + an index +0 | EQUAL+INDEX |
| `___interceptor_free` | +0x13c | `ld a1,1684(a1)` | ADDRESS: the .got cell of _ZN11__sanitizer21common_flags_dont_useE+0x0 | ADDRESS: the .got cell of _ZN11__sanitizer21common_flags_dont_useE+0x0 | EQUAL |
| `___interceptor_free` | +0x140 | `lbu s3,34(a1)` | ADDRESS: _ZN11__sanitizer21common_flags_dont_useE+0x22 | ADDRESS: _ZN11__sanitizer21common_flags_dont_useE+0x22 | EQUAL |

The EQUAL+INDEX root bases, traced by hand (p = s1 = the pointer `free` received in a0; the code is the same in X and Y):
- `___interceptor_free` +0x48 `ld a3,8(a2)`: a2 = internal_allocator() + ((p >> 32) << 3): +0x30 `jal internal_allocator`, +0x3c `srli a1,s1,32`, +0x40 `slli a2,a1,3`, +0x44 `add a2,a0,a2`; internal_allocator() returns &internal_alloc_placeholder in X and in Y (basescan callee_return), so the address is internal_alloc_placeholder + 8 + 8*(p >> 32).
- `___interceptor_free` +0x54 `ld a2,8(a2)`: the same a2 as at +0x48 (no write between): internal_alloc_placeholder + 8 + 8*(p >> 32).
- `___interceptor_free` +0x6c `lbu a0,0(a0)`: a0 = (the pointer loaded at +0x54) + ((p >> 20) & 0xfff): +0x58 `srli s3,s1,20`, +0x60 `slli s3,s3,52`, +0x64 `srli a0,s3,52`, +0x68 `add a0,a2,a0`.
- `___interceptor_free` +0xd0 `lbu a0,0(a0)`: a0 = (the return of TwoLevelMap::Create) + ((p >> 20) & 0xfff): +0xbc `jal Create`, +0xc0 `mv a2,a0`, +0xc4 `slli s3,s3,52`, +0xc8 `srli a0,s3,52`, +0xcc `add a0,a2,a0`.

## Criterion

Two settlements, each fail-closed: a row is settled only by a named class with its evidence, else it stays
UNSETTLED / NOT CERTIFIED.

**1. The kit's differing target pairs** (`tools/settle.py`, `commit/settle.tsv`, `commit/ACCEPTANCES.tsv`): for every
target pair `strictcmp3.tcmp` reports for a function the kit calls "other" (the full list, not the printed first 2),
one ACCEPT row names a reader of the target and the extent it reads, and compares exactly that extent in X and Y.
Classes: TABLE (jtcheck 226254f48c97's `table`, over the entry size and count its proof gives on both images; one ENTRY
row per entry, each the same function-relative offset, C string, or symbol + offset), INDEXED (a bounded index into
a table: `srli *,58`, `andi *,M`, or a guarded `slli`), CSTR (every reader reads a C string: a `const char *`
parameter, a `%s` argument, an lb/lbu inside it, a compare, a spill / reload, a return), RELSTR, INITIALIZER (a
memcpy source, jtcheck's `copy_len` + `blob`), NOT-PCREL (an I/S word whose base no auipc reaches on any
CFG path: 4 raw bytes), CSTR-ESCAPE (`tools/escape.py`: an escaping empty-string pointer, every use measured, field
reads by a whole-image scan, `tools/objscan.py`, `commit/fieldscan.tsv`), and REFUSED (an indexed table jtcheck
226254f48c97 does not prove: no proof, not a difference; settled by hand in `commit/handtable.out`, below). settle.py
loads jtcheck 226254f48c97 (`table` / `copy_len`, with the shape its proof gives; 4bbd had `bound` / `table` /
`memcpy_len`) and reads a string table's entries by jtcheck's own rule (a C string, or equal bytes).

**2. Every lui value of every compared function** (`tools/luitrace.py`, `commit/luitrace.tsv`): a forward dataflow over
the function's CFG follows the lui value and every value computed from it (the ops above), in X and in Y; the lui
value and the event list must be the same in both, else DIFFERS. Each use is ONE row with ONE class:
- **(i) CALL ARGUMENT**: the callee's parameter at that register is an integer (a `uptr` included) that the pinned
  source names a byte count / length / count / size / flags / mode / prot / alignment (the unit owner's ruling (a)), and the
  type the mangled name carries agrees; or a hand citation of the contract (`commit/cite-extra.tsv`: CheckFailed's
  v1 / v2 (b)). A pointer, or a `uptr` address parameter, never settles.
- **(ii) RETURN**: the pinned source's return type is an integer, not address-sized.
- **(iii) DISPLACEMENT**: the base is ONE object pointer (a parameter, a stack address, a call's return, a loaded
  value: (d)); or a lui-built base whose FULL address is the same symbol + offset in X and Y (else DIFFERS).
  A sum of two anchors, a scaled anchor or a widened form never settles.
- **(iv) STORE** (the owner's class; the wire review, R1 / R2): a store into a stack slot of a frame object whose
  address leaves the function settles only when every escape that may cover the slot is a direct call, at least one
  callee receives the object as a parameter the pinned source types as a struct (`commit/cite-extra.tsv` `param` rows),
  and inside it the stored bytes are integer, non-address members or padding (`field` / `size` rows, each member with
  its declaration line). The row lists the callee's reads of those bytes (loads at that offset of the pointer it
  received, followed into the functions it passes the pointer to). Any other escape must be a callee that cannot read
  memory, or a cited struct that ends below the slot.
- **STORE-UNREAD** (the re-reviews: a measured class, not (iv)): the same kind of store, where every callee the frame
  object is passed to has no load, AMO, ecall / CSR or call of any kind, disassembled in both images; the row gives each
  callee and its instruction count in X and in Y (e.g. `internal_iserror`). No struct line is cited.
  A void callee (cited `ret ... void`) returns no frame pointer; a register past a callee's parameters that it never
  reads does not hand it the pointer. Otherwise the store is NOT CERTIFIED: REAL 0. Struct members are cited only from
  the pinned source: these images carry no DWARF member layout (12 DW_TAG_member in the whole image).
- **COMPARE-ONLY** ((c); the rule fixed after the egress review, D1): a lui word with no row and no measured
  non-row on any feasible path, whose trace holds at least one branch / compare (`CMPONLY` lines; the TRACE line lists
  the events). A word with no row, no measured non-row and no compare is **NO USE** (`NOUSE` lines): the value is not
  read, or only by arithmetic or private spills that are not read. Every ALU op keeps its result traced, so "no row"
  means no value derived from the lui reaches a base, an argument, a store, an ecall or a return. A use reached only
  by falling through a call that never returns is on no feasible path: it is an `UNREACH` line (the use, and the
  noreturn calls between the lui and it), not a row.
- **Stack slots** (the egress review, R1): a store of the value into a stack slot is a spill, followed into its
  reloads with no row, only when the slot is PRIVATE: no pointer into a frame object that may cover the slot (an
  object starting at or below it, or a frame pointer with an unknown offset) is passed to a call, a tail jump or an
  ecall, stored, moved to an FP register or a CSR, or returned anywhere in the function (`tools/luitrace.py`
  `stack_escapes` / `slot_escape`). Otherwise the store is a STORE row: class (iv) or STORE-UNREAD above, or **NOT CERTIFIED: REAL 0**
  (its reader, a callee or the kernel, is not traced); the slot's reloads are followed either way.
- **Noreturn callees** (the uci review, D1 and D2): a call to a function that never returns (no return and no tail
  jump anywhere in it, and its last word a jump, a trap or a call to such a function: 11 functions of the compared set,
  among them `Die`, `CheckFailed`, `internal__exit`, `Abort`, `abort`) has no edge to its next word, so a0 there is never
  "the return of" it. A value still live in an argument register at a later call is a use at that call (an arg ROW or
  a measured NOTARG): the traces do not stop at an abort path. Of the 8 sites the uci review names (D2), each is now
  an arg ROW or a NOTARG except two: `StackStore::BlockInfo::Pack` +0x33c, which the lui at +0x100 reaches only through
  the fall-through of the noreturn `Die()` call at +0x31c (the only other predecessor, the branch at +0xc0, holds no
  traced value), and `DenseMap<...GlobalListNode...>::grow` +0x1ac, an `addi` whose register holds no traced value.
- Measured non-rows: NOTARG (the register is past the callee's parameters, which the mangled name counts, AND the
  callee, followed into every callee it calls first, never reads it: (e)); NOTECALL (past the syscall's
  argument registers, by a7); NOTRET (a void return, a1 where the return takes one register, or a1 no caller reads).
- At a call, a caller-saved register that still holds the value stays traced in the caller unless the caller does
  not read it again or the callee writes it on every path (a must-analysis over the callee's CFG): (e).
- Anything else: **NOT CERTIFIED: REAL 0**, with its count.
The citations come from the pinned source, compiler-rt of llvm-project llvmorg-20.1.8 (`Alpine clang version 20.1.8`
in both images' .comment; the release tarball compiler-rt-20.1.8.src.tar.xz, sha256
15277402f6fd63397c0917a5c7171cda82d16d226094b828c1ed0f58f73b9c69), read by `tools/cite_gen.py` into
`commit/cite.tsv`: a declaration counts only when
its parameter count and every parameter's kind (pointer / integer) agree with the mangled name, and every namespace /
class of the mangled name is declared in that file. musl's source is not pinned, so no musl parameter is cited.

## Tools (`commit/tools/`, `commit/tools.sha256`, `commit/tools/DIFFS.md`)

The 8 kit files and `jtcheck.py` are `tools/kitscrub.py`'s copies: the 8 of cmpkit 86da41d3ef68, `jtcheck.py` of jtcheck
226254f48c97 (`tools/jtcheck.py`, from the original sha256 226254f48c97; `tools/DIFFS.md`). Each line below is the copy's row of
`tools/DIFFS.md` (copy sha256, the original's sha256, the changed lines) and what its `code compare` line says;
DIFFS.md gives each whole diff.
drvcmp's block checks over repin_check lines 31-80 / 209-231 still pass unchanged.
- `ambiscan.py` `be1fbb80ad10` (kit `9f61b4cee422`): 2 removed, 2 added (0 comment, 2 docstring, 0 code); no code line
  changed: the syntax tree, docstrings left out, is the kit's.
- `bytecmp-1480ca2faea0.py` `dc384f1b5867` (kit `1480ca2faea0`): 11 removed, 11 added (4 comment, 4 docstring, 3
  code); its changed code lines: the `os` import that environment read needs (line 13); a path read from the
  environment (lines 182, 183); the syntax tree is otherwise the kit's.
- `closure_strict3.py` `6b2293dc8418` (kit `a98d2b3e8857`): 3 removed, 3 added (0 comment, 3 docstring, 0 code); no
  code line changed: the syntax tree, docstrings left out, is the kit's.
- `drvcmp.py` `2fffab5c772f` (kit `4d70e90bc1fa`): 5 removed, 5 added (0 comment, 4 docstring, 1 code); its changed
  code lines: a sha256 pin set to this record's copy of the file it pins (line 21); the syntax tree is otherwise the
  kit's.
- `jtcheck.py` `94c2f3081b0c` (registry `226254f48c97`): 9 removed, 9 added (3 comment, 4 docstring, 2 code); its
  changed code lines: a sha256 pin set to this record's copy of the file it pins (lines 51, 52); the syntax tree is
  otherwise the registry file's.
- `luiscan.py` `25e8c224d06a` (kit `9ae61e4a0e01`): 4 removed, 4 added (0 comment, 4 docstring, 0 code); no code line
  changed: the syntax tree, docstrings left out, is the kit's.
- `paircl.py` `926a9a88afcd`: byte-identical to the kit's file
- `repin_check.py` `47993ba4c4ff` (kit `e6883477399d`): 10 removed, 10 added (2 comment, 2 docstring, 6 code); its
  changed code lines: a path read from the environment (lines 16, 17, 18, 19, 20, 21); the syntax tree is otherwise
  the kit's.
- `strictcmp3.py` `b553126fa224` (kit `65688e94214a`): 13 removed, 13 added (1 comment, 12 docstring, 0 code); no code
  line changed: the syntax tree, docstrings left out, is the kit's.
The rest of `tools/` was written for these records (DIFFS.md names each, with what it does):
- `basescan.py` `a500fff1960c`
- `cite_gen.py` `edd07bf9f741`
- `dupcheck.py` `4606bbcfaf53`
- `earlierscrub.py` `716d50b79f04`
- `escape.py` `ef625371dd49`
- `gates.py` `a2a9422ec685`
- `handtable.py` `95e3bc23db39`
- `kitscrub.py` `b7b6c71d0687`
- `luirows.py` `66635dceece1`
- `luitrace.py` `06d2b1005932`
- `mkaccept.py` `984322748de5`
- `mkdiffs.py` `e196c869957e`
- `objscan.py` `a13d2bd9706c`
- `otherrows.py` `478be38abafd`
- `plants.py` `237bb0a60df5`
- `rolenames.py` `6f3a126a733e`
- `scrub_out.py` `cda7256574a9`
- `settle.py` `4eeeae293912`
- `syms.py` `ebf764d5cdf2`

## Images (`commit/images.sha256`, `commit/twins.out`)

Grant B's addresses are the ones the released donor names: grant `lib/B/YF0l.v:11-12` @ 4f87de75d67 gives
`pc_malloc := 0x530b0; pc_wrap_malloc := 0x52edc` and `pc_free := 0x52ee0; pc_wrap_free := 0x52ed8`. Wire B's roots,
by its own symbol table (`commit/roots-syms.out`): 0x5226c / 0x52098 and 0x5209c / 0x52094.

| token | file | sha256 | pin / twin check |
|---|---|---|---|
| `WIRE_B_PIN` | `fuzz_wire.asan-ubsan` | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` | index/binaries.tsv:7525 and `projects/reac-repacer/fuzz_wire/harness.yaml:64` |
| `WIRE_B_TWIN` | `fuzz_wire.asan-ubsan`, unstripped | `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3` | PT_LOAD equal to the pin (`twins.out`) |
| `GRANT_B_PIN` | `fuzz_grant.asan-ubsan` | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | index/binaries.tsv:5591 (the same line @ 4f87de75d67, released) |
| `GRANT_B_TWIN` | `fuzz_grant.asan-ubsan`, unstripped | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | PT_LOAD equal to the pin |
| `IDENT_B_PIN` (control) | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | index/binaries.tsv:5595 |
| `IDENT_B_TWIN` (control) | `fuzz_identity.asan-ubsan`, unstripped | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` | PT_LOAD equal to the pin |
| `GRANT_B_{PIN,TWIN}_PLANTED_{CALL,RODATA}`, `GRANT_B_TWIN_PLANTED_{DEBRUIJN,CIESLOT}`, `WIRE_B_TWIN_PLANTED_{ADD,UPTR,DIVU,SLLI3,CIELIMIT,CIEARM,CIEZARM,CIEJUMP}`, `GRANT_B_TWIN_PLANTED_{ADD,UPTR,DIVU}` | planted copies | `commit/planted/planted.sha256` | written by `run.sh`; not committed |

## Kit verdict (cmpkit 86da41d3ef68, as the kit printed it)

**strictcmp3 cmp** on the 4 roots, the claim rows (`commit/roots.tsv`): `__interceptor_trampoline_malloc` EQUAL (0 pc-relative words), target-differ 0; `___interceptor_malloc` EQUAL-mod-pcrel (3 pc-relative words), target-differ 0; `__interceptor_trampoline_free` EQUAL (0 pc-relative words), target-differ 0; `___interceptor_free` EQUAL-mod-pcrel (3 pc-relative words), target-differ 0. Real 0, unmeasured 0 and target-differ 0
everywhere, against grant B and against the identity B control. **Unchanged from 4bbd3a74be89.**

**closure_strict3** from `___interceptor_malloc` (`commit/closure-grant.out`): closure 784 functions (register-indirect
call sites inside: 97), EQUAL 198, EQUAL-mod-pcrel 486, **other 100**, 426 members with kit acceptances listed (value /
full-bytes / NAME-ONLY / C-string). The same for the other 3 roots.

**paircl** from `___interceptor_malloc` against the grant pin (`commit/paircl-malloc-grant.out`): 943 functions paired,
EQUAL 239, EQUAL-mod-pcrel 597, **other 107**, 0 pairing conflicts. The same for the other 3 roots.

**jtcheck 226254f48c97** on the 16 members (`commit/jtcheck-members.txt`, `commit/jtcheck-grant.out`): 10 settled by
jtcheck; open:
- `_ZN6__asan9Decorator10ShadowByteEh`: target unmeasured 1. Settled here: +0x14 TABLE SETTLED-EQUAL; +0x80 CSTR SETTLED-EQUAL.
- `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE`: target differs 1. Settled here: +0x140 REFUSED UNSETTLED; by hand (`handtable.out`): SETTLED-BY-HAND.
- `sysconf`: target differs 3. Settled here: +0xdc TABLE SETTLED-EQUAL; 3 lui-in-section target(s): LUI rows (hand traces).
- `__strftime_fmt_1`: target differs 7, target unmeasured 2. Settled here: +0x44 TABLE SETTLED-EQUAL; +0x530 CSTR-ESCAPE SETTLED-EQUAL; +0x54c CSTR-ESCAPE SETTLED-EQUAL; 7 lui-in-section target(s): LUI rows (hand traces).
- `_ZN6__asan22ErrorAllocTypeMismatch5PrintEv`: target unmeasured 2. Settled here: +0x38 CSTR SETTLED-EQUAL; +0xb8 CSTR SETTLED-EQUAL.
- `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE`: target differs 1. Settled here: +0x23c REFUSED UNSETTLED; by hand (`handtable.out`): SETTLED-BY-HAND.

## What changed against the previous version of this slice: jtcheck 226254f48c97 decides the tables

The jtcheck of record for table verdicts is now **jtcheck 226254f48c97** (`tools/jtcheck.py`, from the original sha256
226254f48c97; `tools/DIFFS.md`), which supersedes the kit's jtcheck 8b0ea3862423. 8b0e did not treat a call as writing
a caller-saved register that holds a table's limit, so on a path through a call it could accept a count that the path
does not bound (it fails open); 226254 proves the entry size and count on every path of the function's CFG
(Flow.prove), and refuses where it cannot (it fails closed). A refusal is no proof, never a difference. This slice
ships its copy, `tools/jtcheck.py` `94c2f3081b0c`, which differs from the original in 9 lines (`tools/DIFFS.md`: 3
comment, 4 docstring, 2 code): its sha256 pins (lines 51, 52) point at this record's own copies of strictcmp3.py and
drvcmp.py, its docstring says so (line 4), and the README labels and counts its comments and docstrings cite are set
to its package's README and controls, or dropped where no README item covers the sentence (`tools/kitscrub.py`
JT_WORDS; lines 205, 208, 209, 515, 578, 791). Every jtcheck run of `run.sh` uses it. settle.py and basescan.py
(`kit_table`) take a table's entry size and count only from 226254's proof on both images (`luitrace.table_proof2`).
luitrace.py's `arms_of` (the jump-table arms of the hand traces' CFG, built for one image at a time) takes them from
226254's proof on the image whose CFG it builds (`luitrace.table_proof`); where that proof fails, it reads 4-byte
relative and 8-byte absolute entries, each up to the first entry that does not land on a word of the function. 8b0e's
`table_shape` and settle.py's own `dispatch_bound` (the guard after the table's auipc, read in address order) are
gone. An indexed address 226254 does not prove goes on to settle.py's other classes, and is REFUSED when none settles
it.

Every TABLE row of the previous version's `settle.tsv`, then -> now:

| function | word | then | now |
|---|---|---|---|
| `_ZN11__sanitizer19GetHandleSignalModeEi` | 0x24 | abs8-ptr, 8 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | abs8-ptr, 8 entries (proven: 8-byte entries, bltu x10, 7, ld at +0x2c from the base), SETTLED-EQUAL |
| `_ZN11__sanitizer8OpenFileEPKcNS_14FileAccessModeEPi` | 0x60 | rel4-str, 3 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-str, 3 entries (proven: 4-byte entries, bltu x9, 2, lw at +0x68 from the base), SETTLED-EQUAL |
| `_ZN11__sanitizer9VSNPrintfEPciPKcPv` | 0x1c0 | rel4-jump, 33 entries (settle.py dispatch_bound), SETTLED-EQUAL | rel4-jump, 33 entries (proven: 4-byte entries, bltu x17, 32, lw at +0x1c8 from the base), SETTLED-EQUAL |
| `_ZN6__asan12ErrorGenericC1Ejmmmmbm` | 0x224 | rel4-jump, 82 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 82 entries (proven: 4-byte entries, bltu x11, 81, lw at +0x22c from the base), SETTLED-EQUAL |
| `_ZN6__asan16ErrorDescription5PrintEv` | 0x1c | rel4-jump, 25 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 25 entries (proven: 4-byte entries, bltu x11, 24, lw at +0x24 from the base), SETTLED-EQUAL |
| `_ZN6__asan9Decorator10ShadowByteEh` | 0x14 | rel4-jump, 83 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 83 entries (proven: 4-byte entries, bltu x11, 82, lw at +0x1c from the base), SETTLED-EQUAL |
| `_ZN6__asanL23force_interface_symbolsEv` | 0x20 | rel4-jump, 52 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 52 entries (proven: 4-byte entries, bltu x10, 51, lw at +0x28 from the base), SETTLED-EQUAL |
| `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE` | 0x140 | rel4-jump, 48 entries (settle.py dispatch_bound), SETTLED-EQUAL | REFUSED, UNSETTLED |
| `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE` | 0x23c | rel4-jump, 47 entries (settle.py dispatch_bound), SETTLED-EQUAL | REFUSED, UNSETTLED |
| `_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh` | 0x24 | rel4-jump, 12 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 12 entries (proven: 4-byte entries, bltu x10, 11, lw at +0x2c from the base), SETTLED-EQUAL |
| `_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm` | 0x28 | rel4-jump, 13 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 13 entries (proven: 4-byte entries, bltu x10, 12, lw at +0x30 from the base), SETTLED-EQUAL |
| `_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm` | 0x1a8 | rel4-jump, 6 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 6 entries (proven: 4-byte entries, bltu x11, 5, lw at +0x1b0 from the base), SETTLED-EQUAL |
| `_ZNK11__sanitizer13SignalContext8DescribeEv` | 0x1c | rel4-str, 8 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-str, 8 entries (proven: 4-byte entries, bltu x10, 7, lw at +0x24 from the base), SETTLED-EQUAL |
| `_ZNK6__asan18AddressDescription5PrintEPKc` | 0x14 | rel4-jump, 5 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 5 entries (proven: 4-byte entries, bltu x12, 4, lw at +0x1c from the base), SETTLED-EQUAL |
| `__strftime_fmt_1` | 0x44 | rel4-jump, 86 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 86 entries (proven: 4-byte entries, bltu x11, 85, lw at +0x4c from the base), SETTLED-EQUAL |
| `sysconf` | 0xdc | rel4-jump, 13 entries (jtcheck 8b0ea3862423 table_shape), SETTLED-EQUAL | rel4-jump, 13 entries (proven: 4-byte entries, bltu x11, 12, lw at +0xe4 from the base), SETTLED-EQUAL |

Of the 16 rows, 14 are proven by 226254 with the same kind and count as before. 2 shipped rows went from TABLE
SETTLED-EQUAL to REFUSED UNSETTLED. For each, jtcheck's own refusal reason, as `settle.tsv` quotes it:
`_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEE...` 0x23c (settle.tsv:521): in X and in Y: `the store at
+0x1c4 writes it to memory`: in its words `it` is a value its value flow cannot rule out as an address inside the
function, here the a3 stored by `sd a3,0(sp)`; it does not follow that value, so it proves no table in that function;
`_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDE...` 0x140 (settle.tsv:570): in X and in Y: `the store at
+0x200 writes it to memory`: in its words `it` is a value its value flow cannot rule out as an address inside the
function, here the s8 stored by `sw s8,0(s2)`; it does not follow that value, so it proves no table in that function.
Neither store writes the table base: in `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEE...`, +0x1c4 `sd
a3,0(sp)` writes the CIE parse pointer `p` (a3, whose only reaching definition is `sub a3,a3,a2` at +0x1b4, after the
inlined SLEB128 loop), and no path of the CFG goes from the base's `addi` at +0x23c to it; in
`_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDE...`, +0x200 `sw s8,0(s2)` writes s8, whose only reaching
definition is `mv s8,a0` at +0x178, the return value of the call to `LocalAddressSpace::getULEB128` at +0x174. 226254
refuses because its value flow cannot rule out that the stored value is an address inside the function (an
over-approximation: in parseCIE the stored a3 is carried around a loop whose values it cannot enumerate; in
parseFDEInstructions the stored s8 is the return value of a call whose argument registers carry such loop values, and
its call rule lets a call return an argument), so it proves no table in that function. In basescan this moves the two
table bases, `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEE...` +0x264,
`_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDE...` +0x148, from EQUAL+TABLE to NOT CERTIFIED:
EQUAL+TABLE 32 -> 30, NOT CERTIFIED 411 -> 413. Each refused table is settled by hand in `commit/handtable.out`
(`tools/handtable.py`) under the rule below.

**The rule for settling by hand a table that jtcheck 226254f48c97 refuses** (this record's rule, as the unit owner
ruled it; a settlement missing a part is no evidence, and the refusal then stands as no proof, never as a difference):
(1) ENTRIES: for every slot, base + sign-extended slot decoded on EACH image, each target the same function + offset
on both sides; (2) DISPATCH: the same shape on each image (the jalr, the table base's auipc / addi pair, the guard
branch and its operand registers), cited by address; (3) THE BOUND: for the guard's limit register, EVERY reaching
definition on EVERY path into the guard (a walk of the CFG, not address order), each shown to give a limit no larger
than the table's entry count, on each image, with the source-level reason; (4) a read of the settlement by a
non-writer. handtable.py checks (1) to (3). Its walk assumes, as jtcheck does, that a call returns to the next word
and keeps sp and s0-s11 (the RISC-V psABI's callee-saved rule; callee code is not read); an `ecall` is taken to write
every caller-saved register, and an opcode it does not model, a word no edge reaches or a jump into the dispatch block
refuses the function.
- `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE` +0x23c: **SETTLED-BY-HAND**.
  (1) ENTRIES: 47 of 47 slots name the same function + offset in X and Y (each slot sign-extended and added to the
  table base). (2) DISPATCH: the table base is X 0x20c94 / Y 0x21398, formed by the auipc at +0x238 and the addi at
  +0x23c; in X and in Y the block has the same words at the same offsets but for the immediates of that auipc / addi
  (X shown): +0x258 bltu s5,a1; +0x25c slli a1,a1,2; +0x260 add a1,a1,s6; +0x264 lw a0,0(a1); +0x268 add a0,a0,s6;
  +0x26c jalr zero,0(a0). The slli +0x25c, the word right after the guard +0x258, reads the a1 that the guard
  compared, so nothing runs between the compare and the scaling of that index; every word +0x25c..+0x26c has one
  predecessor, the word before it, so the guard's fall-through is the only way to the indexed load and the jalr; bltu
  is unsigned, so a negative index is out of range. (3) THE BOUND, a backward walk over the whole CFG (the arms of
  part 1 included) in X and in Y: The limit s5 at the guard +0x258: every reaching definition on every path of the
  CFG: +0x234 addi s5,zero,46 -> index < 47, 47 entries; the walk passes 1 call(s), each taken to keep s5, which the
  psABI makes callee-saved (Func.defines: a call writes only its link and the caller-saved registers; callee code is
  not read). Indirect jumps: the dispatch +0x26c and 1 ret, each ra from a load; the base s6 is read only at +0x260,
  +0x268. The source: libunwind `CFI_Parser::parseCIE`, the switch over each augmentation-string character
  (DwarfParser.hpp lines 375-410: cases `z`, `P`, `L`, `R`, `S`, then `B` and `G` under `#if
  defined(_LIBUNWIND_TARGET_AARCH64)`, so not in this RISC-V build, and a default that ignores the rest); the compiled
  index is the character minus 76 (`L`), so the 47 entries cover `L` to `z`: `L`, `P`, `R`, `S` and `z` reach their
  cases, every other entry and every character outside `L`..`z` the default. (4) A non-writer read this table with its
  own disassembler and its own CFG and reaching-definitions code (not handtable.py) and confirmed every entry and the
  bound on both images (`handtable-read.md`, in this slice).
- `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE` +0x140: **SETTLED-BY-HAND**.
  (1) ENTRIES: 48 of 48 slots name the same function + offset in X and Y (each slot sign-extended and added to the
  table base). (2) DISPATCH: the table base is X 0x20d50 / Y 0x21454, formed by the auipc at +0x13c and the addi at
  +0x140; in X and in Y the block has the same words at the same offsets but for the immediates of that auipc / addi
  (X shown): +0x134 bltu s1,s9; +0x138 slli a1,s9,2; +0x13c auipc a2,0xfff9d; +0x140 addi a2,a2,-4; +0x144 add
  a1,a1,a2; +0x148 lw a1,0(a1); +0x14c add a1,a1,a2; +0x150 jalr zero,0(a1). The slli +0x138, the word right after the
  guard +0x134, reads the s9 that the guard compared, so nothing runs between the compare and the scaling of that
  index; every word +0x138..+0x150 has one predecessor, the word before it, so the guard's fall-through is the only
  way to the indexed load and the jalr; bltu is unsigned, so a negative index is out of range. (3) THE BOUND, a
  backward walk over the whole CFG (the arms of part 1 included) in X and in Y: The limit s1 at the guard +0x134:
  every reaching definition on every path of the CFG: +0xd0 addi s1,zero,47 -> index < 48, 48 entries; the walk passes
  63 call(s), each taken to keep s1, which the psABI makes callee-saved (Func.defines: a call writes only its link and
  the caller-saved registers; callee code is not read). Indirect jumps: the dispatch +0x150 and 1 ret, each ra from a
  load; the base a2 is read only at +0x144, +0x14c. The source: libunwind `CFI_Parser::parseFDEInstructions`, the
  switch over the DWARF CFA opcode byte (DwarfParser.hpp lines 466-866; on this target its cases are 0x00 to 0x16,
  0x2e and 0x2f: 0x2c and 0x2d are under the AArch64 / SPARC `#if` at lines 745-825; the default switches on `opcode &
  0xC0`); the compiled index is the opcode byte, so the 48 entries cover 0x00 to 0x2f, and the 23 entries 0x17 to 0x2d
  all go to +0xb94, the default arm, which is also the guard's branch target for every opcode above 0x2f. (4) A
  non-writer read this table with its own disassembler and its own CFG and reaching-definitions code (not
  handtable.py) and confirmed every entry and the bound on both images (`handtable-read.md`, in this slice).
The libunwind source is cited at the llvm-project release tag llvmorg-20.1.8 (libunwind/src/DwarfParser.hpp). Both
images' `.comment` reads `Linker: LLD 20.1.8` and `Alpine clang version 20.1.8`, and the compiled case sets match that
release exactly; it is not pinned by a tarball sha256 the way compiler-rt is. The hand-settlement controls, each a
copy of one image with one word of parseCIE or of its table changed, each gated on its own reason (`run.sh`; the
plants gate): a second definition of the limit, `addi s5,zero,10` in place of `addi a0,a0,1` at +0x278, in an arm that
loops back to the guard and lies after it in address order, in a copy of WIRE_B_TWIN (X), tests part (3), the bound:
every definition on every path, which only a walk of the CFG finds here (`commit/ctl-handtable-bound.out`, must read
NOT SETTLED (the bound differs): **NOT SETTLED (the bound differs between X and Y)**; a larger second limit, `addi
s5,zero,60` in place of `sb s7,0x31(s0)` at +0x28c, in the `z` arm, which only the dispatch enters, in a copy of
WIRE_B_TWIN (X), tests part (3), the bound: the backward walk from the guard reaches +0x28c through the arm's own `j`
at +0x294 (the first walk, which has no arm edges), takes 60 as a limit, and slot 47 then names no word of the
function (`commit/ctl-handtable-zarm.out`, must read NOT SETTLED (X: slot 47): **NOT SETTLED (X: slot 47 targets
0x83cb0, not a word of the function)**; a jump into the dispatch block, `j +0x1c` in place of `sb s7,48(s0)` at
+0x248, in a copy of WIRE_B_TWIN (X), tests part (2), the dispatch: each word after the guard has one predecessor
(`commit/ctl-handtable-jump.out`, must read NOT SETTLED (X: the block word): **NOT SETTLED (X: the block word +0x264
has predecessors ['+0x248', '+0x260'])**; the limit `addi s5,zero,46` at +0x234 raised to 47, so the 48th slot is the
first slot of the next table, in a copy of WIRE_B_TWIN (X), tests part (1), the entries: each slot must name a word of
the function (`commit/ctl-handtable-entries.out`, must read NOT SETTLED (X: slot 47): **NOT SETTLED (X: slot 47
targets 0x83cb0, not a word of the function)**; table slot 3 (vaddr 0x213a4) re-pointed to the target of slot 0, in a
copy of GRANT_B_TWIN (Y), tests part (1), the compare of X's and Y's entries (`commit/ctl-handtable-slot.out`, must
read DIFFERS (1 entries)): **DIFFERS (1 entries)**. The dispatch-size control (`commit/ctl-settle-slli3-planted.tsv`)
now reads REFUSED, UNSETTLED: on the planted copy 226254 proves no table.

Files of `commit/` whose bytes differ from the previous version's (the files `run.sh` does not write left out):
`ACCEPTANCES.tsv`, `ambiscan.out`, `basescan.tsv`, `cite-extra.tsv`, `cite.sha256`, `ctl-jtcheck-identity.out`,
`ctl-settle-slli3-planted.tsv`, `earlier/SCRUB.tsv`, `earlier/v4bbd3a74be89/REVIEW.md`,
`earlier/v4bbd3a74be89/tools.sha256`, `earlier/v4bbd3a74be89/tools/DIFFS.md`,
`earlier/v4bbd3a74be89/tools/bytecmp-1480ca2faea0.py`, `earlier/v4bbd3a74be89/tools/drvcmp.py`,
`earlier/v4bbd3a74be89/tools/jtcheck.py`, `earlier/v4bbd3a74be89/tools/strictcmp2.py`,
`earlier/va88c2822a0f2/RECORD.md`, `earlier/va88c2822a0f2/tools.sha256`, `earlier/va88c2822a0f2/tools/DIFFS.md`,
`earlier/va88c2822a0f2/tools/bytecmp-1480ca2faea0.py`, `earlier/va88c2822a0f2/tools/repin_check-e5487165abb8.py`,
`earlier/va88c2822a0f2/v9cbc3553c09e/tools.sha256`, `earlier/va88c2822a0f2/v9cbc3553c09e/tools/DIFFS.md`,
`earlier/va88c2822a0f2/v9cbc3553c09e/tools/bytecmp-1480ca2faea0.py`,
`earlier/va88c2822a0f2/v9cbc3553c09e/tools/repin_check-9cbc3553c09e.py`, `gate-base.txt`, `gate-controls.txt`,
`gate-kit.txt`, `gate-lui.txt`, `gate-plants.txt`, `images.sha256`, `jtcheck-grant.out`, `planted/planted.cmp`,
`planted/planted.sha256`, `run.sh`, `settle.tsv`, `tools.sha256`, `tools/DIFFS.md`, `tools/ambiscan.py`,
`tools/basescan.py`, `tools/bytecmp-1480ca2faea0.py`, `tools/closure_strict3.py`, `tools/drvcmp.py`,
`tools/earlierscrub.py`, `tools/gates.py`, `tools/jtcheck.py`, `tools/kitscrub.py`, `tools/luiscan.py`,
`tools/luitrace.py`, `tools/mkdiffs.py`, `tools/plants.py`, `tools/repin_check.py`, `tools/rolenames.py`,
`tools/scrub_out.py`, `tools/settle.py`, `tools/strictcmp3.py`; new: `ctl-handtable-bound.out`,
`ctl-handtable-entries.out`, `ctl-handtable-jump.out`, `ctl-handtable-slot.out`, `ctl-handtable-zarm.out`,
`handtable.out`, `tools/handtable.py`.

## What changed against 4bbd3a74be89

- **Claim rows (the 4 roots): none.** EQUAL / EQUAL-mod-pcrel, 0 differing targets, under both kits.
- **Closure rows:** by name other 62 -> 100, paired other 67 -> 107; the union 67 -> 107. The 40 new rows are all one
  class: each carries only `lui-in-section` targets (strictcmp3's rule 8). 0 rows left the set.
- **Target pairs** (178 -> 174): 80 CSTR pairs that settle.py settled are now settled by the kit itself (each is a CSTR
  row of the kit's output: strictcmp3's C-string rule); 1 INDEXED -> TABLE; 1 RELSTR -> TABLE; 2 TABLE -> REFUSED; 76 `lui-in-section` pairs are new (the LUI rows); every
  other pair keeps its class and verdict.
- **jtcheck:** 4bbd3a74be89 left open _ZN6__asan9Decorator10ShadowByteEh (target unmeasured 6); _ZNK11__sanitizer13SignalContext8DescribeEv (target unmeasured 1); __strftime_fmt_1 (target unmeasured 2); _ZN6__asan22ErrorAllocTypeMismatch5PrintEv (target unmeasured 4); _ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEE (target differs 1); now (jtcheck 226254f48c97) open: _ZN6__asan9Decorator10ShadowByteEh (target unmeasured 1); _ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDE (target differs 1); sysconf (target differs 3); __strftime_fmt_1 (target differs 7, target unmeasured 2); _ZN6__asan22ErrorAllocTypeMismatch5PrintEv (target unmeasured 2); _ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEE (target differs 1).

## What changed against the version the reviewers re-read (staged 2026-10-31)

Then the kit outputs, settle.tsv and every CLAIM row were unchanged against that version. Three changes, all in
this record's own tools (a fourth, settle.py's `dispatch_bound` read at its slli entry size, is gone with this
version: above):

1. **STORE-UNREAD is its own class** (the re-reviews): a store into an escaping frame object whose only readers
   cannot read memory was counted as (iv); it is now STORE-UNREAD, with each callee's instruction count in X and Y.
   (iv) 15 -> 7, STORE-UNREAD 0 -> 8.
2. **Unnamed addresses in basescan** (the egress re-review, RR1): an address no symbol covers was named by its bare
   section and compared by that string. It is now `(section)+offset`, compared by its bytes or settled by the table
   rule (EQUAL+BYTES / EQUAL+TABLE), else NOT CERTIFIED. Bases: EQUAL 20490 -> 20292, EQUAL+INDEX 2460 -> 2427,
   EQUAL+BYTES 199, EQUAL+TABLE 32, NOT CERTIFIED 411 -> 411, DIFFERS 0 -> 0 (jtcheck 226254f48c97 then moved two
   bases: see "What changed against the previous version of this slice").
3. **The trace is shown to follow divuw / shifts, and uses beyond a noreturn call are listed** (the wire re-review, and
   the uci re-review's D3). The rule the reviewers asked for was already the rule: every ALU op on a traced value
   (divuw, remu, mul, the shifts included) keeps its result traced, over a flow-sensitive forward dataflow on the CFG
   that iterates to a fixpoint (loops included). Plant (c) now checks it: a lui value reaches a store base only through
   `divuw` and `slli`, and the trace reports **CAUGHT: DIFFERS** (the kit: EQUAL). Division and remainder are now also computed exactly
   on known numbers. The uses the reviewers found lie only beyond a call to `CheckFailed`, which never returns
   (`void NORETURN CheckFailed(...)`, sanitizer_common/sanitizer_common.h:332-333, and measured: no return and no tail
   jump in its code). The trace gives such a call no fall-through edge (the uci review's D1 / D2), so those uses are on
   no feasible path; they are now listed, never dropped: 123 `UNREACH` lines over 11 lui words (`commit/luitrace.tsv`).
   - `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEPNS2_13SizeClassInfoEm` +0xb8: COMPARE-ONLY; the `sb s4,0(a0)` at +0x474 and the CheckFailed call at +0x458 are entered only from +0x98 and +0x84 (before the lui; neither is reachable from it), or by falling through the CheckFailed calls at +0x3fc, +0x418, +0x438.
   - `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEPNS2_13SizeClassInfoEm` +0x488: COMPARE-ONLY; the same two uses, the same paths.
   - `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEPNS2_13SizeClassInfoEm` +0x4bc: COMPARE-ONLY; the same two uses, the same paths.
   - `_ZN6__lsanL21CheckForLeaksCallbackERKN11__sanitizer20SuspendedThreadsListEPv` +0xce0: COMPARE-ONLY; the CheckFailed call at +0x128c is entered only from +0x100 (not reachable from the lui), or by falling through the CheckFailed call at +0x1270.
   - `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEPNS2_13SizeClassInfoEm` +0x268: has a row; the AMO base at +0x300 is a row, (iii) onto parameter a2; its other uses lie beyond the same CheckFailed calls.

Counts: use rows 1613 -> 1613; (i) 322 -> 322, (ii) 7 -> 7, (iii) 251 -> 251, (iv) 15 -> 7, STORE-UNREAD 8, NOT CERTIFIED
1018 -> 1018, DIFFERS 0. NOTARG 793 -> 793; COMPARE-ONLY 74 -> 74; NO USE 1 -> 1. The kit's 76 lui-in-section targets:
settled in full 18 -> 18, with a NOT CERTIFIED use 58 -> 58.

## Acceptances (`commit/ACCEPTANCES.tsv`, `commit/settle.tsv`)

Union of the kit's two "other" lists: **107 functions, 174 target pairs** (the full list from strictcmp3.tcmp).

| class | target pairs | verdict |
|---|---|---|
| CSTR | 62 | SETTLED-EQUAL |
| TABLE | 14 | SETTLED-EQUAL |
| CSTR-ESCAPE | 10 | SETTLED-EQUAL |
| INDEXED | 6 | SETTLED-EQUAL |
| NOT-PCREL | 3 | SETTLED-EQUAL |
| INITIALIZER | 1 | SETTLED-EQUAL |
| REFUSED (a table jtcheck 226254f48c97 does not prove) | 2 | no proof (UNSETTLED); settled by hand in `handtable.out`, parts (1) to (3) |
| `lui-in-section` (UNSETTLED by settle.py) | 76 | LUI rows: the hand traces below |

**96 pairs SETTLED-EQUAL, 0 DIFFERS.** Rows: 62 settled-equal; 45 carry lui-in-section targets or a REFUSED table (the
ACCEPTANCES header names them).

## Hand traces of every lui value (`commit/luitrace.tsv`; per kit target: `LUI` rows of `commit/ACCEPTANCES.tsv`)

633 lui words in 245 compared functions (of 943), traced in X and in Y: **0 DIFFERS**.

| use | (i) | (ii) | (iii) | (iv) | STORE-UNREAD | NOT CERTIFIED: REAL 0 |
|---|---|---|---|---|---|---|
| call argument | 322 | - | - | - | - | 634 |
| return | - | 7 | - | - | - | 70 |
| load / store / jalr / AMO base | - | - | 251 | - | - | 62 |
| store data | - | - | - | 7 | 8 | 199 |
| AMO data | - | - | - | - | - | 36 |
| ecall argument | - | - | - | - | - | 17 |
| **total** | **322** | **7** | **251** | **7** | **8** | **1018** |

Measured non-rows: NOTARG 793, NOTECALL 25, NOTRET 47; COMPARE-ONLY lui words 74; NO USE lui words 1; uses on no
feasible path (beyond a noreturn call, `UNREACH`) 123.

Why each NOT CERTIFIED row stays open (`commit/luitrace.tsv`, column 7 of each ROW):
- 387: past the callee's parameters, and the callee or a callee it calls first may read it
- 160: a store or AMO: no struct field can be cited (no DWARF member layout)
- 118: a parameter no pinned source cites (musl, or no declaration found)
- 75: a store into a stack slot of a frame object whose address leaves the function (its reader is not traced)
- 60: a variadic argument
- 52: a base of unknown form (the constant is unknown on some path)
- 47: a return whose type no pinned source cites (musl)
- 23: an integer parameter whose name is not a count / length
- 22: a return of a pointer / uptr
- 21: a pointer parameter
- 19: an argument register of a syscall
- 15: a register-indirect call
- 10: a base whose anchor is not one object pointer
- 9: a uptr address parameter
- (callees the read analysis met with no prototype, each counted as a read: ___interceptor_memset/__interceptor_memset 3, __block_app_sigs 1, __interceptor_trampoline_memcpy/__wrap_memcpy 1)

The kit's 76 `lui-in-section` targets (LUI rows): 18 settled in full by class or measured non-row, 0 compare-only,
0 with no use,
58 with at least one use NOT CERTIFIED: REAL 0, 0 DIFFERS.

## Exposure scans (`commit/luiscan.tsv`, `commit/luirows.tsv`, `commit/ambiscan.out`)

- **luiscan** (rule 8 exposure, every function of both images): wire B 873 lui words, 134 in a section, 53 luiconst
  (`lui-const (dataflow)`), exposure 81 in 47 functions; grant B 902 / 134 / 53, exposure 81 in 47 functions. memfed 0
  in both, which is NOT proof (the unit owner's ruling): the hand traces above follow every op instead, and every
  `lui-const (dataflow)` word inside a compared function is one of the traced lui words (the unit owner's ruling); those
  outside the compared set are not part of this chain.
- **luirows** (each exposed compared function re-run on strictcmp3.tcmp by address): exposed 43, lui-in-section 76, rerun DIFFERENT-target 43.
- **ambiscan** over every output of this run: files read 31, by-name compares seen (distinct names) 537, ambiguous hits 96, distinct ambiguous names 1. Every hit is the one name `_ZN6__asanL11MemToShadowEm` (5 copies
  per image) on a CSTR row of a paircl output; paircl pairs by address, so no compare took it by name. strictcmp3
  refuses that name itself, and dupcheck below measures the by-name compares.

## Duplicate names (`commit/dupcheck.tsv`)

Names compared by name: 895; with more than one .symtab entry in X or Y: 5; for each, the Y copy the by-name compare takes is the copy the code calls, and the by-address verdict is the
same (`dupcheck.tsv`).

## Controls

**(a) Known-equal, identity B** (`commit/closure-identity.out`, `commit/ctl-jtcheck-identity.out`): roots EQUAL /
EQUAL-mod-pcrel; by-name closure other 100, the same row set as against grant; every jtcheck row the same.

**(b) The kit's plants and the settlement controls** (`commit/planted/planted.sha256`, `commit/planted/planted.cmp`), one changed word or byte each in a copy of one image (each row names it; the kit's plants and the De Bruijn control copy grant B):

| plant | caught by |
|---|---|
| call, in copies of GRANT_B_PIN and GRANT_B_TWIN: `___interceptor_malloc`+0x130 re-pointed from `__asan::asan_malloc` to `__sanitizer_get_allocated_begin` (file 0x421e0) | strictcmp3 DIFFERENT-target (target-differ at +0x130, `names`); closure_strict3 other 100 -> 101; paircl other row `___interceptor_malloc` DIFFERENT-target; jtcheck target differs 1 |
| rodata, in copies of GRANT_B_PIN and GRANT_B_TWIN: `__intscan`+0x4c8 re-pointed from `table` to `all_mask` (file 0x850cc) | strictcmp3 on `__intscan` DIFFERENT-target (`table+0x0` vs `all_mask+0x0`); jtcheck target differs 1; closure_strict3 other 100 -> 101; paircl other 107 -> 108 |
| settlement control, in a copy of GRANT_B_TWIN: one byte of the 64-byte De Bruijn ctz table `Allocator::Allocate` reads at +0xdc (file 0x432, 0x0e -> 0x0f) | settle.py INDEXED: planted copy **DIFFERS**; untouched GRANT_B_TWIN SETTLED-EQUAL |
| dispatch-size control: `_ZN11__sanitizer9VSNPrintfEPciPKcPv` +0x1b8 `slli t3,a7,2` (the dispatch of the table at 0x1c0: 4-byte entries) set to `slli t3,a7,3` in a copy of WIRE_B_TWIN (`commit/ctl-settle-slli3-planted.tsv`) | settle.py on the planted copy: **REFUSED, UNSETTLED** (a table is read only at the entry size and count jtcheck 226254f48c97 proves on both images, or not settled); unplanted (`commit/settle.tsv`): TABLE rel4-jump, 33 entries, SETTLED-EQUAL |
| hand-settlement control (bound): in a copy of WIRE_B_TWIN (X), a second definition of the limit, `addi s5,zero,10` in place of `addi a0,a0,1` at +0x278, in an arm that loops back to the guard and lies after it in address order; tests part (3), the bound: every definition on every path, which only a walk of the CFG finds here (`commit/ctl-handtable-bound.out`) | handtable.py: **NOT SETTLED (the bound differs between X and Y)** (gated: must read NOT SETTLED (the bound differs...) |
| hand-settlement control (zarm): in a copy of WIRE_B_TWIN (X), a larger second limit, `addi s5,zero,60` in place of `sb s7,0x31(s0)` at +0x28c, in the `z` arm, which only the dispatch enters; tests part (3), the bound: the backward walk from the guard reaches +0x28c through the arm's own `j` at +0x294 (the first walk, which has no arm edges), takes 60 as a limit, and slot 47 then names no word of the function (`commit/ctl-handtable-zarm.out`) | handtable.py: **NOT SETTLED (X: slot 47 targets 0x83cb0, not a word of the function)** (gated: must read NOT SETTLED (X: slot 47...) |
| hand-settlement control (jump): in a copy of WIRE_B_TWIN (X), a jump into the dispatch block, `j +0x1c` in place of `sb s7,48(s0)` at +0x248; tests part (2), the dispatch: each word after the guard has one predecessor (`commit/ctl-handtable-jump.out`) | handtable.py: **NOT SETTLED (X: the block word +0x264 has predecessors ['+0x248', '+0x260'])** (gated: must read NOT SETTLED (X: the block word...) |
| hand-settlement control (entries): in a copy of WIRE_B_TWIN (X), the limit `addi s5,zero,46` at +0x234 raised to 47, so the 48th slot is the first slot of the next table; tests part (1), the entries: each slot must name a word of the function (`commit/ctl-handtable-entries.out`) | handtable.py: **NOT SETTLED (X: slot 47 targets 0x83cb0, not a word of the function)** (gated: must read NOT SETTLED (X: slot 47...) |
| hand-settlement control (slot): in a copy of GRANT_B_TWIN (Y), table slot 3 (vaddr 0x213a4) re-pointed to the target of slot 0; tests part (1), the compare of X's and Y's entries (`commit/ctl-handtable-slot.out`) | handtable.py: **DIFFERS (1 entries)** (gated: must read DIFFERS (1 entries)...) |

**(c) The plants the hand traces must catch (a, c) or refuse (b)** (`tools/plants.py`, `commit/plants.out`, `commit/planted/`):

| plant | change (both copies) | hand trace | the kit |
|---|---|---|---|
| (a) a lui value into a STORE base through `add` | `_ZN6__asan16AllocatorOptions7SetFromEPKNS_5FlagsEPKN11__sanitizer11CommonFlagsE` +0x10: lui t0,0x700; lui t1,0xffa00; add t0,t0,t1; sd zero,0(t0); the sum 0x100000 is _ZN11__sanitizerL26internal_alloc_placeholderE+0x5e600 in X, _ZN11__sanitizerL26internal_alloc_placeholderE+0x59480 in Y; both lui values lie in no section | **CAUGHT: DIFFERS** | strictcmp3 cmp: EQUAL, target-differ 0 (FAIL-OPEN #3) |
| (c) a lui value into a STORE base only through `divuw` and `slli` | `_ZN6__asan16AllocatorOptions7SetFromEPKNS_5FlagsEPKN11__sanitizer11CommonFlagsE` +0x10: lui t0,0x700; li t1,14; divuw t0,t0,t1; slli t0,t0,1; sd zero,0(t0); the value 0x100000 is the same address as in (a) | **CAUGHT: DIFFERS** | strictcmp3 cmp: EQUAL, target-differ 0 |
| (b) a lui CALL ARGUMENT to a uptr address parameter | `_ZN11__sanitizer10StackStore9BlockInfo11GetOrUnpackEPS0_` +0x308: the call at +0x30c is re-pointed to _ZN11__sanitizer10ProtectGapEmmmm (X 0x6b70c, Y 0x6c550), whose parameter a3 is `uptr zero_base_max_shadow_start` (an address) | was (i) CALL ARGUMENT; now **REFUSED: NOT CERTIFIED** | strictcmp3 cmp: DIFFERENT-target (its only differing target is the natural lui-in-section word at the lui itself; the re-pointed call names the same function on both sides, so the kit does not see the plant) |

## Limits

- **A fourth fail-open, in this record's own tool, found by the egress review (R1) and fixed here:** luitrace treated
  every store of a traced value into a stack slot as a spill and never asked whether the slot's address leaves the
  function. It now applies the escape rule of "Criterion"; on this unit the traces met a store into a slot of an
  escaping frame object 262 times (the `# SHAPES` count: once per lui trace that meets the store, in X, in Y, and in X
  again with each noreturn call's fall-through put back); those stores are 90 STORE rows (`ROW` lines, one per lui
  value and store): 7 settle by class (iv), 8 as STORE-UNREAD and 75 are NOT CERTIFIED: REAL 0.
- **A fail-open in basescan, found by the egress re-review (RR1) and fixed here:** an address no symbol covers was
  compared by its bare section name; see "What changed" (2) and shape (h).
- **A fail-open in settle.py, this record's own tool, found by the uci series writer's read:** a dispatch table was
  settled at whichever entry size (4, then 8 bytes) settled first, not at the size its `slli` gives. `dispatch_bound`
  is gone with this version (see "What changed against the previous version of this slice"): a table's size and
  count come only from jtcheck 226254f48c97's proof, and the planted `slli 3` control reads REFUSED because 226254 proves
  no table on the planted copy. Two shipped rows changed with it: parseCIE +0x23c and parseFDEInstructions +0x140 went
  from TABLE SETTLED-EQUAL to REFUSED UNSETTLED, and are settled by hand.
- **The table's arms as edges are not exercised by a control.** handtable.py walks the CFG twice: first with no edge
  from the dispatch, then with the table's arms as its edges (handtable.py:227-231), and refuses when the two walks
  find different limit definitions. No shipped control makes the two walks disagree, so that refusal is not
  exercised; the zarm control is refused after the first walk, by its entries.
- **Callee readers are traced only for class (iv) and STORE-UNREAD.** A value stored into an escaping frame object, passed as an
  argument, or handed to the kernel is a row (or a measured non-row). Such a row is NOT CERTIFIED unless a cited
  parameter meaning settles it (class (i)) or every reader receives the bytes as cited integer struct members (class
  (iv), whose row lists the callee's loads of them); the kernel's and musl's structs are not pinned, so a frame
  object handed to a syscall stays NOT CERTIFIED.
- **NOT CERTIFIED: REAL 0** means no difference was found, not that the use was proved harmless: 1018 use rows.
- **Code only.** Register-indirect call sites (97 per by-name closure) take their targets from data; neither the
  kit nor the hand traces compare those targets. A use reaching such a call is NOT CERTIFIED.
- **Citations:** compiler-rt (pinned by its tarball sha256) and, for the two tables settled by hand, libunwind at the
  release tag llvmorg-20.1.8 (not pinned: see those settlements); musl's source is not pinned, so musl parameters and
  returns stay open.
  A citation is the first declaration whose count, kinds and scope agree with the mangled name; a static member
  function reads as a member (a0 = this), which can only refuse, never settle.
- **Not a proof of context.** "Same code" does not say that grant's released walks prove the chain in wire B's call
  contexts.

## Unit gates (`commit/gate-kit.txt`, `gate-lui.txt`, `gate-base.txt`, `gate-plants.txt`, `gate-controls.txt`)

`tools/gates.py` reads the outputs above and writes one verdict file per gate, each holding the counts it read and
every failing line, and ending in its verdict line. The rules: **kit** -- each of the 4 roots reads EQUAL or
EQUAL-mod-pcrel with target-differ 0, every closure row and target pair of `ACCEPTANCES.tsv` is SETTLED-EQUAL or is
left to a hand trace that found no difference or to a hand table settlement of `handtable.out` that reads
SETTLED-BY-HAND (parts (1) to (3) by handtable.py; part (4), a non-writer's read, is stated with each settlement), and
no data line and no hand verdict reads DIFFERS; **lui** -- no `luitrace.tsv` row
reads DIFFERS; **base** -- `basescan.tsv`'s TOTAL line has DIFFERS 0 and its verdict classes sum to the base count,
and no row reads DIFFERS; **plants** -- every planted control of `plants.out` reads CAUGHT or REFUSED, the planted
De Bruijn copy reads NOT SETTLED and its untouched baseline SETTLED-EQUAL, the dispatch-size control has no table
read with 4-byte entries, and the five hand-settlement controls read as listed in "Controls". Each gate file's
`head` is GATE_HEAD (env.sh), the commit this slice was staged on before its files were committed, as a file cannot
name the commit that holds it; the gates read this slice's own outputs, and `run.sh`, run from a
copy of this slice with the same GATE_HEAD, writes the same gate files byte for byte. Each gate's verdict, from its
file (its `head` field left out):

    gate-kit.txt: VERDICT PASS (inputs cmpkit 86da41d3ef68: strictcmp3.py b553126fa224 (roots.tsv); settle.py 4eeeae293912, luitrace.py 06d2b1005932 and mkaccept.py 984322748de5 (ACCEPTANCES.tsv, jtcheck 226254f48c97: jtcheck.py 94c2f3081b0c); handtable.py 95e3bc23db39 (handtable.out))
    gate-lui.txt: VERDICT PASS (inputs luitrace.py 06d2b1005932 (luitrace.tsv))
    gate-base.txt: VERDICT PASS (inputs basescan.py a500fff1960c (basescan.tsv))
    gate-plants.txt: VERDICT PASS (inputs plants.py 237bb0a60df5 (plants.out); settle.py 4eeeae293912 (ctl-settle-*.tsv); handtable.py 95e3bc23db39 (ctl-handtable-*.out))

Before it writes a verdict, gates.py runs the two negative controls on copies, and refuses to write at all unless
each fails (`commit/gate-controls.txt`):

    control: one roots.tsv row set to DIFFERENT -> kit FAIL, lui PASS, base PASS, plants PASS
    the kit gate: VERDICT FAIL (inputs cmpkit 86da41d3ef68: strictcmp3.py b553126fa224 (roots.tsv); settle.py 4eeeae293912, luitrace.py 06d2b1005932 and mkaccept.py 984322748de5 (ACCEPTANCES.tsv, jtcheck 226254f48c97: jtcheck.py 94c2f3081b0c); handtable.py 95e3bc23db39 (handtable.out))
    control: one plant verdict set to EQUAL -> kit PASS, lui PASS, base PASS, plants FAIL
    the plants gate: VERDICT FAIL (inputs plants.py 237bb0a60df5 (plants.out); settle.py 4eeeae293912 (ctl-settle-*.tsv); handtable.py 95e3bc23db39 (ctl-handtable-*.out))

## The committed slice

`commit/` holds everything committed except this file and MANIFEST.md. Its last writer is `tools/scrub_out.py`, the
last step of `run.sh`: each image path becomes the token `images.sha256` defines by sha256 and index line, each path
of a file of this directory becomes the file's name, tool scripts and `run.sh` are copied byte for byte, `earlier/`
(`earlier/` ships `v4bbd3a74be89/` (with its own run.sh) and `va88c2822a0f2/` (with its own run.sh; it holds its own earlier versions `v9cbc3553c09e/`, which have no run.sh of their own: its run.sh runs them); each version as its run wrote it except the rewrites `earlier/SCRUB.tsv` lists) is copied
verbatim, and scrub_out refuses its own output if any file or file name still holds a host path, an internal branch
prefix, the registry's name, a word the scanner of record blocks (the list it reads from SCRUB_FORBIDDEN) or a
SESSION NAME.

## Names: a ruling is cited by role

No file of this slice names a session or holds a time of day. A ruling is cited by the ROLE that made it, with no
time of day ("the unit owner's ruling", "the libc owner", "the record writer's rule": the record writer, the role
that writes this record, is one of those roles), so no fact of this record depends on which session ruled or when.
`tools/rolenames.py` is the one place that knows the rule: the name shapes of the session roster, the role of each
prefix, and the forms a citation takes in these texts. Four writers use it, and each refuses a name left behind:
`tools/kitscrub.py` (this record's copies of the kit files: comment and docstring words only, with the syntax tree,
docstrings left out, equal to the original's -- see the `code compare` line of each entry in `tools/DIFFS.md`),
`tools/scrub_out.py` (every file of `commit/`, and every file name), `tools/mkdiffs.py` (a removed line of a diff) and
`tools/earlierscrub.py` (the archive under `earlier/`). With ROSTER_TSV set (as in this run), the writers also refuse
every name of that roster and every stem of one (the name without its role prefix, and each shorter tail of its
dashed words, when it holds a digit or a dash and is 4 or more characters long; a session is often cited by its stem
alone, and a stem is rewritten as its name is); without it they refuse the shapes, which is what the scanner of
record blocks. The writers also refuse or rewrite every name of the agent-name lists in the directory NAMES_DIR and
of the tool registry's roster.txt (ROSTER_TXT). SCRUB_FORBIDDEN (below), NAMES_DIR and ROSTER_TXT are env.sh
settings that are required: the writers stop without them (`tools/rolenames.py` stops at its import when NAMES_DIR or
ROSTER_TXT is unset or names nothing). The texts of this record (`tools/luitrace.py`, `tools/basescan.py`,
`tools/plants.py`, `cite-extra.tsv`, `run.sh`, this file through its writer) carry the role form themselves.

No file of this slice spells, in any form, a word the scanner of record blocks: the patterns the writers refuse,
redact or rewrite, and the one name they must know, are read at run time from a list outside the slice
(`SCRUB_FORBIDDEN`, set in env.sh) by `rolenames.private`, and each writer stops when the list is missing.

`earlier/` ships `v4bbd3a74be89/` (with its own run.sh) and `va88c2822a0f2/` (with its own run.sh; it holds its own earlier versions `v9cbc3553c09e/`, which have no run.sh of their own: its run.sh runs them), each version as its run wrote it, except the rewrites `tools/earlierscrub.py` applied;
`earlier/SCRUB.tsv` lists each changed file with its sha256 as the version ran -> as shipped:
  `earlier/v4bbd3a74be89/REVIEW.md` 9343101629d1 -> c4729ae0459d (role);
  `earlier/v4bbd3a74be89/tools.sha256` fdc55007637d -> de15a8076206 (sha256 pin repair);
  `earlier/v4bbd3a74be89/tools/DIFFS.md` 42731327b552 -> 8b9f15ed52f2 (time, sha256 pin repair, DIFFS.md note);
  `earlier/v4bbd3a74be89/tools/bytecmp-1480ca2faea0.py` 0ac2ec8db277 -> 145447a50bb2 (time);
  `earlier/v4bbd3a74be89/tools/drvcmp.py` 89ca4b797ed7 -> 5d36e4bd76c6 (sha256 pin repair);
  `earlier/v4bbd3a74be89/tools/jtcheck.py` 3e1e6b8fe5ed -> 5a9e1d5cc57f (sha256 pin repair);
  `earlier/v4bbd3a74be89/tools/mkdiffs.py` 70336fad0e91 -> 5a16d9ee6f83 (loader);
  `earlier/v4bbd3a74be89/tools/scrub_out.py` 4e4f54a60d9f -> d8a9c91ca817 (loader);
  `earlier/v4bbd3a74be89/tools/strictcmp2.py` 5f6c05791a3f -> 61a95130e6d4 (role, time);
  `earlier/va88c2822a0f2/RECORD.md` cd1f26e1a200 -> d5632a5b6ae8 (sha256 pin repair);
  `earlier/va88c2822a0f2/tools.sha256` 4ac8a20973d6 -> 0faaf35183ec (sha256 pin repair);
  `earlier/va88c2822a0f2/tools/DIFFS.md` 5d14d3cb6df7 -> 50347bce3f8a (time, sha256 pin repair, DIFFS.md note);
  `earlier/va88c2822a0f2/tools/bytecmp-1480ca2faea0.py` 0ac2ec8db277 -> 145447a50bb2 (time);
  `earlier/va88c2822a0f2/tools/mkdiffs.py` bd50962aa1a6 -> 6b1b976d4004 (loader);
  `earlier/va88c2822a0f2/tools/repin_check-e5487165abb8.py` f268a01b33c5 -> 7a69dadf5169 (time);
  `earlier/va88c2822a0f2/tools/scrub_out.py` 4ee202522d78 -> 421e40db2b09 (loader);
  `earlier/va88c2822a0f2/v9cbc3553c09e/tools.sha256` 46aa89abf9cc -> 69b8d80a5245 (sha256 pin repair);
  `earlier/va88c2822a0f2/v9cbc3553c09e/tools/DIFFS.md` 9e6044358d6b -> af60f88acb34 (time, sha256 pin repair, DIFFS.md note);
  `earlier/va88c2822a0f2/v9cbc3553c09e/tools/bytecmp-1480ca2faea0.py` 0ac2ec8db277 -> 145447a50bb2 (time);
  `earlier/va88c2822a0f2/v9cbc3553c09e/tools/repin_check-9cbc3553c09e.py` 15045c02875c -> a406b7c1b76e (time);
the role rewrite (a session name written as its role, or dropped with its claim kept), the time rewrite (a time of
day dropped, with the punctuation
that only served it; in a tool, only a comment or a docstring changes: the syntax tree is checked), the forbidden-word
loader (each pattern line of an archived tool that spelled a blocked word
reads the same pattern from SCRUB_FORBIDDEN; with that list present the tool runs as it ran: run on its own inputs,
the archived `v4bbd3a74be89/tools/scrub_out.py` writes byte for byte what the tool as run writes, but for the copy of
itself), the sha256 pin repair (the archive's own pins of a rewritten file set to the shipped copy, repeated until no
pin changes; every archived drvcmp still passes its block checks, and every archived jtcheck.py passes its pins and
runs on its own inputs; the archived `va88c2822a0f2/tools/repin_check-e5487165abb8.py`, `va88c2822a0f2/v9cbc3553c09e/tools/repin_check-9cbc3553c09e.py`, run alone, look for the input `./bytecmp.py` of their docstring; the version's own run did not run them alone: its drvcmp.py loads them by line range (`tools/drvcmp.py:21-24` of that version)) and the DIFFS.md
note (each line the role or the time rewrite changed in a tool copy, shown in its version's `tools/DIFFS.md` and
counted in its row; a note names the original by its sha256 and no registry commit). Nothing else in the archive
changed: files under `earlier/` keep their own text as it ran, apart from the rewrites SCRUB.tsv lists; a commit
named inside them is part of that text, not a citation of this record.

## Checks

- **Runnable from the slice:** `run.sh`, run from a fresh copy of this slice with the record's `env.sh` beside it,
  wrote a `commit/` identical to the slice's (`diff -r`: 0 lines). The files `run.sh` does not write were left out of
  both sides: `RECORD.md`, `MANIFEST.md`, `handtable-read.md` (an independent reader's report) and
  `mk_slice_manifest.py`.
- **Tokens only:** of the 248 files of `commit/` outside the token table `images.sha256`, all 248 are equal to the
  run's own files: tools and `run.sh` byte for byte,
  every raw output under the forward mapping (image path -> token; absolute path of a file of the record directory ->
  its name); differing: none. The 135 that hold no such path also give back the raw output token by token.
- **Scanner of record** (`binscan_of_record.sh`, scanner `0609a660961e` with exceptions `1201aaae30c9`, run over this slice at its
  repository path `projects/reac-repacer/fuzz_wire/proofs/provenance/evidence/wire-b-alloc/`): 254 inputs, 0 files with an uncleared
  flag-tier hit; control: all needles found. The hits listed are 0 non-blocking `codename(embedded)` hits: hex
  addresses and sha256 values.
