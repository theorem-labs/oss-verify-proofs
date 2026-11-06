# UCI-B-MEMCPY: the image-B `__asan_memcpy` contract of reac-repacer/fuzz_uci

Read-only record: no proof file is added or changed. Base `f47e2a8927b9` (the image-B core).

## The theorem

`lib/B/YE2q.v:146` `asan_memcpy_realizes` (already in the base; relocated with the image-B core from fuzz_grant's released
`lib/B/YE2q.v`, recipes `4f87de75d67`). Entry `cfg_at tfibsegs 0x50674` = uci B `__asan_memcpy` (twin symtab: 0x50674,
1180 bytes). The composition takes this statement verbatim as its Section hypothesis (no restatement, no bridge lemma).

## Build and assumptions

`cb build` (cb `98f0481385b6`), FACTS `25e3d17bdb50`, targets `lib/B/YE2q.vo` and a scratch probe
`lib/B/ZH10MemcpyAssm.v` (`Check` + `Print Assumptions`; not committed): rc=0, wall 207 s, 2 targets compiled, 0
restored from the cache, 0 failed; 4 PINNED at facts 25e3d17bdb50 (0 MISMATCH, 0 MISSING, 0 UNPINNED, 0 ABSENT).
Built files: `lib/B/YE2q.v` sha256 `4b02f237f14baa712b932cb39b811a1003cde902748804827ed3e8db78419eb5`, `lib/B/YE2q.vo`
sha256 `28be5342f43ff49f659a4da4b64a9d7d03e7714170df66f017f8f0e996b96169`.
`Print Assumptions YE2q.asan_memcpy_realizes`, every axiom name: `FunctionalExtensionality.functional_extensionality_dep`,
`PrimArray.array`, `PrimInt63.eqb`, `PrimInt63.int`, `PrimInt63.land`, `PrimInt63.leb`, `PrimInt63.lor`, `PrimInt63.lsl`,
`PrimInt63.lsr`, `PrimInt63.ltb`, `PrimInt63.sub`, `PrimString.get`, `PrimString.length`, `PrimString.string`.
No `Admitted` / `admit.` / `Axiom` / `Parameter` in `lib/B/YE2q.v`.

## Donor byte compare (cmpkit 86da41d3ef68)

Kit of record: cmpkit `86da41d3ef68` = `tools/cmpkit/86da41d3ef68/` at commit `98e50c029045` (`sha256sum -c SHA256SUMS`:
all 9 members OK; strictcmp3 `65688e94214a`, closure_strict3 `a98d2b3e8857`, jtcheck `8b0ea3862423`, drvcmp
`4d70e90bc1fa`, repin_check `e6883477399d`, bytecmp `1480ca2faea0`, ambiscan `9f61b4cee422`). Every script here loads the
kit from `KIT=<dir>`. It supersedes cmpkit 4bbd3a74be89, on which this record was first made (`REVIEW-4bbd.md`).

uci B (pin `a1b86e424add`, unstripped twin `8d07ffcf5948`) against fuzz_grant B (pin `fde52226dc48`, unstripped twin
`5a5ee7c02b4e`).

0. **Exposure of the 4bbd record**: ambiscan on the 4bbd slice (commit `7d92e375ee4`): 0 AMBIG over 14 files
   (`ambiscan-4bbd-record.out`). Rule 8 (lui-built
   values) exposed it: the re-run below has 74 `lui-in-section` targets that 4bbd compared raw.
1. **Twins** (`drvcmp.py twins`, `twins.out`): each twin's PT_LOAD layout equals its pin's, and its loadable bytes differ
   only in the ELF header and `.note.gnu.build-id`.
2. **Closure** (`closure_strict3.py <uci twin> <grant twin> __asan_memcpy`, `closure-memcpy.out`): 785 functions (98
   register-indirect call sites inside, counted not followed), each compared once per X address, paired by qualified
   name, none ambiguous or absent: 170 EQUAL, 515 EQUAL-mod-pcrel with all targets equal, 100 DIFFERENT-target (words-only
   EQUAL / EQUAL-mod-pcrel on all 100). Every acceptance and every differing target is printed.
3. **jtcheck** (`jtcheck.py <uci twin> <grant twin> <the 100>`, list `others.txt`, output `jtcheck-others.out`): 10
   settled; 39 with only `lui-in-section` targets; 51 with unnamed `.rodata` targets still open. Open targets: 74
   `lui-in-section`, 74 UNMEASURED, 2 DIFF (data-differs). No REAL difference, no UNPAIRED word, no SKIP, no UNREADABLE.
4. **The 76 unnamed `.rodata` targets** (`settle.py` sha256 `5df19932b74d`, list `unsettled.txt`, output `settle.out`
   sha256 `40b33a314e5c`): one named measurement per target, chosen by the instructions that use the address, decoded on
   both images (docstring). All 76 EQUAL:

| measurement | targets | what is compared |
|---|---|---|
| BYTE64 | 6 | the 64-entry de Bruijn `lbu` table of `Allocator::Deallocate` / `Allocate`, `SizeClassAllocator64` (3), `RZSize2Log`: index `srli _, 58` (<= 63), 64 bytes equal |
| REL4 jump | 3 | `VSNPrintf` +0x1c0 (33 entries; bound `addi s0, zero, 0x20` set once before the loop), `parseFDEInstructions` +0x140 (48), `parseCIE` +0x23c (47): every entry lands on the same in-function offset on both sides |
| CSTRANY | 67 | an address used only as a C string: the empty string (the kit's rule B no longer accepts it); bytes through the NUL equal |

   The table bound is `bound_const`: on every path from the function's entry the last write of the bound register is
   `addi rK, zero, K`, one K. CSTRANY needs `cstr_use` to pass on both images (every path of the function: the address
   is only passed on, stored as a pointer value, copied, compared, or read by `lbu _, 0(r)`). Its known gaps (R1, R3-R6,
   G3a in `REVIEW-4bbd.md`) are reached by no row. Control (`control-notable.out`): with table matching off, the use
   check refuses the three jump-table targets, exit 1.
5. **The 74 `lui-in-section` targets** (kit OPEN LIMIT 1: settled only by showing that the value is not used as an
   address). `luiuse.py` (sha256 `e2b7da60a5fa`, output `luiuse.out` sha256 `4fee24d0ea1f`) traces each lui-built value
   on both images through every path of its function and, through direct calls, its callees (depth 8): a register holds
   it PURE (the value or arithmetic on it and constants) or MIXED (combined with an unknown register: an offset); 8-byte
   stack spills and REL4 jump tables are followed. Result: 0 ADDRESS (no PURE value is ever the base of a load, store, AMO
   or jalr), 46 NUMBER, 28 NUMBER+HAND, the same on both images. The values are sizes, flags, masks and counts (e.g.
   0x100000, 0x104022 = mmap flags, 0xf4240 = 1000000, 0x15180 = 86400, 0x400010 = an offset into `theDepot`).
   `hand.tsv` gives the reason for each of the 47 HAND uses (91 occurrences): a syscall argument that is a size or flags
   or is beyond the syscall's arity (number from a7), a Printf / Report vararg whose conversion is `%zx` / `%zd` / `%p`
   (format string read at the call site) or that the format never reads, a counter or option field, a `long` return.
   `handcheck.py` (output `handcheck.out`): every HAND use has a reason, 0 failures. Controls (`luiuse_control.py`,
   `luiuse_control.out`): 6 planted functions (absolute load, offset, address used in a callee, value + constant as a
   store base, spill-reload-base, returned value) each get their stated verdict.
6. **lui values that become PART of an address** (kit limit of 18:53Z: a lui value added through add / sub / shNadd
   into a load / store / jalr base is settled only by computing the full address in both images). 18 of the 74 rows
   reach a base that way (luiuse's MIXED base uses). `basecalc.py` (sha256 `8a086d1387c5`, output `basecalc.out`
   sha256 `d1a66e775c37`) carries a value per register on every path (a constant; an image address from auipc or from
   a .got / .data.rel.ro pointer cell, with the constants added; or a run-time value), starting from the values every
   path from the function's entry gives the registers at the row's word, into direct callees with their argument
   values, and computes every base that carries the lui value on both images. Result, 204 base sites: 22 IMAGE EQUAL
   (the full address is the same symbol + offset in both images: `internal_alloc_placeholder` +0x40040 .. +0x40dc8 and
   +0x81008 .. +0x81030 in `internal_allocator` and the `memset` it calls; `theDepot` +0x400008 and +0x400010 plus a
   run-time index in `StackDepotGet` and `TwoLevelMap::Create` / `StaticSpinMutex::LockSlow` it calls); 182 RUNTIME (the
   other part is a run-time pointer: a parameter such as an allocator's or a mutex's `this`, a loaded pointer, or a
   masked pointer; the lui value is a field offset, the same number in both images; basecalc only shows that the other
   part is no image address it recognises, and the fresh reviewer's own reaching-definition pass confirmed all 182 as
   run-time pointers); 0 absolute uses, 0 path joins of an
   image address, 0 not measured. Controls (`basecalc_control.py`, `basecalc_control.out`): 4 planted functions (image
   address + lui value, parameter + lui value, the lui value alone, a spilled and reloaded image address + lui value)
   each get their stated class and full address.

7. **The kit's own `lui-const (dataflow)` acceptances** (kit limit of 19:20Z: its dataflow does not follow every
   operation, so its label is not evidence). `luiconst_rows.py` lists the 35 lui-const targets (33 functions; 26 of
   them the mask 0xfffff, each value the same on both images) that `closure-memcpy.out` accepts (`luiconst-rows.txt`); `luiuse.py` and `basecalc.py` trace them like
   the rows above: 17 NUMBER, 18 NUMBER+HAND (`luiuse-luiconst.out`; two more HAND reasons in `hand.tsv`, `handcheck.out`
   covers both outputs: 49 reasons, 115 uses, 0 failures), 0 ADDRESS; 4 base sites, all RUNTIME (`basecalc-luiconst.out`).

Operations the traces follow (luiuse.py and basecalc.py): every register write; add / sub / sh1add-sh3add / addi /
addiw / slli / mul / div and the logical and / or / xor / andi / ori / xori / shifts / slt (a result that mixes the lui
value with anything stays tracked); mv; 8-byte stack spills and reloads; branches both ways; jumps and REL4 jump tables
inside the function; direct calls into the callee with the argument registers; returns.

So every member of the closure is byte-equal to the donor's up to relocation, with every target the same, every
lui-built value a number, and every address it is part of the same symbol + offset or a field offset from a run-time
pointer.

**Fresh review** (`REVIEW-86da.md`, verdict CONFIRM on steps 4 to 7; every output reproduced). After it, the wording of
five `hand.tsv` reasons was corrected as it found (the va_list hand-off of Printf / Report is at +0x30 / +0x34, and the
AsanDeactivate store is two u16 fields), and the lui-const value count above; no row or verdict changed.

## Harness call sites (`callsites.py` on the kit's drvcmp / repin_check `targets`: direct calls whose target is `__asan_memcpy`'s entry; re-run on the kit, output unchanged)

| site | uci B | uci A |
|---|---|---|
| check_no_overread+0x6c | 0x7f5d8 | 0x7f568 |
| check_no_overread+0x7c | 0x7f5e8 | 0x7f578 |
| check_value+0x58 | 0x7f708 | 0x7f684 |
| check_clamp+0x114 | 0x7fa64 | 0x7f99c |

Every other caller is in the runtime. check_clamp's destination lies in its class-1 fake-stack frame. The contract states
that case: `dest_ok` asks `~ aowned B ly S a`, and `aowned` (`lib/Reusable/YG0n.v:237`) excludes `aclient_byte S a`, which
holds for every byte of a live frame in `frames S` (and its shadow). The caller supplies `writable_at`,
`range_addressable` (stack_malloc's post gives the frame zero shadow) and the not-in-the-real-stack-window conjunct.
