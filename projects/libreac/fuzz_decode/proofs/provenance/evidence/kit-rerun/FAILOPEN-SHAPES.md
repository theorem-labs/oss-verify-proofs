# kit-rerun: the KNOWN FAIL-OPEN shapes (a)-(h) of cmpkit 86da41d3ef68, on every function the records compare

cmpkit 86da41d3ef68 stays the kit of record. Its registry of known fail-opens (tools commit 7f2e3c70626) says: an
EQUAL verdict of the kit is not evidence where an address value reaches a load / store / jalr / AMO base through one
of these shapes:

- (a) the load / store immediate (V + imm: the kit never forms it);
- (b) an addi / addiw chain;
- (c) ori / xori / slli;
- (d) a stack spill, an FP move or a CSR round trip;
- (e) a jump-table arm reached only by fall-through;
- (f) an in-function callee (the address passed in a0-a7 to a callee inside the compared function's region);
- (g) c.lui;
- (h) an address built without lui (auipc, or a loaded constant).

This file checks every compared function of the four records here, on both sides, for every site of those shapes,
and names the target of each site on both sides. Provenance only: no file here proves a function, and no verdict of a
record changes.

## One line per record

Counts are in-scope sites per shape (a site with two shapes counts under both). Hand pass: `failopen.py`
a4a1e11fc4e9; kit verdicts: cmpkit 86da41d3ef68.

| record | line |
|---|---|
| A record, `A/kit-rerun-4bbd3a74be89/` (7 pairs, donor twin C : decode A twin) | shapes (a)-(h): a 53, b 28, c 27, h 59 (86 in-scope sites of 221); d 0, e 0, f 0, g 0; DIFFERENT 0 (failopen.py a4a1e11fc4e9). The record's author's own trace answers the same shapes; see "The A record: its author's trace". |
| B record, `B/fncmp.cmpkit-4bbd3a74be89.log` (8 functions, T : E and S : E) | shapes (a)-(h): T : E a 53, b 28, c 27, h 59 (86 of 249); S : E the same (86 of 249); d 0, e 0, f 0, g 0; DIFFERENT 0 (failopen.py a4a1e11fc4e9) |
| settled rows, `cmpkit-4bbd3a74be89/settled.tsv` (Allocate +0xdc T:E and S:E, PoisonShadow +0x48c S:E) | shapes (a)-(h): Allocate T : E and S : E each a 30, b 23, c 22, h 22 (44 of 92); PoisonShadow S : E a 20, h 35 (35 of 67); d 0, e 0, f 0, g 0; DIFFERENT 0 (failopen.py a4a1e11fc4e9) |
| the 86da41d3ef68 scans record, `cmpkit-86da41d3ef68/` (`SCANS.md`, the three scan logs, `LUI-COMBINED.md`) | it scans the compares of the three records above, so its line is theirs: C : A a 53, b 28, c 27, h 59; T : E and S : E the same; d 0, e 0, f 0, g 0; DIFFERENT 0 (failopen.py a4a1e11fc4e9) |

No site of any record has a different target on the two sides. No CLAIM row moves toward a real difference.

## Method

Everything is in `cmpkit-86da41d3ef68/failopen/`. `run.sh` (sha256 `e0d18d3d4764`) runs inside the toolchain image
`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b`
(GNU objdump 2.42, python 3.12.15; nothing else). It checks the sha256 of each image before use:

| side | image | sha256 |
|---|---|---|
| donor twin, C (A record) and T (B record) | `cgif_file_fuzzer.asan-ubsan` | `ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7` |
| symtwin, S (B record) | `cgif_file_fuzzer.asan-ubsan.symtwin` | `3f110c1db582567aa8b745a910f641e51b80b8aa84dbd5bc5478c823ca0783f4` |
| decode A twin, A | `fuzz_decode.asan` | `4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2` |
| decode B twin, E | `fuzz_decode.asan-ubsan` | `6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4` |

The instructions come from `riscv64-alpine-linux-musl-objdump -d -M no-aliases --disassemble=FN` of the twin. objdump
follows the ELF's arch attribute, and these images say `rv64i2p1_m2p0_a2p1_f2p2_d2p2_zicsr2p0_zifencei2p0_…` (no C).
So objdump prints a compressed parcel as `.insn 2, …`, while the CPU still runs it. For that reason, `run.sh` also
lists the same bytes as a plain binary (`-b binary -m riscv:rv64`), and `failopen.py` reads a parcel from that listing
only where the ELF listing says `.insn`. In the 8 functions of the 4 images there is no such parcel (`parcels decoded
from the raw listing 0` in every function), and no line is undecoded.

`failopen.py` (sha256 `a4a1e11fc4e9037b0df21c76bcd36be4c8f7e0789b36be54b4bf514ba20fff8b`) runs one MAY forward dataflow
per function and image, over the whole CFG to a fixpoint, with symbolic values in every register, FP register, CSR,
stack slot (by its offset from the entry sp) and statically addressed cell:

- A load from a static address in read-only or RELRO memory (`.got`, `.rodata`) gives the constant stored there. A
  load from writable memory gives a runtime value, named by the address it was read from.
- Every jal / jalr edge into the function's own region is followed, with a0-a7.
- Code not reached from the entry is seeded from the unresolved indirect jumps and walked.
- Loops are widened to `phi(+off,reg){…}` terms that keep every constant that flowed in.

A site is in scope when its base carries an address value formed in the function: a lui, c.lui, auipc or loaded
constant, or a constant inside a PT_LOAD of the image. The pass is path-insensitive, so it can report a value on a
path the code never takes. That gives more in-scope sites and shapes, never fewer.

The target of a site on each side is one of these:

- `static <symbol>+<offset>` when the effective address (base + immediate) is a constant;
- `GOT[<symbol>+<offset>]` for a `.got` cell, named by the address it holds;
- `(section) unnamed, the N bytes read …` for an address in no sized symbol: the bytes the access reads, as the kit's
  full-bytes acceptance compares them;
- `runtime <term>` otherwise. Every static address inside the term is named in the same way.

A site whose base holds several values lists every target. Verdict: SAME when the two sides give the same string,
else DIFFERENT. Each function's instruction offsets, mnemonics and register operands are also checked equal on the two
sides: 0 differ in every function of every pair.

Outputs, one SITE row per load / store / jalr / AMO with both targets and the verdict, one TOTAL row per function:
`failopen-CA.out` (A record), `failopen-TE.out` and `failopen-SE.out` (B record and the settled rows). Over the 7
functions the three runs share, their SITE rows are the same in all three: the same offset, shapes, targets on both
sides and verdict.

## Why d, e, f and g are 0

These are measured in the three runs (the `#` line of each function in the `.out` files), on both sides:

- (d): no in-scope base value passed through a stack slot, an FP register or a CSR. The pass models all three; the
  `d.spill`, `d.fmv` and `d.csr` controls below show it reports them.
- (e): `unreached-by-entry instructions 0` in every function, so no code is reached only through an indirect jump.
  The only indirect jump that is neither a return nor a call is PoisonShadow +0x39c `jalr zero,0(t1)`, the epilogue
  tail jump. Its base is `runtime [s8 &_ZN14__interception11real_memsetE+0x0]` on both sides, SAME.
- (f): `calls into its own region 0` in every function. No compared function calls into its own region.
- (g): no compressed parcel (see Method). The 19 lui of the records are 4-byte `lui`.

## Per function

The kit verdicts are those of strictcmp3 65688e94214a in cmpkit 86da41d3ef68 (`A/kit-rerun-4bbd3a74be89/
out/strictcmp3-cmp-86da41d3ef68.out`; `B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log`, `control` section).
`target-differ` rows are the settled rows of `cmpkit-4bbd3a74be89/settled.tsv`.

### A record, C : decode A (`failopen-CA.out`)

| function | kit verdict (cmpkit 86da41d3ef68) | sites | in scope (static / runtime) | a | b | c | d | e | f | g | h | DIFFERENT (failopen.py a4a1e11fc4e9) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `__asan::Allocator::Allocate` | DIFFERENT-target: EQUAL-mod-pcrel words, 1 target-differ (+0xdc, settled) | 92 | 44 (21 / 23) | 30 | 23 | 22 | 0 | 0 | 0 | 0 | 22 | 0 |
| `__sanitizer::CombinedAllocator<…>::Allocate` | EQUAL-mod-pcrel | 22 | 7 (2 / 5) | 3 | 5 | 5 | 0 | 0 | 0 | 0 | 2 | 0 |
| `__sanitizer::SizeClassAllocator64LocalCache<…>::Refill` | EQUAL | 12 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `__asan::PoisonShadow` | EQUAL-mod-pcrel | 67 | 35 (34 / 1) | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 35 | 0 |
| `__sanitizer::internal_mmap` | EQUAL | 1 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `__sanitizer::StackDepotPut` | EQUAL-mod-pcrel | 0 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `memset` | EQUAL | 27 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### B record, T : E (`failopen-TE.out`) and S : E (`failopen-SE.out`)

The two runs give the same counts. The kit verdicts differ in one row only: PoisonShadow is DIFFERENT-target on S : E
(+0x48c `got-tls`, settled) and EQUAL-mod-pcrel on T : E.

| function | kit verdict (cmpkit 86da41d3ef68), T : E / S : E | sites | in scope (static / runtime) | a | b | c | d | e | f | g | h | DIFFERENT (failopen.py a4a1e11fc4e9), T : E / S : E |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `__asan::Allocator::Allocate` | DIFFERENT-target (+0xdc, settled) / the same | 92 | 44 (21 / 23) | 30 | 23 | 22 | 0 | 0 | 0 | 0 | 22 | 0 / 0 |
| `__sanitizer::CombinedAllocator<…>::Allocate` | EQUAL-mod-pcrel / EQUAL-mod-pcrel | 22 | 7 (2 / 5) | 3 | 5 | 5 | 0 | 0 | 0 | 0 | 2 | 0 / 0 |
| `__sanitizer::SizeClassAllocator64LocalCache<…>::Refill` | EQUAL / EQUAL | 12 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 |
| `__asan::PoisonShadow` | EQUAL-mod-pcrel / DIFFERENT-target (+0x48c, settled) | 67 | 35 (34 / 1) | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 35 | 0 / 0 |
| `__sanitizer::internal_mmap` | EQUAL / EQUAL | 1 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 |
| `__sanitizer::StackDepotPut` | EQUAL-mod-pcrel / EQUAL-mod-pcrel | 0 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 |
| `memset` | EQUAL / EQUAL | 27 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 |
| `__sanitizer::TryMemCpy` | EQUAL-mod-pcrel / EQUAL-mod-pcrel | 28 | 0 (0 / 0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 |

### Static targets (all three runs)

These are the in-scope sites whose effective address is a constant on every path. The target is the same string on
both sides in C : A, T : E and S : E. The shapes follow each offset. Verdicts are by failopen.py a4a1e11fc4e9.

| function | target on both sides | sites (offset, shapes) | verdict |
|---|---|---|---|
| `__asan::Allocator::Allocate` | `(.rodata) unnamed, the 8 bytes read bf5d3dcd92a31802` | +0xc4 ah | SAME |
| `__asan::Allocator::Allocate` | `GOT[__asan_shadow_memory_dynamic_address+0x0]` | +0x3c4 ah, +0x4c8 ah | SAME |
| `__asan::Allocator::Allocate` | `__asan_shadow_memory_dynamic_address+0x0` | +0x3c8 h, +0x4cc h | SAME |
| `__asan::Allocator::Allocate` | `GOT[_ZN6__asan10kMidMemBegE+0x0]` | +0x4ec ah | SAME |
| `__asan::Allocator::Allocate` | `GOT[_ZN6__asan10kMidMemEndE+0x0]` | +0x4f4 ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan10kMidMemBegE+0x0` | +0x4f8 h | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan10kMidMemEndE+0x0` | +0x4fc h | SAME |
| `__asan::Allocator::Allocate` | `GOT[_ZN6__asan11kHighMemEndE+0x0]` | +0x510 ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan11kHighMemEndE+0x0` | +0x514 h | SAME |
| `__asan::Allocator::Allocate` | `GOT[_ZN6__asan28asan_flags_dont_use_directlyE+0x0]` | +0x52c ah, +0x6b0 ah, +0x778 ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan28asan_flags_dont_use_directlyE+0x55` | +0x530 ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan28asan_flags_dont_use_directlyE+0x2c` | +0x6b4 ah | SAME |
| `__asan::Allocator::Allocate` | `GOT[_ZN14__interception11real_memsetE+0x0]` | +0x6cc ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN14__interception11real_memsetE+0x0` | +0x6d0 h | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan28asan_flags_dont_use_directlyE+0x34` | +0x6d4 ah | SAME |
| `__asan::Allocator::Allocate` | `(.rodata) unnamed, the 8 bytes read b9966eccb9966ecc` | +0x718 ah | SAME |
| `__asan::Allocator::Allocate` | `_ZN6__asan28asan_flags_dont_use_directlyE+0x4e` | +0x77c ah | SAME |
| `__sanitizer::CombinedAllocator<…>::Allocate` | `GOT[_ZN11__sanitizer17SanitizerToolNameE+0x0]` | +0x30 ah | SAME |
| `__sanitizer::CombinedAllocator<…>::Allocate` | `_ZN11__sanitizer17SanitizerToolNameE+0x0` | +0x34 h | SAME |
| `__asan::PoisonShadow` | `_ZN6__asanL17can_poison_memoryE+0x0` | +0x28 ah | SAME |
| `__asan::PoisonShadow` | `GOT[__asan_shadow_memory_dynamic_address+0x0]` | +0x40 ah | SAME |
| `__asan::PoisonShadow` | `__asan_shadow_memory_dynamic_address+0x0` | +0x44 h | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN6__asan10kMidMemBegE+0x0]` | +0x60 ah, +0x248 ah | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN6__asan10kMidMemEndE+0x0]` | +0x68 ah, +0x250 ah | SAME |
| `__asan::PoisonShadow` | `_ZN6__asan10kMidMemBegE+0x0` | +0x6c h, +0x254 h | SAME |
| `__asan::PoisonShadow` | `_ZN6__asan10kMidMemEndE+0x0` | +0x70 h, +0x258 h | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN6__asan11kHighMemEndE+0x0]` | +0x84 ah, +0x26c ah | SAME |
| `__asan::PoisonShadow` | `_ZN6__asan11kHighMemEndE+0x0` | +0x88 h, +0x270 h | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN6__asan28asan_flags_dont_use_directlyE+0x0]` | +0xa0 ah, +0x178 ah, +0x3a4 ah | SAME |
| `__asan::PoisonShadow` | `_ZN6__asan28asan_flags_dont_use_directlyE+0x4e` | +0xa4 ah, +0x17c ah, +0x3a8 ah | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN14__interception11real_memsetE+0x0]` | +0x288 ah | SAME |
| `__asan::PoisonShadow` | `_ZN14__interception11real_memsetE+0x0` | +0x28c h, +0x30c h, +0x320 h, +0x370 h | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN11__sanitizer21common_flags_dont_useE+0x0]` | +0x2b0 ah | SAME |
| `__asan::PoisonShadow` | `_ZN11__sanitizer21common_flags_dont_useE+0x78` | +0x2b4 ah | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN11__sanitizer14PageSizeCachedE+0x0]` | +0x2c0 ah | SAME |
| `__asan::PoisonShadow` | `_ZN11__sanitizer14PageSizeCachedE+0x0` | +0x2c4 h, +0x2dc h | SAME |
| `__asan::PoisonShadow` | `GOT[0x1]` (the TLS cell of the settled row: it holds 0x1 on both sides) | +0x48c ah | SAME |
| `__asan::PoisonShadow` | `GOT[_ZN11__sanitizer25sealed_report_in_progressE+0x0]` | +0x498 ah | SAME |
| `__asan::PoisonShadow` | `_ZN11__sanitizer25sealed_report_in_progressE+0x0` | +0x49c h | SAME |

Shape (a), the one the registry measured as "5 Allocator::Allocate rows per asan image": 15 sites of Allocate have a
static target and a non-zero immediate (+0xc4 … +0x77c above, the `a` rows), 36 over the 7 functions. Each is the same
symbol + offset, or the same bytes read, on both sides.

### Runtime-pointer sites in scope

There are 29 such sites (Allocate 23, CombinedAllocator::Allocate 5, PoisonShadow 1). Each one is the same term on
both sides, so each is SAME (failopen.py a4a1e11fc4e9). Every static address inside a term has the same name on both
sides. The terms, in the `.out` files, are of four kinds:

- Allocate +0xe4 `lbu a1,0(a1)`, the settled +0xdc table read: `srl(mul(0x218a392cd3d5dbf, and(x, -x)), 0x3a)` + the
  unnamed `.rodata` table, whose 64 bytes `00010207…3b3a` are the same on both sides (KIT-RERUN.md 4.2).
- The other 20 Allocate sites (+0x16c … +0x704, but not +0x548): the allocator, chunk and per-class pointers
  (`in:a0`, chunk and stack pointers, widened at the loop heads). The lui masks and bounds of the hand traces
  (0x10000, 0xfc01, 0xfffffffffff8, 0x10001) flow into them on some path. They are the same numbers on both sides and
  in no section.
- Allocate +0x548 `sb a1,0(a0)`, the shadow-byte store: `[s8 &__asan_shadow_memory_dynamic_address+0x0]` + (a masked
  pointer >> 3).
- CombinedAllocator::Allocate +0x1ac / +0x1c0 / +0x1c8 / +0x1d4 / +0x2b4: `in:a1` (the cache argument) +
  class * 0x50.

PoisonShadow +0x160 `ld t2,0(t0)` is `static _ZN6__asan11kHighMemEndE+0x0` on one path and a register clobbered by the
call at +0x484 on another path, on both sides.

## The settled rows

The pass checks the code around the settled rows. It does not settle them again: the settlements in
`cmpkit-4bbd3a74be89/settled.tsv` still apply.

- Allocate +0xdc (T : E, S : E) is the `addi` that forms the table address. It is not a base. Its use is the site
  +0xe4 above, SAME. The constant K that indexes the table is the site +0xc4: `(.rodata) unnamed, the 8 bytes read
  bf5d3dcd92a31802` on both sides, SAME.
- PoisonShadow +0x48c (S : E) is the site `ld t1,1472(t1)`: `GOT[0x1]` on both sides, SAME. The kit's difference was
  only the naming of a value in PT_TLS (the symtwin has no STT_TLS symbol). The pass names the cell by the value it
  holds, 0x1 on both sides.

## The A record: its author's trace

The A record's author answered the same eight shapes in a reviewed trace of the A record (the original record, of
which `A/` here is a token copy):

- commit `ec63ec6c4edeb4e7ee2360980dbd3f1070504c41`;
- `proofs/libreac/fuzz_decode/provenance/alloc-reloc/A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md`;
- sha256 `0a84f50288235502c4c3173fb276d808f802796accb9d47fec960580ec83a119`, section 9.

That trace is not copied into this tree. `A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md` here is the earlier version
(sha256 `358c174f6bc4`). It covers all 7 functions of the A record. Per shape:

| shape | the author's trace, section 9 | this pass on the same 7 pairs |
|---|---|---|
| (a) | covered by its tool, and by hand for every static base: 36 sites with a non-zero immediate, 15 in Allocate, 0 differ | 36 and 15, the same counts; 0 DIFFERENT |
| (b), (c) | covered by its tool | b 28, c 27; 0 DIFFERENT |
| (d) | spill and FP covered; CSR not modelled, 0 CSR instructions measured | modelled (spill, FP, CSR); 0 sites |
| (e) | by measurement: one `jr t1` (PoisonShadow +0x39c, a tail jump), 0 unreached instructions | the same jump, 0 unreached instructions |
| (f) | partial: not traced into callee bodies | in-region callees followed: 0 calls into a function's own region, so no such callee exists |
| (g) | 0 compressed instructions | 0 compressed parcels, read through the plain-binary listing |
| (h) | covered by its may-static check: 61 static base sites, 0 differ | 58 sites with a static target (57 on every path, PoisonShadow +0x160 on one path), 0 DIFFERENT |

This pass checks the one shape the author's trace leaves partial, (f), and finds no site of it. The site counts differ
only by these 5 sites, and each one is SAME both ways:

- Allocate +0x6dc and PoisonShadow +0x318 / +0x330 / +0x39c, the calls through REAL(memset). The author's evaluator
  reads the initial `.data` word of `_ZN14__interception11real_memsetE` from the image and names `memset+0x0`. This
  pass treats a load from writable memory as a runtime value, `runtime [s8 &_ZN14__interception11real_memsetE+0x0]`,
  on both sides.
- PoisonShadow +0x160. This pass reports it with a static target on one path. The author's evaluator drops a register
  that holds two values.

## The planted controls

`plant.py` (sha256 `21fe1a423b92`) writes copies of the donor twin (side 1) and the decode A twin (side 2). Each copy
holds one synthetic sequence at memset+0. Variant `diff` aims side 1 and side 2 at different symbols, so the pass must
report the planted site DIFFERENT, with its shape. Variant `same` aims both sides at the same symbol + offset (at
different absolute addresses), so the site must be SAME. `controls.out` holds, for each control, the planted words as
objdump lists them, the planted site's SITE row and a CHECK line. Result: `controls PASS 28 of 28` (failopen.py
a4a1e11fc4e9).

| control | shape | planted sequence | `diff` targets (side 1 / side 2) |
|---|---|---|---|
| a | a | `lui; addi` V; `ld a1,8(a0)` | V = `oft_aligned_copy.empty+0x18` on BOTH sides; V+8 = `_ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE+0x0` / `__odr_asan_gen_REAC_MODE_44K1+0x0`. Only V + imm differs, which the kit never forms. |
| b | b | `lui; addiw; addi 0x100; ld` | `asan_flags+0x10` / `common_flags+0x10` |
| c.ori, c.xori, c.slli | c | `lui; addi; ori` (or `xori 0x40`, or `slli 3`); `ld` | the same |
| d.spill | d | `lui; addi; addi sp,-16; sd a0,8(sp); li a0,0; ld a1,8(sp); ld a2,0(a1)` | the same |
| d.fmv | d | `…; fmv.d.x ft0,a0; li a0,0; fmv.x.d a1,ft0; ld a2,0(a1)` | the same |
| d.csr | d | `…; csrrw zero,sscratch,a0; li a0,0; csrrs a1,sscratch,zero; ld a2,0(a1)` | the same |
| e | e | `jalr zero,0(a5)`; arm 1 `lui; addi`; arm 2 `ld` (reached by fall-through) | the same |
| f | f | `lui; addi; jal ra,L; j over`; `L: ld a1,0(a0); ret` | the same |
| g | g | `c.lui a0,0x11; c.nop; slli 1; addi; ld` (objdump lists the parcels as `.insn` in the ELF) | `errmsgidx+0x0` / `__c_locale+0x0` |
| h.auipc | h | `auipc; addi; ld` | `asan_flags+0x10` / `common_flags+0x10` |
| h.ldk | h | `auipc; ld` of the `.got` cell that holds the target; `ld` | `asan_flags+0x0` / `common_flags+0x0` |
| h.li | h | `addi a0,zero,K; slli 11; ld a1,lo(a0)` (no lui, no auipc) | `asan_flags+0x10` / `common_flags+0x10` |

`asan_flags` is `_ZN6__asan28asan_flags_dont_use_directlyE` and `common_flags` is
`_ZN11__sanitizer21common_flags_dont_useE`. All 14 `diff` controls give DIFFERENT with their shape, and all 14 `same`
controls give SAME. The unplanted memset of the same pair has 0 in-scope sites (`failopen-CA.out`).

## Verdict

cmpkit 86da41d3ef68 stays of record. For the A record, the B record, the settled rows and the 86da41d3ef68 scans
record, every load / store / jalr / AMO site of every compared function was checked on both sides for shapes (a)-(h)
by failopen.py a4a1e11fc4e9. The shapes present are a, b, c and h. d, e, f and g have no site. DIFFERENT is 0
everywhere, so no EQUAL verdict of these records is open to the fail-opens, and no verdict changes.
