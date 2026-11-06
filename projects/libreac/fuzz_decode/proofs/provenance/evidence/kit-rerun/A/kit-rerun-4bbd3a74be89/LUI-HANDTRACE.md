# libreac/fuzz_decode, image A alloc-reloc: every lui of the 7 compared functions, hand-traced through ALL ALU ops

Why: the KIT LIMIT registered by WORKER at BRANCH 6d8ff128a01 (AGENT TIME) and its addendum at
797c750bbb0 (TIME). strictcmp3 65688e94214a's rule 8, and therefore luiscan 9ae61e4a0e01, carry a lui value
forward through addi / load / store / jalr only, and call a value that goes through logical ops `lui-const
(dataflow)` and prints EQUAL. So `memfed 0` is not proof, and SCANS-86da41d3ef68.md beside this file, which reports
`exposure 0` for all 7 pairs, needs this hand trace under it. Provenance only: no .v file, no theorem, no function
proved here.

This is the THIRD version of the file. The fresh review of AGENT TIME REJECTED the second one: the 18-row
result reproduced and the reviewer's own independent check agreed with it, but three method claims were false
("fail-closed", "never drops a use", "`val=?` is a measurement") and two base attributions in section 4 were wrong.
All five are corrected here, the reviewer's three plants are added, and the verdict now rests on an independent
may-static check, not on the trace's value evaluator.

Record covered: this directory (KIT-RERUN.md, DATE), 7 function pairs, donor twin
`cgif_file_fuzzer.asan-ubsan` ce511d541cda (pin 1c29845fe605) against decode A twin `fuzz_decode.asan` 4cb0a852e826
(pin 5973b76807d8).

## 1. Method, and exactly what it does and does not cover

`luitrace.py` beside this file (python3, pyelftools 0.33, capstone 5.0.7; read-only, no image is written). For every
`lui` of every one of the 7 functions, in BOTH images, it runs a MAY forward dataflow over the function's whole
control-flow graph — both edges of every conditional branch, every in-function `j` target, and the FALL-THROUGH of
`jal` and of `jalr` (a call returns), loops iterated to a fixpoint — and carries the lui's destination register
into every register the value reaches, transitively, until that register is written again.

WHAT CARRIES THE VALUE. The trace knows the operand roles of one family only: rd first, every other register
operand a source. Everything else is REFUSED, not given a default rule: an op outside that family is reported
`UNKNOWN-OP` and every register it names is tainted. The ops present in these functions, and their handling, are
listed per mnemonic in out/luitrace-ops.out (57 mnemonics, 0 refused).

OPS FOLLOWED: add addi addiw addw sub subw mul mulh mulhu mulhsu mulw div divu divw divuw rem remu remw remuw and
andi or ori xor xori sll slli sllw slliw srl srli srlw srliw sra srai sraw sraiw slt slti sltu sltiu mv neg negw
not seqz snez sltz sgtz sext.b sext.h sext.w zext.b zext.h zext.w sh1add sh2add sh3add (and the .uw forms) add.uw
slli.uw min max minu maxu andn orn xnor rol ror rori rev8 orc.b clz ctz cpop, every `c.`-compressed form of those,
and EVERY floating-point op (`fmv.d.x`, `fmv.x.d`, `fmv.w.x`, `fcvt.*`, ...), because a value can leave the integer
file through an FP register and come back. FP registers ft0-ft11 / fs0-fs11 / fa0-fa7 / f0-f31 are tracked like
integer registers, so `fld ft0, 0(a0)` writes ft0 and no longer clears the taint of its base a0.

REPORTED USES, per lui:

- `MEMBASE` — a tainted register used as the base of a load / store / AMO / LR / SC,
- `JUMPBASE` — a tainted register used as the base of a `jalr` / `jr`,
- `CALLARG` — a tainted value live in a0-a7 at a `jal` / `jalr`,
- `TAILARG` — a tainted value in a0-a7 at a tail `j` out of the function or at a `jr`,
- `RETVAL` — a tainted a0 / a1 at `ret`, the value the function returns,
- `RELOAD` — a load that reads back a slot a tainted value was spilled to (slots `sd/sw <reg>, imm(base)` are
  tracked by base+imm; a tainted store through a pointer that is not sp / s0 makes every later load a RELOAD),
- `STOREDATA`, `BRANCH`, `ALU` — every other use.

Class **(a)** = no MEMBASE, JUMPBASE, CALLARG, TAILARG or RETVAL use on any path. Class **(b)** = at least one.

WHAT IT DOES NOT DO. The analysis is path-insensitive: it keeps a value live on paths the code never takes, which
over-reports uses, and it is a MAY analysis over registers and tracked stack slots only — it does not model heap
memory, callee behaviour, or the contents of a slot across a call. It is therefore NOT a proof that nothing escapes;
it is a measurement whose only one-sided direction is that it over-reports. The ADDRESS question is not answered by
the trace's value column at all (section 4): `val=?` means the evaluator could not fold the value, not that the base
is a runtime pointer.

MAY-STATIC CHECK (the address question). out/luitrace-maystatic.out, `luitrace.py static`, is the fresh reviewer's
`static_base.py` with the memory extension of `static_mem.py` (REVIEW_DIR/, AGENT TIME and TIME), their
logic copied into luitrace.py and cited there. Independent of the trace's value evaluator, it asks per load /
store / AMO / `jalr` site whether the base register CAN, on some path from function entry, hold a value built from
constants only (lui / auipc / zero / immediates, through ANY op), with no call return value, no entry argument and
no sp / gp / tp in it. OR over paths, fixpoint, every CFG edge including the fall-through of jal and jalr.

- WHAT IT MODELS: integer registers; FLOATING-POINT registers, kept across every CFG join (the join unions the
  whole state, not a fixed register list); and memory slots keyed by (base register, immediate) — a store of a
  may-static value makes the slot may-static, a load from the same key reads it back, a write of the base register
  forgets its slots. So a value that is spilled and reloaded, or that crosses a join in an FP register, stays
  may-static (the reviewer's `spill` and `fpjoin` plants, §6).
- WHAT IT DOES NOT MODEL: path conditions (a MAY analysis: it over-reports static-possible, the safe direction
  here), and memory other than those slots — a value stored through a pointer and read back under a different
  (base, imm) key is not followed.
- So a site this check calls `runtime` is runtime UNDER THIS MODEL. This file does not claim more than that, and
  in particular does not claim that no possible dataflow can make it static.

Commands (the kit copy is the one SCANS-86da41d3ef68.md checked, sha256(SHA256SUMS)[:12] = 86da41d3ef68):

```
FNS=$(awk -F'\t' '$2=="C:A" && $1!="fn"{printf "%s%s",(NR>5?",":""),$1}' out/run-strictcmp2.out | sed 's/^,//')
python3 luitrace.py pair $C $A "$FNS"                  > out/luitrace-pair-86da41d3ef68.out   # the table + both traces
python3 luitrace.py static $C $A "$FNS"                > out/luitrace-maystatic.out           # the address question
python3 luitrace.py uses $C $A "$FNS"                  > out/luitrace-uses.out                # every non-base use, §7
python3 luitrace.py deadarg $C $A "<callee>:<reg>,..." > out/luitrace-deadarg.out             # class (e), §7
python3 luitrace.py ops $C $A "$FNS"                   > out/luitrace-ops.out                 # per-mnemonic handling
python3 <kit>/strictcmp3.py cmp "$FNS" C=$C A=$A C:A   > out/strictcmp3-cmp-86da41d3ef68.out  # the kit's own compare
python3 plant_controls.py <plant> $A <Allocate> <off> planted-<plant>.asan                    # the 7 controls, §6
```

out/luitrace-words.out, out/luitrace-bases.out and out/luitrace-windows.out hold the supporting measurements of
sections 4-5 (word compare, base-register definitions, disassembly windows), made with the same loader.

DEADARG, what it really does (AGENT's third review asked for this in writing). `luitrace.py deadarg` walks the
callee from its entry and asks whether the register is READ before it is written. A path ends at a write of the
register, at a `ret`, or at a direct `jal` — there it recurses into the callee and, if that returns `dead`, uses
the ABI to drop the register when it is caller-saved. A `jalr` / `jr` gives `unknown`. The two gaps the reviewer
found are now CLOSED, not merely stated: a tail `j` out of the function is followed into the target function when
it resolves to a symbol (nothing is clobbered by a tail call) and gives `unknown` otherwise; and an `ecall` /
`ebreak` gives `unknown`, because a syscall may read a0-a7. Closing them changed one result and needed one hand
step, both recorded in section 8.

Count check: 18 lui in each image (Allocator::Allocate 12, CombinedAllocator::Allocate 5, memset 1; the other four
functions have none), exactly luiscan's `luis 18` per image. 36 rows, 18 pairs.

## 2. The 18 lui, both images

`chain` = instructions of the trace (the lui and every reported use); `=` = of those, byte-identical in the two
images; `jal+ld` = the rest, all of them pc-relative words that differ in the immediate only (section 4).

| # | function | +off | reg | value X | value Y | equal | class | use kinds | uses | chain | = | jal+ld |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Allocator::Allocate | +0x120 | a0 | 0x1000 | 0x1000 | yes | **a** | ALU,BRANCH | 2 | 3 | 3 | 0+0 |
| 2 | Allocator::Allocate | +0x134 | a0 | 0x4000 | 0x4000 | yes | **a** | ALU,BRANCH | 2 | 3 | 3 | 0+0 |
| 3 | Allocator::Allocate | +0x148 | a0 | 0x8000 | 0x8000 | yes | **a** | ALU,BRANCH | 2 | 3 | 3 | 0+0 |
| 4 | Allocator::Allocate | +0x15c | a0 | 0x10000 | 0x10000 | yes | **b** | ALU,BRANCH,CALLARG,JUMPBASE,MEMBASE,RELOAD,RETVAL,STOREDATA | 427 | 340 | 307 | 22+11 |
| 5 | Allocator::Allocate | +0x174 | s4 | 0x10000 | 0x10000 | yes | **b** | ALU,BRANCH,CALLARG,JUMPBASE,MEMBASE,RELOAD,RETVAL,STOREDATA | 431 | 342 | 309 | 22+11 |
| 6 | Allocator::Allocate | +0x498 | a0 | 0xfffffffffff80000 | 0xfffffffffff80000 | yes | **b** | ALU,BRANCH,CALLARG,MEMBASE | 49 | 47 | 41 | 6+0 |
| 7 | Allocator::Allocate | +0x564 | a4 | 0x10000 | 0x10000 | yes | **b** | ALU,BRANCH,CALLARG | 4 | 5 | 4 | 1+0 |
| 8 | Allocator::Allocate | +0x5b8 | a2 | 0x55555000 | 0x55555000 | yes | **b** | ALU,CALLARG,MEMBASE | 33 | 33 | 32 | 1+0 |
| 9 | Allocator::Allocate | +0x5bc | a3 | 0x33333000 | 0x33333000 | yes | **b** | ALU,CALLARG,MEMBASE | 30 | 30 | 29 | 1+0 |
| 10 | Allocator::Allocate | +0x5c0 | a4 | 0x0f0f1000 | 0x0f0f1000 | yes | **b** | ALU,CALLARG,MEMBASE | 25 | 25 | 24 | 1+0 |
| 11 | Allocator::Allocate | +0x5c4 | a5 | 0x01010000 | 0x01010000 | yes | **b** | ALU,CALLARG,MEMBASE | 26 | 24 | 23 | 1+0 |
| 12 | Allocator::Allocate | +0x8b4 | a0 | 0xfffffffffff80000 | 0xfffffffffff80000 | yes | **b** | ALU,CALLARG | 4 | 5 | 4 | 1+0 |
| 13 | CombinedAllocator::Allocate | +0x74 | a5 | 0x10000 | 0x10000 | yes | **b** | BRANCH,CALLARG | 7 | 8 | 5 | 3+0 |
| 14 | CombinedAllocator::Allocate | +0xbc | a5 | 0x55555000 | 0x55555000 | yes | **b** | ALU,BRANCH,CALLARG,MEMBASE,RETVAL | 62 | 50 | 47 | 3+0 |
| 15 | CombinedAllocator::Allocate | +0xc0 | a6 | 0x33333000 | 0x33333000 | yes | **b** | ALU,BRANCH,CALLARG,MEMBASE,RETVAL | 59 | 47 | 44 | 3+0 |
| 16 | CombinedAllocator::Allocate | +0xc4 | a7 | 0x0f0f1000 | 0x0f0f1000 | yes | **b** | ALU,BRANCH,CALLARG,MEMBASE,RETVAL | 54 | 42 | 39 | 3+0 |
| 17 | CombinedAllocator::Allocate | +0xc8 | t0 | 0x01010000 | 0x01010000 | yes | **b** | ALU,BRANCH,CALLARG,MEMBASE,RETVAL | 53 | 41 | 38 | 3+0 |
| 18 | memset | +0x48 | a1 | 0x10101000 | 0x10101000 | yes | **a** | ALU,STOREDATA | 24 | 25 | 25 | 0+0 |

TOTAL (out/luitrace-pair-86da41d3ef68.out): `lui rows 18, class a 4, class b 14, unmatched none`. Every lui sits at
the SAME offset in both images, in the same register, with the SAME value, and both traces are structurally
identical (same offsets, same registers, same use kinds; the only textual difference is the target of a `jal`).

The lui values the kit's own decoder forms (strictcmp3 `lui_scan`, the lui + its paired `addi/addiw` where there is
one) are identical in the two images as well: Allocate 0xf81, 0x3f01, 0x7e01, 0xfc01, 0x10000, 0xffff, 0x10001,
0xfffffffffff80000 (x2), 0x55555555, 0x33333333, 0x0f0f0f0f, 0x01010101; CombinedAllocator::Allocate 0x10000,
0x55555555, 0x33333333, 0x0f0f0f0f, 0x01010101; memset 0x10101000. `memfed` is 0 for all of them and `unmeasured`
is 0 (no 2-byte parcel in any of the three functions).

## 3. The four class (a) rows: the value never reaches an address, a call, a tail call or a return

- **+0x120 / +0x134 / +0x148** (`lui a0,0x1000` / `0x4000` / `0x8000`): each is followed by one `addiw a0,a0,-0x7f` /
  `-0xff` / `-0x1ff` giving 0xf81 / 0x3f01 / 0x7e01, and that value's only other use is the `bgeu s5,a0` three words
  later; the next `lui`, or the `lh a0` at +0x16c, then overwrites a0, with no call in between.
- **memset +0x48** (`lui a1,0x10101`, with `slli a4,a1,4` and `addi a3,a4,0x100` it builds the 0x01010101 /
  0x0101010101010101 byte-splat): 24 uses, every one ALU or STOREDATA — the splat is the DATA of `sw a2,0(a1)`,
  `sd a2,0x18(a1)` and the rest; a1 is overwritten at +0x58 and a3 at +0x6c / +0xd4, and a0 at `ret` is untainted.

All four stay class (a) under every rule added in this version (FP moves, spill/reload, jalr fall-through, tail and
return reporting), which is also what the fresh reviewer measured independently.

## 4. The class (b) rows: what the value becomes, and why no address of this record depends on it

1. **No value lies in an allocated section of either image.** strictcmp3's own `insec` is false for every one of the
   18 values in both images (luiscan `insec 0`, SCANS-86da41d3ef68.md section 4). The only value inside a PT_LOAD is
   0x10000 (`inload`, rows 4, 5, 7, 13): the ELF header region [0x10000,0x10040) of each image, which belongs to no
   section and carries no symbol. 0x10000 is used as the size-class granularity (`addiw s8,s4,-1` -> mask 0xffff at
   +0x178; `addiw a2,s4,1` -> 0x10001 at +0x1e4; `bltu s3,a4` at +0x580; `bltu a5,a3` / `bltu a5,a4` at
   CombinedAllocator::Allocate +0x78 / +0x7c), never as a pointer.
2. **No lui-derived base can be static under the may-static model.** out/luitrace-maystatic.out (the model of
   section 1, now with memory slots and FP registers through joins): 215 base sites per image, of which 28 MAY be
   static — all of them the `auipc`+`ld` GOT-style loads (+0xc4, +0x3c4, +0x4c8, +0x4ec, +0x4f4, +0x510, +0x52c,
   +0x6b0, +0x6cc, +0x718, +0x778 and the rest), identical in the two images and not lui-derived. The trace's 226
   base uses lie at 42 distinct (function, offset) sites; the script's last line reports the INTERSECTION of those
   42 sites with the may-static sites as EMPTY in both images. That, and not the trace's `val` column, is what
   says a lui-derived base is a runtime pointer — under the model of section 1, not beyond it.
3. **Which runtime pointer, per site** (out/luitrace-bases.out, out/luitrace-windows.out; the two attributions the
   reviewer corrected are marked):
   - `s10` (Allocate +0x16c, +0x188, +0x21c, +0x25c, +0x308) = `addi s10,s6,0x7ff` at +0x8c, with s6 the allocator
     object pointer (`this`) the function was called on;
   - `a0` at +0x548 (`sb a1,0(a0)`, the shadow byte write) = the pointer loaded at +0x4c4/+0x4c8/+0x4cc
     (`auipc a0,0x6c; ld a0,0x7f4(a0); ld a0,0(a0)`) plus `a2 = s6 >> 3` (+0x534/+0x538);
   - `a0` at +0x698 / +0x6a0 (the per-class counter) = **the return value of `GetCurrentThreadStats()`**, the call
     at +0x54c, through +0x580 and +0x59c, then `+0x70` (+0x5a0) and `+ (class << 3)` (+0x690/+0x694). (CORRECTED:
     the previous version said "that same loaded pointer"; it is the call's return value, and the only path to
     +0x5a0 is +0x54c -> +0x580 -> +0x59c.)
   - `a2` at +0x328 / +0x33c (`lr.w.aq` / `sc.w`), and the bases at +0x368, +0x3dc, +0x418 = **offsets from s6, the
     `this` argument**: `addi a0,s6,0x3d8` at +0x318 then `andi a2,a0,-4` at +0x320; `sb zero,0x3d8(s6)`;
     `ld a0,0x20(s6)`; `ld a0,0x40(s6)`. (CORRECTED: the previous version grouped these under "the call at
     +0x29c".)
   - `s4` (Allocate +0x2c8..+0x2e8) = the CombinedAllocator::Allocate return value in s2 plus an offset, then
     masked; `s5` = `addi s5,s4,-0x10` (+0x2f0);
   - `s1` at CombinedAllocator::Allocate +0x1ac / +0x1c0 / +0x1c8 / +0x2b4, and `a4` at +0x1d4 = `add s1,a1,s1` at
     +0x1a8, with a1 the `SizeClassAllocator64LocalCache*` argument and `s1 = class_id * 0x50` (+0x1a0/+0x1a4).
   So in every (b) row the lui value is a MASK, a BOUND or an INDEX: the ctz / popcount constants 0x55555555,
   0x33333333, 0x0f0f0f0f, 0x01010101 (rows 8-11, 14-17), the alignment masks 0xffff (rows 4, 5) and
   0x0000fffffffffff8 / 0x0000ffffffffffff (rows 6, 12), and the bounds 0x10000 / 0x10001 (rows 7, 13). The CALLARG
   and RETVAL uses carry these masked sizes and class ids, not addresses.
4. **The effective address is the same expression in both images.** Over all 854 instruction words of the three
   lui-carrying functions (out/luitrace-words.out), 757 are byte-identical and 97 differ ONLY in the immediate
   field (auipc 13, addi 29, ld 12, jal 43 — opcode and register operands identical in every one, `other none`).
   Not one `lui` and not one ALU word of any of the 36 traces is among the 97: inside the traces the differing
   words are 71 `jal` call words and 22 `ld` lo12 words of `auipc`+`ld` pairs, and strictcmp3's target pass
   (section 5) resolves every one of them to the same symbol + offset on both sides. No (b) row has a statically
   computable address, and none whose address can differ between the two layouts.

## 5. The kit's own compare on 86da41d3ef68, run as the cross-check

`strictcmp3.py cmp` on the same 7 pairs (out/strictcmp3-cmp-86da41d3ef68.out):

| function | verdict | pcrel | real | unmeasured | target-differ |
|---|---|---|---|---|---|
| __asan::Allocator::Allocate | DIFFERENT-target (words-only EQUAL-mod-pcrel) | 81 | 0 | 0 | 1: +0xdc `(.rodata)` data-differs |
| __sanitizer::CombinedAllocator<…>::Allocate | EQUAL-mod-pcrel | 16 | 0 | 0 | 0 |
| __sanitizer::SizeClassAllocator64LocalCache<…>::Refill | EQUAL | 0 | 0 | 0 | 0 |
| __asan::PoisonShadow | EQUAL-mod-pcrel | 61 | 0 | 0 | 0 |
| __sanitizer::internal_mmap | EQUAL | 0 | 0 | 0 | 0 |
| __sanitizer::StackDepotPut | EQUAL-mod-pcrel | 2 | 0 | 0 | 0 |
| memset | EQUAL | 0 | 0 | 0 | 0 |

Same word counts as the record's strictcmp2 run (KIT-RERUN.md 4.1), 0 real and 0 unmeasured words everywhere, and
exactly one differing target in the 7 pairs: Allocator::Allocate +0xdc, the kit's OPEN LIMIT 5 class (an unnamed
.rodata target read through a bounded index, compared on its whole region), which KIT-RERUN.md 4.2 settles by hand
with its own 64-byte measurement and an independent audit. That row is built by `auipc`/`addi`, not by a `lui`.

## 6. The seven planted controls

Each plant goes into its own COPY of the decode A twin (`plant_controls.py`; no pinned image is touched), over
Allocator::Allocate. PASS = the planted load base is reported by the trace (MEMBASE) AND by the may-static check.
Full runs, including the unplanted baseline, in out/plant-controls.out.

| plant | shape | trace | may-static | verdict |
|---|---|---|---|---|
| static-base (TIME) | `lui 0xfff80; srli 16; auipc t2,0; addi t2,t2,0x10; and t3,t2,t1; ld t4,0(t3)` | MEMBASE +0x574, val=ea=0x317c0, .text, …Allocate+0x574 | yes | PASS |
| x5-logical (TIME) | `lui 0x40; ori 0x100; xor t2,t1,zero; andi t3,t2,-8; ld t4,0(t3)` — logical only, the lui value IS the base | MEMBASE +0x570, val=ea=0x40100, .text, __asan_after_dynamic_init+0x2bc | yes | PASS |
| srai (TIME) | the static-base plant with `srli` -> `srai`, an op the value evaluator does not fold | MEMBASE +0x574, **val=?** | yes | PASS |
| jalr (TIME) | `lui s11,0x40; jalr a3; ld t4,0(s11)` at +0x6d8 — the load is reached only through the jalr fall-through | MEMBASE +0x6e0, val=ea=0x40000, .text, __asan_after_dynamic_init+0x1bc | yes | PASS |
| fp (TIME) | `lui t1,0x40; fmv.d.x ft0,t1; fmv.x.d t2,ft0; ld t4,0(t2)` — the value leaves the integer file | MEMBASE +0x56c, **val=?** | yes | PASS |
| spill (TIME) | `lui t1,0x40; sd t1,0(sp); ld t2,0(sp); ld t4,0(t2)` — spilled and reloaded, then the base | MEMBASE +0x56c, **val=?** | yes | PASS |
| fpjoin (TIME) | `lui t1,0x40; fmv.d.x ft0,t1; bnez a0,+4; fmv.x.d t2,ft0; ld t4,0(t2)` — an FP value across a join | MEMBASE +0x570, **val=?** | yes | PASS |

The srai, fp, spill and fpjoin rows are why the verdict of section 4 rests on the may-static check and not on the
trace's `val`: all four print `val=?`, the same text a runtime base prints. The last two also broke the FIRST
version of that check (the reviewer's `static_base.py`, which counted every load as runtime and dropped FP
registers at a join); they are caught now that the check tracks (base, imm) slots and unions the whole state at a
join. On the version of this file rejected at TIME, the jalr and fp plants printed `class a, none`.

Unplanted baseline (out/plant-controls.out, last block): the 12 lui rows of Allocator::Allocate, the decode A side
of out/luitrace-pair-86da41d3ef68.out, with no may-static base anywhere. (Each plant overwrites one baseline lui,
so every run shows 12 rows.)

Defects the controls and the reviews exposed, all fail-OPEN, all fixed here: `lui` / `auipc` not sign-extended
from bit 31; `jr` treated as a write instead of an indirect jump; the `zero` register without a value; `jalr`
without its fall-through edge; FP moves dropping the taint and `fld` clearing its base register; `ret`, tail calls
and stack spill/reload never reported; a default rule for ops the script does not know, replaced by UNKNOWN-OP
refusal; and, in the may-static check, every load counted as runtime and FP registers dropped at every join.

## 7. Settlement class of every lui-derived use that is NOT a load / store / jump base

The owner's addendum of AGENT TIME. `luitrace.py uses` lists every non-base use with the may-static verdict
for the value it carries, the callee a call resolves to, its class and its citation: out/luitrace-uses.out, 408
rows (204 per image, the same offsets on both sides). PINNED SOURCE: the compiler-rt of these binaries is
llvm-project llvmorg-20.1.8 (DEPOT_NAME/depot/README.md:9-13); the depot's local copy
DEPOT_DIR/src-llvm-20.1.8/ holds 11 of its files, and asan_allocator.cpp there is
byte-identical (sha256 30b715c3a51877995f0d5be8a169d5c8beb0111e87556c2d587cab52a5dec15a) to the file fetched from
the llvmorg-20.1.8 tag, which is how the other headers cited below were read. Line numbers are that tag's.

| class | rows | what it is |
|---|---|---|
| (iii-v) no constant value under the model | 332 | NARROWED after AGENT's third review, and an image-address check added — BOTH, not one of the two. The class now claims only what it measures: no path gives the register a value built from constants only (out/luitrace-maystatic.out). It no longer claims 'not an image address': that question is answered by a second column, IMG, the reviewer's REVIEW_DIR3/imgaddr.py copied into `luitrace.py` as `imgaddr_run()` and cited there, which marks a register that may hold a value derived from an auipc result or from a GOT-style load. A row is (iii-v) only when may-static is `no` AND IMG is `no` |
| STORE: an integer-typed field | 2 | owner ruling AGENT TIME (2): NOT a new class. `sd a0, 0(s2)` at Allocator::Allocate +0x724 stores kAllocBegMagic into `atomic_uintptr_t magic` of `class LargeChunkHeader` (asan_allocator.cpp:168-171) — a field DECLARED as an integer, not a pointer; the constant is asan_allocator.cpp:169-170, stored at :184. The constant-pool words at +0x714 / +0x718, which strictcmp3 compares byte-equal (`full+0x718[0x10328\|0x10330]=8` in out/strictcmp3-cmp-86da41d3ef68.out), are the evidence that both images store the same constant. The class is keyed on the function AND the offset |
| (iii) runtime pointer returned | 4 | the two `ret` rows per image: §8 item (2) |
| OPEN | 0 | nothing is open after §8; the totals of this table are exactly out/luitrace-uses.out's `TOTAL class` lines (22 + 4 + 38 + 4 + 2 + 4 + 332 + 2 = 408) |
| (c) compare-only use | 22 | the use is a branch / compare operand: it neither passes nor stores the value. Every other use of the same value is its own row of the table |
| (e) dead at call | 38 | an argument register beyond the callee's arity, with the callee analysed to its return: `luitrace.py deadarg` (out/luitrace-deadarg.out) walks the callee and, recursively, its direct calls, and reports the register never read before being written |
| (i) size parameter | 4 | a `uptr size` parameter |
| (ii) CheckFailed v1 | 2 | the first printed value of a CHECK |
| (d) frame spill | 4 | a store to an sp / s0 slot: per the ruling a spill is not a use |


The 34 per-image uses whose value CAN be static under the model (the ones the reviewer singled out: 0x10000,
0x10001, 0xfffffffffff8, 0x01010101) — offsets are the decode A twin's and the donor's are the same:

| function | pc | use | reg | class | citation |
|---|---|---|---|---|---|
| Allocator::Allocate | +0x128, +0x13c, +0x150 | `bgeu s5, a0` | a0 | (c) | compare operand; a0 is rewritten by the next `lui` / by `lh a0` at +0x16c |
| Allocator::Allocate | +0x198, +0x244, +0x580, +0x5a4 | `bltu`/`bgeu` on s3 | s3 | (c) | compare operand; s3's other uses are their own rows (e.g. ReportAllocationSizeTooBig a1) |
| Allocator::Allocate | +0x3bc | `beqz s0` | s0 | (c) | compare operand |
| Allocator::Allocate | +0x580 | `bltu s3, a4` | a4 | (c) | compare operand |
| CombinedAllocator::Allocate | +0x78, +0x7c | `bltu a5, a3` / `bltu a5, a4` | a5 | (c) | compare operand (the 0x10000 size-class bound) |
| Allocator::Allocate | +0x94 | `sd a1, 0x10(sp)` | a1 | (d) | a frame spill, not a use (ruling TIME (d)) |
| Allocator::Allocate | +0x35c | `jal` CombinedAllocator::Allocate | a2 | (i) | sanitizer_allocator_combined.h:44 `void *Allocate(AllocatorCache *cache, uptr size, uptr alignment)`; call site asan_allocator.cpp:583,587 `allocator.Allocate(cache, needed_size, 8)` — a2 is `size` |
| Allocator::Allocate | +0x27c | `jal` ReportAllocationSizeTooBig | a2 | (i) | asan_report.h:74-75 `(uptr user_size, uptr total_size, uptr max_size, BufferedStackTrace*)`; call site asan_allocator.cpp:576 — a2 is `max_size` |
| Allocator::Allocate | +0x8b0 | `jal` CheckFailed | a3 | (ii) | sanitizer_common.h:332-333 decl; body sanitizer_termination.cpp:67-72, which only formats v1 / v2: `Printf("... (0x%zx, 0x%zx) ...", ..., (uptr)v1, (uptr)v2, tid)`. NOTE: the ruling says `%llu`; at this pin the conversion is `(uptr)` + `%zx`. Printed, never dereferenced, never stored |
| Allocator::Allocate | +0x6e0 | `jal` DisabledInThisThread | a2,a3,a4,a5,a6 | (e) | lsan_common.h:278 `bool DisabledInThisThread()`, no parameter; call site asan_allocator.cpp:650; out/luitrace-deadarg.out: `dead` for all five |
| Allocator::Allocate | +0x180 | `jal` RZSize2Log | a1 | (e) | asan_allocator.cpp:46 `static u32 RZSize2Log(u32 rz_size)`, one parameter; call sites 466-468; deadarg: `dead` |
| Allocator::Allocate | +0x54c | `jal` GetCurrentThreadStats | a0 | (e) | asan_stats.h:55 `AsanStats &GetCurrentThreadStats()`, no parameter; call site asan_allocator.cpp:635; deadarg: `dead` |
| Allocator::Allocate | +0x224 | `jal` AllocatorMayReturnNull | a0 | (e) | sanitizer_allocator.h:36 `bool AllocatorMayReturnNull()`, no parameter; call sites asan_allocator.cpp:534,569,591; deadarg: `dead` |
| Allocator::Allocate | +0x4bc | `jal` CanPoisonMemory | a0 | (e) | asan_poisoning.h:24 `bool CanPoisonMemory()`, no parameter; call site asan_allocator.cpp:629; deadarg: `dead` |
| CombinedAllocator::Allocate | +0x250, +0x26c, +0x28c | `jal` CheckFailed | a5 | (e) | CheckFailed takes 5 parameters (a0-a4), so a5 is beyond its arity; deadarg: `dead` |
| Allocator::Allocate | +0x6dc | `jalr a3` | a4, a5, a6 | (e) | REAL(memset), asan_allocator.cpp:647, through `__interception::real_memset`; the escape of its address is closed read-only, and deadarg(memset, a4/a5/a6) = dead — §8 item (1) |
| Allocator::Allocate +0x770, CombinedAllocator::Allocate +0x220 | those two offsets | `ret` | a0 | (iii) | no lui / auipc definition reaches either `ret`: the null return, or the allocator's own result plus a redzone offset, aligned — §8 item (2) |
| CombinedAllocator::Allocate | +0xa4 | `jal` LargeMmapAllocator::Allocate | a5 | (e) | a5 is beyond the callee's arity (sanitizer_allocator_secondary.h:85); all four stops of the exhaustive walk are settled, the last of them with the REAL(memset) row above — §8 item (3) |
| CombinedAllocator::Allocate | +0x2ac | `jal` **Refill** | a5 | (e) | the callee is `Refill(PerClass*, SizeClassAllocator*, uptr class_id)` (sanitizer_allocator_local_cache.h:99-100), which takes a0-a3, so a5 is beyond its arity; `deadarg(Refill, a5) = dead` in both images — §8 item (4) |

NOT CERTIFIED, as the ruling requires: no `uptr` ADDRESS parameter, non-linear base or auipc-derived sum is
claimed settled here. After section 8 nothing is open. The counts above are exactly the `TOTAL class` lines of
out/luitrace-uses.out.

## 8. Closing the open uses

The rows the earlier passes left open were re-measured round by round; after the fifth review all of them close. Every command is a mode of luitrace.py and its
output is out/luitrace-openclose.out. Both images give the same answer everywhere, and no use forms an image
address that differs between them.

**(1) `jalr a3` at Allocator::Allocate +0x6dc, a4 / a5 / a6 — (e), the escape closed read-only.** The call is
`REAL(memset)(...)` of asan_allocator.cpp:647, through a runtime function pointer: `+0x6c8 auipc a1,0x67;
+0x6cc ld a1,0x44c(a1)` take the address of `__interception::real_memset` out of the GOT cell and `+0x6d0
ld a3,0(a1)` loads the pointer in it. The CELL is at **0x9abc0** in decode A and **0xa0098** in the donor, both in **`.data`**, and its VALUE is
`0x0000000000092474` = `memset+0x0` (decode A) and `0x000000000009790c` = `memset+0x0` (donor) — and
`luitrace.py ptrscan`, whose write test compares base+imm, finds **0 writers in `.text` of either image**; the
expected writer (`InitializeInterceptors` / `INTERCEPT_FUNCTION`) is absent, so the value is the image's own
relocated initialiser.

CORRECTION of the earlier versions of this file, which said the spill slot "is never reloaded" and that "its only
access is the store itself" (false, AGENT's fifth review) and then gave the lowest handed-out pointer as
s0-0x1000 (too high: the join kept a delta only when both paths agreed and did not handle `addiw`, AGENT's
final review). `luitrace.py frameesc` is now the MAY version — a register holds a SET of possible s0-deltas,
unioned at every join, `addiw` included, more than 64 deltas or a frame pointer plus an unknown becoming ANY —
copied from the reviewer's REVIEW_DIR6/frameesc_may2.py and cited there. It gives, in BOTH images, exactly
two accesses to the slot s0-0x10d0, 0 accesses through an ANY pointer, and they are:

```
  +0x3ec  sd a1, -0xd0(a2)        # a2 = s0-0x1000: the spill of &real_memset
  +0x860  lui a4, 1
  +0x864  sub a4, s0, a4
  +0x868  ld a4, -0xd0(a4)        # the RELOAD of the slot
  +0x86c  ld a4, 0(a4)            # and a READ of real_memset through it
```

The reload at +0x868 is followed only by `ld a4,0(a4)`: the pointer is dereferenced for reading, never used as
the base of a store into the cell (and ptrscan's base+imm scan finds no store into it anywhere). The same walk
lists every frame pointer the function MAY hand out: 19 call arguments in each image, none of them ANY, the
lowest **s0-0x10a8** — the `BufferedStackTrace` passed as `this` to `UnwindImpl` (+0x354) and to
`StackTrace::Print` (+0x364), and as a1 to `DenseMap::FindAndConstruct` (+0x800); the others are s0-0x1000,
s0-2160, s0-2176, s0-2200 and s0+0. Six stores put a frame pointer into memory, the lowest **s0-0x1098** at
+0x31c (`sd a0, 0(a1)`); one of the six, +0xf8, is ANY and is counted as reaching anywhere the ANY set allows,
which the walk reports as 0 ANY memory accesses in the function. The slot at s0-0x10d0 = s0-4304 lies **0x28
bytes BELOW** the lowest pointer handed out, s0-0x10a8 = s0-4264. How I know the object does not extend
downward: it is a C++ object passed by `this` / by reference, whose members sit at NON-NEGATIVE offsets from the
pointer (BufferedStackTrace, asan_stack.h / sanitizer_stacktrace.h), so a callee indexes upward from
s0-0x10a8; reaching s0-0x10d0 would need a negative index out of the object. That is a language-and-ABI
argument, named as such, on top of the measured deltas. Under
the owner's indirect-call rule (AGENT TIME (1)) the callee set is therefore {this image's memset}, and
`deadarg(memset, a4) = deadarg(memset, a5) = deadarg(memset, a6) = dead` — memset reads a0 / a1 / a2 only. The
rows settle as (e). LIMIT, stated: this closes the escape of the pointer inside `__asan_register_globals` and the
writer scan over `.text`; it is a measurement over the image's code, not a proof about a running process.

**(2) the two returned a0 — now (iii) applied to the return value.** `luitrace.py reachdefs`: at
Allocator::Allocate's single `ret` (+0x770) the only definition of a0 is `+0x734 mv a0,s4`, and the definitions of
s4 reaching +0x734 are `+0x23c mv s4,zero`, `+0x850 mv s4,zero`, `+0x2a8 add s4,s2,s4`, `+0x388 add s4,s2,s4` and
`+0x2bc and s4,s4,s8` — the null return, or the allocator's own result s2 plus a redzone offset, masked. At
CombinedAllocator::Allocate's `ret` (+0x220) they are `+0x44 mv a0,zero`, `+0x1ec add a0,a4,a0`, and the results
of the calls at +0xa4 and +0x2ac. NO lui or auipc definition reaches either `ret` in either image. So the returned
value is the constant 0, or the allocator's own result plus a redzone offset, aligned down by `and s4,s4,s8` with
s8 = `neg s8,s0` (+0x1b8), the two's complement of the alignment — NOT a lui constant (AGENT's fourth review
corrected the earlier wording); the case AGENT TIME puts under (iii) — and it is the allocation itself, which `asan_malloc` hands to the caller as an opaque pointer.

**(3) CombinedAllocator::Allocate +0xa4, a5 — OPEN, one stop left.** `readsites` now closes the two gaps that
deadarg had closed (a tail `j` is followed into the target symbol; `ecall`, `jalr` and `jr` are fail-closed) and
enumerates EVERY stop instead of the first. LargeMmapAllocator::Allocate itself never reads a5, which is beyond
its arity (sanitizer_allocator_secondary.h:85). The walk gives four stops in each image:
- `sd a5, 0x38(sp)` at `Report+0xc` — the varargs save on the overflow path; its format string has three
  conversions (secondary.h:92-93), so the slot is never read back. SETTLED, the ruling's (d): a spill is not a use.
- `ecall` at `GetTid+0x4`, with `addi a7, zero, 0xb2` = 178 = `gettid`, which takes no argument. SETTLED (hand).
- `ecall` at `getrlimit+0x44`, with a7 = 261 = `prlimit64`, which takes four arguments (a0-a3). SETTLED (hand).
- `jr a1` at `sysconf+0xf4` — RESOLVED: it is a base-relative (rel4) switch table, base = `auipc a0,0xfff99;
  addi a0,a0,0x630` at +0xd8 / +0xdc, guarded by `bltu a2, a1` with a2 = 0xc, so 13 entries. `luitrace.py swtab`
  reads them entry by entry: decode A table 0x21318, donor 0x213fc, and the 13 targets are the SAME symbol +
  offset in both images (sysconf +0xa4, +0x214, +0x200, +0x208, +0xf8, +0x164, +0x164, +0x138, +0x138, +0x21c,
  +0xf8, +0x104, +0x104). Walking a5 from every distinct target reads a5 nowhere; it leaves three stops, two of
  them settled the same way (`gettid`, and `__lsysinfo+0xc` with a7 = 179 = `sysinfo`, one argument), and one
  that is `jalr a3` at `__interceptor_memset+0x9c` — REAL(memset) again.
The last stop is the same REAL(memset) call as item (1), whose escape is closed read-only there, so this row
settles as (e) with it.

**(4) CombinedAllocator::Allocate +0x2ac, a5 — now (e), and the callee name in section 7 was wrong.** The target
of that `jal` is `SizeClassAllocator64LocalCache::Refill` (decode A 0x35f10, donor 0x36134 — one of the record's 7
pairs), not LocalCache::Allocate: the earlier row matched on a name prefix. `Refill(PerClass*,
SizeClassAllocator*, uptr class_id)` takes a0-a3, so a5 is beyond its arity, and `deadarg(Refill, a5) = dead` in
both images (`Refill` is declared at sanitizer_allocator_local_cache.h:99-100 and takes a0-a3). There was no
indirect call to resolve at all: `LocalCache::Allocate` carries no symbol in either image, which is why deadarg
printed `unknown` for a name it could not find.

**(5) the six (iii-v) rows with a false reason — three per image.** AGENT's third review showed that
'not may-static' does not mean 'not an image address', because the may-static model counts a GOT load as runtime.
Both remedies are applied: the class is narrowed to what it measures, and an IMG column is added
(`imgaddr_run()`, the reviewer's imgaddr.py copied and cited). The IMG column flags exactly the six rows the
reviewer named, all of which reach the trace only through the coarse M:ANY reload, and each now carries its own
class:
- Allocator::Allocate +0x54c, a3 at `jal GetCurrentThreadStats` — a3 is a GOT-loaded `&global` from +0x4f0 /
  +0x4f4: now **(e)**, `deadarg(GetCurrentThreadStats, a3) = dead` in both images (out/luitrace-deadarg.out).
- Allocator::Allocate +0x6e0, a0 at `jal DisabledInThisThread` — a0 is the `flags()` pointer from +0x6ac /
  +0x6b0: now **(e)**, `deadarg(DisabledInThisThread, a0) = dead` in both images.
- Allocator::Allocate +0x724, `sd a0, 0(s2)` — kAllocBegMagic from the constant pool at +0x714 / +0x718
  (asan_allocator.cpp:169-170, 184): its own new class **(f)**, a constant that strictcmp3 compares byte for byte
  (`full+0x718[0x10328|0x10330]=8` in out/strictcmp3-cmp-86da41d3ef68.out).
The `deadarg(GetCurrentThreadStats, a3)` walk is also where closing the tail-jump gap mattered: with the gap open
it stopped at the tail `j` of `AsanTSDGet+0x14` into `__pthread_getspecific`; following that tail call gives
`dead`. The ecall gap left one walk, `deadarg(CheckFailed, a5)`, at `unknown`, stopping at the `ecall` of
`__sanitizer::GetTid+0x4`; the hand step is that the two words there are `addi a7, zero, 0xb2` = syscall 178 =
`gettid`, which takes no argument, so a5 is not read. That is the ONE hand step in section 8; everything else is
measured.

Nothing in these measurements produces an address that differs between the two images: the one function pointer
involved resolves to `memset+0x0` on both sides, and the reaching definitions are identical offsets in both.

## 9. 86da fail-open shapes (a)-(h)

WORKER's registry of cmpkit 86da41d3ef68's known fail-opens (BRANCH 7f2e3c70626, AGENT TIME):
an EQUAL verdict of the kit is no evidence where an address reaches a load / store / jalr / AMO base through one
of eight shapes. Per shape: whether luitrace + the may-static check cover it, with the code line, and the
measurement on the 7 functions (out/luitrace-shapes.out; both images give the same numbers).

| shape | covered | where, and what was measured |
|---|---|---|
| (a) the load / store IMMEDIATE, V+imm | YES | the trace forms it: `report()` computes `ea = (val + (imm or 0)) & M64` for every MEMBASE / JUMPBASE row and resolves `ea` to section + symbol; the may-static check keys memory on base AND imm (`'M:%s:%s' % (base, imm)` in `sta_run()`), and the static verdict of base+imm is the verdict of base, imm being a constant field of the instruction. Measured: 23 lui-derived base uses per image carry a non-zero immediate (+44, +52, +85, +78, +16, +8, -15, -14, -12, +1, +8, +1, +1, +984, +1577, +1579, +32, +64, +1569 …, all listed in out/luitrace-shapes.out). In every one of them the base is runtime under the model, so no combined target exists to name; the `static-base` and `x5-logical` plants show the combined target IS formed and resolved when the base is static (ea 0x317c0 = …Allocate+0x574, ea 0x40100 = __asan_after_dynamic_init+0x2bc, the same symbol + offset in both images). I could not reproduce a set of exactly 5 such rows; the full list is the 23 per image |
| (b) an addi / addiw chain | YES | `RD_FIRST` carries the trace through addi / addiw / add / addw (luitrace.py, the ops table), and `sta_run()`'s generic `w(flat[0], all(sta.get(r, False) for r in flat[1:]))` carries may-static through any such op. The `static-base` plant is exactly this shape (`auipc; addi; and; ld`) |
| (c) ori / xori / slli | YES | same two lines; the `x5-logical` plant is exactly this shape (`lui; ori; xor; andi; ld`) and is caught by both checks |
| (d) a stack spill, an FP move, a CSR round trip | spill YES, FP YES, CSR **not modelled** | spill: slot keys in `step()` and in `sta_run()`; the `spill` plant is caught. FP: `XF` holds ft/fs/fa/f0-f31 in `regs_of()`, every `f`-prefixed op is rd-first, so `fmv.d.x` / `fmv.x.d` carry the value; the `fp` and `fpjoin` plants are caught. CSR: a value written to a CSR and read back would be lost — `csrrw` / `csrrs` are not in `RD_FIRST`, so `step()` refuses them as UNKNOWN-OP (fail-closed for the registers they name) but no CSR is modelled as state. MEASURED: **0 CSR instructions** in the 7 functions in either image, so the gap cannot arise here |
| (e) a jump-table arm reached only by fall-through | YES here, by measurement | the CFG of `analyse()` and of `sta_run()` has fall-through plus direct branch / `j` / `jal` edges; an arm reached only through an indirect `jr` is NOT an edge. MEASURED: the 7 functions hold exactly ONE indirect jump in each image, `jr t1` at PoisonShadow+0x39c, and it is an epilogue tail jump (`ld s0..s5, …(sp); addi sp,sp,0x40; jr t1`), not a switch; PoisonShadow holds 0 lui words; and the may-static walk reaches ALL 319 instructions of PoisonShadow in both images (0 unreached), so no base site is skipped. Where a real switch did appear off-record (sysconf+0xf4) it was read entry by entry with `luitrace.py swtab`, §8 item (3) |
| (f) an in-function callee, with the caller's a0-a7 | **partial — stated, not claimed** | luitrace does NOT follow a lui value into a callee's body: a value live in a0-a7 at a call is reported as CALLARG and settled by its class (§7). `deadarg` DOES see a base use inside a callee, because a base use is a read of the register — so every `(e)` row is positive evidence that the callee never touches the value at all (38 rows). For the CALLARG rows settled as (i), (ii) or (iii-v) the callee's internal use is settled by the parameter's declared role in the pinned source, not by a walk of the callee |
| (g) c.lui (compressed) | YES | `regs_of()` / `step()` / `sta_run()` treat `c.lui` like `lui`, and `luiscan` counts a function holding a 2-byte parcel as `unmeasured`. MEASURED: **0 compressed (2-byte) instructions** in the 7 functions in either image, 18 four-byte `lui` each, and `unmeasured 0` in luiscan |
| (h) an address built WITHOUT lui (auipc, or constants only) | YES, by the may-static check | the trace is seeded by `lui` by design, so it says nothing about such an address; the may-static check does: `if m in ('lui', 'auipc'): w(flat[0], True)` plus the constant-only rule, which is how it finds the 28 may-static base sites per image — all `auipc`+`ld` GOT loads — and the kit's own target pass compares every pc-relative target by symbol + offset (§5, 0 differing targets outside the settled +0xdc row) |

### (a) and (h) for EVERY static base, not only the lui-derived ones

The shapes apply to any address in an EQUAL verdict, so the combined target was computed for every base site in
the 7 functions whose base has a value built from constants only, GOT-loaded pointers included:
`luitrace.py eaval` (out/luitrace-ea.out) runs the same CFG MAY fixpoint as the may-static check but carries the
VALUE — lui, auipc, addi / add / sub / and / or / xor / shifts of such values, (base, imm) slots, and a load whose
address is itself static, whose word is then READ OUT OF THE IMAGE (so an `auipc; addi; ld` GOT load gives the
pointer it holds, and a following `ld / sd X, imm2(that pointer)` gives a second, named target). A register with
two different static values on two paths is dropped, so a printed value is the one every path gives. At each
site it prints `ea = value + the instruction's immediate`, its section and its symbol + offset.

MEASURED, per image: **61** base sites have a computable static base (the 28 may-static GOT loads plus the
second-level loads through them); **36** of those have a NON-ZERO immediate; **15** of the 36 are in
Allocator::Allocate — **not 5**. An UNNAMED target is compared by its CONTENTS, as AGENT's final review
requires: a `.got` cell by the symbol + offset of the pointer it holds, another read-only word by that symbol if
the word is an address and by the word's value otherwise (27 of the 61 per image are unnamed). On that
comparison — section, symbol + offset, and contents — **0 of the 61 differ between the two images**, so no CLAIM
row moves toward a real difference.

The 15 Allocator::Allocate rows with a non-zero immediate (`ea` differs as a number because the layouts differ;
what must match is the right-hand column):

| +off | insn (donor / decode A) | ea donor | ea decode A | section | symbol + offset, or CONTENTS of an unnamed target | same |
|---|---|---|---|---|---|---|
| +0xc4 | `ld a2, -0x258(a2) / ld a2, 0xbc(a2)` | 0x103b8 | 0x103c8 | .rodata | unnamed, contents: `word 0x0218a392cd3d5dbf` | yes |
| +0x3c4 | `ld a0, -0x708(a0) / ld a0, 0x734(a0)` | 0x9e208 | 0x98d40 | .got | unnamed, contents: `__asan_shadow_memory_dynamic_address+0x0` | yes |
| +0x4c8 | `ld a0, 0x7f4(a0) / ld a0, 0x630(a0)` | 0x9e208 | 0x98d40 | .got | unnamed, contents: `__asan_shadow_memory_dynamic_address+0x0` | yes |
| +0x4ec | `ld a2, 0x7d8(a2) / ld a2, 0x614(a2)` | 0x9e210 | 0x98d48 | .got | unnamed, contents: `_ZN6__asan10kMidMemBegE+0x0` | yes |
| +0x4f4 | `ld a3, 0x7d8(a3) / ld a3, 0x614(a3)` | 0x9e218 | 0x98d50 | .got | unnamed, contents: `_ZN6__asan10kMidMemEndE+0x0` | yes |
| +0x510 | `ld a3, 0x7c4(a3) / ld a3, 0x600(a3)` | 0x9e220 | 0x98d58 | .got | unnamed, contents: `_ZN6__asan11kHighMemEndE+0x0` | yes |
| +0x52c | `ld a1, 0x788(a1) / ld a1, 0x5c4(a1)` | 0x9e200 | 0x98d38 | .got | unnamed, contents: `_ZN6__asan28asan_flags_dont_use_directlyE+0x0` | yes |
| +0x530 | `lbu a1, 0x55(a1)` | 0xa3acd | 0x9e60d | .bss | _ZN6__asan28asan_flags_dont_use_directlyE+0x55 | yes |
| +0x6b0 | `ld a0, 0x604(a0) / ld a0, 0x440(a0)` | 0x9e200 | 0x98d38 | .got | unnamed, contents: `_ZN6__asan28asan_flags_dont_use_directlyE+0x0` | yes |
| +0x6b4 | `lw a1, 0x2c(a0)` | 0xa3aa4 | 0x9e5e4 | .bss | _ZN6__asan28asan_flags_dont_use_directlyE+0x2c | yes |
| +0x6cc | `ld a1, 0x610(a1) / ld a1, 0x44c(a1)` | 0x9e228 | 0x98d60 | .got | unnamed, contents: `_ZN14__interception11real_memsetE+0x0` | yes |
| +0x6d4 | `lw a1, 0x34(a0)` | 0xa3aac | 0x9e5ec | .bss | _ZN6__asan28asan_flags_dont_use_directlyE+0x34 | yes |
| +0x718 | `ld a0, 0x6c4(a0) / ld a0, -0x630(a0)` | 0x10328 | 0x10330 | .rodata | unnamed, contents: `word 0xcc6e96b9cc6e96b9` | yes |
| +0x778 | `ld a7, 0x53c(a7) / ld a7, 0x378(a7)` | 0x9e200 | 0x98d38 | .got | unnamed, contents: `_ZN6__asan28asan_flags_dont_use_directlyE+0x0` | yes |
| +0x77c | `lbu a7, 0x4e(a7)` | 0xa3ac6 | 0x9e606 | .bss | _ZN6__asan28asan_flags_dont_use_directlyE+0x4e | yes |

The two `.rodata` words are the De Bruijn constant K = 0x0218a392cd3d5dbf read at +0xc4 (the +0xdc table's
multiplier, KIT-RERUN.md 4.2) and kAllocBegMagic = 0xcc6e96b9cc6e96b9 read at +0x718 (§7's STORE row) — both
byte-equal, and the kit accepts the same +0x718 target as `full+0x718[0x10328|0x10330]=8` (§5).


No row moved toward a real difference: the shapes that are covered report what they already reported, and the
three hand-traced ones (CSR absent, the one `jr` a tail jump with nothing unreached, the callee limit of (f))
leave every class of §7 as it stands.

covers (a)-(h): a, b, c, d (spill, FP), e, g, h; hand-traced: a/h over EVERY static base (61 sites per image, 36
with a non-zero immediate, 15 of them in Allocator::Allocate — not 5 — and all 61 the same section, symbol+offset
and, for the 27 unnamed ones, the same CONTENTS in both images), d (CSR: 0 sites in the 7 functions), e (the single `jr t1` at PoisonShadow+0x39c is an epilogue
tail jump; 0 unreached instructions; PoisonShadow has no lui), f (not traced into callee bodies; CALLARG is
classified per §7, and the 38 (e) rows are proven unread); change: none

## 10. What this settles, and what it does not

- Re-running the 18 rows on the fixed script changes no class and no value: `TOTAL lui rows 18, class a 4,
  class b 14, unmatched none`, the same 4 (a) rows and the same 14 (b) rows as the two earlier versions. The new
  rules add uses (226 base uses at 42 sites, up from 166 at 27; rows 4 and 5 grow from 220 / 228 uses to 427 / 431
  through the spill/reload and jalr-fall-through edges) and no new kind of conclusion.
- It settles the KIT LIMIT for this record: following every ALU op and every logical op, not just addi / load /
  store / jalr, adds 14 (b) rows that luiscan's `memfed 0` did not show, and in every one the value is a mask, a
  bound or an index on a runtime pointer, computed by word-identical code from identical constants in the two
  images. No address of this record depends on a lui value.
- It does not prove any function and changes no verdict of KIT-RERUN.md: 3 EQUAL, 4 EQUAL-mod-pcrel, the one
  settled +0xdc row, as before.
- The trace is not a proof and is not called fail-closed: it is path-insensitive (over-reports uses), it models
  registers and tracked (base, imm) slots only, and it refuses rather than guesses on an op it does not know. The
  address claim comes from the may-static check, under the model stated in section 1 and no further.
- The eight known fail-open shapes of cmpkit 86da41d3ef68 are answered one by one in section 9: six covered by
  the tools, three hand-traced (CSR, the one indirect jump, the callee limit), no row changed.
- All seven planted controls PASS, including the four whose value the evaluator cannot fold and the two that
  broke the first version of the may-static check.
- All 408 non-base uses carry a settlement class with its citation: 332 (iii-v) no constant value under the
  model, 38 (e) dead at call, 22 (c) compare-only, 4 (d) frame spill, 4 (i) size parameter, 4 (iii) runtime
  pointer returned, 2 (ii) CheckFailed v1, 2 STORE into an integer-typed field — the same numbers as the
  `TOTAL class` lines of out/luitrace-uses.out. Section 8 gives each measurement; no class was stretched.

18 rows hand-traced: 4 (a), 14 (b) equal, no MISMATCH

uses settled 408 / 408; open: none
