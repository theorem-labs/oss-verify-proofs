(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from lib/Reusable/YCbq.v:1551-1633 aj_malloc_at04 (copied from
   proofs/cgif/cgif_file_fuzzer/lib/YCbq.v) and lib/Reusable/YCbp.v:28-35 amalloc04_rule_triv (copied from
   proofs/cgif/cgif_file_fuzzer/lib/YCbp.v), at the calloc contract of lib/Reusable/YGCalloc.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YCbpCalloc.v; 108 of its 127 lines of code are new or changed and 117 lines of the source are left out. *)
(* The runtime contract of the ASan interceptor of calloc, as a THIN CALLER WALK over the runtime's
   Allocator::Allocate contract, in the core form of cgif_file_fuzzer's malloc contract and malloc CALL RULE
   (Reusable/YG0d.v:253-260 amalloc_realizes over :243-252 malloc_leaf and :225-233 acall_pre;
   Reusable/YC5d.v:56-70 amalloc04_rule, the form a walk consumes; the world-indexed Reusable/YA0n.v:34 SRr
   through Reusable/YG0d.v:67 amreal, Reusable/YG0n.v:489 AR and Reusable/YG0n.v:17 aview).

   cgif's allocator model has malloc and free but no calloc (its plain and ubsan calloc lemmas are vacuous:
   lib/YN33.v:18, lib/UN33.v:18; lib/A names only the symbol address, A/AB1w.v:479 tfib_A_calloc), so this
   contract is new.  It is written once and unit-generically: the malloc tree, the call precondition, the
   realization relation, the leaves, the trace universe, the stack-buffer predicate, the journal, the kept-frame
   predicate and the meter are Section Variables, as a Theorem Labs lane's realloc kit abstracts its own
   (proofs/cgif/cgif_rgb_fuzzer/lib/ReallocP.v on a working branch c6ef6b691bf: segs, B, U,
   mt, cpre, rpre, areal, rleaf, mleaf), so a second unit instantiates the same text at its own model.
   [*_cgif] below instantiates what can be instantiated from this unit's lib/Reusable today: YG00.malloc,
   YG0d.acall_pre, YG0d.amreal, YG0d.malloc_leaf.

   calloc gets NO second copy of Allocate.  asan_calloc calls the very same
   Allocator::Allocate(size, 8, stack, FROM_MALLOC, can_fill) that asan_malloc calls, with one argument changed
   (can_fill = false), and then zeroes the block.  So [aallocate_realizesP] below is the Allocate contract as a
   Section-level Prop, and [acalloc_of_allocateP] is the phase-1 claim the walk discharges:

       aallocate_realizesP alloc_pc -> acalloc_realizesP pc pc0

   the interceptor's prologue, the unwind, the argument marshalling, the zero fill and the epilogue, over an
   abstract Allocate.  When a Theorem Labs lane's frame-generic Allocate statement (milestone M1 of
   a working branch) lands, [aallocate_realizesP] is replaced by it: nothing else in this file
   changes, because every consumer takes it as that one hypothesis.  At 2026-10-28 21:05Z that branch carries the
   realloc P forms (ReallocP.v) and no Allocate statement, so the shape below is this lane's, measured from the
   two call sites that reach Allocate in this image (asan_malloc A 0x31218, asan_calloc A 0x31c24): the allocator
   instance base, the size, the alignment, the stack object, the AllocType and can_fill in a0..a5, the entry sp
   and the return pc of the caller's frame left abstract in [cpre], and the callee-saved registers carried as
   atoms by the leaf's [aregs_preserved].

   calloc(nm, sz) is Allocate at n = nm * sz computed in 64-bit arithmetic, then a zero fill, with an overflow arm
   that allocates nothing.  Nothing else of the allocator differs, so the allocator-state post of the in-range arm
   IS cgif's malloc post at n = nm * sz: the same block table, the same unpoisoned user bytes and poisoned
   redzones, the same chunk header, the same ONE allocation event (calloc ticks once, as malloc does: the tree is
   [mt (nm * sz) tr], whose head at mt = YG00.malloc is YG00.v:411 [tick]), and the allocation-refusal case
   exactly as cgif's malloc contract states it.  [acalloc04_rule] is the call-rule form of the same thing, in
   amalloc04_rule's shape: its post states [4096 <= res], so a walk refutes the caller's abort-on-NULL branch at a
   calloc site exactly as it does at a malloc site (cgif derives that from the realizes form in
   YCbp.v:30-38 amalloc04_rule_triv = YCbq.v:1550-1632 aj_malloc_at04, where NULL is refuted at :1602-1604 from
   :1591 atok_apath_flag and :1586 ml_malloc_ns over :1589 amreal_SRr04; a kernel answer of 0 ends the path as a
   REFUSAL, not as a NULL return).

   What is NOT stated here, and why.  The allocation-size-too-big path is Allocate's, not calloc's: image A
   0x31458 `slli a0, a1, 0x28` (= 2 ^ 40 = kMaxAllowedMallocSize), 0x31460 / 0x31464 `bltu` on the request and on
   the needed size, 0x31470 `jal 0x5df50 <AllocatorMayReturnNull>`, then either the NULL return (0x31474) or
   0x314a8..0x314c8 `jal 0x5624c <ReportAllocationSizeTooBig>`, all inside Allocate 0x3124c.  Stating it here
   would be the second copy of Allocate this file exists to avoid; it belongs to M1, and the in-range arm's room
   premise (n < MALLOC_MAX = 2 ^ 28, far below 2 ^ 40) keeps calloc's walk clear of it.

   ---------------------------------------------------------------------------------------------------------------
   Each conjunct against the machine code of libreac/fuzz_decode (ORIGINAL binaries, FACTS f0e6eb38667;
   fuzz_decode.asan and
   .asan-ubsan, read with capstone).  Image A = fuzz_decode.asan, image B = fuzz_decode.asan-ubsan.

   trampoline  __wrap_calloc / __interceptor_trampoline_calloc   A 0x51f68   B 0x51fb4   (4 bytes, 1 insn)
     A 0x51f68: j 0x52364                      the only instruction: it jumps to the interceptor.
   interceptor ___interceptor_calloc                             A 0x52364   B 0x523b0   (368 bytes, 92 insns)
   entry       _ZN6__asan11asan_callocEmmPN11__sanitizer18BufferedStackTraceE  A 0x31bd4  B 0x31c20  (224 b, 56 i)
   callee      _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb  A 0x3124c

   | conjunct of the contract | machine fact (image A; image B is the same code at +0x4c) |
   |---|---|
   | [acalloc_realizesP] / [acalloc04_rule] start at the trampoline, as cgif's malloc contract starts at pc_wrap_malloc | A 0x51f68 `j 0x52364` |
   | [pc0], the pc the allocation's stack trace records | A 0x52434 `jal 0x72a08 <StackTrace::GetCurrentPc>`; the recorded pc is its return address A 0x52438 = interceptor + 0xd4, the form of mbedtls/fuzz_pkcs7 AHeap/AW_CallocA.v:27 A_PC_CALLOC (entry + 0xd4) and of tcpreplay/fuzz_services aleaf/A1IcptCalloc.v:64 PC0 |
   | the call trace is the fast frame-pointer unwind ([call_trace] in the realizes form, [ctrace0] in the call rule, as YC5d.v:66 uses call_trace0) | A 0x52368 `sd ra, 0x7e8(sp)`, A 0x5236c `sd s0, 0x7e0(sp)`, A 0x52388 `addi s0, sp, 0x7f0`: ra and the caller's s0 are saved and s0 becomes this frame's pointer, exactly as the malloc interceptor does (A 0x5213c..0x52148); A 0x52490 `jal 0x59e44 <BufferedStackTrace::UnwindImpl>` fills the buffer |
   | the ASTACK = 16384 stack room premise | A 0x52364 `addi sp, sp, -0x7f0` + A 0x5238c `addi sp, sp, -0x70`: 2144 bytes, and the entry takes 48 more (A 0x31bd4 `addi sp, sp, -0x30`) |
   | nm in a0, sz in a1 | A 0x52398 `mv s2, a0` (nm), A 0x52394 `mv s1, a1` (sz); handed on unchanged at A 0x5249c-0x524a0, A 0x524a4 `jal 0x31bd4` |
   | overflow test: the overflow arm is taken exactly when the 64-bit product overflows | A 0x31bf4 `mulhu a2, a1, a0`, A 0x31bf8 `bnez a2, 0x31c64`; sz = 0 short-circuits to the in-range arm (A 0x31bf0 `beqz a1, 0x31bfc`) |
   | in-range size is the 64-bit product nm * sz | A 0x31bfc `mul s0, a1, a0`, passed as a1 of Allocate (A 0x31c18 `mv a1, s0`) |
   | [aallocate_realizesP]'s register premises, read at calloc's call of Allocate | a0 = the allocator instance base [inst]: A 0x31c00 `auipc a0, 0x6c` + A 0x31c08 `addi s2, a0, -0x4a8` = 0x9d758 `__asan::instance` (3632 bytes, the size [asyms_areas] gives [as_inst B]), A 0x31c14 `mv a0, s2`; a1 = the size (above); a2 = 8 (A 0x31c04 `addi a2, zero, 8`); a3 = the BufferedStackTrace the unwinder filled (A 0x31c1c `mv a3, s1`); a4 = 1 = FROM_MALLOC (A 0x31c0c `addi a4, zero, 1`); a5 = 0 = can_fill FALSE (A 0x31c20 `mv a5, zero`) |
   | that it is the SAME Allocate asan_malloc calls, so no second copy is stated | asan_malloc A 0x311f0 sets the same a0 (A 0x31204 auipc + A 0x31210 `addi a0, a0, 0x554` = 0x9d758), a2 = 8 (A 0x31208), a4 = 1 (A 0x3120c) and calls A 0x31218 `jal 0x3124c`; its only difference is a5 = 1 (A 0x31214 `addi a5, zero, 1`), can_fill TRUE |
   | ONE allocation event (tick) | the single Allocate call above; the tree is [mt (nm * sz) tr], whose head is YG00.v:411 `tick` |
   | the user bytes come back zero, over the FULL requested size n = nm * sz | the memset is called with a2 = n: A 0x31c54 `mv a2, s0` (s0 = nm * sz from A 0x31bfc), a1 = 0 (A 0x31c50 `mv a1, zero`), a0 = the block (A 0x31c4c `mv s1, a0`), through the variable `__interception::real_memset` at 0x9abc0, whose address the GOT slot 0x98d60 holds (A 0x31c40 auipc + A 0x31c44 `ld a1, 0x120(a1)` load the GOT slot, A 0x31c48 `ld a3, 0(a1)` loads the variable, A 0x31c58 `jalr a3`; the variable holds 0x92474, the image's memset) |
   | the memset runs ONLY for a primary-allocator block; a secondary (mmap) block is zero already | A 0x31c2c `ld a1, 0x20(s2)` (instance + 0x20 = the primary space base), A 0x31c30 `bltu a0, a1, 0x31c7c` -> skip; A 0x31c34 `slli s3, s3, 0x25` (2 ^ 37 = the primary space size), A 0x31c38 `add a1, a1, s3`, A 0x31c3c `bgeu a0, a1, 0x31c7c` -> skip. So the walk takes two branches to one post: primary, where the zero comes from the memset; secondary, where it comes from the fresh mmap pages the model's KMmapSec grant maps |
   | the overflow arm allocates nothing and returns NULL | A 0x31c64..0x31c70: `jal 0x5df50 <AllocatorMayReturnNull>`, `beqz a0, 0x31c98`; on the non-zero arm A 0x31c74 `jal 0x6be1c <SetErrnoToENOMEM>` then A 0x31c78 `mv a0, zero` and the epilogue A 0x31c7c..0x31c94 `ret`. Allocate is not reached on this path, so no tick and no depot trace |
   | [amrn], the premise of the overflow arm | A 0x5df50 auipc + A 0x5df54 `lb a0, 0xd1(a0)` + A 0x5df58 `snez a0, a0`: the byte at 0x123021 (`__sanitizer::allocator_may_return_null`), a .bss byte that start-up writes; the harness's `__asan_default_options` (A 0x7fbb8, string at 0x1dcdf) is "allocator_may_return_null=1" |
   | errno = ENOMEM on the overflow arm | A 0x6be1c..0x6be2c `jal <__errno_location>` then `addi a1, zero, 0xc`, `sw a1, 0(a0)`: 12 = ENOMEM, written as a 4-byte word |
   | the epilogue restores ra, s0-s6 and sp and returns to the caller | A 0x524a8..0x524d0 (`ld ra, 0x7e8(sp)` .. `ret`), the [acall_post] / [kept] register and frame conjuncts |

   No AddrHashMap meta-region premise.  cgif's malloc SITE rule does not carry one either: YC5d.v:56-70
   amalloc04_rule's premises are the journal, the size and room bounds, the sp / stack-room / gp / tp / ra
   facts, st_nev < EV_MAX, chain_pre, the trace in the universe and the meter, and the call precondition it
   rests on (YG0d.v:225-233 acall_pre) adds only AR, aregime and qmeter.  The meta region enters one level up,
   in the program contract and the frame invariant (A/ACfn.v:45 and :56 tfib_lib_pre_x / tfib_lib_post_x,
   A/AD1u.v:61 FINV), and is carried across a site by ameta_inv_kept (A/ACh1.v:310).  For this chain it is also
   unreachable: every call the three functions make is to TryAsanInitFromRtl, GetMallocContextSize,
   StackTrace::GetCurrentPc, BufferedStackTrace::UnwindImpl, asan_calloc, Allocator::Allocate,
   AllocatorMayReturnNull, SetErrnoToENOMEM, ReportCallocOverflow or DlSymAllocator::Callocate, and the only
   indirect call in the chain is A 0x31c58 `jalr a3`, whose target it reads from the variable
   `__interception::real_memset` at 0x9abc0 (reached through the GOT slot 0x98d60), which holds the image's
   memset 0x92474; no path reaches a metadata lookup, a refcount or a lock.  decode's
   program lane carries the invariant for the contract that consumes this rule.

   Not taken from the machine code and NOT premises of this contract: that the runtime is initialized
   (A 0x5239c `jal <TryAsanInitFromRtl>`, A 0x523a0 `beqz a0` -> the DlsymAlloc arm at A 0x52400), which the
   unit's call precondition carries, as it does for malloc.

   Released templates this is ported from (rule 24; what is taken from each):
   - tcpreplay/fuzz_services lib/aleaf/A1IcptCalloc.v (origin/main e966c513ee6): the interceptor's split into a
     prefix to the entry and a suffix after it (:401 calloc_prefix_T, :444 calloc_suffix_T) and the stack-trace pc
     at entry + 0x3c / the return at entry + 0x144 - decode's interceptor is the same 368-byte, 92-instruction
     function;
   - mbedtls/fuzz_pkcs7 lib/AHeap/AW_CallocA.v:25-27 (A_CALLOC, A_ASAN_CALLOC, A_PC_CALLOC): naming the three
     addresses of the chain, and the stack-trace pc at entry + 0xd4;
   - json-c/json_object_fuzzer lib/QEyY.v:44-54 calloc_icpt_spec and lib/QsDw.v:46-66 calloc_post: the contract is
     the allocator's malloc contract at n = cnt * sz (QEyY.v:51 `asan_malloc (ae_L RE) a (cnt * sz)`), with the
     user bytes zero in the post (QsDw.v:65 `rw_cells ... [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]`);
   - openssl/bndiv lib/A/R_asan_calloc.v:120-122 calloc_A_spec: the premises on the two arguments
     (`0 <= k < 2^64`, `0 <= sz < 2^64`, a bound on the product), which this file states as
     `0 <= nm`, `0 <= sz` and `nm * sz < MALLOC_MAX`;
   - cgif_rgb_fuzzer lib/ReallocP.v (a working branch c6ef6b691bf): the Section-variable shape
     and the P-suffix naming;
   - cgif_file_fuzzer lib/YC5d.v:56-70 amalloc04_rule: the call-rule shape of [acalloc04_rule], conjunct for
     conjunct, with n = nm * sz and the zero conjunct added. *)
(* Name resolution (the SHADOWED-NAME hazard: lib/Lib/PropExec.v also defines getr, mkst and seg_rom, and its
   mkst empties the FP registers).  This file imports no lib/Lib module, so its getr / mkst / seg_rom are
   YK11's, the ones YG0d's cfg_at uses.  Checked by printing the elaborated statements in a scratch file beside
   lib/A/DecodeCalloc.v (which does reach PropExec, through AB1v): Locate shows both constants in scope
   there, and the printed body of acalloc04_rule reads
   `YA0n.SRr segs W {| Run.cfg_ms := YK11.mkst regsT (Z_to_bv 64 pc) memT (YK11.seg_rom segs); ... |}` and
   `YK11.getr regsT ...` throughout. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YM05 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YGAlloc.
Import ListNotations.
Open Scope Z_scope.

(* FROM_MALLOC, the AllocType asan_calloc and asan_malloc both pass in a4 (A 0x31c0c / A 0x3120c). *)
Definition AT_FROM_MALLOC : Z := 1.
(* The alignment both pass in a2 (A 0x31c04 / A 0x31208). *)
Definition ALLOC_ALIGN : Z := 8.
(* can_fill: calloc passes 0 (A 0x31c20), malloc passes 1 (A 0x31214). *)
Definition CF_CALLOC : Z := 0.
(* The largest request the primary allocator serves: YG00.v's class_table_ok checks from_primary 64512 = true and
   from_primary 64513 = false.  The calloc contract takes a unit-supplied size bound [cmax] with cmax <= PRIM_MAX,
   so every request it covers is a primary one; asan_calloc fills a primary block itself (A 0x31c40..0x31c58), so
   the contract needs no fact about the bytes of a secondary (freshly mapped) block. *)
Definition PRIM_MAX : Z := 64512.
(* The contract also takes the unit's call depth [cdepth]: the distance from the wrapper's entry sp down to
   Allocate's entry sp (the wrapper's frame plus asan_calloc's).  a Theorem Labs lane's Allocate statement asks
   ly_bot ly < sp at Allocate's entry (YGAlloc.v alloc_pre), and the unit's call precondition gives that bound
   only at the wrapper's entry, so the claim carries `ly_bot ly + cdepth < sp`, which the program-level caller
   discharges per call site (cgif carries the same per-call bound at its program level, A/ACjy.v:211 Hbot). *)
(* ENOMEM is LPS's (LinuxProcessSem/State.v:557, = 12), the value SetErrnoToENOMEM stores
   (A 0x6be28 `addi a1, zero, 0xc`). *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section p.
Variable segs : list Segment.
Variable B : asyms.
(* The trace universe, as ReallocP.v takes it ([as_universe B] instantiates it). *)
Variable U : list (list Z).
(* The allocator model's malloc tree; [malloc] of this unit's YG00 instantiates it. *)
Variable mt : Z -> list Z -> M sptr.
(* The call precondition at an interceptor's entry; [acall_pre segs B] instantiates it. *)
Variable cpre : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> list (Z * Z * Z) -> Prop.
(* The realization relation of the model's trees against the machine; [amreal segs] instantiates it. *)
Variable areal : forall R : Type, itree astate R -> world segs -> config -> (R -> world segs -> config -> Prop) -> Prop.
(* The leaf of an allocation of n bytes; [malloc_leaf segs B] instantiates it, so calloc's leaf carries cgif's
   whole ASan post (the block table, the addressable user bytes, the poisoned redzones and the chunk header) and
   adds only the zero conjunct. *)
Variable aleaf : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
Z -> sptr * astate -> world segs -> config -> Prop.
(* The parameters of a Theorem Labs lane's frame-generic Allocate statement (lib/Reusable/YGAlloc.v, this unit's by-path copy
   of proofs/cgif/cgif_file_fuzzer/lib/AllocG.v at the frozen a working branch 95e6f1d72b6), in its order:
   the allocator relation over the instance, the addresses the allocator owns, the premise on state and size, the
   size and live-byte bounds, the extra post on the state, and the allocator's out-of-memory byte.  cgif's
   instantiation is ARX inst := (inst = the image's instance /\ AR), AOX := aowned B, rpre := aregime /\ qmeter,
   nmax := MALLOC_MAX, lmax := LIVE_MAX, lpost := qtight. *)
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable oomb : Z.

(* The Allocate contract this walk consumes is a Theorem Labs lane's frozen primary-size statement, copied by path into
   lib/Reusable/YGAlloc.v and applied to the parameters above: [YGAlloc.aalloc_prim_realizes segs B (fun tr _ => In tr
   U) mt ARX AOX rpre nmax lmax lpost alloc_pc oomb ALLOC_ALIGN AT_FROM_MALLOC CF_CALLOC] (every n <= PRIM_MAX, the
   only sizes [acalloc_of_allocateP] passes, since cmax <= PRIM_MAX; the trace premise is the frozen statement's
   predicate form of In tr U).  The three trailing numbers are calloc's own call-site arguments,
   measured at A 0x31c04 (a2 = 8), A 0x31c0c (a4 = 1 = FROM_MALLOC) and A 0x31c20 (a5 = 0 = can_fill false);
   asan_malloc's call of the same Allocate differs only in a5 = 1 (A 0x31214).  No part of Allocate is restated
   here. *)

(* ------------------------------------------------------------------------------------------------------------
   calloc's own contract, realizes form. *)

(* The user bytes of the returned block read as zero, over the FULL requested size n = nm * sz (the size the
   memset is called with).  The block is the one a0 names (the leaf's own conjunct
   getr regs' 10 = w64 (sptr_addr B ly' (fst r))), so this is stated of the reached configuration's registers and
   memory, and is vacuous when the allocator returned NULL. *)
Definition calloc_zeroed (W' : world segs) (c' : config) (n : Z) : Prop :=
forall i, 0 <= i < n ->
bv_unsigned (getr (ms_regs (cfg_ms c')) 10) <> 0 ->
aview segs (w_H W') (ms_mem (cfg_ms c')) (bv_unsigned (getr (ms_regs (cfg_ms c')) 10) + i) = Some 0.

(* calloc's leaf: the allocation leaf at n = nm * sz - cgif's whole malloc post at that n - and the user bytes
   zero. *)
Definition calloc_leaf_with (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
aleaf ly S W regs mem md n r W' c' /\ calloc_zeroed W' c' n.

(* The in-range arm: at the trampoline [pc], with nm in a0 and sz in a1 and the product within the allocator's
   room, the run realizes the malloc tree at n = nm * sz and lands in calloc's leaf.  Premises, and the refusal
   case, are cgif's malloc contract's (YG0d.v:253-260) with n = nm * sz. *)
Definition acalloc_realizesP (pc pc0 cmax cdepth : Z) : Prop :=
forall ly S W regs mem md nm sz ch,
cpre ly S W regs mem md ch ->
ly_bot ly + cdepth < spZ regs ->
getr regs 10 = w64 nm -> getr regs 11 = w64 sz ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes S + nm * sz <= LIVE_MAX ->
In (call_trace ly pc0 regs ch) U ->
areal _ (mt (nm * sz) (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(calloc_leaf_with ly S W regs mem md (nm * sz)).

(* THE PHASE-1 CLAIM: calloc is a thin caller walk over Allocate.  Phase 2 proves this implication - the
   interceptor's prologue, the unwind into the stack object, the overflow test, the argument marshalling
   (a0 = inst, a2 = 8, a4 = FROM_MALLOC, a5 = 0), the two zero-fill branches (primary: the memset; secondary: the
   fresh mmap pages) and the epilogue - and nothing of Allocate itself. *)
Definition acalloc_of_allocateP (pc pc0 alloc_pc cmax cdepth : Z) : Prop :=
cmax <= PRIM_MAX ->
YGAlloc.aalloc_prim_realizes segs B (fun tr _ => In tr U) mt ARX AOX rpre nmax lmax lpost alloc_pc oomb
ALLOC_ALIGN AT_FROM_MALLOC CF_CALLOC ->
acalloc_realizesP pc pc0 cmax cdepth.

(* ------------------------------------------------------------------------------------------------------------
   calloc's call rule, the form a walk consumes (YC5d.v:56-70 amalloc04_rule, conjunct for conjunct).  Its post
   states [4096 <= res]: the caller's abort-on-NULL branch at a calloc site is refuted exactly as at a malloc
   site, and a kernel answer of 0 ends the path as a refusal rather than as a NULL return. *)

(* YCbq.v:316 call_trace0's text.  It is stated here so that this file needs no file of the walk layer; at
   mt = YG00.malloc and the unit's journal it is convertible with YCbq's. *)
Definition ctrace0 (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
unwind_of_chain pc0 ((spZ regs, raZ regs, s0Z regs) :: ch).

(* The walk's journal and kept-frame predicate ([ajournal segs B] and [acall_kept segs B] of YCbq.v:349 and
   :823 instantiate them), and the meter ([mo_ok MT], [mo_le MT], [mo_malloc MT] of YC5d.v:17-20). *)
Variable journal : Z -> Z -> list (Z * Z) ->
alayout -> astate -> world segs -> (word -> option byte) -> Model -> list (Z * Z) ->
alayout -> astate -> world segs -> (word -> option byte) -> Model -> Z -> Prop.
Variable kept : alayout -> astate -> world segs -> (word -> option byte) ->
world segs -> (word -> option byte) -> Z -> Z -> (Z -> Prop) -> Prop.
Variable mok : astate -> Z -> Prop.
Variable mle : astate -> astate -> Z -> Prop.
Variable mcost : Z -> Z.

Definition acalloc04_rule (pc pc0 cmax cdepth : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k nm sz (o : Z) raw ch,
journal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
ly_bot lyc + cdepth < spZ regsT ->
getr regsT 10 = w64 nm -> getr regsT 11 = w64 sz ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes Sc + nm * sz <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (ctrace0 pc0 regsT ch) U ->
mok Sc (mcost (nm * sz)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nm * sz)] /\
(forall i, 0 <= i < nm * sz -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
kept lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size (nm * sz)) /\
mle Sc S2 (mcost (nm * sz))).

(* ------------------------------------------------------------------------------------------------------------
   The overflow arm.  It is calloc's own code (A 0x31bf4 / 0x31bf8 / 0x31c64), not Allocate's, so it is stated
   here; it consumes no Allocate contract.  A unit uses it only where the runtime's allocator_may_return_null
   byte is known to be non-zero at the call, which is a start-up fact: the byte lives in .bss and start-up writes
   it from the harness's __asan_default_options.  libreac/fuzz_decode does NOT instantiate this arm; see
   lib/A/DecodeCalloc.v for the measurement and for why its single call site cannot reach the arm. *)

(* The leaf of the overflow arm: the allocator is not entered, so the allocator state is the one it was called
   with, a0 is 0 and errno is ENOMEM.  [opost] is the unit's call post ([acall_post segs B ASTACK] instantiates
   it): the same register, io and frame conjuncts as the allocation leaf. *)
Variable opost : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
(Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

Definition calloc_ovf_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
fst r = PNull /\ snd r = S /\
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
opost ly S W regs mem md (fun _ => False) ly' S W' regs' mem' md' /\
getr regs' 10 = w64 0 /\
rd32 (aview segs (w_H W') mem') (as_errno B) ENOMEM.

(* When the 64-bit product of nm and sz overflows and the allocator_may_return_null byte at [amrn] is not zero,
   the call allocates nothing (no allocation event, no trace put in the depot: the tree is [ret PNull], not the
   malloc tree) and returns NULL with errno = ENOMEM.  No [In (ctrace0 ...) U] premise: this arm reaches no
   allocator entry, so the model asks nothing of the trace universe.  This arm is NOT an allocation refusal: a
   caller discharges it by refuting its overflow premise (2 ^ 64 <= nm * sz) from the call site's constants, not
   by the room premises of the in-range arm. *)
Definition acalloc_overflow_realizesP (pc : Z) (amrn : Z) : Prop :=
forall ly S W regs mem md nm sz v ch,
cpre ly S W regs mem md ch ->
getr regs 10 = w64 nm -> getr regs 11 = w64 sz ->
0 <= nm < 2 ^ 64 -> 0 < sz < 2 ^ 64 -> 2 ^ 64 <= nm * sz ->
aview segs (w_H W) mem amrn = Some v -> v <> 0 ->
areal _ (YG00.ret PNull S) W
(cfg_at segs pc regs mem md)
(calloc_ovf_leaf ly S W regs mem md).
End p.

(* The instantiation at this unit's own allocator model and predicates (cgif_file_fuzzer's, in lib/Reusable).
   [sbuf] stays a parameter (a Theorem Labs lane's M1 fixes the BufferedStackTrace's shape), and the call rule's journal, kept
   and meter stay parameters until the unit's walk layer (YCbq, YC5d) is relocated beside these files. *)
Section q.
Variable segs : list Segment.
Variable B : asyms.
(* cgif's instantiation of the Allocate statement's parameters (AllocG.v:136-139's ARX_cgif / rpre_cgif, with
   the image's allocator instance as a parameter because it is a per-image address). *)
Definition ARX_cgif (inst : Z) (inst' : Z) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (md : Model) : Prop :=
inst' = inst /\ AR segs B ly S W mem md.
Definition rpre_cgif (S : astate) (n : Z) : Prop := aregime S /\ qmeter S.

(* Primary sizes only (n <= PRIM_MAX): the frozen closed Allocate (AGtopcgifC.aalloc_prim_realizes_cgif_closed) is
   that form, and every calloc request of this unit is a primary one. *)
Definition aalloc_realizes_cgif (inst oomb alloc_pc cf : Z) : Prop :=
YGAlloc.aalloc_prim_realizes segs B (fun tr _ => In tr (as_universe B)) malloc (ARX_cgif inst) (aowned B) rpre_cgif
MALLOC_MAX LIVE_MAX qtight alloc_pc oomb ALLOC_ALIGN AT_FROM_MALLOC cf.
(* [acalloc_realizesP] does not mention [B] (its trace premise is over [U]), so it takes none here. *)
Definition acalloc_realizes_cgif (pc pc0 cmax cdepth : Z) : Prop :=
acalloc_realizesP segs (as_universe B) malloc (acall_pre segs B)
(fun R t W c Q => amreal segs t W c Q) (malloc_leaf segs B) pc pc0 cmax cdepth.
Definition acalloc_of_allocate_cgif (inst oomb pc pc0 alloc_pc cmax cdepth : Z) : Prop :=
acalloc_of_allocateP segs B (as_universe B) malloc (acall_pre segs B)
(fun R t W c Q => amreal segs t W c Q) (malloc_leaf segs B) (ARX_cgif inst) (aowned B) rpre_cgif
MALLOC_MAX LIVE_MAX qtight oomb pc pc0 alloc_pc cmax cdepth.
Definition acalloc_overflow_realizes_cgif (pc amrn : Z) : Prop :=
acalloc_overflow_realizesP segs B (acall_pre segs B) (fun R t W c Q => amreal segs t W c Q)
(acall_post segs B ASTACK) pc amrn.
End q.
End d.
