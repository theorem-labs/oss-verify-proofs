(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, module names and addresses changed; 40 of its 62 lines of code are new or changed and 45 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput (fuzz_link.c:764-790), UBSAN build: the slot. One driver call runs at most
   48 operations and answers 0.

   The twin of lib/Prog/LLVMFuzzerTestOneInput_c.v. This is the obligation the relocated frame
   already asks for: lib/U/FrameAPI.v:48-54 discharges `Statements.ubsan_halts` from
   `lib_contract_o` at ENTRY = 0x13a30 with ra, empty and SLOT_STACK = 65536, for every j below 4
   (lines 52-53). So the contract of this function is THAT statement with link`s own bindings, and
   not a new shape. It has NO Pre slot: no UBSan guard below can be answered by a premise on the
   input, and none is. The file fixes the bindings the frame leaves open, read from
   lib/U/FrameAPI.v (malloc 0x17d48, free 0x17c08, calloc 0x17ad0, realloc none, guard 0x960b8
   through GOT 0x21110), and records what link`s slot adds over the released boxreg slot it is
   modelled on:
   - the two calloc blocks of the driver call (8856 bytes of struct model, 516 of struct
     reac_served_marks), freed before the return;
   - per-operation heap: two text_buf blocks of at most 40 bytes and up to two fuzz_str copies of
     at most 320, each freed in the operation that made it;
   - THE CROSS-CALL STATE: g_sink, g_say and g_said live across driver calls and the FILE is never
     closed, so link`s `G` is not empty, where boxreg`s is. The globals list `llvm_G` below names
     them (the `A_*` of lib/U/Prog/link_mem.v, the ubsan addresses); the invariant `GI` over them
     is the sink lane`s, so this contract takes it as a PARAMETER and the frame`s G_local_c and
     G_img_c obligations are stated over it.
   The abort at +0x914 (0x14344, reached from the `beqz` at 0x13bf4 and 0x13bfc) is the harness`s
   own calloc failure; the allocation budget rules it out. A size of 2^26 or more returns 0 at once
   (+0x3c, `srli a1, a1, 0x1a; bnez`).
   K = 17792: LLVMFuzzerTestOneInput 480, mark_quietly 32, reac_served_mark 320,
   reac_link_alias_write 336, nl_talk 16512, fuzz_recv 112 (link/donors/REPORT.md section 4, over
   the ubsan callee lists of link/donors/premises-ubsan.txt). The call edges of the ubsan build only
   (the slot to name_of, frame 0; kernel to nl_begin, frame 0, and to nl_attr_put, 32; talk to
   take_text, 32) reach at most 480 + 4400 = 4880, below K.
   NOTE for the frame owner: lib/U/FrameAPI.v:13 has frame_G = [(0x221d8, 4)], so the premise
   `(forall a, in_globals llvm_G a -> in_globals frame_G a)` cannot hold until frame_G is widened to
   link`s six globals; the same note as the plain twin (link/CONTRACTS.md section 3 item 6).
   The model block, calloc(1, 8856) at 0x13be0, and the marks block, calloc(1, 516) at 0x13bf0, are
   both inside the frame's calloc_contract, which asks m * n < 2 ^ 62 (lib/U/Contract.v:153; the
   calloc lane lifted it from 4096). `llvm_calloc_model` below is calloc_contract for m = 1,
   n = MODEL_BYTES at LLVM_CALLOC; lib/U/CallocModelGap.v proves it (zlib_llvm_calloc_model, from
   lib/U/CallocSite.v calloc_model_site), so it is no longer a premise of the contract. It gives the
   model block's alignment (the five model_begin guards below), its zero fill (n_mark = 0 at the
   start) and its bound (the mark-address guards); malloc_ret gives `res mod 16 = 0` for both blocks.
   UBSan guards (link/donors/ubsan-checks.tsv lines 102-126, link/ct/dis/ubsan/LLVMFuzzerTestOneInput.s);
   every guard branches to the `unimp` at 0x14340 (+0x910):
   - branches 0x13af8 and 0x13b20 (fuzz_link.c:93-94, interfaces() inlined, first loop,
     `bltu s10, n_if` with s10 = 79) and 0x13b80 and 0x13bac (fuzz_link.c:97-98, second loop,
     `bltu a3, n_if` with a3 = 79): trap when n_if > 79, past if_name[80] or if_index[80].
     ANSWERED BY THE PROGRAM: memset zeroes g_nl first (0x13a90); the first loop stores 60 entries
     (k = 0 to 63, less the four with k mod 16 = 15) and the second 4, so every index is at most 63.
     snprintf writes only g_names[k] and its own frame, both outside g_nl.
   - branches 0x13b18 and 0x13ba4 (fuzz_link.c:94 and :98, `blt n_if + 1, n_if`): signed overflow of
     n_if++. ANSWERED BY THE PROGRAM: n_if <= 63 at each increment.
   - branches 0x13b00 and 0x13b88 (fuzz_link.c:93 and :97, `bltu`, the complement of
     g_nl + 0x422b0 against 8 * n_if) and 0x13b28 and 0x13bb4 (fuzz_link.c:94 and :98, the complement
     of g_nl + 0x42530 against 4 * n_if): the element address wraps. ANSWERED BY A CONSTANT ADDRESS:
     g_nl is A_G_NL = 0x323c0 and the offsets are below NK_SIZE.
   - branches 0x13c80 (fuzz.h:42, the operation selector of fuzz_link.c:778), 0x13ce4 and 0x13d18
     (fuzz.h:42, the two fuzz_u8 of op_read, fuzz_link.c:680) and 0x13ff4 (fuzz.h:42, the fuzz_u8
     of op_refused, fuzz_link.c:757), all `addi a, p, 1; bgeu s9, a` with s9 = 1: trap when the
     cursor p is 0 or 2^64 - 1; each runs only when the cursor count n is not 0. ANSWERED BY THE
     INPUT MODEL: lib_pre_x puts a non-empty input in a user block of the allocator, so
     4096 <= data (blocks_low) and data + size <= alloc_ceiling < 2^64 (mr_owned_low), and the
     cursor at sp+0x40 keeps data <= p and p + n = data + size: the inlined fuzz_u8 does, and so do
     the cursor clauses of the U Posts of name_of, text_of and kernel. Hence 0 < p and
     p + 1 < 2^64.
   - branches 0x13db0, 0x13e3c, 0x13f30, 0x14024 and 0x14138 (fuzz_link.c:670, model_begin inlined
     into op_mark, op_unmark, op_write, op_read and op_refused: `ld a0, 0x20(sp); bnez a0`, where
     0x20(sp) holds m AND 7, stored at +0x1e0): trap unless the model block is 8-aligned.
     ANSWERED BY THE ALLOCATOR, through calloc_contract (llvm_calloc_model): malloc_ret gives
     `res mod 16 = 0`.
   - branches 0x13e78 (fuzz_link.c:466, model_unmark, `beq s4, a0` with a0 = 33) and 0x14270
     (fuzz_link.c:436, model_remember, `beq s6, a0` with s6 = 16 i and a0 = 0x210): trap when the
     loop index reaches 33. ANSWERED BY THE PROGRAM: both loops run i < n_mark, and
     0 <= n_mark <= MARKS_MAX = 32 holds throughout (link_spec`s model_marks_wf): the block starts
     zero (through calloc_contract, llvm_calloc_model), model_remember increments n_mark only below 32
     (fuzz_link.c:438), model_unmark resets it to 0, and model_read and model_write leave it alone.
   - branch 0x142b4 (fuzz_link.c:439, `bltu a0, s5` with a0 = 32, unsigned): traps when n_mark > 32
     or n_mark < 0. ANSWERED BY THE PROGRAM: it is reached only with n_mark <= 31 (the
     `blt a0, s5` with a0 = 31 at 0x142a4) or n_mark <= 0 (the `blez` at 0x14254), and n_mark >= 0
     as above.
   - branches 0x13e80 (fuzz_link.c:466), 0x14278 (fuzz_link.c:436) and 0x142c0 (fuzz_link.c:439),
     each `bltu` of the complement of m + 8340 (MD_MARK) against 16 i: the address of m->mark[i]
     wraps. ANSWERED BY THE ALLOCATOR, through calloc_contract (llvm_calloc_model): fresh_block gives
     m + 8856 <= alloc_ceiling < 2^64, and 8340 + 16 * 32 = 8852 <= 8856.
   - the `unimp` at 0x14348 (+0x918) follows the call to abort and is reached only through it (the
     `fallthrough` row, line 127).
   The callee U premises on alignment are met by the program: the cursor (sp+0x40) and the two own
   cells (sp+0x50, sp+0x78) are 8-aligned because sp is 16-aligned (lib_pre) and the frame is 480;
   the marks block is 16-aligned by calloc_contract; the model block is by the same contract (llvm_calloc_model).
   OPEN: the UBSan twin of a callee (reac_served_mark, through mark_quietly) carries an arithmetic
   premise its guard needs, `m_rc (mark_lib ...) <> - 2 ^ 31`, which the slot cannot discharge
   from the input alone.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt). This contract has the SR shape of the released
   allocator-facing contracts: the function reaches malloc, so it is stated over the frame`s
   allocator interface (lib/U/Contract.v) and not with the `leaf` shape of
   lib/U/Prog/link_mem.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract OutForm Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require StdioModel.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x13a30.
Lemma LLVM_ENTRY_is_entry : LLVM_ENTRY = P_LLVMFuzzerTestOneInput. Proof. reflexivity. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition LLVM_FRAME : Z := 480.
Definition LLVM_K : Z := 17792.
Definition LLVM_MALLOC : Z := 0x17d48.
Definition LLVM_FREE : Z := 0x17c08.
Definition LLVM_CALLOC : Z := 0x17ad0.
Definition LLVM_GUARD_GOT : Z := 0x21110.
Definition LLVM_GUARD : Z := 0x960b8.
Definition MODEL_BYTES : Z := 8856.
Definition MARKS_BYTES : Z := 516.

(* what one driver call may leave changed outside the allocator`s blocks: the fake kernel, the
   interface names, the long alias msg_build uses, and the three words of the harness`s own
   stream. g_sink, g_say and g_said are the ones that live ACROSS calls. *)
(* ofl_head is in the list as well: mark_quietly's first call runs fmemopen, whose tail call to
   __ofl_add stores the new FILE there, and the plain frame's widened frame_G lists it too. *)
Definition llvm_G : list (Z * Z) :=
  [(A_G_NL, NK_SIZE); (A_G_NAMES, G_NAMES_SIZE); (A_LONG_ALIAS, LONG_ALIAS_SIZE);
   (A_G_SINK, 8); (A_G_SAID, SAID_SIZE); (A_G_SAY, 8); (StdioModel.A_OFL_HEAD, 8)].

Definition llvm_binds : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = LLVM_MALLOC /\ ms_free B = LLVM_FREE
  /\ ms_calloc B = Some LLVM_CALLOC /\ ms_realloc B = None
  /\ ms_got_guard B = LLVM_GUARD_GOT /\ ms_guard B = LLVM_GUARD
  /\ AllocExtra B MR.

(* calloc_contract (lib/U/Contract.v:150-159) for calloc(1, MODEL_BYTES) at 0x13be0. Proved in
   lib/U/CallocModelGap.v (zlib_llvm_calloc_model), which imports this definition, so the definition
   stays while the contract no longer takes it as a premise. The start state is written
   `YK11.mkst`, the FP-aware form lib/U/Contract.v states calloc_contract in: by import order the
   bare `mkst` of this file resolves to lib/Lib/PropExec.v`s (bvmap_empty FP registers), which
   lib/U/Prog/link_mem.v exports after the YK11 import. *)
Definition llvm_calloc_model : Prop :=
  forall L A regs mem md (b : sbound),
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MODEL_BYTES ->
    res_ok_slots A b -> room_slots b MODEL_BYTES ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_CALLOC) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md MODEL_BYTES b c'
         /\ exists ms' md', c' = mkCfg ms' md'
         /\ forall i, 0 <= i < MODEL_BYTES ->
             mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

(* the budget: five blocks live at once at most, and 11316 bytes requested at most
   (8856 + 516 + 1304 + 2 x 40 + 2 x 320 is the peak of link/donors/REPORT.md section 4) *)
Definition llvm_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

Definition llvm_ls_laws (f : list byte -> list byte) : Prop :=
  (forall n b, lib_room b n -> llvm_room b) /\ (forall n b, lib_delta n b = b).

(* THE CONTRACT: exactly what lib/U/FrameAPI.v:52-53 asks of this entry, with the bindings, the
   frame_G meeting point as the premise the frame discharges. *)
Definition LLVMFuzzerTestOneInput_contract
    (f : list byte -> list byte) (GI : nat -> (word -> option byte) -> Prop) : Prop :=
  llvm_binds ->
  (forall a, in_globals llvm_G a -> in_globals frame_G a) ->
  G_local_c B llvm_G GI ->
  (forall mem, G_img_c B llvm_G mem -> GI 0%nat mem) ->
  forall j, (j < 4)%nat ->
  forall ra empty, LLVM_K <= SLOT_STACK -> ra mod 2 = 0 ->
    @lib_contract_o fx rc (out_shape f) B API SH SK f llvm_G frame_RELRO GI j LLVM_ENTRY ra empty
      SLOT_STACK.

End K.
