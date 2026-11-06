(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths, module names and addresses changed; 56 of its 83 lines of code are new or changed and 140 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract OutForm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0.
From OSSVerify.reac_pw.fuzz_link Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := 0x13a30.
Definition SLOT_STACK : Z := 65536.
Definition frame_G : list (Z * Z) := [(0x221d8, 4)].
Definition frame_RELRO : list (Z * Z) := [(0x20fe8, 296); (0x21118, 16); (0x22150, 136); (0x221dc, 92)].

Lemma wx_apart_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Definition frame_allocator {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract B API /\ free_contract B API /\ free_null_contract B /\
  (forall pc, ms_realloc B = Some pc -> realloc_contract B API pc /\ realloc_null_contract B API pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract B API pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\ libc_no_locks B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a).

Definition frame_ubsan : Prop :=
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x17d48 /\ ms_free B = 0x17c08 /\ ms_realloc B = None /\ ms_calloc B = (Some 0x17ad0) /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x960b8 /\ ms_got_guard B = 0x21110 /\
    ms_ctx B = 0x96150 /\ ms_lock B = 0x96148 /\ ms_libc B = 0x960d8 /\ ms_size_classes B = 0x10788 /\
    ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10803 /\ ms_debruijn B = 0x10768 /\ ms_tp B = 0x75e48 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x96508 /\ @sk_ofl_lock SK = 0x96500 /\ @sk_threaded SK = 0x960d8 + 1 /\
    empty = 0x323a0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (f : list byte -> list byte) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).

Definition frame_facts_ubsan (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x17d48 /\ ms_free B = 0x17c08 /\ ms_realloc B = None /\ ms_calloc B = (Some 0x17ad0) /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x960b8 /\ ms_got_guard B = 0x21110 /\
    ms_ctx B = 0x96150 /\ ms_lock B = 0x96148 /\ ms_libc B = 0x960d8 /\ ms_size_classes B = 0x10788 /\
    ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10803 /\ ms_debruijn B = 0x10768 /\ ms_tp B = 0x75e48 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x96508 /\ @sk_ofl_lock SK = 0x96500 /\ @sk_threaded SK = 0x960d8 + 1 /\
    empty = 0x323a0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma frame_ubsan_split : frame_ubsan ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B API LS SH SK ra empty /\
    (forall (f : list byte -> list byte) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_o fx rc (out_shape f) B (API rc) SH SK f G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_ubsan. tauto.
Qed.
