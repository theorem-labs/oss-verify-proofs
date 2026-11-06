(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module names changed; 154 of its 182 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Prog/CF/SRCF.v, with its module paths changed; 71 of its 89 lines of code are new or changed and 164 lines of the source are left out. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/FrameAPI.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_egress; the unit links no calloc: frame_plain binds ms_calloc B = None; the RELRO list is the unit image's; addresses moved by symbol and offset; module path OSSVerify.Proofs.reac_repacer.fuzz_egress.lib. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.reac_repacer.fuzz_egress Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition ENTRY : Z := 0x12c6c.
Definition SLOT_STACK : Z := 65536.
Definition frame_G : list (Z * Z) := [].
Definition frame_RELRO : list (Z * Z) := [(0x1ca90, 160); (0x1cb38, 16)].

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
    ms_malloc B = 0x14240 /\ ms_free B = 0x14100 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4e120 /\ ms_got_guard B = 0x1cb30 /\
    ms_ctx B = 0x4e1b8 /\ ms_lock B = 0x4e1b0 /\ ms_libc B = 0x4e140 /\ ms_size_classes B = 0x10474 /\
    ms_small_cnt B = 0x104d4 /\ ms_med_cnt B = 0x104ef /\ ms_debruijn B = 0x10454 /\ ms_tp B = 0x2deb0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x4e570 /\ @sk_ofl_lock SK = 0x4e568 /\ @sk_threaded SK = 0x4e140 + 1 /\
    empty = 0x2ddc0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) /\
    (forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_g fx rc LS B (API rc) SH SK G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).

Definition frame_facts_ubsan (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x14240 /\ ms_free B = 0x14100 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4e120 /\ ms_got_guard B = 0x1cb30 /\
    ms_ctx B = 0x4e1b8 /\ ms_lock B = 0x4e1b0 /\ ms_libc B = 0x4e140 /\ ms_size_classes B = 0x10474 /\
    ms_small_cnt B = 0x104d4 /\ ms_med_cnt B = 0x104ef /\ ms_debruijn B = 0x10454 /\ ms_tp B = 0x2deb0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x4e570 /\ @sk_ofl_lock SK = 0x4e568 /\ @sk_threaded SK = 0x4e140 + 1 /\
    empty = 0x2ddc0 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Lemma frame_ubsan_split : frame_ubsan ->
  exists (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B API LS SH SK ra empty /\
    (forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
       (forall a, in_globals G a -> in_globals frame_G a) ->
       G_local_c B G GI ->
       (forall mem, G_img_c B G mem -> GI 0%nat mem) ->
       (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
          @lib_contract_g fx rc LS B (API rc) SH SK G frame_RELRO GI j ENTRY ra empty SLOT_STACK) ->
       Statements.ubsan_halts).
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H). exists B, API, LS, SH, SK, ra, empty.
  unfold frame_facts_ubsan. tauto.
Qed.
