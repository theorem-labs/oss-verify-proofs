From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import FrameAPI Img0.
From OSSVerify.libreac.fuzz_grant Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition frame_facts_plain (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
        ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x15964 /\ ms_free B = 0x15824 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x4f940 /\ ms_got_guard B = 0x1e358 /\
    ms_ctx B = 0x4f9d8 /\ ms_lock B = 0x4f9d0 /\ ms_libc B = 0x4f960 /\ ms_size_classes B = 0x10698 /\
    ms_small_cnt B = 0x106f8 /\ ms_med_cnt B = 0x10713 /\ ms_debruijn B = 0x1061c /\ ms_tp B = 0x2f6d0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 124 /\
    @sk_ofl_head SH = 0x4fd90 /\ @sk_ofl_lock SK = 0x4fd88 /\ @sk_threaded SK = 0x4f960 + 1 /\
    empty = 0x2f5e0 /\ 0 < empty < 2 ^ 62 /\
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

Definition grant_slot_plain : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_plain B API LS SH SK ra empty ->
    forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
      @lib_contract_g fx rc LS B (API rc) SH SK [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

Theorem plain_halts_of_frame : frame_plain -> grant_slot_plain -> Statements.plain_halts.
Proof.
  intros (B & API & LS & SH & SK & ra & empty & H) SLOT.
  assert (HF : frame_facts_plain B API LS SH SK ra empty) by (unfold frame_facts_plain; tauto).
  repeat match type of H with _ /\ _ => destruct H as [_ H] end.
  apply (H [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. exact (SLOT B API LS SH SK ra empty HF rc fx j Hj).
Qed.
