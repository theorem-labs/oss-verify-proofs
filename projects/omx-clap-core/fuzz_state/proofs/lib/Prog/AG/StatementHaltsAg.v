From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AgreeCap.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
Local Open Scope Z_scope.

(* StatementHalts.frame_facts_plain at the agreement shape's room: lib_room gives the allocator capacity CAP_AG
   (AgreeCap.v) in place of CAPMAX; slot_premise_plain over it, with the same conclusion. *)

Definition frame_facts_plain_ag (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z) : Prop :=
    ms_segs B = rsegs /\
    ms_malloc B = 0x16594 /\ ms_free B = 0x16454 /\ ms_realloc B = (Some 0x17e00) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x537a8 /\ ms_got_guard B = 0x221a0 /\
    ms_ctx B = 0x53840 /\ ms_lock B = 0x53838 /\ ms_libc B = 0x537c8 /\ ms_size_classes B = 0x10584 /\
    ms_small_cnt B = 0x105e4 /\ ms_med_cnt B = 0x105ff /\ ms_debruijn B = 0x10564 /\ ms_tp B = 0x33538 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x53bf8 /\ @sk_ofl_lock SK = 0x53bf0 /\ @sk_threaded SK = 0x537c8 + 1 /\
    empty = 0x33430 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAP_AG) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)).

Definition slot_premise_plain_ag : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_plain_ag B API LS SH SK empty ->
    forall (rc : RunCeil) (fx : FPState), @fuzz_state_slot_contract fx rc LS B (API rc) SH SK empty.
