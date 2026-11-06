From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import ContractCF FrameCF FrameFactsCG AgBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require LLVMFuzzerTestOneInput LinkCG.
Import ListNotations.
Local Open Scope Z_scope.

(* The ubsan cut-free slot of fuzz_state (lib_contract_cg, for ubsan_agrees) from the frame's facts: the halts frame
   facts with the agreement shape's room (frame_facts_ag), the frame's cut-free allocator contracts (realloc
   included) and the budget law limlaw_at (2 ^ 34) (zlib_limit gives it for the unit's allocator); the room comes from
   AgreeCap.room_cf_of_limit33 (the U run makes the plain run's requests, proved below 2^33). *)
Definition frame_facts_ag (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z) : Prop :=
    ms_segs B = rsegs /\
    ms_malloc B = 0x16c7c /\ ms_free B = 0x16b3c /\ ms_realloc B = (Some 0x184e8) /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x53e98 /\ ms_got_guard B = 0x22888 /\
    ms_ctx B = 0x53f30 /\ ms_lock B = 0x53f28 /\ ms_libc B = 0x53eb8 /\ ms_size_classes B = 0x10584 /\
    ms_small_cnt B = 0x105e4 /\ ms_med_cnt B = 0x105ff /\ ms_debruijn B = 0x10564 /\ ms_tp B = 0x33c28 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x542e8 /\ @sk_ofl_lock SK = 0x542e0 /\ @sk_threaded SK = 0x53eb8 + 1 /\
    empty = 0x33b20 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAP_AG) /\
    (forall (rc : RunCeil) (fx : FPState), @FrameAPI.frame_allocator rc fx B (API rc)).

Theorem fuzz_state_slot_cg :
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
    (SK : sink_syms) (empty : Z),
    frame_facts_ag B API LS SH SK empty ->
    (forall (rc : RunCeil) (fx : FPState), @malloc_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @free_contract_cf fx rc B (API rc)) ->
    (forall (rc : RunCeil) (fx : FPState), @free_null_contract_cf fx B) ->
    (forall (rc : RunCeil) (fx : FPState) pc, ms_realloc B = Some pc ->
       realloc_contract_cf B (API rc) pc /\ realloc_null_contract_cf B (API rc) pc) ->
    (forall rc : RunCeil, @limlaw_at rc (2 ^ 34) B (API rc)) ->
    forall (rc : RunCeil) (fx : FPState) (j : nat) (ra : Z), (j < 4)%nat -> ra mod 2 = 0 ->
      @lib_contract_cg fx rc LS B (API rc) SH SK omx_G frame_RELRO (omx_GI B) j FUZZ_STATE_ENTRY ra empty
        FUZZ_STATE_STK.
Proof.
  intros B API LS SH SK empty FF MCF FCF FNCF RCF LIMLAW.
  pose proof room_cf_of_limit33 as ROOM33.
  assert (FFcg : frame_facts_cg B API LS SH SK empty).
  { destruct FF as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & FA).
    assert (FAcf : forall (rc : RunCeil) (fx : FPState), @FrameCF.frame_allocator rc fx B (API rc)).
    { intros rc fx. apply (@ag_frame_allocator fx rc B (API rc) (2 ^ 34) (LIMLAW rc) ROOM33 (FA rc fx)).
      - assumption.
      - exact (MCF rc fx).
      - exact (FCF rc fx).
      - exact (FNCF rc fx).
      - intros pc Hpc. destruct (RCF rc fx pc Hpc) as (R1 & R2). split; [exact R1 | exact R2]. }
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23 (conj H24 (conj H25 (conj H26 (conj H27 (conj H28 (conj H29 (conj H30 (conj H31 FAcf))))))))))))))))))))))))))))))). }
  exact (LinkCG.slot_premise_cg_proved B API LS SH SK empty FFcg).
Qed.
