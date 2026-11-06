From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d YM05 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Contract FrameAPI SlotAgree ZAllocator FrameProof CallocCf.
Import ListNotations.
Local Open Scope Z_scope.

(* UBSan build. The harness's two calloc calls (fuzz_link.c:771-772), both calloc(1, n) at link's calloc 0x17ad0:
   - the model block, n = sizeof (struct model) = 8856: 0x13be0, a0 = 1 (0x13bdc), a1 = 0x2298 (0x13bd4-0x13bd8);
   - the marks block, n = sizeof (struct reac_served_marks) = 516: 0x13bf0, a0 = 1 (0x13be8), a1 = 0x204 (0x13bec).
   The frame's calloc_contract (lib/U/Contract.v) asks m * n < 2^62 (malloc's own bound), so it covers both. For 8856
   the request goes to malloc, then to __malloc_allzerop (U/CallocAZ.az_SR) and, when the slot is not known to be
   zero, through the page loop of U/CallocBig.run_clear_big. Under the allocation budget (room_slots b n) calloc
   does not return 0, so the harness's abort on a null block (fuzz_link.c:774) is not reached: the caller gets a
   fresh, live block of n zero bytes, 16-aligned, with the allocator state accounted (malloc_ret). *)
Definition CALLOC_PC : Z := 0x17ad0.
Definition MODEL_SIZE : Z := 8856.
Definition MARKS_SIZE : Z := 516.

Section S.
Context {rc : RunCeil} {fx : FPState}.

Definition calloc_one_post (B : malloc_syms) (API : AllocAPI B) L A regs mem md (n : Z) (b : sbound)
    (c' : config) : Prop :=
  malloc_ret B API CALLOC_STACK L A regs mem md n b c' /\
  exists ms' md', c' = mkCfg ms' md' /\
    forall i, 0 <= i < n -> mbyte (ms_segs B) (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0).

(* calloc(1, n) for any n below malloc's bound *)
Lemma calloc_one_site : forall (B : malloc_syms) (API : AllocAPI B) pc,
  calloc_contract B API pc -> ms_calloc B = Some pc ->
  forall n, 0 <= n < 2 ^ 62 ->
  forall L A regs mem md (b : sbound),
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_slots b n ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md)
      (calloc_one_post B API L A regs mem md n b).
Proof.
  intros B API pc HCAL HC n Hn L A regs mem md b PRE RO H10 H11 HR HRm.
  pose proof (HCAL L A regs mem md 1 n b PRE RO H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) HC HR
    ltac:(rewrite Z.mul_1_l; exact HRm)) as H.
  rewrite Z.mul_1_l in H. exact H.
Qed.

Lemma calloc_model_site : forall (B : malloc_syms) (API : AllocAPI B),
  calloc_contract B API CALLOC_PC -> ms_calloc B = Some CALLOC_PC ->
  forall L A regs mem md (b : sbound),
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MODEL_SIZE ->
    res_ok_slots A b -> room_slots b MODEL_SIZE ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs B))) md)
      (calloc_one_post B API L A regs mem md MODEL_SIZE b).
Proof. intros B API HCAL HC. apply (calloc_one_site B API CALLOC_PC HCAL HC). unfold MODEL_SIZE. lia. Qed.

Lemma calloc_marks_site : forall (B : malloc_syms) (API : AllocAPI B),
  calloc_contract B API CALLOC_PC -> ms_calloc B = Some CALLOC_PC ->
  forall L A regs mem md (b : sbound),
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MARKS_SIZE ->
    res_ok_slots A b -> room_slots b MARKS_SIZE ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs B))) md)
      (calloc_one_post B API L A regs mem md MARKS_SIZE b).
Proof. intros B API HCAL HC. apply (calloc_one_site B API CALLOC_PC HCAL HC). unfold MARKS_SIZE. lia. Qed.

(* from the frame's allocator record (lib/U/FrameAPI.v frame_allocator, the record frame_ubsan gives) *)
Lemma calloc_model_frame : forall (B : malloc_syms) (API : AllocAPI B),
  frame_allocator B API -> ms_calloc B = Some CALLOC_PC ->
  forall L A regs mem md (b : sbound),
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MODEL_SIZE ->
    res_ok_slots A b -> room_slots b MODEL_SIZE ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs B))) md)
      (calloc_one_post B API L A regs mem md MODEL_SIZE b).
Proof.
  intros B API FA HC. destruct FA as (_ & _ & _ & _ & HCAL & _).
  exact (calloc_model_site B API (HCAL CALLOC_PC HC) HC).
Qed.

(* link's own allocator (lib/U/ZAllocator.v zlib_API over lib/U/Reusable/YH02.v src0_msyms) *)
Lemma zlib_calloc_model : forall L A regs mem md (b : sbound),
  call_pre_k src0_msyms (aa_MR (@zlib_API rc)) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs src0_msyms) mem ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MODEL_SIZE ->
  res_ok_slots A b -> room_slots b MODEL_SIZE ->
  SR (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs src0_msyms))) md)
    (calloc_one_post src0_msyms (@zlib_API rc) L A regs mem md MODEL_SIZE b).
Proof. exact (calloc_model_frame src0_msyms (@zlib_API rc) (zlib_frame_allocator rc fx) eq_refl). Qed.

Lemma zlib_calloc_marks : forall L A regs mem md (b : sbound),
  call_pre_k src0_msyms (aa_MR (@zlib_API rc)) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs src0_msyms) mem ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MARKS_SIZE ->
  res_ok_slots A b -> room_slots b MARKS_SIZE ->
  SR (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs src0_msyms))) md)
    (calloc_one_post src0_msyms (@zlib_API rc) L A regs mem md MARKS_SIZE b).
Proof.
  pose proof (zlib_frame_allocator rc fx) as FA. destruct FA as (_ & _ & _ & _ & HCAL & _).
  exact (calloc_marks_site src0_msyms (@zlib_API rc) (HCAL CALLOC_PC eq_refl) eq_refl).
Qed.

(* the cut-free form the agreement route uses (lib/U/SlotAgree.v calloc_contract_cf, room_cf) *)
Lemma calloc_one_site_cf : forall (B : malloc_syms) (API : AllocAPI B) pc,
  calloc_contract_cf B API pc -> ms_calloc B = Some pc ->
  forall n, 0 <= n < 2 ^ 62 ->
  forall L A regs mem md (b : sbound),
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md)
      (calloc_one_post B API L A regs mem md n b).
Proof.
  intros B API pc HCAL HC n Hn L A regs mem md b PRE RO H10 H11 HR HRm.
  pose proof (HCAL L A regs mem md 1 n b PRE RO H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) HC HR
    ltac:(rewrite Z.mul_1_l; exact HRm)) as H.
  rewrite Z.mul_1_l in H. exact H.
Qed.

Lemma zlib_calloc_model_cf : forall L A regs mem md (b : sbound),
  call_pre_k src0_msyms (aa_MR (@zlib_API rc)) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs src0_msyms) mem ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 MODEL_SIZE ->
  res_ok_slots A b -> room_cf md b MODEL_SIZE ->
  SRcf src0_msyms (mkCfg (mkst regs (Z_to_bv 64 CALLOC_PC) mem (seg_rom (ms_segs src0_msyms))) md)
    (calloc_one_post src0_msyms (@zlib_API rc) L A regs mem md MODEL_SIZE b).
Proof.
  apply (calloc_one_site_cf src0_msyms (@zlib_API rc) CALLOC_PC (@zlib_calloc_contract_cf fx rc CALLOC_PC) eq_refl).
  unfold MODEL_SIZE. lia.
Qed.

End S.
