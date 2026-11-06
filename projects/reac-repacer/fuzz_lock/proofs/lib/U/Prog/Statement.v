(* fuzz_lock.ubsan halts, from the frame step for a return of 0 or -1 (U/Prog/FrameRet.v frame_ret_hyp), the
   contracts of check_no_overread and check_lookup, and the walk of LLVMFuzzerTestOneInput: the shape of
   libreac/fuzz_decode's released lib/U/Prog/Statement.v (25e3d17bdb50). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0s YK15 YM05 YO0f YO0d YO09 YO0o YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet check_no_overread_c check_lookup_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_end.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* the two harness functions meet their contracts for every allocator the frame gives *)
Definition checks_hold : Prop :=
  forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms),
    llvm_binds B API -> @llvm_frame rc B API SH SK ->
    @check_no_overread_contract fx rc B API /\ @check_lookup_contract fx rc B API.

Definition slot_contract_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    @llvm_frame rc B API SH SK ->
    (forall fx' : FPState, @check_no_overread_contract fx' rc B API) ->
    (forall fx' : FPState, @check_lookup_contract fx' rc B API) ->
    @LLVMFuzzerTestOneInput_contract fx rc LS B API SH SK.

Lemma llvm_G_inside : forall a, in_globals llvm_G a -> in_globals frame_G a.
Proof. intros a (lo & len & Hin & _). destruct Hin. Qed.

Lemma llvm_GI_local : forall B, G_local_c B llvm_G llvm_GI.
Proof. intros B j m m' _ _. exact I. Qed.

Lemma llvm_GI_img : forall B mem, G_img_c B llvm_G mem -> llvm_GI 0%nat mem.
Proof. intros B mem _. exact I. Qed.

Lemma ret_ok_of_even : forall ra, ra mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 ra).
Proof.
  intros ra H. apply ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Theorem ubsan_halts_of_slot : slot_contract_all -> checks_hold -> frame_ret_hyp -> Statements.ubsan_halts.
Proof.
  intros SLOT CHK FRH.
  destruct (FRH lock_ret lock_ret_cases) as (B & API & LS & SH & SK & ra & empty & H).
  assert (Hs : ms_segs B = rsegs) by tauto. assert (Hra : ra mod 2 = 0) by tauto.
  assert (Hm : ms_malloc B = 0x14178) by tauto. assert (Hf : ms_free B = 0x14038) by tauto.
  assert (Hg : ms_guard B = 0x4e0e0) by tauto. assert (Hgg : ms_got_guard B = 0x1caf8) by tauto.
  assert (HK : forall pl fs K, @LIBK LS pl fs K = K (LL (lock_ret pl) fs [])) by tauto.
  assert (HD : forall n b, @lib_delta LS n b = b) by tauto.
  assert (HR : forall b n, @lib_room LS b n -> llvm_room b).
  { unfold llvm_room. intros b n Hb.
    assert (HRK : forall b' n', @lib_room LS b' n' -> sb_live b' <= 64 /\ 0 <= sb_bytes b' <= 2 ^ 28 /\
      sb_cap b' = CAPMAX) by tauto.
    destruct (HRK b n Hb) as (R1 & R2 & R3). unfold CAPMAX in *. lia. }
  assert (HA : forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) by tauto.
  assert (Hel : forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) by tauto.
  assert (HFR : forall rc : RunCeil, @llvm_frame rc B (API rc) SH SK).
  { intros rc. unfold llvm_frame. split; [intros fx; exact (HA rc fx)|]. split; [exact (Hel rc)|]. tauto. }
  repeat match type of H with _ /\ _ => apply proj2 in H end.
  apply (H llvm_G llvm_GI llvm_G_inside (llvm_GI_local B) (llvm_GI_img B)).
  intros rc fx j Hj.
  assert (HX : AllocExtra B (aa_MR (API rc))).
  { pose proof (HA rc fx) as HAX. unfold frame_allocator in HAX. tauto. }
  assert (BI : llvm_binds B (API rc)).
  { unfold llvm_binds, LLVM_MALLOC, LLVM_FREE, LLVM_GUARD_GOT, LLVM_GUARD.
    repeat (split; [assumption|]). exact HX. }
  apply (SLOT rc fx LS B (API rc) SH SK (HFR rc)
           (fun fx' => proj1 (CHK rc fx' B (API rc) SH SK BI (HFR rc)))
           (fun fx' => proj2 (CHK rc fx' B (API rc) SH SK BI (HFR rc)))).
  - exact BI.
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - exact (ret_ok_of_even ra Hra).
Qed.
