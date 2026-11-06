From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK15 YM05 YO0f YO0d YO09 YO0o YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition llvm_frame (rc : RunCeil) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms) : Prop :=
  (forall fx : FPState, @frame_allocator rc fx B API) /\ errno_addr B + 4 <= @alloc_ceiling rc /\
  ms_ctx B = 0x4e968 /\ ms_lock B = 0x4e960 /\ ms_libc B = 0x4e8f0 /\ ms_size_classes B = 0x10414 /\
  ms_small_cnt B = 0x10474 /\ ms_med_cnt B = 0x1048f /\ ms_debruijn B = 0x103f4 /\ ms_tp B = 0x2e660 /\
  ms_errno_off B = -164 /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
  @sk_ofl_head SH = 0x4ed20 /\ @sk_ofl_lock SK = 0x4ed18 /\ @sk_threaded SK = 0x4e8f0 + 1.

Definition slot_contract_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B (API) SH SK ->
    LLVMFuzzerTestOneInput_contract B API.

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

Theorem plain_halts_of_slot : slot_contract_all -> frame_plain -> Statements.plain_halts.
Proof.
  intros SLOT (B & API & LS & SH & SK & ra & empty & H).
  assert (Hs : ms_segs B = rsegs) by tauto. assert (Hra : ra mod 2 = 0) by tauto.
  assert (Hm : ms_malloc B = 0x14788) by tauto. assert (Hf : ms_free B = 0x14648) by tauto.
  assert (Hg : ms_guard B = 0x4e8d0) by tauto. assert (Hgg : ms_got_guard B = 0x1d2e0) by tauto.
  assert (HK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) by tauto.
  assert (HD : forall n b, @lib_delta LS n b = b) by tauto.
  assert (HR : forall b n, @lib_room LS b n -> llvm_room b).
  { assert (HR0 : forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX)
      by tauto.
    intros b n Hb. destruct (HR0 b n Hb) as (H1 & H2 & H3). unfold llvm_room. rewrite H3. unfold CAPMAX. lia. }
  assert (HA : forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) by tauto.
  assert (Hel : forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) by tauto.
  assert (HFR : forall rc : RunCeil, llvm_frame rc B (API rc) SH SK).
  { intros rc. unfold llvm_frame. split; [intros fx; exact (HA rc fx)|]. split; [exact (Hel rc)|]. tauto. }
  repeat match type of H with _ /\ _ => apply proj2 in H end.
  apply (H llvm_G llvm_GI llvm_G_inside (llvm_GI_local B) (llvm_GI_img B)).
  intros rc fx j Hj.
  destruct (HA rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
  apply (SLOT rc fx LS B (API rc) SH SK (HFR rc)).
  - unfold llvm_binds, LLVM_MALLOC, LLVM_FREE, LLVM_GUARD_GOT, LLVM_GUARD.
    repeat (split; [assumption|]). exact HX.
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, SLOT_STACK. lia.
  - exact (ret_ok_of_even ra Hra).
Qed.
