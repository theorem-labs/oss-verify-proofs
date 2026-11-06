(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/Statement.v, with its module paths and addresses changed; 7 of its 61 lines of code are new or changed and 6 lines of the source are left out. *)
(* Modified by Theorem Labs: libreac/fuzz_decode's released lib/U/Prog/Statement.v for libdiginet/fuzz_decode,
   module paths changed and the image values moved to fuzz_decode.ubsan (those of lib/U/FrameAPI.v: malloc 0x15028,
   free 0x14ee8, the guard 0x4ef30 and its GOT slot 0x1d948, the libc globals and the stdio sink words). The unit links
   no calloc, so llvm_frame binds ms_calloc B = None. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0s YK15 YM05 YO0f YO0d YO09 YO0o YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.libdiginet.fuzz_decode Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition llvm_frame (rc : RunCeil) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms) : Prop :=
  (forall fx : FPState, @frame_allocator rc fx B API) /\ errno_addr B + 4 <= @alloc_ceiling rc /\
  ms_calloc B = None /\
  ms_ctx B = 0x4efc8 /\ ms_lock B = 0x4efc0 /\ ms_libc B = 0x4ef50 /\ ms_size_classes B = 0x10480 /\
  ms_small_cnt B = 0x104e0 /\ ms_med_cnt B = 0x104fb /\ ms_debruijn B = 0x10460 /\ ms_tp B = 0x2ecc0 /\
  ms_errno_off B = -164 /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
  @sk_ofl_head SH = 0x4f380 /\ @sk_ofl_lock SK = 0x4f378 /\ @sk_threaded SK = 0x4ef50 + 1.

Definition slot_contract_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK ->
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

Theorem ubsan_halts_of_slot : slot_contract_all -> frame_ubsan -> Statements.ubsan_halts.
Proof.
  intros SLOT (B & API & LS & SH & SK & ra & empty & H).
  assert (Hs : ms_segs B = rsegs) by tauto. assert (Hra : ra mod 2 = 0) by tauto.
  assert (Hm : ms_malloc B = 0x15028) by tauto. assert (Hf : ms_free B = 0x14ee8) by tauto.
  assert (Hg : ms_guard B = 0x4ef30) by tauto. assert (Hgg : ms_got_guard B = 0x1d948) by tauto.
  assert (HK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) by tauto.
  assert (HD : forall n b, @lib_delta LS n b = b) by tauto.
  assert (HR : forall b n, @lib_room LS b n -> llvm_room b) by (unfold llvm_room; tauto).
  assert (HA : forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) by tauto.
  assert (Hel : forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) by tauto.
  assert (HFR : forall rc : RunCeil, llvm_frame rc B (API rc) SH SK).
  { intros rc. unfold llvm_frame. split; [intros fx; exact (HA rc fx)|]. split; [exact (Hel rc)|]. tauto. }
  repeat match type of H with _ /\ _ => apply proj2 in H end.
  apply (H llvm_G llvm_GI llvm_G_inside (llvm_GI_local B) (llvm_GI_img B)).
  intros rc fx j Hj.
  assert (HX : AllocExtra B (aa_MR (API rc))).
  { pose proof (HA rc fx) as HAX. unfold frame_allocator in HAX. tauto. }
  apply (SLOT rc fx LS B (API rc) SH SK (HFR rc)).
  - unfold llvm_binds, LLVM_MALLOC, LLVM_FREE, LLVM_GUARD_GOT, LLVM_GUARD.
    repeat (split; [assumption|]). exact HX.
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - exact (ret_ok_of_even ra Hra).
Qed.
