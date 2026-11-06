From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_live_c bcmp_c check_reject_clean_c.
Open Scope Z_scope.

Lemma check_reject_clean_empty : forall m, mem_inv rsegs m ->
  bytes_at rsegs m CHECK_REJECT_CLEAN_EMPTY (repeat (Z_to_bv 8 0) 56).
Proof.
  intros m MI. unfold CHECK_REJECT_CLEAN_EMPTY.
  apply ro_bytes_at; [exact MI | lia | rewrite repeat_length; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma check_reject_clean_rc : forall rc, - 2 ^ 31 <= rc < 2 ^ 31 -> rc <> 0 ->
  bv_unsigned (Z_to_bv 64 rc) <> 0.
Proof.
  intros rc R NZ. rewrite unsigned_lit_wrap.
  destruct (Z_lt_le_dec rc 0) as [N|P].
  - rewrite <- (Z.mod_add rc 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. exact NZ.
Qed.

Theorem check_reject_clean_holds : fuzz_alloc_live_contract -> bcmp_contract -> check_reject_clean_contract.
Proof.
  intros LIVE BC. unfold check_reject_clean_contract, CHECK_REJECT_CLEAN, CHECK_REJECT_CLEAN_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rc lo
    E0 RC NZ HD HL HMI ST LO DJD DJL.
  subst a0.
  pose proof (check_reject_clean_rc rc RC NZ) as HRC.
  unfold G_LIVE in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  cbn [repeat] in HD.
  carve_frame 16%nat ST.
  do 4 zstep.
  if_cases HC.
  { exfalso. unfold bv_eqb in HC. apply Z.eqb_eq in HC. apply HRC. rewrite HC. reflexivity. }
  do 7 zstep.
  call (BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (repeat (Z_to_bv 8 0) 56) (repeat (Z_to_bv 8 0) 56) 0).
  { exact HD. }
  { rewrite unsigned_lit by lia. apply check_reject_clean_empty. assumption. }
  { vm_compute. reflexivity. }
  { assumption. }
  zstep.
  if_false.
  zstep.
  eapply evt_cut; [eapply LIVE; eassumption|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13c20)) with (Z_to_bv 64 0x13c20) by (apply bv_eq; vm_compute; reflexivity).
  zstep.
  if_cases HC2.
  { exfalso. unfold bv_eqb in HC2. rewrite Z.eqb_refl in HC2. discriminate. }
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
