(* Walk of diginet_frame_is_keepalive (src/diginet_frame.c:55-58 at 835f336c) in fuzz_frame.plain, 0x136c0.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import FrameBytes diginet_frame_is_keepalive_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* All the bytes bs at a, read at once. *)
Lemma rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

Theorem diginet_frame_is_keepalive_holds : diginet_frame_is_keepalive_contract.
Proof.
  unfold diginet_frame_is_keepalive_contract, DIGINET_FRAME_IS_KEEPALIVE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f cmd body bb
    Hf Hcmd Hbody BC BW BB.
  pose proof (bytes_at_bound rsegs m _ _ BC) as BCb. cbn [length] in BCb. change (Z.of_nat 1) with 1 in BCb.
  pose proof (bytes_at_bound rsegs m _ _ BB) as BBb.
  apply bytes_at_app in BW. destruct BW as [BW1 BW2].
  rewrite length_le8 in BW2. change (Z.of_nat 8) with 8 in BW2.
  replace (f + 32 + 8) with (f + 40) in BW2 by lia.
  pose proof (rd_all m _ _ 8 BW1 (length_le8 _)) as RB.
  pose proof (rd_all m _ _ 8 BW2 (length_le8 _)) as RL.
  pose proof (rd_all m _ _ 1 BC eq_refl) as RC.
  clear BW1 BW2 BC.
  assert (UC : bv_unsigned (b8 cmd) = cmd) by (exact (bz_b8 cmd Hcmd)).
  step.
  replace (bv_eqb (Z_to_bv 64 f) (Z_to_bv 64 0)) with false;
    [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite unsigned_lit_wrap; apply Z.eqb_neq;
                Z.div_mod_to_equations; lia].
  step. step.
  if_cases Ka.
  - zify_cond Ka. rewrite zxb_u, UC in Ka.
    assert (W : keepalive_of cmd (Z.of_nat (length bb)) bb = false).
    { unfold keepalive_of. rewrite (proj2 (Z.eqb_neq _ _) Ka). reflexivity. }
    step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
  - zify_cond Ka. rewrite zxb_u, UC in Ka.
    step. step. step.
    if_cases Kb.
    + zify_cond Kb.
      assert (N1 : Z.of_nat (length bb) <> 1) by (intro E; rewrite E in Kb; apply Kb; reflexivity).
      assert (W : keepalive_of cmd (Z.of_nat (length bb)) bb = false).
      { unfold keepalive_of. rewrite Ka, (proj2 (Z.eqb_neq _ _) N1). reflexivity. }
      step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
    + zify_cond Kb.
      assert (N1 : Z.of_nat (length bb) = 1) by (Z.div_mod_to_equations; lia).
      pose proof (rd1 m _ bb 0 BB ltac:(lia)) as RBB. change (Z.of_nat 0) with 0 in RBB. rewrite Z.add_0_r in RBB.
      remember (nth 0 bb (Z_to_bv 8 0)) as b eqn:Eb.
      step. step. step. step.
      apply evt_done.
      assert (A0 : v_sltiu (zxb b) 1 = Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)).
      { unfold v_sltiu, zxb. rewrite zxb_u. change (bv_wrap 64 1) with 1.
        unfold keepalive_of, at8, bz, b8. rewrite <- Eb, Ka, N1, !Z.eqb_refl. cbn [andb].
        pose proof (byte_range b) as Xb. destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E].
        - rewrite E. reflexivity.
        - rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_ge (bv_unsigned b) 1)) by lia. reflexivity. }
      rewrite A0. do 2 eexists. reflexivity.
Qed.
