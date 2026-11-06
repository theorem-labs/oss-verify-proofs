(* proves the UBSan contract of diginet_frame_is_keepalive (fuzz_transport.ubsan, 0x17ff4), with its alignment and null-pointer traps not taken. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_is_keepalive.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_frame_is_keepalive (src/diginet_frame.c:55-58 at 835f336c) in fuzz_transport.ubsan, 0x17ff4.
   The UBSan checks at 0x17ffc (f & 7 is not 0) and 0x18018 (f->body is 0) branch to the trap at
   0x18030; the premises f mod 8 = 0 and 0 < body keep them from firing. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import FrameBytes diginet_frame_is_keepalive_c.
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

(* The UBSan alignment check of a: the low 3 bits of the register value are 0. *)
Lemma al8 : forall x, x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x H. rewrite unsigned_lit_wrap. change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

(* Decide the branch to the alignment trap: not taken. *)
Ltac br_al H := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cd then _ else _) _ _ _ _) =>
      replace cd with false; [cbv iota | symmetry; unfold_cond; rewrite H; fold_lit_ux; reflexivity]
  end.

Theorem diginet_frame_is_keepalive_holds : diginet_frame_is_keepalive_contract.
Proof.
  unfold diginet_frame_is_keepalive_contract, DIGINET_FRAME_IS_KEEPALIVE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f cmd body bb
    Hf Hf8 Hcmd Hbody BC BW BB.
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
  pose proof (al8 f Hf8) as L7.
  (* 0x17ff4 beqz a0: f is not 0. *)
  step.
  replace (bv_eqb (Z_to_bv 64 f) (Z_to_bv 64 0)) with false;
    [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite unsigned_lit_wrap; apply Z.eqb_neq;
                Z.div_mod_to_equations; lia].
  (* 0x17ffc bnez (f & 7): the UBSan alignment trap, not taken. *)
  step. step. br_al L7.
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
      (* 0x18018 beqz f->body: the UBSan null-pointer trap, not taken (0 < body). *)
      step. step. br false.
      step. step. step.
      apply evt_done.
      assert (A0 : v_sltiu (zxb b) 1 = Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)).
      { unfold v_sltiu, zxb. rewrite zxb_u. change (bv_wrap 64 1) with 1.
        unfold keepalive_of, at8, bz, b8. rewrite <- Eb, Ka, N1, !Z.eqb_refl. cbn [andb].
        pose proof (byte_range b) as Xb. destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E].
        - rewrite E. reflexivity.
        - rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_ge (bv_unsigned b) 1)) by lia. reflexivity. }
      rewrite A0. do 2 eexists. reflexivity.
Qed.
