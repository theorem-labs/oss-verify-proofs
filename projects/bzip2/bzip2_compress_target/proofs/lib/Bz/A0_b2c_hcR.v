(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream BzCState BzCBlock BzCDriver CmpSess CmpSessB A0_b2c_hcV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition hc_rest (e e' : est) : Prop :=
  e_unseqToSeq e' = e_unseqToSeq e /\ e_mtfFreq e' = e_mtfFreq e /\ e_selector e' = e_selector e /\ e_selectorMtf e' = e_selectorMtf e /\
  e_len e' = e_len e /\ e_code e' = e_code e /\ e_rfreq e' = e_rfreq e /\ e_len_pack e' = e_len_pack e /\ e_arr1 e' = e_arr1 e /\ e_ftab e' = e_ftab e.

Lemma hc_rest_refl : forall e, hc_rest e e. Proof. intros e. unfold hc_rest. repeat split; reflexivity. Qed.
Lemma hc_rest_trans : forall e1 e2 e3, hc_rest e1 e2 -> hc_rest e2 e3 -> hc_rest e1 e3.
Proof.
  intros e1 e2 e3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold hc_rest.
  rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10. repeat split; assumption.
Qed.
Lemma hc_rest_set_rl : forall e r, hc_rest e (est_set_rl e r). Proof. intros. unfold hc_rest. repeat split; reflexivity. Qed.
Lemma hc_rest_set_modes : forall e a b c, hc_rest e (est_set_modes e a b c). Proof. intros. unfold hc_rest. repeat split; reflexivity. Qed.
Lemma hc_rest_set_outpos : forall e p, hc_rest e (est_set_outpos e p). Proof. intros. unfold hc_rest. repeat split; reflexivity. Qed.
Lemma hc_flush_rest : forall e, hc_rest e (hc_flush e). Proof. intros e. unfold hc_flush. apply hc_rest_set_rl. Qed.
Lemma hc_prep_rest : forall e, hc_rest e (hc_prep e). Proof. intros e. rewrite hc_prep_of_a. unfold hc_rest. repeat split; reflexivity. Qed.

Lemma ci_step_rest : forall e z, hc_rest e (fst (ci_step e z)).
Proof.
  intros e z. unfold ci_step. destruct (z_in z); [apply hc_rest_refl|]. destruct (inc64 _ _). cbn [fst]. apply hc_rest_set_rl.
Qed.

Lemma copy_input_rest : forall f e z p, hc_rest e (fst (fst (copy_input f e z p))).
Proof.
  induction f as [|f IH]; intros e z p; cbn [copy_input]; [apply hc_rest_refl|].
  destruct (NBLOCKMAX <=? e_nblock e); [apply hc_rest_refl|]. destruct (z_avail_in z =? 0); [apply hc_rest_refl|].
  destruct (e_mode e =? BZ_M_RUNNING).
  - pose proof (ci_step_rest e z) as R. destruct (ci_step e z) as [e1 z1]. cbn [fst] in R. exact (hc_rest_trans _ _ _ R (IH _ _ _)).
  - destruct (e_avail_in_expect e =? 0); [apply hc_rest_refl|].
    pose proof (ci_step_rest e z) as R. destruct (ci_step e z) as [e1 z1]. cbn [fst] in R.
    exact (hc_rest_trans _ _ _ (hc_rest_trans _ _ _ R (hc_rest_set_modes e1 _ _ _)) (IH _ _ _)).
Qed.

Lemma copy_output_rest : forall f e z p, hc_rest e (fst (fst (copy_output f e z p))).
Proof. intros f e z p. rewrite copy_output_frame. apply hc_rest_set_outpos. Qed.

(* [comment removed for export] *)
Lemma hc_out_rest : forall e z pout x z1 p1 b, hc_out e z pout = (x, z1, p1, b) -> hc_rest e x.
Proof.
  intros e z pout x z1 p1 b H. rewrite hc_out_aft in H.
  pose proof (copy_output_rest (Z.to_nat (z_avail_out z) + 1) e z pout) as R.
  destruct (copy_output (Z.to_nat (z_avail_out z) + 1) e z pout) as [[ec zc] qc]. cbn [fst] in R.
  unfold hc_aft in H.
  destruct (e_state_out_pos ec <? bw_numZ (e_bw ec)); [injection H as <- _ _ _; exact R|].
  destruct ((e_mode ec =? BZ_M_FINISHING) && (e_avail_in_expect ec =? 0) && isempty_RL_e ec)%bool; [injection H as <- _ _ _; exact R|].
  destruct ((e_mode (hc_prep ec) =? BZ_M_FLUSHING) && (e_avail_in_expect (hc_prep ec) =? 0) && isempty_RL_e (hc_prep ec))%bool;
    injection H as <- _ _ _; exact (hc_rest_trans _ _ _ R (hc_prep_rest ec)).
Qed.

(* [comment removed for export] *)
Lemma hc_out_ret_inuse : forall e z pout x z1 p1, e_mode e = BZ_M_FINISHING -> hc_out e z pout = (x, z1, p1, true) -> e_inUse x = e_inUse e.
Proof.
  intros e z pout x z1 p1 MD H. rewrite hc_out_aft in H.
  pose proof (copy_output_frame (Z.to_nat (z_avail_out z) + 1) e z pout) as R.
  destruct (copy_output (Z.to_nat (z_avail_out z) + 1) e z pout) as [[ec zc] qc]. cbn [fst] in R.
  assert (EI : e_inUse ec = e_inUse e) by (rewrite R; reflexivity).
  assert (EM : e_mode ec = BZ_M_FINISHING) by (rewrite R; exact MD).
  unfold hc_aft in H.
  destruct (e_state_out_pos ec <? bw_numZ (e_bw ec)); [injection H as <- _ _; exact EI|].
  destruct ((e_mode ec =? BZ_M_FINISHING) && (e_avail_in_expect ec =? 0) && isempty_RL_e ec)%bool; [injection H as <- _ _; exact EI|].
  replace (e_mode (hc_prep ec) =? BZ_M_FLUSHING) with false in H by (rewrite hc_prep_of_a; cbn [e_mode]; rewrite EM; reflexivity).
  cbn [andb] in H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma hc_out_ms_facts : forall e z pout e1 z1 p1, hc_out e z pout = (hc_prep e1, z1, p1, false) ->
  e_mode e1 = e_mode e /\ e_blockNo e1 = e_blockNo e /\ hc_rest e (hc_prep e1).
Proof.
  intros e z pout e1 z1 p1 H. pose proof (hc_out_rest _ _ _ _ _ _ _ H) as R. split; [| split; [| exact R]].
  - rewrite hc_out_aft in H.
    pose proof (copy_output_frame (Z.to_nat (z_avail_out z) + 1) e z pout) as F.
    destruct (copy_output (Z.to_nat (z_avail_out z) + 1) e z pout) as [[ec zc] qc]. cbn [fst] in F.
    unfold hc_aft in H.
    destruct (e_state_out_pos ec <? bw_numZ (e_bw ec)); [discriminate H|].
    destruct ((e_mode ec =? BZ_M_FINISHING) && (e_avail_in_expect ec =? 0) && isempty_RL_e ec)%bool; [discriminate H|].
    destruct ((e_mode (hc_prep ec) =? BZ_M_FLUSHING) && (e_avail_in_expect (hc_prep ec) =? 0) && isempty_RL_e (hc_prep ec))%bool; [discriminate H|].
    apply (f_equal (fun t => e_mode (fst (fst (fst t))))) in H. cbn [fst] in H. rewrite !hc_prep_of_a in H. cbn [e_mode] in H. rewrite <- H, F. reflexivity.
  - rewrite hc_out_aft in H.
    pose proof (copy_output_frame (Z.to_nat (z_avail_out z) + 1) e z pout) as F.
    destruct (copy_output (Z.to_nat (z_avail_out z) + 1) e z pout) as [[ec zc] qc]. cbn [fst] in F.
    unfold hc_aft in H.
    destruct (e_state_out_pos ec <? bw_numZ (e_bw ec)); [discriminate H|].
    destruct ((e_mode ec =? BZ_M_FINISHING) && (e_avail_in_expect ec =? 0) && isempty_RL_e ec)%bool; [discriminate H|].
    destruct ((e_mode (hc_prep ec) =? BZ_M_FLUSHING) && (e_avail_in_expect (hc_prep ec) =? 0) && isempty_RL_e (hc_prep ec))%bool; [discriminate H|].
    apply (f_equal (fun t => e_blockNo (fst (fst (fst t))))) in H. cbn [fst] in H. rewrite !hc_prep_of_a in H. cbn [e_blockNo] in H. rewrite F in H. cbn [e_blockNo est_set_outpos] in H. lia.
Qed.

(* [comment removed for export] *)
Lemma ci_step_out : forall e z, let '(e', z') := ci_step e z in z_outr z' = z_outr z /\ z_avail_out z' = z_avail_out z.
Proof.
  intros e z. unfold ci_step. destruct (z_in z) as [|c rest]; [split; reflexivity|].
  destruct (inc64 (z_tin_lo z) (z_tin_hi z)) as [lo hi]. split; reflexivity.
Qed.

Lemma copy_input_out : forall f e z p, let '(e', z', p') := copy_input f e z p in z_outr z' = z_outr z /\ z_avail_out z' = z_avail_out z.
Proof.
  induction f as [|f IH]; intros e z p; cbn [copy_input].
  - split; reflexivity.
  - destruct (NBLOCKMAX <=? e_nblock e); [split; reflexivity|].
    destruct (z_avail_in z =? 0); [split; reflexivity|].
    pose proof (ci_step_out e z) as CS. destruct (ci_step e z) as [e1 z1]. destruct CS as [C1 C2].
    destruct (e_mode e =? BZ_M_RUNNING).
    + specialize (IH e1 z1 true). destruct (copy_input f e1 z1 true) as [[e' z'] p']. destruct IH as [I1 I2]. split; congruence.
    + destruct (e_avail_in_expect e =? 0); [split; reflexivity|].
      match goal with |- context [copy_input f ?e2 z1 true] => specialize (IH e2 z1 true); destruct (copy_input f e2 z1 true) as [[e' z'] p'] end.
      destruct IH as [I1 I2]. split; congruence.
Qed.

Lemma hc_in_outr : forall lj e z pin pout x z1 p1 q1 b, hc_in lj e z pin pout = (x, z1, p1, q1, b) -> z_outr z1 = z_outr z /\ z_avail_out z1 = z_avail_out z.
Proof.
  intros lj e z pin pout x z1 p1 q1 b H. unfold hc_in in H.
  pose proof (copy_input_out (Z.to_nat (z_avail_in z) + 1) e z pin) as CO.
  destruct (copy_input (Z.to_nat (z_avail_in z) + 1) e z pin) as [[ec zc] pc].
  destruct (negb (e_mode ec =? BZ_M_RUNNING) && (e_avail_in_expect ec =? 0))%bool.
  - destruct (compressBlock _ _ lj) as [e2 y2]. injection H as _ <- _ _ _. exact CO.
  - destruct (NBLOCKMAX <=? e_nblock ec).
    + destruct (compressBlock _ _ lj) as [e2 y2]. injection H as _ <- _ _ _. exact CO.
    + destruct (z_avail_in zc =? 0); injection H as _ <- _ _ _; exact CO.
Qed.

End ACeilS1.
