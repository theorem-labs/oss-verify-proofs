(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec ClaVerdict HTSpec HUSel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition tin_of (data : list byte) : tin :=
  TIN (Z.of_nat (ht_payload_len data)) (Z.of_nat (config_len data)) (byte_at data 2) (32768 <=? cfg_word data).

Lemma W1_line : forall neg, W1 (lineZ neg) = W 1 (line_ht neg).
Proof. intros [|]; reflexivity. Qed.
Lemma W1_lines : forall neg c, W1 (rep (lineZ neg) c) = W 1 (lines_ht neg c).
Proof.
  intros neg c. induction c as [|c IH]; [reflexivity|]. cbn [rep lines_ht]. unfold W1, W in *.
  rewrite !map_app. rewrite IH. f_equal. exact (W1_line neg).
Qed.

Lemma tgt_of_content : forall data fs,
  t_eq (TGT (t_n (tin_of data) <? 11) (Z.to_nat (t_calls (tin_of data))) (t_cnt (tin_of data)) fs) (t_target_ht data fs).
Proof.
  intros data fs. eapply t_eq_trans; [|exact (t_target_ht_split data fs)].
  assert (Hneg : (t_n (tin_of data) <? 11) = ht_neg data).
  { unfold tin_of, ht_neg. cbn [t_n]. destruct (Nat.ltb_spec (ht_payload_len data) 11); [apply Z.ltb_lt | apply Z.ltb_ge]; lia. }
  assert (Hcalls : Z.to_nat (t_calls (tin_of data)) = ht_calls data).
  { unfold t_calls, tin_of, ht_calls. cbn [t_cl t_b2]. destruct (config_len data) as [|c] eqn:Hc.
    - reflexivity.
    - replace (Z.of_nat (S c) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (Z.mod_pos_bound (byte_at data 2) 4 ltac:(lia)). rewrite Z2Nat.inj_add by lia. reflexivity. }
  rewrite Hneg, Hcalls. unfold TGT. rewrite W1_line.
  replace (ht_calls data - 1)%nat with (Init.Nat.pred (ht_calls data)) by lia. rewrite W1_lines.
  assert (Hex : Z_to_bv 64 0 = exit_code (ht_status data)) by reflexivity.     (* [comment removed for export] *)
  rewrite Hex. apply t_eq_refl.
Qed.
