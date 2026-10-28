(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel PrintfModelX ApFmt CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with [], [] => true | x :: l1', y :: l2' => (x =? y) && zlist_eqb l1' l2' | _, _ => false end.
Lemma zlist_eqb_eq : forall l1 l2, zlist_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Fixpoint zrange (k : nat) (z : Z) : list Z := match k with O => [] | S k' => z :: zrange k' (z + 1) end.
Lemma zrange_In : forall k z x, z <= x < z + Z.of_nat k -> In x (zrange k z).
Proof.
  induction k as [|k IH]; intros z x H; [lia|]. cbn. destruct (Z.eq_dec z x); [left; exact e| right]. apply IH. lia.
Qed.

Lemma days_in_month_le31 : forall y m, days_in_month y m <= 31.
Proof. intros y m. unfold days_in_month. repeat (match goal with |- context [if ?c then _ else _] => destruct c; cbn end); lia. Qed.
Lemma dec2_bytes : forall n, 0 <= n <= 99 -> Forall (fun c => 0 < c < 256) (dec2 n).
Proof.
  intros n Hn. unfold dec2. pose proof (digit_range (n / 10)). pose proof (digit_range (n mod 10)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)). assert (0 <= n / 10 < 10) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  repeat constructor; lia.
Qed.
Lemma dec4_bytes : forall n, 0 <= n <= 9999 -> Forall (fun c => 0 < c < 256) (dec4 n).
Proof.
  intros n Hn. unfold dec4. pose proof (digit_range (n / 1000)). pose proof (digit_range ((n / 100) mod 10)). pose proof (digit_range ((n / 10) mod 10)). pose proof (digit_range (n mod 10)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)). pose proof (Z.mod_pos_bound (n / 100) 10 ltac:(lia)). pose proof (Z.mod_pos_bound (n / 10) 10 ltac:(lia)).
  assert (0 <= n / 1000 < 10) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  repeat constructor; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zpad2_checkf (n : Z) : bool := zlist_eqb (zpad 2 n) (dec2 n).
Lemma zpad2_check_all : check_from zpad2_checkf (Z.to_nat 100) 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma zpad2_dec2 : forall n, 0 <= n < 100 -> zpad 2 n = dec2 n.
Proof.
  intros n Hn. apply zlist_eqb_eq. apply (check_from_ok zpad2_checkf (Z.to_nat 100) 0); [exact zpad2_check_all| rewrite Z2Nat.id by lia; lia].
Qed.
Definition zpad4_checkf (n : Z) : bool := zlist_eqb (zpad 4 n) (dec4 n).
Lemma zpad4_check_all : check_from zpad4_checkf (Z.to_nat 10000) 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma zpad4_dec4 : forall n, 0 <= n < 10000 -> zpad 4 n = dec4 n.
Proof.
  intros n Hn. apply zlist_eqb_eq. apply (check_from_ok zpad4_checkf (Z.to_nat 10000) 0); [exact zpad4_check_all| rewrite Z2Nat.id by lia; lia].
Qed.

Lemma ct_gentime_gen15 : forall t, tm_valid t ->
  ct_gentime (t_year t) (t_mon t) (t_mday t) (t_hour t) (t_min t) (t_sec t) = gen15 t.
Proof.
  intros t (Y & MO & MD & HH & MI & SS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  unfold ct_gentime, gen15. rewrite zpad4_dec4 by lia. rewrite !zpad2_dec2 by lia. reflexivity.
Qed.

Lemma gen15_tm_bytes : forall t, tm_valid t -> Forall (fun c => 0 < c < 256) (gen15 t).
Proof.
  intros t (Y & MO & MD & HH & MI & SS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  unfold gen15. repeat (apply Forall_app; split); first [apply dec4_bytes; lia| apply dec2_bytes; lia| repeat constructor; unfold CH_Z; lia].
Qed.


Lemma gen15_zlength : forall t, zlength (gen15 t) = 15.
Proof. intros t. unfold zlength. rewrite gen15_length. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dec3_bytes : forall n, 0 <= n <= 999 -> Forall (fun c => 0 < c < 256) (dec3 n).
Proof.
  intros n Hn. unfold dec3. pose proof (digit_range (n / 100)). pose proof (digit_range ((n / 10) mod 10)). pose proof (digit_range (n mod 10)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)). pose proof (Z.mod_pos_bound (n / 10) 10 ltac:(lia)).
  assert (0 <= n / 100 < 10) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  repeat constructor; lia.
Qed.
Lemma firstn14_gen15 : forall t,
  firstn 14 (gen15 t) = dec4 (t_year t) ++ dec2 (t_mon t) ++ dec2 (t_mday t) ++ dec2 (t_hour t) ++ dec2 (t_min t) ++ dec2 (t_sec t).
Proof. intros t. reflexivity. Qed.
Lemma genstr_bytes : forall ts, Forall (fun c => 0 < c < 256) (genstr ts).
Proof.
  intros ts. pose proof (ts_ms_range ts) as MS. unfold genstr. destruct (gentime_adj ts) as [t|] eqn:GA.
  - pose proof (gentime_adj_valid ts t GA) as TV. pose proof TV as (Y & MO & MD & HH & MI & SS). pose proof (days_in_month_le31 (t_year t) (t_mon t)).
    rewrite firstn14_gen15.
    repeat (apply Forall_app; split); first [apply dec4_bytes; lia| apply dec2_bytes; lia| apply dec3_bytes; lia| repeat constructor; unfold CH_DOT, CH_Z; lia].
  - repeat (apply Forall_app; split); first [apply dec3_bytes; lia| repeat constructor; unfold CH_DOT, CH_Z; lia].
Qed.
(* [comment removed for export] *)
Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (map (fun z => Z_to_bv 8 z) s).
Proof.
  intros s H IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
  apply Forall_forall with (x := c) in H; [| exact Hc].
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite Z.mod_small in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.
Lemma genstr_nonul : forall ts, ~ In (Z_to_bv 8 0) (map (fun z => Z_to_bv 8 z) (genstr ts)).
Proof. intros ts. apply zb_nonul. apply genstr_bytes. Qed.
