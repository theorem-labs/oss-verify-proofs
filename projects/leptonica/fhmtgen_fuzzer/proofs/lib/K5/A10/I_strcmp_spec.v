(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint strcmp_idx_aux (b1 b2 : list byte) : nat :=
  match b1, b2 with
  | x :: b1', y :: b2' => if negb (bv_unsigned x =? bv_unsigned y) || (bv_unsigned x =? 0) then O else S (strcmp_idx_aux b1' b2')
  | _, _ => O
  end.
Definition strcmp_idx (b1 b2 : list byte) : Z := Z.of_nat (strcmp_idx_aux b1 b2).
Definition strcmp_sz (b1 b2 : list byte) : Z := strcmp_idx b1 b2 + 1.
(* [comment removed for export] *)
Definition strcmp_ok (b1 b2 : list byte) : Prop := strcmp_sz b1 b2 <= Z.of_nat (length b1) /\ strcmp_sz b1 b2 <= Z.of_nat (length b2).
Definition cmpx (x1 x2 : Z) : Z := if x1 <? x2 then -1 else if x2 <? x1 then 1 else 0.
Definition strcmp_res (b1 b2 : list byte) : Z :=
  let i := strcmp_idx_aux b1 b2 in
  match nth_error b1 i, nth_error b2 i with
  | Some x, Some y => cmpx (bv_unsigned x) (bv_unsigned y)
  | _, _ => 0
  end.

Example strcmp_res_ex1 : strcmp_res [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 0] [Z_to_bv 8 97; Z_to_bv 8 99; Z_to_bv 8 0] = -1.
Proof. reflexivity. Qed.
Example strcmp_res_ex2 : strcmp_res [Z_to_bv 8 97; Z_to_bv 8 0] [Z_to_bv 8 97; Z_to_bv 8 0] = 0 /\ strcmp_sz [Z_to_bv 8 97; Z_to_bv 8 0] [Z_to_bv 8 97; Z_to_bv 8 0] = 2.
Proof. split; reflexivity. Qed.

(* [comment removed for export] *)
Definition sc_pre (b1 b2 : list byte) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists z, nth_error b1 j = Some z /\ nth_error b2 j = Some z /\ bv_unsigned z <> 0.

Lemma sc_pre_S : forall b1 b2 k x, sc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some x -> bv_unsigned x <> 0 ->
  sc_pre b1 b2 (S k).
Proof.
  intros b1 b2 k x HP H1 H2 HX j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [exists x; auto|]. apply HP. lia.
Qed.

Lemma sc_pre_tl : forall x1 x2 b1 b2 k, sc_pre (x1 :: b1) (x2 :: b2) (S k) -> sc_pre b1 b2 k.
Proof. intros x1 x2 b1 b2 k HP j Hj. destruct (HP (S j) ltac:(lia)) as (z & E1 & E2 & NZ). exists z. cbn in E1, E2. auto. Qed.

Lemma idx_aux_step : forall z b1 b2, bv_unsigned z <> 0 -> strcmp_idx_aux (z :: b1) (z :: b2) = S (strcmp_idx_aux b1 b2).
Proof.
  intros z b1 b2 NZ. cbn [strcmp_idx_aux]. rewrite Z.eqb_refl. cbn [negb orb].
  rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma idx_aux_break : forall k b1 b2 x y,
  sc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  strcmp_idx_aux b1 b2 = k.
Proof.
  induction k as [|k IH]; intros b1 b2 x y HP H1 H2 HB.
  - destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in H1, H2. injection H1 as ->. injection H2 as ->. cbn [strcmp_idx_aux].
    destruct HB as [HB|HB].
    + rewrite (proj2 (Z.eqb_neq _ _) HB). reflexivity.
    + rewrite HB. cbn. rewrite orb_true_r. reflexivity.
  - destruct (HP 0%nat ltac:(lia)) as (z & Hz1 & Hz2 & Hnz).
    destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
    rewrite idx_aux_step by exact Hnz. f_equal.
    apply (IH b1' b2' x y); [exact (sc_pre_tl _ _ _ _ _ HP)| exact H1| exact H2| exact HB].
Qed.

Lemma idx_aux_ge : forall k b1 b2, sc_pre b1 b2 k -> (k <= strcmp_idx_aux b1 b2)%nat.
Proof.
  induction k as [|k IH]; intros b1 b2 HP; [lia|].
  destruct (HP 0%nat ltac:(lia)) as (z & Hz1 & Hz2 & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite idx_aux_step by exact Hnz. specialize (IH b1' b2' (sc_pre_tl _ _ _ _ _ HP)). lia.
Qed.

Lemma res_break : forall b1 b2 k x y, sc_pre b1 b2 k ->
  nth_error b1 k = Some x -> nth_error b2 k = Some y -> (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  strcmp_idx b1 b2 = Z.of_nat k /\ strcmp_res b1 b2 = cmpx (bv_unsigned x) (bv_unsigned y).
Proof.
  intros b1 b2 k x y HP H1 H2 HB.
  pose proof (idx_aux_break k b1 b2 x y HP H1 H2 HB) as E.
  split; [unfold strcmp_idx; rewrite E; reflexivity|]. unfold strcmp_res. rewrite E, H1, H2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma idx_aux_firstn : forall b1 b2 j, (strcmp_idx_aux b1 b2 < j)%nat ->
  strcmp_idx_aux (firstn j b1) (firstn j b2) = strcmp_idx_aux b1 b2.
Proof.
  induction b1 as [|x1 b1' IH]; intros b2 j HJ; [rewrite firstn_nil; reflexivity|].
  destruct j as [|j']; [lia|].
  destruct b2 as [|y1 b2']; [rewrite firstn_nil; reflexivity|].
  cbn [firstn strcmp_idx_aux]. cbn [strcmp_idx_aux] in HJ.
  destruct (_ || _); [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma nth_error_firstn_lt : forall (l : list byte) j i, (i < j)%nat -> nth_error (firstn j l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros j i Hij; [rewrite firstn_nil; destruct i; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma sc_trunc : forall b1 b2, strcmp_ok b1 b2 ->
  let j := Z.to_nat (strcmp_sz b1 b2) in
  strcmp_idx (firstn j b1) (firstn j b2) = strcmp_idx b1 b2
  /\ strcmp_res (firstn j b1) (firstn j b2) = strcmp_res b1 b2
  /\ strcmp_sz (firstn j b1) (firstn j b2) = strcmp_sz b1 b2
  /\ strcmp_ok (firstn j b1) (firstn j b2)
  /\ length (firstn j b1) = j /\ length (firstn j b2) = j.
Proof.
  intros b1 b2 (L1 & L2) j. unfold strcmp_sz, strcmp_idx in *.
  assert (HJ : (strcmp_idx_aux b1 b2 < j)%nat) by (unfold j, strcmp_sz, strcmp_idx; lia).
  pose proof (idx_aux_firstn b1 b2 j HJ) as EI.
  assert (LJ1 : length (firstn j b1) = j) by (rewrite length_firstn; unfold j, strcmp_sz, strcmp_idx; lia).
  assert (LJ2 : length (firstn j b2) = j) by (rewrite length_firstn; unfold j, strcmp_sz, strcmp_idx; lia).
  split; [rewrite EI; reflexivity|]. split.
  - unfold strcmp_res. rewrite EI. rewrite !nth_error_firstn_lt by exact HJ. reflexivity.
  - split; [rewrite EI; reflexivity|]. split; [unfold strcmp_ok, strcmp_sz, strcmp_idx; rewrite EI, LJ1, LJ2; unfold j, strcmp_sz, strcmp_idx; lia|].
    split; [exact LJ1| exact LJ2].
Qed.

Lemma cmpx_range : forall x y, -1 <= cmpx x y <= 1.
Proof. intros x y. unfold cmpx. destruct (x <? y); [lia|]. destruct (y <? x); lia. Qed.
