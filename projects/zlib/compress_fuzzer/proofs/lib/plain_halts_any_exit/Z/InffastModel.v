(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zmask_pow2 : forall n, 0 <= n < 32 -> zmask n = 2 ^ n - 1.
Proof.
  intros n Hn. unfold zmask. rewrite Z.shiftl_1_l. apply wrap32_id.
  split; [pose proof (Z.pow_pos_nonneg 2 n); lia|].
  pose proof (Z.pow_lt_mono_r 2 n 32 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. apply Z.pow_le_mono_r; lia. Qed.

Fixpoint cpn (x : ffx) (n : nat) (f : ffs) : ffs :=
  match n with
  | O => f
  | S n' => cpn x n' (cp1 x f)
  end.

Lemma cpn_add : forall x a b f, cpn x (a + b) f = cpn x b (cpn x a f).
Proof. intros x a. induction a as [|a IH]; intros b f; [reflexivity|]. cbn [cpn Nat.add]. apply IH. Qed.

Lemma cp1_keep : forall x f,
  f_in (cp1 x f) = f_in f /\ f_hold (cp1 x f) = f_hold f /\ f_bits (cp1 x f) = f_bits f
  /\ f_len (cp1 x f) = f_len f /\ f_dist (cp1 x f) = f_dist f /\ f_op (cp1 x f) = f_op f.
Proof. intros x f. unfold cp1. destruct (f_from f); repeat split; reflexivity. Qed.

Lemma cpn_keep : forall x n f,
  f_in (cpn x n f) = f_in f /\ f_hold (cpn x n f) = f_hold f /\ f_bits (cpn x n f) = f_bits f
  /\ f_len (cpn x n f) = f_len f /\ f_dist (cpn x n f) = f_dist f /\ f_op (cpn x n f) = f_op f.
Proof.
  intros x n. induction n as [|n IH]; intros f; [repeat split; reflexivity|].
  cbn [cpn]. destruct (IH (cp1 x f)) as (A & B & C & D & E & F).
  destruct (cp1_keep x f) as (A' & B' & C' & D' & E' & F').
  rewrite A, B, C, D, E, F, A', B', C', D', E', F'. repeat split; reflexivity.
Qed.

Lemma cp1_out : forall x f, f_out (cp1 x f) = f_out f + 1.
Proof. intros x f. unfold cp1. destruct (f_from f); reflexivity. Qed.
Lemma cpn_out : forall x n f, f_out (cpn x n f) = f_out f + Z.of_nat n.
Proof.
  intros x n. induction n as [|n IH]; intros f; [cbn; lia|].
  cbn [cpn]. rewrite IH, cp1_out. lia.
Qed.

Lemma cp1_len_ob : forall x f, arr_len (f_ob (cp1 x f)) = arr_len (f_ob f).
Proof. intros x f. unfold cp1. destruct (f_from f); cbn; apply arr_len_set. Qed.
Lemma cpn_len_ob : forall x n f, arr_len (f_ob (cpn x n f)) = arr_len (f_ob f).
Proof. intros x n. induction n as [|n IH]; intros f; [reflexivity|]. cbn [cpn]. rewrite IH. apply cp1_len_ob. Qed.

Lemma cp1_fset_len : forall x f v, cp1 x (fset_len f v) = fset_len (cp1 x f) v.
Proof. intros x f v. unfold cp1. destruct f; cbn. destruct f_from; reflexivity. Qed.
Lemma cpn_fset_len : forall x n f v, cpn x n (fset_len f v) = fset_len (cpn x n f) v.
Proof. intros x n. induction n as [|n IH]; intros f v; [reflexivity|]. cbn [cpn]. rewrite cp1_fset_len. apply IH. Qed.
Lemma cp1_fset_op : forall x f v, cp1 x (fset_op f v) = fset_op (cp1 x f) v.
Proof. intros x f v. unfold cp1. destruct f; cbn. destruct f_from; reflexivity. Qed.
Lemma cpn_fset_op : forall x n f v, cpn x n (fset_op f v) = fset_op (cpn x n f) v.
Proof. intros x n. induction n as [|n IH]; intros f v; [reflexivity|]. cbn [cpn]. rewrite cp1_fset_op. apply IH. Qed.

Lemma copy_op_cpn_gen : forall x n f,
  1 <= f_op f -> f_op f < 2 ^ 32 -> f_op f <= Z.of_nat n ->
  loopZ (Z.of_nat n)
    (fun f => let f := cp1 x f in let f := fset_op f (wrap32 (f_op f - 1)) in (negb (f_op f =? 0), f)) f
  = fset_op (cpn x (Z.to_nat (f_op f)) f) 0.
Proof.
  intros x n. set (stp := fun f0 : ffs => _).
  assert (Hs : forall f0, stp f0 = (negb (wrap32 (f_op f0 - 1) =? 0), fset_op (cp1 x f0) (wrap32 (f_op f0 - 1)))).
  { intros f0. subst stp. cbv beta zeta. destruct (cp1_keep x f0) as (_ & _ & _ & _ & _ & E). rewrite E. reflexivity. }
  induction n as [|n IH]; intros f H1 H2 Hn; [lia|].
  rewrite loopZ_step by lia. rewrite Hs. rewrite wrap32_id by lia.
  replace (Z.to_nat (f_op f)) with (S (Z.to_nat (f_op f - 1))) by lia. cbn [cpn].
  destruct (Z.eqb_spec (f_op f - 1) 0) as [E|E]; cbn [negb].
  - replace (Z.to_nat (f_op f - 1)) with 0%nat by lia. cbn [cpn]. rewrite E. reflexivity.
  - replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    rewrite (IH (fset_op (cp1 x f) (f_op f - 1))) by (cbn; lia).
    cbn [f_op fset_op]. rewrite cpn_fset_op. destruct (cpn x (Z.to_nat (f_op f - 1)) (cp1 x f)); reflexivity.
Qed.

Lemma copy_op_cpn : forall x f,
  1 <= f_op f < 2 ^ 32 -> copy_op x f = fset_op (cpn x (Z.to_nat (f_op f)) f) 0.
Proof.
  intros x f H. unfold copy_op.
  rewrite <- (Z2Nat.id (f_op f)) at 1 by lia. apply copy_op_cpn_gen; lia.
Qed.

Lemma copy_while3_gen : forall x n f,
  0 <= f_len f -> f_len f < 2 ^ 32 -> f_len f <= Z.of_nat n ->
  loopZ (Z.of_nat n)
    (fun f => if 2 <? f_len f then let f := cp1 x (cp1 x (cp1 x f)) in (true, fset_len f (wrap32 (f_len f - 3))) else (false, f)) f
  = fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3).
Proof.
  intros x n. set (stp := fun f0 : ffs => _).
  assert (Hs : forall f0, stp f0 = if 2 <? f_len f0 then (true, fset_len (cpn x 3 f0) (wrap32 (f_len f0 - 3))) else (false, f0)).
  { intros f0. subst stp. cbv beta zeta. destruct (cpn_keep x 3 f0) as (_ & _ & _ & E & _). cbn [cpn] in E |- *. rewrite E. reflexivity. }
  induction n as [|n IH]; intros f H0 H32 Hn.
  - rewrite loopZ_le0 by lia. destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]. cbn in H0, Hn |- *.
    assert (a5 = 0) by lia. subst a5. reflexivity.
  - rewrite loopZ_step by lia. rewrite Hs. destruct (Z.ltb_spec 2 (f_len f)) as [C|C].
    + replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      rewrite wrap32_id by lia.
      rewrite IH by (cbn; lia). cbn [f_len fset_len].
      rewrite cpn_fset_len.
      replace (Z.to_nat (3 * (f_len f / 3))) with (3 + Z.to_nat (3 * ((f_len f - 3) / 3)))%nat.
      2:{ replace (f_len f / 3) with ((f_len f - 3) / 3 + 1) by (rewrite <- (Z.div_add _ 1 3) by lia; f_equal; lia).
          pose proof (Z.div_pos (f_len f - 3) 3 ltac:(lia) ltac:(lia)). lia. }
      rewrite cpn_add.
      replace (f_len f mod 3) with ((f_len f - 3) mod 3) by (rewrite <- (Z.mod_add _ 1 3) by lia; f_equal; lia).
      destruct (cpn x _ _); reflexivity.
    + assert (Hq : f_len f / 3 = 0) by (apply Z.div_small; lia).
      rewrite Hq. cbn [Z.mul Z.to_nat cpn]. rewrite Z.mod_small by lia. destruct f; reflexivity.
Qed.

Lemma copy_while3_cpn : forall x f,
  0 <= f_len f < 2 ^ 32 -> copy_while3 x f = fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3).
Proof.
  intros x f H. unfold copy_while3. rewrite <- (Z2Nat.id (f_len f)) at 1 by lia.
  apply copy_while3_gen; lia.
Qed.

Lemma copy_do3_gen : forall x n f,
  3 <= f_len f -> f_len f < 2 ^ 32 -> f_len f <= 3 * Z.of_nat n ->
  loopZ (Z.of_nat n)
    (fun f => let f := cp1 x (cp1 x (cp1 x f)) in let f := fset_len f (wrap32 (f_len f - 3)) in (2 <? f_len f, f)) f
  = fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3).
Proof.
  intros x n. set (stp := fun f0 : ffs => _).
  assert (Hs : forall f0, stp f0 = (2 <? wrap32 (f_len f0 - 3), fset_len (cpn x 3 f0) (wrap32 (f_len f0 - 3)))).
  { intros f0. subst stp. cbv beta zeta. destruct (cpn_keep x 3 f0) as (_ & _ & _ & E & _). cbn [cpn] in E |- *. rewrite E. reflexivity. }
  induction n as [|n IH]; intros f H3 H32 Hn; [lia|].
  rewrite loopZ_step by lia. rewrite Hs. rewrite wrap32_id by lia.
  replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
  replace (Z.to_nat (3 * (f_len f / 3))) with (3 + Z.to_nat (3 * ((f_len f - 3) / 3)))%nat.
  2:{ replace (f_len f / 3) with ((f_len f - 3) / 3 + 1) by (rewrite <- (Z.div_add _ 1 3) by lia; f_equal; lia).
      pose proof (Z.div_pos (f_len f - 3) 3 ltac:(lia) ltac:(lia)). lia. }
  rewrite cpn_add.
  replace (f_len f mod 3) with ((f_len f - 3) mod 3) by (rewrite <- (Z.mod_add _ 1 3) by lia; f_equal; lia).
  destruct (Z.ltb_spec 2 (f_len f - 3)) as [C|C].
  - rewrite IH by (cbn; lia). cbn [f_len fset_len]. rewrite cpn_fset_len. destruct (cpn x _ _); reflexivity.
  - rewrite (Z.div_small (f_len f - 3) 3) by lia. rewrite (Z.mod_small (f_len f - 3) 3) by lia.
    cbn [Z.mul Z.to_nat cpn]. reflexivity.
Qed.

Lemma copy_do3_cpn : forall x f,
  3 <= f_len f < 2 ^ 32 -> copy_do3 x f = fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3).
Proof.
  intros x f H. unfold copy_do3.
  replace (f_len f + 1) with (Z.of_nat (Z.to_nat (f_len f + 1))) by lia.
  apply copy_do3_gen; lia.
Qed.

Lemma copy_tail_cpn : forall x f,
  0 <= f_len f <= 2 -> copy_tail x f = cpn x (Z.to_nat (f_len f)) f.
Proof.
  intros x f H. unfold copy_tail.
  destruct (cp1_keep x f) as (_ & _ & _ & El & _).
  destruct (Z.eqb_spec (f_len f) 0) as [E|E]; cbn [negb].
  - rewrite E. reflexivity.
  - rewrite El. destruct (Z.ltb_spec 1 (f_len f)) as [C|C].
    + replace (Z.to_nat (f_len f)) with 2%nat by lia. reflexivity.
    + replace (Z.to_nat (f_len f)) with 1%nat by lia. reflexivity.
Qed.

Lemma cp1_from : forall x f, f_from (cp1 x f) = from_succ (f_from f).
Proof. intros x [a1 a2 a3 a4 a5 a6 a7 fr ob]. unfold cp1. cbn. destruct fr; reflexivity. Qed.

Definition fval (win ob : arr) (fr : fromptr) : Z :=
  match fr with FWin i => arr_get win i | FOut i => arr_get ob i end.

Fixpoint cblit (win : arr) (fr : fromptr) (ob : arr) (i : Z) (n : nat) : arr :=
  match n with
  | O => ob
  | S n' => cblit win (from_succ fr) (arr_set ob i (fval win ob fr)) (i + 1) n'
  end.

Fixpoint fr_add (fr : fromptr) (k : nat) : fromptr :=
  match k with O => fr | S k' => fr_add (from_succ fr) k' end.

Lemma fr_add_win : forall k i, fr_add (FWin i) k = FWin (i + Z.of_nat k).
Proof. induction k as [|k IH]; intros i; cbn; [f_equal; lia|]. rewrite IH. f_equal. lia. Qed.
Lemma fr_add_out : forall k i, fr_add (FOut i) k = FOut (i + Z.of_nat k).
Proof. induction k as [|k IH]; intros i; cbn; [f_equal; lia|]. rewrite IH. f_equal. lia. Qed.

Lemma cblit_len : forall win n fr ob i, arr_len (cblit win fr ob i n) = arr_len ob.
Proof. induction n as [|n IH]; intros fr ob i; [reflexivity|]. cbn [cblit]. rewrite IH. apply arr_len_set. Qed.

Lemma cp1_ob : forall x f, f_ob (cp1 x f) = arr_set (f_ob f) (f_out f) (fval (x_window x) (f_ob f) (f_from f)).
Proof. intros x [a1 a2 a3 a4 a5 a6 a7 fr ob]. cbn. destruct fr; reflexivity. Qed.

Lemma cpn_cblit : forall x n f,
  f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n
  /\ f_out (cpn x n f) = f_out f + Z.of_nat n
  /\ f_from (cpn x n f) = fr_add (f_from f) n.
Proof.
  intros x n. induction n as [|n IH]; intros f.
  - cbn. rewrite Z.add_0_r. repeat split; reflexivity.
  - cbn [cpn cblit fr_add]. destruct (IH (cp1 x f)) as (A & B & C). rewrite A, B, C.
    rewrite cp1_from, cp1_ob, cp1_out. repeat split. lia.
Qed.

Lemma fpull_eq : forall x f,
  0 <= f_hold f -> 0 <= f_bits f <= 48 -> f_hold f < 2 ^ f_bits f ->
  0 <= arr_get (x_input x) (f_in f) < 256 ->
  fpull x f = mkF (f_in f + 1) (f_out f) (f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f) (f_bits f + 8)
                  (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)
  /\ f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f < 2 ^ (f_bits f + 8).
Proof.
  intros x [fin fout hold bits len dist op fr ob] Hh Hb Hhb Hv. cbn in *.
  set (b := arr_get (x_input x) fin) in *.
  pose proof (Z.pow_pos_nonneg 2 bits ltac:(lia) ltac:(lia)) as Hp.
  assert (Hs : hold + b * 2 ^ bits < 2 ^ (bits + 8)).
  { rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia. }
  split; [| exact Hs].
  assert (H56 : 2 ^ (bits + 8) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 56) with 72057594037927936 in H56.
  unfold fpull, shl64. cbn. rewrite Z.shiftl_mul_pow2 by lia.
  fold b. rewrite (wrap64_id (b * 2 ^ bits)) by nia.
  rewrite wrap64_id by nia. rewrite wrap32_id by lia. reflexivity.
Qed.
