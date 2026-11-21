(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms InflateGarbBase InflateGarbFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint cpn (x : ffx) (n : nat) (f : ffs) : ffs :=
  match n with O => f | S n' => cpn x n' (cp1 x f) end.

Definition from_add (fr : fromptr) (n : Z) : fromptr :=
  match fr with FWin j => FWin (j + n) | FOut j => FOut (j + n) end.

Lemma from_add_0 : forall fr, from_add fr 0 = fr.
Proof. intros [j|j]; cbn; rewrite Z.add_0_r; reflexivity. Qed.
Lemma from_succ_add : forall fr n, from_add (from_succ fr) n = from_add fr (n + 1).
Proof. intros [j|j] n; cbn; f_equal; lia. Qed.

Lemma cpn_add : forall x m n f, cpn x (m + n) f = cpn x n (cpn x m f).
Proof. induction m as [|m IH]; intros n f; cbn; [reflexivity | apply IH]. Qed.


Lemma cpn_fields : forall x n f,
  f_in (cpn x n f) = f_in f /\ f_hold (cpn x n f) = f_hold f /\ f_bits (cpn x n f) = f_bits f
  /\ f_len (cpn x n f) = f_len f /\ f_dist (cpn x n f) = f_dist f /\ f_op (cpn x n f) = f_op f
  /\ f_out (cpn x n f) = f_out f + Z.of_nat n /\ f_from (cpn x n f) = from_add (f_from f) (Z.of_nat n)
  /\ arr_len (f_ob (cpn x n f)) = arr_len (f_ob f).
Proof.
  intros x. induction n as [|n IH]; intros f.
  - cbn [cpn]. rewrite from_add_0. repeat split; try reflexivity. lia.
  - cbn [cpn]. destruct (IH (cp1 x f)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. destruct f as [i o h b l d op fr ob]. unfold cp1. cbn.
    rewrite from_succ_add, arr_len_set. repeat split; try reflexivity; try lia. f_equal. lia.
Qed.

Lemma cp1_set_op : forall x f v, cp1 x (fset_op f v) = fset_op (cp1 x f) v.
Proof. intros x [] v; reflexivity. Qed.
Lemma cp1_set_len : forall x f v, cp1 x (fset_len f v) = fset_len (cp1 x f) v.
Proof. intros x [] v; reflexivity. Qed.
Lemma cpn_set_op : forall x n f v, cpn x n (fset_op f v) = fset_op (cpn x n f) v.
Proof. induction n as [|n IH]; intros f v; cbn; [reflexivity|]. rewrite cp1_set_op. apply IH. Qed.
Lemma cpn_set_len : forall x n f v, cpn x n (fset_len f v) = fset_len (cpn x n f) v.
Proof. induction n as [|n IH]; intros f v; cbn; [reflexivity|]. rewrite cp1_set_len. apply IH. Qed.
Lemma fset_op_op : forall f a b, fset_op (fset_op f a) b = fset_op f b.
Proof. intros [] a b; reflexivity. Qed.
Lemma fset_len_len : forall f a b, fset_len (fset_len f a) b = fset_len f b.
Proof. intros [] a b; reflexivity. Qed.
Lemma fset_len_same : forall f, fset_len f (f_len f) = f.
Proof. intros []; reflexivity. Qed.
Lemma f_op_set_op : forall f v, f_op (fset_op f v) = v.  Proof. intros [] v; reflexivity. Qed.
Lemma f_len_set_len : forall f v, f_len (fset_len f v) = v.  Proof. intros [] v; reflexivity. Qed.
Lemma f_len_set_op : forall f v, f_len (fset_op f v) = f_len f.  Proof. intros [] v; reflexivity. Qed.
Lemma f_len_cp1 : forall x f, f_len (cp1 x f) = f_len f.  Proof. intros x []; reflexivity. Qed.


Section Loops.
  Variable x : ffx.

  Lemma copy_op_eqN : forall n f, f_op f = Z.of_nat (S n) -> f_op f < 2 ^ 32 ->
    loopZ (f_op f) (copy_op_step x) f = fset_op (cpn x (S n) f) 0.
  Proof.
    induction n as [|n IH]; intros f Hop Hlt.
    - rewrite loopZ_step by lia. unfold copy_op_step at 1. rewrite f_op_set_op.
      assert (Eop : f_op (cp1 x f) = f_op f) by (destruct f; reflexivity). rewrite Eop, Hop.
      change (wrap32 (Z.of_nat 1 - 1)) with 0. cbn. reflexivity.
    - rewrite loopZ_step by lia. unfold copy_op_step at 1. rewrite f_op_set_op.
      assert (Eop : f_op (cp1 x f) = f_op f) by (destruct f; reflexivity).
      rewrite Eop, Hop. rewrite (wrap32_id (Z.of_nat (S (S n)) - 1)) by lia.
      replace (Z.of_nat (S (S n)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      replace (Z.of_nat (S (S n)) - 1) with (Z.of_nat (S n)) by lia.
      specialize (IH (fset_op (cp1 x f) (Z.of_nat (S n)))). rewrite f_op_set_op in IH.
      rewrite (IH eq_refl ltac:(lia)). rewrite cpn_set_op, fset_op_op. reflexivity.
  Qed.

  Lemma copy_op_eq : forall f, 1 <= f_op f < 2 ^ 32 -> copy_op x f = fset_op (cpn x (Z.to_nat (f_op f)) f) 0.
  Proof.
    intros f H. change (copy_op x f) with (loopZ (f_op f) (copy_op_step x) f).
    destruct (Z.to_nat (f_op f)) as [|n] eqn:E; [lia|].
    apply copy_op_eqN; lia.
  Qed.

  Lemma copy_while3_eqN : forall q f fuel r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat q + r -> f_len f < 2 ^ 32 -> Z.of_nat q <= fuel ->
    loopZ fuel (copy_while3_step x) f = fset_len (cpn x (3 * q) f) r.
  Proof.
    induction q as [|q IH]; intros f fuel r Hr Hl Hlt Hf.
    - cbn [cpn Nat.mul]. destruct (Z_le_gt_dec fuel 0).
      + rewrite loopZ_le0 by lia. rewrite <- (fset_len_same f) at 1. f_equal. lia.
      + rewrite loopZ_step by lia. unfold copy_while3_step at 1. replace (2 <? f_len f) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite <- (fset_len_same f) at 1. f_equal. lia.
    - rewrite loopZ_step by lia. unfold copy_while3_step at 1. replace (2 <? f_len f) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite !f_len_cp1. rewrite (wrap32_id (f_len f - 3)) by lia.
      specialize (IH (fset_len (cp1 x (cp1 x (cp1 x f))) (f_len f - 3)) (fuel - 1) r Hr).
      rewrite f_len_set_len in IH. rewrite (IH ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite cpn_set_len, fset_len_len. replace (3 * S q)%nat with (3 + 3 * q)%nat by lia. rewrite (cpn_add x 3). reflexivity.
  Qed.

  Lemma copy_while3_eq : forall f q r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat q + r -> f_len f < 2 ^ 32 ->
    copy_while3 x f = fset_len (cpn x (3 * q) f) r.
  Proof. intros f q r Hr Hl Hlt. change (copy_while3 x f) with (loopZ (f_len f) (copy_while3_step x) f). apply copy_while3_eqN; lia. Qed.

  Lemma copy_do3_eqN : forall q f fuel r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat (S q) + r -> f_len f < 2 ^ 32 -> Z.of_nat (S q) <= fuel ->
    loopZ fuel (copy_do3_step x) f = fset_len (cpn x (3 * S q) f) r.
  Proof.
    induction q as [|q IH]; intros f fuel r Hr Hl Hlt Hf.
    - rewrite loopZ_step by lia. unfold copy_do3_step at 1. rewrite !f_len_cp1, f_len_set_len. rewrite (wrap32_id (f_len f - 3)) by lia.
      replace (2 <? f_len f - 3) with false by (symmetry; apply Z.ltb_ge; lia).
      change (cp1 x (cp1 x (cp1 x f))) with (cpn x 3 f). cbn [Nat.mul Nat.add]. f_equal. lia.
    - rewrite loopZ_step by lia. unfold copy_do3_step at 1. rewrite !f_len_cp1, f_len_set_len. rewrite (wrap32_id (f_len f - 3)) by lia.
      replace (2 <? f_len f - 3) with true by (symmetry; apply Z.ltb_lt; lia).
      specialize (IH (fset_len (cp1 x (cp1 x (cp1 x f))) (f_len f - 3)) (fuel - 1) r Hr).
      rewrite f_len_set_len in IH. rewrite (IH ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite cpn_set_len, fset_len_len. replace (3 * S (S q))%nat with (3 + 3 * S q)%nat by lia. rewrite (cpn_add x 3). reflexivity.
  Qed.

  Lemma copy_do3_eq : forall f q r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat (S q) + r -> f_len f < 2 ^ 32 ->
    copy_do3 x f = fset_len (cpn x (3 * S q) f) r.
  Proof. intros f q r Hr Hl Hlt. change (copy_do3 x f) with (loopZ (f_len f + 1) (copy_do3_step x) f). apply copy_do3_eqN; lia. Qed.

  Lemma copy_tail_eq : forall f r, 0 <= r <= 2 -> f_len f = r -> copy_tail x f = cpn x (Z.to_nat r) f.
  Proof.
    intros f r Hr Hl. unfold copy_tail. rewrite f_len_cp1, Hl.
    assert (E : r = 0 \/ r = 1 \/ r = 2) by lia. destruct E as [-> | [-> | ->]]; reflexivity.
  Qed.

  Lemma copy_w3_tail : forall f, 0 <= f_len f < 2 ^ 32 ->
    copy_tail x (copy_while3 x f) = fset_len (cpn x (Z.to_nat (f_len f)) f) (f_len f mod 3).
  Proof.
    intros f Hl.
    set (q := Z.to_nat (f_len f / 3)). set (r := f_len f mod 3).
    assert (Hr : 0 <= r <= 2) by (subst r; pose proof (Z.mod_pos_bound (f_len f) 3); lia).
    assert (Hq : f_len f = 3 * Z.of_nat q + r) by (subst q r; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_mod; lia).
    rewrite (copy_while3_eq f q r Hr Hq ltac:(lia)).
    rewrite (copy_tail_eq _ r Hr) by apply f_len_set_len.
    rewrite cpn_set_len. rewrite <- cpn_add. f_equal. f_equal. lia.
  Qed.

  Lemma copy_d3_tail : forall f, 3 <= f_len f < 2 ^ 32 ->
    copy_tail x (copy_do3 x f) = fset_len (cpn x (Z.to_nat (f_len f)) f) (f_len f mod 3).
  Proof.
    intros f Hl.
    set (q := Z.to_nat (f_len f / 3 - 1)). set (r := f_len f mod 3).
    assert (Hr : 0 <= r <= 2) by (subst r; pose proof (Z.mod_pos_bound (f_len f) 3); lia).
    assert (Hq : f_len f = 3 * Z.of_nat (S q) + r).
    { subst q r. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)). pose proof (Z.div_le_lower_bound (f_len f) 3 1 ltac:(lia) ltac:(lia)).
      rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
    rewrite (copy_do3_eq f q r Hr Hq ltac:(lia)).
    rewrite (copy_tail_eq _ r Hr) by apply f_len_set_len.
    rewrite cpn_set_len. rewrite <- cpn_add. f_equal. f_equal. lia.
  Qed.

  Variable ON : Z.

  Definition cps_ok (f : ffs) (n : nat) : Prop := forall k, (k < n)%nat -> cp1_ok ON (cpn x k f) = true.

  Lemma cps_ok_intro : forall f n, 0 <= f_out f -> f_out f + Z.of_nat n <= ON ->
    match f_from f with FWin _ => True | FOut i => 0 <= i < f_out f end -> cps_ok f n.
  Proof.
    intros f n H0 Hn Hfr k Hk. unfold cp1_ok.
    destruct (cpn_fields x k f) as (_ & _ & _ & _ & _ & _ & Eo & Efr & _). rewrite Eo, Efr.
    apply andb_true_intro; split.
    - apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - destruct (f_from f) as [j|j]; cbn [from_add]; [reflexivity|].
      apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma cps_ok_le : forall f n m, (m <= n)%nat -> cps_ok f n -> cps_ok f m.
  Proof. intros f n m H C k Hk. apply C. lia. Qed.
  Lemma cps_ok_shift : forall f n m, cps_ok f (m + n) -> cps_ok (cpn x m f) n.
  Proof. intros f n m C k Hk. rewrite <- cpn_add. apply C. lia. Qed.
  Lemma cps_ok_set_op : forall f n v, cps_ok f n -> cps_ok (fset_op f v) n.
  Proof. intros f n v C k Hk. rewrite cpn_set_op. specialize (C k Hk). destruct (cpn x k f); exact C. Qed.
  Lemma cps_ok_set_len : forall f n v, cps_ok f n -> cps_ok (fset_len f v) n.
  Proof. intros f n v C k Hk. rewrite cpn_set_len. specialize (C k Hk). destruct (cpn x k f); exact C. Qed.

  Lemma cps_ok_at : forall f n k, cps_ok f n -> (k < n)%nat -> cp1_ok ON (cpn x k f) = true.
  Proof. intros f n k C Hk. apply C. exact Hk. Qed.
  Ltac cps k C := let H := fresh in pose proof (cps_ok_at _ _ k C ltac:(cbn; lia)) as H; cbn [cpn] in H; rewrite H; clear H.

  Lemma copy_opG_okN : forall n f, f_op f = Z.of_nat (S n) -> f_op f < 2 ^ 32 -> cps_ok f (S n) ->
    loop_okN (S n) (copy_op_step x) (cp1_ok ON) f = true.
  Proof.
    induction n as [|n IH]; intros f Hop Hlt C.
    - cbn [loop_okN]. cps 0%nat C. cbn [andb]. unfold copy_op_step. destruct (negb _); reflexivity.
    - cbn [loop_okN]. cps 0%nat C. cbn [andb]. unfold copy_op_step at 1. rewrite f_op_set_op.
      assert (Eop : f_op (cp1 x f) = f_op f) by (destruct f; reflexivity).
      rewrite Eop, Hop. rewrite (wrap32_id (Z.of_nat (S (S n)) - 1)) by lia.
      replace (Z.of_nat (S (S n)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      apply IH; [rewrite f_op_set_op; lia | rewrite f_op_set_op; lia |].
      apply cps_ok_set_op. apply (cps_ok_shift f (S n) 1). exact C.
  Qed.

  Lemma copy_opG_ok : forall f, 1 <= f_op f < 2 ^ 32 -> cps_ok f (Z.to_nat (f_op f)) -> copy_opG x ON f = true.
  Proof.
    intros f H C. unfold copy_opG, loopZ_ok.
    destruct (Z.to_nat (f_op f)) as [|n] eqn:E; [lia|]. apply copy_opG_okN; [lia | lia | exact C].
  Qed.

  Lemma ok3_of : forall f, cps_ok f 3 -> ok3 x ON f = true.
  Proof.
    intros f C. unfold ok3. cps 0%nat C. cps 1%nat C. cps 2%nat C. reflexivity.
  Qed.

  Lemma copy_while3G_okN : forall q f fuel r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat q + r -> f_len f < 2 ^ 32 ->
    cps_ok f (3 * q) ->
    loop_okN fuel (copy_while3_step x) (fun f => if 2 <? f_len f then ok3 x ON f else true) f = true.
  Proof.
    induction q as [|q IH]; intros f fuel r Hr Hl Hlt C.
    - destruct fuel as [|fuel]; [reflexivity|]. cbn [loop_okN].
      replace (2 <? f_len f) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
      unfold copy_while3_step. replace (2 <? f_len f) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - destruct fuel as [|fuel]; [reflexivity|]. cbn [loop_okN].
      replace (2 <? f_len f) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (ok3_of f) by (apply (cps_ok_le f (3 * S q)); [lia | exact C]). cbn [andb].
      unfold copy_while3_step at 1. replace (2 <? f_len f) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite !f_len_cp1. rewrite (wrap32_id (f_len f - 3)) by lia.
      apply (IH _ fuel r Hr); [rewrite f_len_set_len; lia | rewrite f_len_set_len; lia |].
      apply cps_ok_set_len. change (cp1 x (cp1 x (cp1 x f))) with (cpn x 3 f). apply cps_ok_shift.
      replace (3 + 3 * q)%nat with (3 * S q)%nat by lia. exact C.
  Qed.

  Lemma copy_while3G_ok : forall f q r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat q + r -> f_len f < 2 ^ 32 ->
    cps_ok f (3 * q) -> copy_while3G x ON f = true.
  Proof. intros f q r Hr Hl Hlt C. unfold copy_while3G, loopZ_ok. apply (copy_while3G_okN q f _ r); assumption. Qed.

  Lemma copy_do3G_okN : forall q f fuel r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat (S q) + r -> f_len f < 2 ^ 32 ->
    cps_ok f (3 * S q) ->
    loop_okN fuel (copy_do3_step x) (ok3 x ON) f = true.
  Proof.
    induction q as [|q IH]; intros f fuel r Hr Hl Hlt C.
    - destruct fuel as [|fuel]; [reflexivity|]. cbn [loop_okN]. rewrite (ok3_of f C). cbn [andb].
      unfold copy_do3_step. rewrite !f_len_cp1, f_len_set_len. rewrite (wrap32_id (f_len f - 3)) by lia.
      replace (2 <? f_len f - 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - destruct fuel as [|fuel]; [reflexivity|]. cbn [loop_okN].
      rewrite (ok3_of f) by (apply (cps_ok_le f (3 * S (S q))); [lia | exact C]). cbn [andb].
      unfold copy_do3_step at 1. rewrite !f_len_cp1, f_len_set_len. rewrite (wrap32_id (f_len f - 3)) by lia.
      replace (2 <? f_len f - 3) with true by (symmetry; apply Z.ltb_lt; lia).
      apply (IH _ fuel r Hr); [rewrite f_len_set_len; lia | rewrite f_len_set_len; lia |].
      apply cps_ok_set_len. change (cp1 x (cp1 x (cp1 x f))) with (cpn x 3 f). apply cps_ok_shift.
      replace (3 + 3 * S q)%nat with (3 * S (S q))%nat by lia. exact C.
  Qed.

  Lemma copy_do3G_ok : forall f q r, 0 <= r <= 2 -> f_len f = 3 * Z.of_nat (S q) + r -> f_len f < 2 ^ 32 ->
    cps_ok f (3 * S q) -> copy_do3G x ON f = true.
  Proof. intros f q r Hr Hl Hlt C. unfold copy_do3G, loopZ_ok. apply (copy_do3G_okN q f _ r); assumption. Qed.

  Lemma copy_tailG_ok : forall f r, 0 <= r <= 2 -> f_len f = r -> cps_ok f (Z.to_nat r) -> copy_tailG x ON f = true.
  Proof.
    intros f r Hr Hl C. unfold copy_tailG. rewrite f_len_cp1, Hl.
    assert (E : r = 0 \/ r = 1 \/ r = 2) by lia. destruct E as [-> | [-> | ->]]; cbn [Z.eqb Z.ltb negb Pos.eqb Z.compare Pos.compare].
    - reflexivity.
    - cps 0%nat C. reflexivity.
    - cps 0%nat C. cps 1%nat C. reflexivity.
  Qed.

  Lemma copy_w3_tailG : forall f, 0 <= f_len f < 2 ^ 32 -> cps_ok f (Z.to_nat (f_len f)) ->
    copy_while3G x ON f = true /\ copy_tailG x ON (copy_while3 x f) = true.
  Proof.
    intros f Hl C.
    set (q := Z.to_nat (f_len f / 3)). set (r := f_len f mod 3).
    assert (Hr : 0 <= r <= 2) by (subst r; pose proof (Z.mod_pos_bound (f_len f) 3); lia).
    assert (Hq : f_len f = 3 * Z.of_nat q + r) by (subst q r; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_mod; lia).
    assert (En : Z.to_nat (f_len f) = (3 * q + Z.to_nat r)%nat) by lia.
    split.
    - apply (copy_while3G_ok f q r Hr Hq ltac:(lia)). apply (cps_ok_le f (Z.to_nat (f_len f))); [lia | exact C].
    - rewrite (copy_while3_eq f q r Hr Hq ltac:(lia)). apply (copy_tailG_ok _ r Hr); [apply f_len_set_len|].
      apply cps_ok_set_len. apply cps_ok_shift. rewrite <- En. exact C.
  Qed.

  Lemma copy_d3_tailG : forall f, 3 <= f_len f < 2 ^ 32 -> cps_ok f (Z.to_nat (f_len f)) ->
    copy_do3G x ON f = true /\ copy_tailG x ON (copy_do3 x f) = true.
  Proof.
    intros f Hl C.
    set (q := Z.to_nat (f_len f / 3 - 1)). set (r := f_len f mod 3).
    assert (Hr : 0 <= r <= 2) by (subst r; pose proof (Z.mod_pos_bound (f_len f) 3); lia).
    assert (Hq : f_len f = 3 * Z.of_nat (S q) + r).
    { subst q r. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)). pose proof (Z.div_le_lower_bound (f_len f) 3 1 ltac:(lia) ltac:(lia)).
      rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
    assert (En : Z.to_nat (f_len f) = (3 * S q + Z.to_nat r)%nat) by lia.
    split.
    - apply (copy_do3G_ok f q r Hr Hq ltac:(lia)). apply (cps_ok_le f (Z.to_nat (f_len f))); [lia | exact C].
    - rewrite (copy_do3_eq f q r Hr Hq ltac:(lia)). apply (copy_tailG_ok _ r Hr); [apply f_len_set_len|].
      apply cps_ok_set_len. apply cps_ok_shift. rewrite <- En. exact C.
  Qed.
End Loops.


Definition obytes (ON : Z) (ob : arr) : Prop := arr_len ob = ON /\ forall i, 0 <= i < ON -> 0 <= arr_get ob i < 256.

Definition src_ok (x : ffx) (ON : Z) (f : ffs) (n : Z) : Prop :=
  match f_from f with
  | FWin j => 0 <= j /\ j + n <= arr_len (x_window x)
  | FOut j => 0 <= j /\ j + n <= ON
  end.

Lemma cpn_obytes : forall x ON n f,
  (forall i, 0 <= i < arr_len (x_window x) -> 0 <= arr_get (x_window x) i < 256) ->
  obytes ON (f_ob f) -> src_ok x ON f (Z.of_nat n) -> obytes ON (f_ob (cpn x n f)).
Proof.
  intros x ON. induction n as [|n IH]; intros f Hw OB SRC; cbn [cpn]; [exact OB|].
  apply IH; [exact Hw | |].
  - destruct f as [i o h b l d op fr ob]. unfold cp1. destruct fr as [j|j]; cbn; cbn in OB, SRC; destruct OB as [L B];
      (split; [rewrite arr_len_set; exact L|]);
      intros k Hk; rewrite arr_get_set; unfold arr_inb; rewrite L;
      (destruct (Z.eqb_spec o k); cbn [andb]; [| apply B; exact Hk]);
      (destruct ((0 <=? o) && (o <? ON)); [| apply B; exact Hk]); [apply Hw; lia | apply B; lia].
  - destruct f as [i o h b l d op fr ob]. destruct fr as [j|j]; cbn in SRC |- *; lia.
Qed.
