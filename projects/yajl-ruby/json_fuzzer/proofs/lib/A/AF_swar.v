(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition K55 : Z := 6148914691236517205.
Definition K33 : Z := 3689348814741910323.
Definition K0F : Z := 1085102592571150095.
Definition K01 : Z := 72340172838076673.
Definition M64 : Z := 18446744073709551616.
Definition ONES64 : Z := 18446744073709551615.

Definition smear1 (x : Z) : Z := Z.lor x (Z.shiftr x 1).
Definition smear2 (x : Z) : Z := let u1 := smear1 x in Z.lor u1 (Z.shiftr u1 2).
Definition smear3 (x : Z) : Z := let u2 := smear2 x in Z.lor u2 (Z.shiftr u2 4).
Definition smear4 (x : Z) : Z := let u3 := smear3 x in Z.lor u3 (Z.shiftr u3 8).
Definition smear5 (x : Z) : Z := let u4 := smear4 x in Z.lor u4 (Z.shiftr u4 16).
Definition smear6 (x : Z) : Z := let u5 := smear5 x in Z.lor u5 (Z.shiftr u5 32).

(* [comment removed for export] *)
Definition swar_tail (u6 : Z) : Z :=
  let y := Z.lxor u6 ONES64 in
  let c1 := y - Z.land (Z.shiftr y 1) K55 in
  let c2 := Z.land c1 K33 + Z.land (Z.shiftr c1 2) K33 in
  let c3 := c2 + Z.shiftr c2 4 in
  Z.shiftr ((Z.land c3 K0F * K01) mod M64) 56.

Definition swar_res (x : Z) : Z := swar_tail (smear6 x).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition winor (t : nat) (x : Z) (i : Z) : bool := existsb (fun d => Z.testbit x (i + Z.of_nat d)) (seq 0 t).

Lemma existsb_app : forall {A} (f : A -> bool) l1 l2, existsb f (l1 ++ l2) = existsb f l1 || existsb f l2.
Proof. aceil. intros A f l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. rewrite IH, orb_assoc. reflexivity. Qed.

Lemma existsb_ext : forall {A} (g h : A -> bool) l, (forall d, In d l -> g d = h d) -> existsb g l = existsb h l.
Proof. aceil.
  intros A g h l H. induction l as [|a l IH]; cbn; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH by (intros d Hd; apply H; right; exact Hd). reflexivity.
Qed.

Lemma existsb_seq_shift : forall t (f : nat -> bool) s, existsb f (seq s t) = existsb (fun d => f (s + d)%nat) (seq 0 t).
Proof. aceil.
  induction t as [|t IH]; intros f s; [reflexivity|].
  cbn [seq existsb]. rewrite Nat.add_0_r. f_equal.
  rewrite (IH f (S s)), (IH (fun d => f (s + d)%nat) 1%nat).
  apply existsb_ext. intros d _. f_equal. lia.
Qed.

Lemma winor_double : forall t u x,
  (forall i, 0 <= i -> Z.testbit u i = winor t x i) ->
  forall i, 0 <= i -> Z.testbit (Z.lor u (Z.shiftr u (Z.of_nat t))) i = winor (t + t) x i.
Proof. aceil.
  intros t u x HU i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite !HU by lia.
  unfold winor. rewrite seq_app, existsb_app. cbn [Nat.add]. f_equal.
  rewrite (existsb_seq_shift t (fun d => Z.testbit x (i + Z.of_nat d)) t). apply existsb_ext. intros d _. f_equal. lia.
Qed.

Lemma winor_1 : forall x i, 0 <= i -> Z.testbit x i = winor 1 x i.
Proof. aceil. intros x i Hi. unfold winor. cbn. rewrite Z.add_0_r, orb_false_r. reflexivity. Qed.

Lemma smear6_bits : forall x i, 0 <= i -> Z.testbit (smear6 x) i = winor 64 x i.
Proof. aceil.
  intros x.
  assert (S1 : forall i, 0 <= i -> Z.testbit (smear1 x) i = winor 2 x i).
  { unfold smear1. change 1 with (Z.of_nat 1). apply (winor_double 1 x x). apply winor_1. }
  assert (S2 : forall i, 0 <= i -> Z.testbit (smear2 x) i = winor 4 x i).
  { unfold smear2. cbv zeta. change 2 with (Z.of_nat 2). apply (winor_double 2). exact S1. }
  assert (S3 : forall i, 0 <= i -> Z.testbit (smear3 x) i = winor 8 x i).
  { unfold smear3. cbv zeta. change 4 with (Z.of_nat 4). apply (winor_double 4). exact S2. }
  assert (S4 : forall i, 0 <= i -> Z.testbit (smear4 x) i = winor 16 x i).
  { unfold smear4. cbv zeta. change 8 with (Z.of_nat 8). apply (winor_double 8). exact S3. }
  assert (S5 : forall i, 0 <= i -> Z.testbit (smear5 x) i = winor 32 x i).
  { unfold smear5. cbv zeta. change 16 with (Z.of_nat 16). apply (winor_double 16). exact S4. }
  unfold smear6. cbv zeta. change 32 with (Z.of_nat 32). apply (winor_double 32). exact S5.
Qed.

Lemma winor_true : forall t x i d, (d < t)%nat -> Z.testbit x (i + Z.of_nat d) = true -> winor t x i = true.
Proof. aceil.
  intros t x i d Hd Hb. unfold winor. apply existsb_exists. exists d. split; [apply in_seq; lia| exact Hb].
Qed.

Lemma winor_false : forall t x i, (forall d, (d < t)%nat -> Z.testbit x (i + Z.of_nat d) = false) -> winor t x i = false.
Proof. aceil.
  intros t x i H. unfold winor. apply Bool.not_true_is_false. intros E. apply existsb_exists in E as (d & Hd & Hb).
  apply in_seq in Hd. rewrite H in Hb by lia. discriminate.
Qed.

Lemma smear6_eq : forall x, 0 < x < 2^64 -> smear6 x = 2 ^ (Z.log2 x + 1) - 1.
Proof. aceil.
  intros x Hx. pose proof (Z.log2_nonneg x) as K0.
  assert (K63 : Z.log2 x <= 63).
  { apply Z.lt_succ_r. change 64 with (Z.succ 63) in Hx. apply Z.log2_lt_pow2; lia. }
  replace (2 ^ (Z.log2 x + 1) - 1) with (Z.ones (Z.log2 x + 1)) by (rewrite Z.ones_equiv; lia).
  apply Z.bits_inj'. intros i Hi.
  rewrite smear6_bits by exact Hi.
  destruct (Z.le_gt_cases i (Z.log2 x)) as [LE|GT].
  - rewrite Z.ones_spec_low by lia. apply (winor_true 64 x i (Z.to_nat (Z.log2 x - i))); [lia|].
    replace (i + Z.of_nat (Z.to_nat (Z.log2 x - i))) with (Z.log2 x) by lia. apply Z.bit_log2. lia.
  - rewrite Z.ones_spec_high by lia. apply winor_false. intros d Hd. apply Z.bits_above_log2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swar_tail_table : forallb (fun k => swar_tail (2 ^ (Z.of_nat k + 1) - 1) =? 63 - Z.of_nat k) (seq 0 64) = true.
Proof. aceil. vm_compute. reflexivity. Qed.

Lemma swar_tail_eq : forall k, 0 <= k <= 63 -> swar_tail (2 ^ (k + 1) - 1) = 63 - k.
Proof. aceil.
  intros k Hk.
  pose proof (proj1 (forallb_forall _ _) swar_tail_table (Z.to_nat k) ltac:(apply in_seq; lia)) as E.
  cbv beta in E. rewrite Z2Nat.id in E by lia. apply Z.eqb_eq in E. exact E.
Qed.

Theorem swar_res_spec : forall x, 0 < x < 2^64 -> swar_res x = 63 - Z.log2 x.
Proof. aceil.
  intros x Hx. unfold swar_res. rewrite smear6_eq by exact Hx. apply swar_tail_eq.
  split; [apply Z.log2_nonneg|]. apply Z.lt_succ_r. change 64 with (Z.succ 63) in Hx. apply Z.log2_lt_pow2; lia.
Qed.

Corollary swar_res_range : forall x, 0 < x < 2^64 -> 0 <= swar_res x <= 63.
Proof. aceil. intros x Hx. rewrite swar_res_spec by exact Hx. pose proof (Z.log2_nonneg x). pose proof (Z.log2_lt_pow2 x 64). lia. Qed.

(* [comment removed for export] *)
Lemma lxor63_table : forallb (fun k => Z.lxor (Z.of_nat k) 63 =? 63 - Z.of_nat k) (seq 0 64) = true.
Proof. aceil. vm_compute. reflexivity. Qed.

Lemma lxor63 : forall v, 0 <= v <= 63 -> Z.lxor v 63 = 63 - v.
Proof. aceil.
  intros v Hv.
  pose proof (proj1 (forallb_forall _ _) lxor63_table (Z.to_nat v) ltac:(apply in_seq; lia)) as E.
  cbv beta in E. rewrite Z2Nat.id in E by lia. apply Z.eqb_eq in E. exact E.
Qed.

Lemma swar_idx : forall x, 0 < x < 2^64 -> Z.lxor (swar_res x) 63 = Z.log2 x.
Proof. aceil.
  intros x Hx. rewrite lxor63 by (apply swar_res_range; exact Hx). rewrite swar_res_spec by exact Hx. lia.
Qed.
End RC__1.
