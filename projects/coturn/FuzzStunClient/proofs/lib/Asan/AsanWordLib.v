(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zbv_u : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

Lemma zbv_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma v_addi_zbv : forall z i, (0 <= z < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof. intros z i Hz. unfold v_addi. rewrite zbv_u by exact Hz. reflexivity. Qed.

Lemma v_add_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb. unfold v_add. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_sub_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b Ha Hb. unfold v_sub. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_or_zero : forall (x : word), v_or x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_r. apply zbv_self.
Qed.

Lemma v_or_zero_l : forall (x : word), v_or (Z_to_bv 64 0) x = x.
Proof.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_l. apply zbv_self.
Qed.

Lemma land_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> Z.land z (2 ^ 64 - 8) = (z / 8 * 8)%Z.
Proof.
  intros z Hz.
  assert (E : (2 ^ 64 - 8)%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  rewrite E. transitivity (Z.ldiff (Z.land z (Z.ones 64)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit z i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_andi_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) (-8) = Z_to_bv 64 (z / 8 * 8).
Proof.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z. rewrite land_m8 by exact Hz. reflexivity.
Qed.

Lemma c_ltu_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma c_eq_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_sltiu_zero1 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma zbv_add1 : forall a, Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  apply Zplus_mod_idemp_l.
Qed.


Lemma bv_eq_dec : forall n (a b : bv n), {a = b} + {a <> b}.
Proof.
  intros n0 a b. destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
  - left. apply bv_eq. exact E.
  - right. intros ->. apply NE. reflexivity.
Qed.

Section WithSegs.
Variable SEGS : list Segment.

Lemma wbytes_none_back : forall bs m a x, wbytes m a bs x = None -> m x = None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn [wbytes] in H; [exact H|].
  apply IH in H. destruct (bv_eqb x a); [discriminate | exact H].
Qed.
Lemma store_ok1_wbytes : forall m a bs x,
  store_ok SEGS m x 1 = true -> store_ok SEGS (wbytes m a bs) x 1 = true.
Proof.
  intros m a bs x H. cbn [store_ok] in H |- *. unfold wview in H |- *.
  destruct (wbytes m a bs x) eqn:E; [reflexivity|].
  rewrite (wbytes_none_back _ _ _ _ E) in H. exact H.
Qed.

Lemma store_ok_bytes : forall nb m (a : Z),
  (0 <= a)%Z -> (a + Z.of_nat nb < 2 ^ 64)%Z ->
  (forall j, (0 <= j < Z.of_nat nb)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) nb = true.
Proof.
  induction nb as [|nb IH]; intros m a Ha Hw H; [reflexivity|].
  cbn [store_ok]. pose proof (H 0%Z ltac:(lia)) as H0. cbn [store_ok] in H0. rewrite Z.add_0_r in H0.
  destruct (wview SEGS m (Z_to_bv 64 a)); [|discriminate].
  rewrite zbv_add1. apply IH; [lia|lia|].
  intros j Hj. replace (a + 1 + j)%Z with (a + (1 + j))%Z by lia. apply H. lia.
Qed.
Lemma store_ok8_bytes : forall m (a : Z),
  (0 <= a)%Z -> (a + 8 < 2 ^ 64)%Z ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) 8 = true.
Proof. intros m a Ha Hw H. apply store_ok_bytes; [exact Ha | cbn; lia | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


End WithSegs.
