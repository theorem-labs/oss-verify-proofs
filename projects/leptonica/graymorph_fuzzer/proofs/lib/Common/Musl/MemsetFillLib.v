(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec StartupTac RefMemcpyLib MemSplit StoreOk.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cf (c8 : byte) (m : word -> option byte) (d : Z) (l : list (Z * Z)) : word -> option byte :=
  fun x => if inzr (bv_unsigned x - d) l then Some c8 else m x.

Lemma cf_nil : forall c8 m d, cf c8 m d [] = m.
Proof. intros c8 m d. apply functional_extensionality. intros x. reflexivity. Qed.

Lemma cf_ext : forall c8 m d l1 l2, (forall i, inzr i l1 = inzr i l2) -> cf c8 m d l1 = cf c8 m d l2.
Proof. intros c8 m d l1 l2 H. apply functional_extensionality. intros x. unfold cf. rewrite H. reflexivity. Qed.

Lemma cf_extP : forall c8 m d l1 l2, (forall i, inzrP i l1 <-> inzrP i l2) -> cf c8 m d l1 = cf c8 m d l2.
Proof. intros c8 m d l1 l2 H. apply cf_ext. intros i. apply inzr_eqP, H. Qed.

Lemma cf_drop_empty : forall c8 m d lo l, cf c8 m d ((lo, lo) :: l) = cf c8 m d l.
Proof. intros. apply cf_ext. intros i. inzr_tac. Qed.

(* [comment removed for export] *)
Lemma wbytes_cf : forall c8 m d l o (w : nat),
  0 <= d -> 0 <= o -> d + o + Z.of_nat w <= 2 ^ 64 ->
  wbytes (cf c8 m d l) (Z_to_bv 64 (d + o)) (repeat c8 w) = cf c8 m d ((o, o + Z.of_nat w) :: l).
Proof.
  intros c8 m d l o w Hd Ho Hnw.
  destruct w as [|w'].
  { cbn [wbytes repeat Z.of_nat]. rewrite Z.add_0_r. symmetry. apply cf_drop_empty. }
  set (w := S w') in *.
  assert (Hw : 1 <= Z.of_nat w) by (subst w; lia).
  apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z.lt_ge_cases (bv_unsigned x) (d + o)) as [Hlt|Hge].
  - rewrite wbytes_outside by (rewrite repeat_length, u_Z2bv by lia; lia).
    unfold cf. cbn [inzr]. replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w))%bool with false by lia.
    reflexivity.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (d + o + Z.of_nat w)) as [Hin|Hout].
    + rewrite wbytes_inside by (rewrite repeat_length, u_Z2bv by lia; lia).
      assert (NR : forall k, nth k (repeat c8 w) (Z_to_bv 8 0) = c8 \/ (w <= k)%nat).
      { intros k. destruct (Nat.lt_ge_cases k w) as [L|G]; [left | right; exact G].
        rewrite (nth_indep _ _ c8) by (rewrite repeat_length; exact L). apply nth_repeat. }
      destruct (NR (Z.to_nat (bv_unsigned x - bv_unsigned (Z_to_bv 64 (d + o))))) as [E|G].
      * rewrite E. unfold cf. cbn [inzr].
        replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w))%bool with true by lia. reflexivity.
      * exfalso. rewrite u_Z2bv in G by lia. lia.
    + rewrite wbytes_outside by (rewrite repeat_length, u_Z2bv by lia; lia).
      unfold cf. cbn [inzr]. replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w))%bool with false by lia.
      reflexivity.
Qed.

Lemma cf_outside : forall c8 m d l (x : word), inzr (bv_unsigned x - d) l = false -> cf c8 m d l x = m x.
Proof. intros c8 m d l x H. unfold cf. rewrite H. reflexivity. Qed.

Lemma cf_inside : forall c8 m d l (x : word), inzr (bv_unsigned x - d) l = true -> cf c8 m d l x = Some c8.
Proof. intros c8 m d l x H. unfold cf. rewrite H. reflexivity. Qed.

Lemma cf_grows : forall c8 m d l, mem_grows m (cf c8 m d l).
Proof. intros c8 m d l x Hx. unfold cf. destruct (inzr (bv_unsigned x - d) l); [discriminate | exact Hx]. Qed.

Lemma store_ok_cf : forall segs c8 m d l (a : word) n,
  store_ok segs m a n = true -> store_ok segs (cf c8 m d l) a n = true.
Proof. intros. eapply store_ok_mono; [apply cf_grows | eassumption]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint rep256 (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * rep256 k' end.

Lemma fill_bytes : forall (k : nat) c, 0 <= c < 256 -> Z_to_le_bytes k (c * rep256 k) = repeat (Z_to_bv 8 c) k.
Proof.
  induction k as [|k IH]; intros c Hc; [reflexivity|].
  cbn [Z_to_le_bytes repeat rep256]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (c * (1 + 256 * rep256 k)) with (c + (c * rep256 k) * 256) by lia. apply Z_mod_plus_full.
  - rewrite <- (IH c Hc). f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (c * (1 + 256 * rep256 k)) with (c + (c * rep256 k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small c 256) by lia. lia.
Qed.

Definition C32 : Z := 16843009.                 (* [comment removed for export] *)
Definition C64 : Z := 72340172838076673.        (* [comment removed for export] *)

Lemma fill_sb : forall c, 0 <= c < 256 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c)) = Z_to_bv 8 c.
Proof. intros c Hc. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma fill_sw : forall c, 0 <= c < 256 -> word_to_le_bytes 4 (Z_to_bv 64 (c * C32)) = repeat (Z_to_bv 8 c) 4.
Proof.
  intros c Hc. unfold word_to_le_bytes, C32. rewrite u_Z2bv by lia. exact (fill_bytes 4 c Hc).
Qed.

Lemma fill_sd : forall c, 0 <= c < 256 -> word_to_le_bytes 8 (Z_to_bv 64 (c * C64)) = repeat (Z_to_bv 8 c) 8.
Proof.
  intros c Hc. unfold word_to_le_bytes, C64. rewrite u_Z2bv by lia. exact (fill_bytes 8 c Hc).
Qed.

(* [comment removed for export] *)
Lemma fill_mulhu : forall c, 0 <= c < 256 ->
  v_mulhu (Z_to_bv 64 (c * 2 ^ 56)) (Z_to_bv 64 4311810304) = Z_to_bv 64 (c * C32).
Proof.
  intros c Hc. unfold v_mulhu, C32. rewrite !u_Z2bv by lia. f_equal.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (c * 2 ^ 56 * 4311810304) with ((c * 16843009) * 2 ^ 64) by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_shift32 : forall x, 0 <= x < 2 ^ 32 -> Z.lor (x * 2 ^ 32) x = x * 2 ^ 32 + x.
Proof.
  intros x Hx. rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (L0 : Z.land (Z.shiftl x 32) x = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [L|G].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - replace (Z.testbit x i) with false; [apply andb_false_r|].
      symmetry. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 32) by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_lor_land (Z.shiftl x 32) x) as E. rewrite L0 in E. lia.
Qed.

Lemma fill_or64 : forall c, 0 <= c < 256 ->
  v_or (Z_to_bv 64 (c * C32 * 2 ^ 32)) (Z_to_bv 64 (c * C32)) = Z_to_bv 64 (c * C64).
Proof.
  intros c Hc. unfold v_or, C32, C64. rewrite !u_Z2bv by lia. f_equal.
  rewrite lor_shift32 by lia. lia.
Qed.
