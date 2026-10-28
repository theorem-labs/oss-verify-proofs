(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import CidBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope Z_scope.

Definition smear (x : Z) : Z := cb6 (cb5 (cb4 (cb3 (cb2 (cb1 x))))).
Definition popbits (y : Z) : Z := cb11 (cb10 (cb9 (cb8 (cb7 y)))).
Definition clzbits (x : Z) : Z := popbits (smear x).

(* [comment removed for export] *)
Definition st (j y : Z) : Z := Z.lor y (Z.shiftr y j).
Definition smear0 (x : Z) : Z := st 32 (st 16 (st 8 (st 4 (st 2 (st 1 x))))).

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n) by (destruct (Z.neg_nonneg_cases n) as [H|H]; [rewrite Z.pow_neg_r in Ha by lia; lia|exact H]).
  assert (H0 : 0 <= Z.lor a b) by (apply (proj2 (Z.lor_nonneg a b)); lia).
  split; [exact H0|].
  destruct (Z.eq_dec a 0) as [->|A]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftr_le_self : forall y j, 0 <= y -> 0 <= j -> 0 <= Z.shiftr y j <= y.
Proof.
  intros y j Hy Hj. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; [lia|]. assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma st_lt : forall j y n, 0 <= j -> 0 <= y < 2^n -> 0 <= st j y < 2^n.
Proof. intros j y n Hj Hy. unfold st. pose proof (shiftr_le_self y j ltac:(lia) Hj). apply lor_lt_pow2; lia. Qed.

Lemma smear0_lt : forall x n, 0 <= x < 2^n -> 0 <= smear0 x < 2^n.
Proof. intros x n Hx. unfold smear0. repeat (apply st_lt; [lia|]). exact Hx. Qed.

Lemma st_lor : forall j a b, st j (Z.lor a b) = Z.lor (st j a) (st j b).
Proof.
  intros j a b. unfold st. rewrite Z.shiftr_lor.
  rewrite <- !Z.lor_assoc. f_equal. rewrite !Z.lor_assoc. rewrite (Z.lor_comm b (Z.shiftr a j)). reflexivity.
Qed.

Lemma smear0_lor : forall a b, smear0 (Z.lor a b) = Z.lor (smear0 a) (smear0 b).
Proof. intros a b. unfold smear0. rewrite !st_lor. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cb_st : forall j y, 0 <= j -> 0 <= y < 2^64 ->
  Z.lor y (Z.shiftr y j mod 18446744073709551616) mod 18446744073709551616 = st j y.
Proof.
  intros j y Hj Hy. pose proof (shiftr_le_self y j ltac:(lia) Hj) as Hs.
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small (Z.shiftr y j)) by lia.
  rewrite Z.mod_small; [reflexivity|]. apply lor_lt_pow2; lia.
Qed.

Lemma smear_smear0 : forall x, 0 <= x < 2^64 -> smear x = smear0 x.
Proof.
  intros x Hx. unfold smear, smear0, cb1, cb2, cb3, cb4, cb5, cb6.
  rewrite (cb_st 1 x) by lia.
  pose proof (st_lt 1 x 64 ltac:(lia) Hx) as H1.
  rewrite (cb_st 2) by lia. pose proof (st_lt 2 _ 64 ltac:(lia) H1) as H2.
  rewrite (cb_st 4) by lia. pose proof (st_lt 4 _ 64 ltac:(lia) H2) as H3.
  rewrite (cb_st 8) by lia. pose proof (st_lt 8 _ 64 ltac:(lia) H3) as H4.
  rewrite (cb_st 16) by lia. pose proof (st_lt 16 _ 64 ltac:(lia) H4) as H5.
  rewrite (cb_st 32) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_ones_low : forall n t, 0 <= n -> 0 <= t < 2^n -> Z.lor (Z.ones n) t = Z.ones n.
Proof.
  intros n t Hn Ht. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn.
    destruct (Z.eq_dec t 0) as [->|T]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply Z.lt_le_trans with (m := 2^n); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma smear0_pow2_chk : forall_rangeZ (fun k => Z.eqb (smear0 (2^k)) (Z.ones (k+1))) 0 64 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma smear0_pow2 : forall k, 0 <= k < 64 -> smear0 (2^k) = Z.ones (k+1).
Proof. intros k Hk. apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 k smear0_pow2_chk); lia. Qed.

Lemma smear0_eq : forall x, 0 < x < 2^64 -> smear0 x = Z.ones (Z.log2 x + 1).
Proof.
  intros x Hx. set (k := Z.log2 x).
  assert (Hk : 0 <= k < 64).
  { subst k. split; [apply Z.log2_nonneg|]. apply Z.log2_lt_pow2; lia. }
  destruct (Z.log2_spec x ltac:(lia)) as [Hlo Hhi]. fold k in Hlo, Hhi.
  set (r := x - 2^k).
  assert (Hr : 0 <= r < 2^k) by (subst r; rewrite Z.pow_succ_r in Hhi by lia; lia).
  assert (Hx2 : x = Z.lor (2^k) r).
  { rewrite <- Z.lxor_lor.
    - rewrite <- Z.add_nocarry_lxor. + subst r; lia.
      + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec k i); [|reflexivity]. subst i. cbn.
        destruct (Z.eq_dec r 0) as [->|R]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec k i); [|reflexivity]. subst i. cbn.
      destruct (Z.eq_dec r 0) as [->|R]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite Hx2, smear0_lor, smear0_pow2 by lia.
  apply lor_ones_low; [lia|].
  pose proof (smear0_lt r k Hr) as Hs.
  split; [lia|]. apply Z.lt_le_trans with (m := 2^k); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma popbits_chk : forall_rangeZ (fun k => Z.eqb (popbits (Z.ones (k+1))) (63 - k)) 0 64 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem clzbits_eq : forall x, 0 < x < 2^64 -> clzbits x = 63 - Z.log2 x.
Proof.
  intros x Hx. unfold clzbits. rewrite smear_smear0, smear0_eq by lia.
  assert (Hk : 0 <= Z.log2 x < 64) by (split; [apply Z.log2_nonneg|apply Z.log2_lt_pow2; lia]).
  apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 (Z.log2 x) popbits_chk); lia.
Qed.

Corollary clzbits_range : forall x, 0 < x < 2^64 -> 0 <= clzbits x <= 63.
Proof. intros x Hx. rewrite clzbits_eq by lia. pose proof (Z.log2_nonneg x). assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. Qed.

(* [comment removed for export] *)
Lemma lxor63_sub : forall c, 0 <= c <= 63 -> Z.lxor c 63 = 63 - c.
Proof.
  intros c Hc.
  assert (E : forall_rangeZ (fun c => Z.eqb (Z.lxor c 63) (63 - c)) 0 64 = true) by (vm_compute; reflexivity).
  apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 c E); lia.
Qed.
