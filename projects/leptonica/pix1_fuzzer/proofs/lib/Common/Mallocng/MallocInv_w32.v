(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocOps MallocInv_word.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.


(* [comment removed for export] *)
Definition sx32 (x : Z) : Z :=
  let r := x mod 2^32 in if r <? 2^31 then r else r + (2^64 - 2^32).

Definition w32 (x : Z) : word := Z_to_bv 64 (bv_swrap 32 x).

Lemma land_le_left : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  assert (Hd : Z.land (Z.land a b) (Z.ldiff a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hd) as E.
  rewrite Z.lxor_lor in E by exact Hd. rewrite Z.lor_comm, Z.lor_ldiff_and in E.
  pose proof (Z.ldiff_nonneg a b). lia.
Qed.

Lemma land_range32 : forall a b, 0 <= a < 2^32 -> 0 <= b -> 0 <= Z.land a b < 2^32.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|]. apply Z.le_lt_trans with a; [apply land_le_left; lia | lia].
Qed.

Lemma lor_range32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= Z.lor a b < 2^32.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [Ea|Na]. { rewrite Ea, Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [Eb|Nb]. { rewrite Eb, Z.lor_0_r. lia. }
  assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (NE : Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia).
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma sx32_range : forall x, 0 <= sx32 x < 2^64.
Proof.
  intros x. unfold sx32. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (x mod 2^32 <? 2^31) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma sx32_mod : forall x, sx32 (x mod 2^32) = sx32 x.
Proof. intros x. unfold sx32. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma swrap32_sx32 : forall x, Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 (sx32 x).
Proof.
  intros x. rewrite swrap32_eq. unfold sx32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as Hr.
  set (r := x mod 2^32) in *.
  assert (E : (x + 2^31) mod 2^32 = (r + 2^31) mod 2^32).
  { subst r. rewrite <- Z.add_mod_idemp_l by lia. reflexivity. }
  rewrite E. destruct (r <? 2^31) eqn:L; [apply Z.ltb_lt in L | apply Z.ltb_ge in L].
  - rewrite Z.mod_small by lia. f_equal. lia.
  - replace ((r + 2^31) mod 2^32) with (r + 2^31 - 2^32).
    2:{ replace (r + 2^31) with ((r + 2^31 - 2^32) + 1 * 2^32) at 2 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite <- ZZ_mod. f_equal.
    replace (r + 2^31 - 2^32 - 2^31) with ((r + (2^64 - 2^32)) + (-1) * 2^64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma w32_eq : forall x, w32 x = Z_to_bv 64 (sx32 x).
Proof. intros x. apply swrap32_sx32. Qed.

Lemma w32_mod : forall x, w32 (x mod 2^32) = w32 x.
Proof. intros x. rewrite !w32_eq, sx32_mod. reflexivity. Qed.

Lemma u_w32 : forall x, bv_unsigned (w32 x) = sx32 x.
Proof. intros x. rewrite w32_eq. apply uZ. apply sx32_range. Qed.

(* [comment removed for export] *)
Lemma sx32_testbit : forall x j, 0 <= x < 2^32 -> 0 <= j ->
  Z.testbit (sx32 x) j = if j <? 32 then Z.testbit x j else if j <? 64 then Z.testbit x 31 else false.
Proof.
  intros x j Hx Hj. unfold sx32. rewrite Z.mod_small by lia.
  destruct (x <? 2^31) eqn:L; [apply Z.ltb_lt in L | apply Z.ltb_ge in L].
  - assert (B31 : Z.testbit x 31 = false).
    { destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
    destruct (j <? 32) eqn:J; [reflexivity|]. apply Z.ltb_ge in J.
    rewrite B31. destruct (j <? 64);
      (destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|]; apply Z.bits_above_log2; [lia|];
       apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; lia | lia]).
  - assert (B31 : Z.testbit x 31 = true).
    { apply Z.testbit_true; [lia|].
      replace (x / 2^31) with 1; [reflexivity|]. apply (Z.div_unique x (2^31) 1 (x - 2^31)); lia. }
    (* [comment removed for export] *)
    assert (D : Z.land x (2^64 - 2^32) = 0).
    { rewrite land_high_mask by lia. rewrite Z.mod_small by lia. lia. }
    rewrite (Z.add_nocarry_lxor _ _ D), (Z.lxor_lor _ _ D), Z.lor_spec.
    rewrite testbit_high_mask by lia.
    destruct (j <? 32) eqn:J.
    + apply Z.ltb_lt in J. replace (32 <=? j) with false by (symmetry; apply Z.leb_gt; lia). cbn. apply orb_false_r.
    + apply Z.ltb_ge in J. replace (32 <=? j) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      assert (Bx : Z.testbit x j = false).
      { apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32; [apply Z.log2_lt_pow2; lia | lia]. }
      rewrite Bx, B31. cbn [orb]. destruct (j <? 64); reflexivity.
Qed.

Lemma land_sx32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 ->
  Z.land (sx32 a) (sx32 b) = sx32 (Z.land a b).
Proof.
  intros a b Ha Hb.
  pose proof (land_range32 a b ltac:(lia) ltac:(lia)) as Hab.
  apply Z.bits_inj'. intros j Hj.
  rewrite Z.land_spec, !sx32_testbit by lia. rewrite !Z.land_spec.
  destruct (j <? 32); [reflexivity|]. destruct (j <? 64); [reflexivity | reflexivity].
Qed.

Lemma lor_sx32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 ->
  Z.lor (sx32 a) (sx32 b) = sx32 (Z.lor a b).
Proof.
  intros a b Ha Hb.
  pose proof (lor_range32 a b Ha Hb) as Hab.
  apply Z.bits_inj'. intros j Hj.
  rewrite Z.lor_spec, !sx32_testbit by lia. rewrite !Z.lor_spec.
  destruct (j <? 32); [reflexivity|]. destruct (j <? 64); [reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma v_and_w32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> v_and (w32 a) (w32 b) = w32 (Z.land a b).
Proof.
  intros a b Ha Hb. rewrite !w32_eq. rewrite v_and_Z by apply sx32_range. f_equal.
  rewrite land_sx32 by lia. reflexivity.
Qed.

Lemma v_or_w32 : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> v_or (w32 a) (w32 b) = w32 (Z.lor a b).
Proof.
  intros a b Ha Hb. rewrite !w32_eq. rewrite v_or_Z by apply sx32_range. f_equal.
  rewrite lor_sx32 by lia. reflexivity.
Qed.

Lemma sx32_eqmod : forall x, (sx32 x) mod 2^32 = x mod 2^32.
Proof.
  intros x. unfold sx32. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (x mod 2^32 <? 2^31) eqn:L; [apply Z.ltb_lt in L | apply Z.ltb_ge in L].
  - apply Z.mod_mod. lia.
  - replace (x mod 2^32 + (2^64 - 2^32)) with (x mod 2^32 + (2^32 - 1) * 2^32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma v_addw_w32 : forall a b, v_addw (w32 a) (w32 b) = w32 (a + b).
Proof.
  intros a b. unfold v_addw. rewrite !u_w32. unfold w32. rewrite !swrap32_eq. f_equal.
  rewrite <- (Z.add_mod_idemp_l (sx32 a + sx32 b)) by lia.
  rewrite <- (Z.add_mod_idemp_l (a + b)) by lia. f_equal. f_equal. f_equal.
  rewrite Z.add_mod, !sx32_eqmod, <- Z.add_mod by lia. reflexivity.
Qed.

Lemma v_addiw_w32 : forall a i, v_addiw (w32 a) i = w32 (a + i).
Proof.
  intros a i. unfold v_addiw. rewrite u_w32. unfold w32. rewrite !swrap32_eq. f_equal.
  rewrite <- (Z.add_mod_idemp_l (sx32 a + i)) by lia.
  rewrite <- (Z.add_mod_idemp_l (a + i)) by lia. f_equal. f_equal. f_equal.
  rewrite Z.add_mod, sx32_eqmod, <- Z.add_mod by lia. reflexivity.
Qed.

Lemma v_sllw_1 : forall i, 0 <= i < 32 -> v_sllw (wlit 1) (Z_to_bv 64 i) = w32 (2^i).
Proof.
  intros i Hi. unfold wlit. rewrite v_sllw_Z by lia. rewrite Z.mod_small by lia. unfold w32. f_equal. f_equal. lia.
Qed.

Lemma v_sllw_2 : forall i, 0 <= i < 2^64 -> v_sllw (wlit 2) (Z_to_bv 64 i) = w32 (2^(i mod 32 + 1)).
Proof.
  intros i Hi. unfold wlit. rewrite v_sllw_Z by lia. unfold w32. f_equal. f_equal.
  rewrite Z.pow_add_r by (pose proof (Z.mod_pos_bound i 32); lia). lia.
Qed.

Lemma v_lw_w32 : forall a, 0 <= a < 2^64 -> v_lw (Z_to_bv 64 a) = w32 a.
Proof. intros a Ha. apply v_lw_Z. exact Ha. Qed.

(* [comment removed for export] *)
Lemma is0_w32 : forall a, is0 (w32 a) = (a mod 2^32 =? 0).
Proof.
  intros a. rewrite w32_eq, is0_Z by apply sx32_range.
  unfold sx32. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
  destruct (a mod 2^32 <? 2^31) eqn:L; [reflexivity|]. apply Z.ltb_ge in L.
  rewrite (proj2 (Z.eqb_neq _ 0)) by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma c_eq_w32 : forall a b, c_eq (w32 a) (w32 b) = (a mod 2^32 =? b mod 2^32).
Proof.
  intros a b. rewrite !w32_eq, c_eq_Z by apply sx32_range.
  rewrite <- (sx32_mod a), <- (sx32_mod b).
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^32) ltac:(lia)).
  set (x := a mod 2^32) in *. set (y := b mod 2^32) in *.
  destruct (Z.eq_dec x y) as [E|NE].
  - rewrite E, Z.eqb_refl. symmetry. apply Z.eqb_eq. reflexivity.
  - rewrite (proj2 (Z.eqb_neq x y) NE). apply Z.eqb_neq. intros E. apply NE.
    rewrite <- (Z.mod_small x (2^32)), <- (Z.mod_small y (2^32)) by lia.
    rewrite <- (sx32_eqmod x), <- (sx32_eqmod y), E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_pow2_testbit : forall m i, 0 <= m -> 0 <= i -> (Z.land m (2^i) =? 0) = negb (Z.testbit m i).
Proof.
  intros m i Hm Hi. destruct (Z.testbit m i) eqn:B; cbn [negb].
  - apply Z.eqb_neq. intros E.
    pose proof (Z.land_spec m (2^i) i) as Hs. rewrite E, Z.bits_0, B, Z.pow2_bits_true in Hs by lia. discriminate.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eq_dec i j) as [<-|NE]; [rewrite B; reflexivity|].
    rewrite (proj2 (Z.eqb_neq i j) NE). apply andb_false_r.
Qed.

Lemma mask_bit_test : forall m i, 0 <= m < 2^32 -> 0 <= i < 32 ->
  is0 (v_and (w32 m) (w32 (2^i))) = negb (Z.testbit m i).
Proof.
  intros m i Hm Hi.
  assert (Hp : 0 <= 2^i < 2^32) by (split; [lia | apply Z.pow_lt_mono_r; lia]).
  rewrite v_and_w32 by lia. rewrite is0_w32.
  rewrite Z.mod_small by (apply land_range32; lia).
  apply land_pow2_testbit; lia.
Qed.

End WithLayout.
