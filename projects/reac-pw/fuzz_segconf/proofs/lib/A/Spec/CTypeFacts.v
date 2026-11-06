From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import CType.
Import ListNotations.
Open Scope Z_scope.

Lemma swrap32_eqm : forall x y, x mod 2^32 = y mod 2^32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
  intros x y H. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^32) with 4294967296 in H.
  rewrite <- (Zplus_mod_idemp_l x), <- (Zplus_mod_idemp_l y), H. reflexivity.
Qed.

Lemma swrap32_range : forall z, -2^31 <= bv_swrap 32 z < 2^31.
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

Lemma byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma space_t : forall b : byte, bv_unsigned b = 32 \/ 9 <= bv_unsigned b <= 13 -> c_space b = true.
Proof.
  intros b H. unfold c_space.
  destruct (Z.eqb_spec (bv_unsigned b) 32); destruct (Z.leb_spec 9 (bv_unsigned b));
    destruct (Z.leb_spec (bv_unsigned b) 13); cbn; try reflexivity; lia.
Qed.

Lemma space_f : forall b : byte, bv_unsigned b <> 32 -> ~ (9 <= bv_unsigned b <= 13) -> c_space b = false.
Proof.
  intros b H1 H2. unfold c_space.
  destruct (Z.eqb_spec (bv_unsigned b) 32); destruct (Z.leb_spec 9 (bv_unsigned b));
    destruct (Z.leb_spec (bv_unsigned b) 13); cbn; try reflexivity; lia.
Qed.

Lemma digit_t : forall b : byte, 48 <= bv_unsigned b <= 57 -> c_digit b = true.
Proof.
  intros b H. unfold c_digit.
  destruct (Z.leb_spec 48 (bv_unsigned b)); destruct (Z.leb_spec (bv_unsigned b) 57); cbn; try reflexivity; lia.
Qed.

Lemma digit_f : forall b : byte, ~ (48 <= bv_unsigned b <= 57) -> c_digit b = false.
Proof.
  intros b H. unfold c_digit.
  destruct (Z.leb_spec 48 (bv_unsigned b)); destruct (Z.leb_spec (bv_unsigned b) 57); cbn; try reflexivity; lia.
Qed.

Lemma nth_txt : forall (str : list byte) j, (j <= length str)%nat -> exists b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b.
Proof.
  intros str j H. destruct (nth_error (str ++ [Z_to_bv 8 0]) j) eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma txt_cases : forall (str : list byte) j b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  (j < length str /\ skipn j str = b :: skipn (S j) str)%nat \/ (j = length str /\ b = Z_to_bv 8 0 /\ skipn j str = []).
Proof.
  intros str j b H HJ. destruct (Nat.lt_ge_cases j (length str)) as [L|L].
  - left. split; [exact L|]. rewrite nth_error_app1 in H by exact L.
    clear HJ L. revert j H. induction str as [|x str IH]; intros [|j] H; cbn in H |- *; try discriminate.
    + injection H as ->. reflexivity.
    + apply IH. exact H.
  - right. assert (j = length str) by lia. subst j. split; [reflexivity|].
    rewrite nth_error_app2 in H by lia. rewrite Nat.sub_diag in H. cbn in H. injection H as <-.
    split; [reflexivity|]. apply skipn_all.
Qed.

Lemma txt_nz_lt : forall (str : list byte) j b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  bv_unsigned b <> 0 -> (j < length str)%nat.
Proof.
  intros str j b H HJ NZ. destruct (txt_cases str j b H HJ) as [(L & _) | (L & -> & _)]; [exact L|].
  exfalso. apply NZ. reflexivity.
Qed.

