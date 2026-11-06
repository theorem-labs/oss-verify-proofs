From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.

Definition T0z : list Z :=
  [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x40; 0xab; 0x00; 0x00; 0x01; 0x88; 0x19; 0x00; 0x00].

Definition T0 : list byte := bl T0z.

Definition F50 (ch p v : Z) : list byte := T0 ++ GA ch p v.

Lemma length_F50 : forall ch p v, length (F50 ch p v) = 50%nat.
Proof. reflexivity. Qed.

Lemma u8_lit : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. exact Hx.
Qed.

Lemma eff_range : forall T t ch p, 0 <= eff T t ch p < 256.
Proof.
  intros. unfold eff, dflt, tb.
  destruct (3 <=? p); [lia|].
  destruct ((t =? 0) || (48 <=? ch)); [destruct (p =? 2); lia|].
  destruct (_ =? 0); [destruct (p =? 2); lia|].
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (3 * ch + p)) T (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma F50_ga_sum : forall ch p v,
  (1 + 1 + ch + p + v + ga_r ch p v) mod 128 = 0.
Proof. intros. apply GA_record_sum. Qed.

Lemma ga_r_range : forall ch p v, 0 <= ga_r ch p v < 128.
Proof. intros. unfold ga_r. apply Z.mod_pos_bound. lia. Qed.

Lemma ga_c_range : forall ch p v, 0 <= ga_c ch p v < 256.
Proof. intros. unfold ga_c. apply Z.mod_pos_bound. lia. Qed.
