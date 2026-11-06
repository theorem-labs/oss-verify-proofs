From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition fits (base width : Z) : bool :=
  (1 <=? width) && (width <=? 40) && (0 <=? base) && (base + width <=? 48).

Definition int32 (z : Z) : Prop := -2^31 <= z < 2^31.

Lemma mod64_mod32 : forall y, (y mod 18446744073709551616) mod 4294967296 = y mod 4294967296.
Proof. intros. symmetry. apply Zmod_div_mod; [lia|lia|]. exists 4294967296. reflexivity. Qed.

Lemma swrap32_mod64 : forall a b, bv_swrap 32 (a mod 18446744073709551616 + b) = bv_swrap 32 (a + b).
Proof.
  intros. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  f_equal. rewrite <- (Zplus_mod_idemp_l (a mod 18446744073709551616 + b)), <- (Zplus_mod_idemp_l (a + b)).
  rewrite <- (Zplus_mod_idemp_l (a mod 18446744073709551616)), <- (Zplus_mod_idemp_l a).
  rewrite mod64_mod32. reflexivity.
Qed.

Lemma swrap32_id : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed64_small : forall z, -9223372036854775808 <= z < 9223372036854775808 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_half_modulus 64) with 9223372036854775808.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
