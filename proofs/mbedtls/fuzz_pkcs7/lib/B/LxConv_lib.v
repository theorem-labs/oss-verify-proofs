From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Asn1Aux.
Import ListNotations.
Open Scope Z_scope.


Lemma ro_byte_of_bytes : forall segs m BUF bs a,
  bytes_at segs m BUF bs -> BUF <= a -> a < BUF + Z.of_nat (length bs) ->
  ro_cells segs m a [C1 (Z_to_bv 8 (bv_unsigned (nth (Z.to_nat (a - BUF)) bs (Z_to_bv 8 0))))].
Proof.
  intros segs m BUF bs a [H0 [H1 H]] Ha1 Ha2.
  rewrite Z_to_bv_bv_unsigned.
  split; [cbn; tauto|].
  cbn [cells_bytes cbytes app].
  assert (Hi : (Z.to_nat (a - BUF) < length bs)%nat) by lia.
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. cbn [nth_error].
  replace (a + Z.of_nat 0) with (BUF + Z.of_nat (Z.to_nat (a - BUF))) by lia.
  rewrite H by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Lemma byte_range : forall (b : bv 8), 0 <= bv_unsigned b <= 255.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma lor_256_byte : forall v b, 0 <= v -> 0 <= b < 256 -> Z.lor (256 * v) b = 256 * v + b.
Proof.
  intros v b Hv Hb.
  transitivity (Z.lor (Z.shiftl v 8) b).
  { f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. }
  rewrite lor_shl8_byte by lia. lia.
Qed.

Lemma rw_cells_eq : forall segs m a cs cs', rw_cells segs m a cs -> cs = cs' -> rw_cells segs m a cs'.
Proof. intros; subst; assumption. Qed.

Lemma ro_cells_eq : forall segs m a cs cs', ro_cells segs m a cs -> cs = cs' -> ro_cells segs m a cs'.
Proof. intros; subst; assumption. Qed.

Ltac lxc_cell_eq := first [ reflexivity | (do 2 f_equal; lia) ].
Ltac lxc_cells_eq :=
  lazymatch goal with
  | |- @eq (list cell) (cons _ _) (cons _ _) => apply (f_equal2 (@cons cell)); [lxc_cell_eq | lxc_cells_eq]
  | |- @eq (list cell) nil nil => reflexivity
  end.

Ltac lxc_cells_conv :=
  lazymatch goal with
  | |- rw_cells ?sg ?mm ?a _ =>
      match goal with H : rw_cells sg mm a _ |- _ => eapply (rw_cells_eq sg mm a _ _ H); lxc_cells_eq end
  | |- ro_cells ?sg ?mm ?a _ =>
      match goal with H : ro_cells sg mm a _ |- _ => eapply (ro_cells_eq sg mm a _ _ H); lxc_cells_eq end
  end.

Lemma uw64' : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. cbn in H. lia. Qed.

Ltac lxc_b2z :=
  lazymatch goal with |- context [Z.b2z (?a <? ?b)] => destruct (Z.ltb_spec a b) end;
  cbn [Z.b2z Z.opp] in *; rewrite ?Z.land_m1_l, ?Z.land_0_l in *; rewrite ?uw64' by lia; try lia.
