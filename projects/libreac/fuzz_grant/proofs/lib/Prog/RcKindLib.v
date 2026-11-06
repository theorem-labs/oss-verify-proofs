From Stdlib Require Import String ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind.
Import ListNotations.
Open Scope Z_scope.

Lemma KL1_spec : forall x,
  (x = 0 /\ KL1 x = 2) \/ (x = 1 /\ KL1 x = 3) \/ (x = 16 /\ KL1 x = 10) \/
  ((x = 128 \/ x = 130 \/ x = 132) /\ KL1 x = 9) \/ (x = 129 /\ KL1 x = 7) \/
  (x <> 0 /\ x <> 1 /\ x <> 16 /\ x <> 128 /\ x <> 129 /\ x <> 130 /\ x <> 132 /\ KL1 x = 13).
Proof.
  intros x. unfold KL1.
  destruct (Z.eqb_spec x 0) as [E|E0]; [subst x; left; split; reflexivity|].
  destruct (Z.eqb_spec x 1) as [E|E1]; [subst x; right; left; split; reflexivity|].
  destruct (Z.eqb_spec x 16) as [E|E2]; [subst x; do 2 right; left; split; reflexivity|].
  destruct (Z.eqb_spec x 128) as [E|E3]; [subst x; do 3 right; left; split; [left|]; reflexivity|].
  destruct (Z.eqb_spec x 129) as [E|E4]; [subst x; do 4 right; left; split; reflexivity|].
  destruct (Z.eqb_spec x 130) as [E|E5]; [subst x; do 3 right; left; split; [right; left|]; reflexivity|].
  destruct (Z.eqb_spec x 132) as [E|E6]; [subst x; do 3 right; left; split; [right; right|]; reflexivity|].
  do 5 right. repeat split; first [assumption | reflexivity].
Qed.

Lemma rc_signed_cases : forall x : word,
  0 <= bv_unsigned x < 2^64 /\
  ((bv_signed x = bv_unsigned x /\ bv_unsigned x < 2^63) \/
   (bv_signed x = bv_unsigned x - 2^64 /\ 2^63 <= bv_unsigned x)).
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 64) with (2^64) in Hr. split; [exact Hr|].
  rewrite zb_signed. destruct (Z.ltb_spec (bv_unsigned x) (2^63)); [left|right]; split; (reflexivity || lia).
Qed.

Lemma rc_word_le13 : forall a : word, bv_unsigned a <= 13 ->
  a = Z_to_bv 64 0 \/ a = Z_to_bv 64 1 \/ a = Z_to_bv 64 2 \/ a = Z_to_bv 64 3 \/ a = Z_to_bv 64 4 \/
  a = Z_to_bv 64 5 \/ a = Z_to_bv 64 6 \/ a = Z_to_bv 64 7 \/ a = Z_to_bv 64 8 \/ a = Z_to_bv 64 9 \/
  a = Z_to_bv 64 10 \/ a = Z_to_bv 64 11 \/ a = Z_to_bv 64 12 \/ a = Z_to_bv 64 13.
Proof.
  intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
  rewrite <- (Z_to_bv_bv_unsigned a).
  assert (bv_unsigned a = 0 \/ bv_unsigned a = 1 \/ bv_unsigned a = 2 \/ bv_unsigned a = 3 \/ bv_unsigned a = 4 \/
          bv_unsigned a = 5 \/ bv_unsigned a = 6 \/ bv_unsigned a = 7 \/ bv_unsigned a = 8 \/ bv_unsigned a = 9 \/
          bv_unsigned a = 10 \/ bv_unsigned a = 11 \/ bv_unsigned a = 12 \/ bv_unsigned a = 13) as H by lia.
  repeat (destruct H as [H|H]; [rewrite H; auto 20|]). rewrite H. auto 20.
Qed.

Lemma rc_Z_to_bv_mod : forall z v, z mod 2^64 = v -> Z_to_bv 64 z = Z_to_bv 64 v.
Proof.
  intros z v E. subst v. apply bv_eq. rewrite !unsigned_lit_wrap. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Ltac rc_wrap_lits :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] =>
      is_Zlit z;
      let v := eval vm_compute in (z mod 2^64) in
      tryif constr_eq v z then fail else rewrite (rc_Z_to_bv_mod z v) by (vm_compute; reflexivity)
  end.

Lemma rc_Z_le13 : forall x, 0 <= x <= 13 ->
  x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/
  x = 12 \/ x = 13.
Proof. intros x Hx. lia. Qed.

Lemma kind_name_big : forall x, 13 < x -> kind_name x = "?"%string.
Proof. intros x Hx. unfold kind_name. rewrite (proj2 (Z.leb_gt x 13) Hx). reflexivity. Qed.

Lemma rc_ro_in_image : forall segs m a bs, mem_inv segs m ->
  (ro_bytes_b segs a bs && (0 <=? a) && (a + Z.of_nat (length bs) <=? 2^64))%bool = true ->
  bytes_at segs m a bs.
Proof.
  intros segs m a bs Hm H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3.
  apply ro_bytes_at; [exact Hm | exact H2 | exact H3 |]. apply ro_bytes_b_sound. exact H1.
Qed.
