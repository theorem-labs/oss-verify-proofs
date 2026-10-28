(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma strncmp_walk_zero_prefix : forall k l r,
  strncmp_walk l r k = Some 0 -> (forall j b, (j <= k)%nat -> nth_error r j = Some b -> bv_unsigned b <> 0) ->
  (k < length r)%nat -> firstn (S k) l = firstn (S k) r.
Proof.
  induction k as [|k IH]; intros [|a l] [|b r] H NZ LR; cbn in H, LR; try discriminate; try lia.
  - assert (NB : bv_unsigned b <> 0) by (apply (NZ 0%nat b); [lia| reflexivity]).
    destruct (_ || _)%bool eqn:C; [| cbn in H]; injection H; intros E; cbn; f_equal; apply bv_eq; lia.
  - assert (NB : bv_unsigned b <> 0) by (apply (NZ 0%nat b); [lia| reflexivity]).
    destruct (Z.eqb_spec (bv_unsigned a) 0) as [A0|A0]; cbn [orb] in H. { injection H; intros E. exfalso. lia. }
    destruct (Z.eqb_spec (bv_unsigned b) 0) as [B0|B0]; cbn [orb] in H; [exfalso; exact (NB B0)|].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [AB|AB]; cbn [negb orb] in H; [| injection H; intros E; exfalso; lia].
    assert (EAB : a = b) by (apply bv_eq; exact AB). subst a.
    change (firstn (S (S k)) (b :: l)) with (b :: firstn (S k) l). change (firstn (S (S k)) (b :: r)) with (b :: firstn (S k) r). f_equal.
    apply IH; [exact H| intros j b' Hj Hb'; apply (NZ (S j) b'); [lia| exact Hb']| lia].
Qed.

Lemma strncmp_model_zero_prefix : forall l r n,
  strncmp_model l r n = Some 0 -> 0 <= n -> (Z.to_nat n <= length r)%nat ->
  (forall j b, (j < Z.to_nat n)%nat -> nth_error r j = Some b -> bv_unsigned b <> 0) ->
  firstn (Z.to_nat n) l = firstn (Z.to_nat n) r.
Proof.
  intros l r n H Hn LR NZ. unfold strncmp_model in H. destruct (Z.eqb_spec n 0) as [E0|N0]. { rewrite E0. reflexivity. }
  assert (EN : Z.to_nat n = S (Z.to_nat (n - 1))) by lia. rewrite EN in LR, NZ |- *.
  apply strncmp_walk_zero_prefix; [exact H| intros j b Hj Hb; apply (NZ j b); [lia| exact Hb]| lia].
Qed.

(* [comment removed for export] *)
Definition pem_begin_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x20527 11 with Some bs => bs | None => [] end).
Definition pem_tail6_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x341ae 6 with Some bs => bs | None => [] end).
Lemma pem_begin_ro : ro_bytes Image.usegs 0x20527 pem_begin_str.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_tail6_ro : ro_bytes Image.usegs 0x341ae pem_tail6_str.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_begin_len : length pem_begin_str = 11%nat. Proof. reflexivity. Qed.
Lemma pem_tail6_len : length pem_tail6_str = 6%nat. Proof. reflexivity. Qed.
Lemma pem_begin_nonul : forall j b, (j < 11)%nat -> nth_error pem_begin_str j = Some b -> bv_unsigned b <> 0.
Proof.
  intros j b Hj Hb. do 11 (destruct j as [|j]; [cbn in Hb; injection Hb; intros <-; vm_compute; discriminate|]). lia.
Qed.
Lemma pem_tail6_nonul : forall j b, (j < 6)%nat -> nth_error pem_tail6_str j = Some b -> bv_unsigned b <> 0.
Proof.
  intros j b Hj Hb. do 6 (destruct j as [|j]; [cbn in Hb; injection Hb; intros <-; vm_compute; discriminate|]). lia.
Qed.

(* [comment removed for export] *)
Lemma pem_begin_tail_apart : forall (bs : list byte) (p : nat),
  (17 <= length bs)%nat -> firstn 11 bs = pem_begin_str -> firstn 6 (skipn p bs) = pem_tail6_str -> (11 <= p)%nat.
Proof.
  intros bs p LEN HB HT.
  destruct (Nat.lt_ge_cases p 11) as [HP|HP]; [exfalso| exact HP].
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16 rest]]]]]]]]]]]]]]]]];
    try (cbn in LEN; lia).
  cbn in HB. injection HB; intros E10 E9 E8 E7 E6 E5 E4 E3 E2 E1 E0.
  subst.
  do 11 (destruct p as [|p]; [cbn in HT; injection HT; intros; discriminate|]).
  lia.
Qed.

(* [comment removed for export] *)
Lemma pem_begin_tail_17 : forall (bs : list byte) (len' : Z),
  6 <= len' -> (17 <= length bs)%nat -> firstn 11 bs = pem_begin_str -> firstn 6 (skipn (Z.to_nat (len' - 6)) bs) = pem_tail6_str -> 17 <= len'.
Proof.
  intros bs len' H6 LEN HB HT. pose proof (pem_begin_tail_apart bs (Z.to_nat (len' - 6)) LEN HB HT). lia.
Qed.

(* [comment removed for export] *)
Lemma strncmp_walk_range : forall k l r v, strncmp_walk l r k = Some v -> -255 <= v <= 255.
Proof.
  induction k as [|k IH]; intros [|a l] [|b r] v H; cbn in H; try discriminate;
    pose proof (bv_unsigned_in_range 8 a) as Ha; pose proof (bv_unsigned_in_range 8 b) as Hb; change (bv_modulus 8) with 256 in Ha, Hb.
  - destruct (_ || _)%bool; injection H; intros <-; lia.
  - destruct (_ || _)%bool; [injection H; intros <-; lia| exact (IH _ _ _ H)].
Qed.
Lemma strncmp_model_range : forall l r n v, strncmp_model l r n = Some v -> -255 <= v <= 255.
Proof. intros l r n v H. unfold strncmp_model in H. destruct (n =? 0); [injection H; intros <-; lia| exact (strncmp_walk_range _ _ _ _ H)]. Qed.
Lemma strncmp_reg_zero : forall l r n v, strncmp_model l r n = Some v -> Z.land v 18446744073709551615 = 0 -> v = 0.
Proof.
  intros l r n v H HZ. pose proof (strncmp_model_range _ _ _ _ H) as R.
  change 18446744073709551615 with (2 ^ 64 - 1) in HZ. rewrite zb_land_mask in HZ by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma strncmp_reg_nonzero : forall l r n v, strncmp_model l r n = Some v -> Z.land v 18446744073709551615 <> 0 -> v <> 0.
Proof. intros l r n v H HZ ->. apply HZ. reflexivity. Qed.
