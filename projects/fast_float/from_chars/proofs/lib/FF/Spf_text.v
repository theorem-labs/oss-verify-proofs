(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.

Module Spf_swar.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition isdigZ (z : Z) : Prop := 48 <= z <= 57.

Definition v4 (z0 z1 z2 z3 : Z) : Z := z0 + 256 * (z1 + 256 * (z2 + 256 * z3)).
Definition v8 (z0 z1 z2 z3 z4 z5 z6 z7 : Z) : Z := v4 z0 z1 z2 z3 + 2^32 * v4 z4 z5 z6 z7.

Lemma v4_range : forall z0 z1 z2 z3,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 -> 0 <= v4 z0 z1 z2 z3 < 2^32.
Proof. intros. unfold v4. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_false_high : forall y k i, 0 <= y < 2^k -> 0 <= k <= i -> Z.testbit y i = false.
Proof.
  intros y k i Hy Hk.
  destruct (Z.eq_dec y 0) as [->|Hnz]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|].
  apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_shl_small : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.land (Z.shiftl x k) y = 0.
Proof.
  intros x y k Hx Hy Hk. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (testbit_false_high y k i) by lia. apply andb_false_r.
Qed.

Lemma lor_shl : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.lor (Z.shiftl x k) y = x * 2^k + y.
Proof.
  intros x y k Hx Hy Hk.
  rewrite <- Z.lxor_lor by (apply land_shl_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shl_small; lia).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma lor_mul : forall x y k, 0 <= x -> 0 <= y < 2^k -> 0 <= k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros x y k Hx Hy Hk. rewrite <- (lor_shl x y k) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation U := bv_unsigned.

Lemma ortree4_eq : forall z0 z1 z2 z3,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  Z.lor (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z3) ≪ 24))) (U (Z_to_bv 64 (U (Z_to_bv 64 z2) ≪ 16))))))
        (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z1) ≪ 8))) (U (Z_to_bv 64 z0)))))
  = v4 z0 z1 z2 z3.
Proof.
  intros z0 z1 z2 z3 H0 H1 H2 H3.
  rewrite (unsigned_lit z0), (unsigned_lit z1), (unsigned_lit z2), (unsigned_lit z3) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (z3 * 2^24)), (unsigned_lit (z2 * 2^16)), (unsigned_lit (z1 * 2^8)) by lia.
  rewrite (lor_mul z1 z0 8) by lia.
  rewrite (lor_mul z3 (z2 * 2^16) 24) by lia.
  rewrite (unsigned_lit (z3 * 2^24 + z2 * 2 ^ 16)), (unsigned_lit (z1 * 2^8 + z0)) by lia.
  replace (z3 * 2^24 + z2 * 2 ^ 16) with ((z3 * 2^8 + z2) * 2^16) by lia.
  rewrite (lor_mul (z3 * 2^8 + z2) (z1 * 2^8 + z0) 16) by lia.
  unfold v4. lia.
Qed.

Lemma ortree8_eq : forall z0 z1 z2 z3 z4 z5 z6 z7,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
  Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64
           (Z.lor (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z7) ≪ 24))) (U (Z_to_bv 64 (U (Z_to_bv 64 z6) ≪ 16))))))
                  (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z5) ≪ 8))) (U (Z_to_bv 64 z4))))))) ≪ 32)))
        (U (Z_to_bv 64
           (Z.lor (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z3) ≪ 24))) (U (Z_to_bv 64 (U (Z_to_bv 64 z2) ≪ 16))))))
                  (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (U (Z_to_bv 64 z1) ≪ 8))) (U (Z_to_bv 64 z0))))))))
  = v8 z0 z1 z2 z3 z4 z5 z6 z7.
Proof.
  intros z0 z1 z2 z3 z4 z5 z6 z7 H0 H1 H2 H3 H4 H5 H6 H7.
  rewrite (ortree4_eq z4 z5 z6 z7), (ortree4_eq z0 z1 z2 z3) by lia.
  pose proof (v4_range z0 z1 z2 z3 H0 H1 H2 H3). pose proof (v4_range z4 z5 z6 z7 H4 H5 H6 H7).
  rewrite (unsigned_lit (v4 z4 z5 z6 z7)), (unsigned_lit (v4 z0 z1 z2 z3)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (v4 z4 z5 z6 z7 * 2^32)) by lia.
  rewrite lor_mul by lia. unfold v8. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b2z_inj : forall a b : bool, Z.b2z a = Z.b2z b -> a = b.
Proof. intros [|] [|]; cbn; congruence. Qed.

Lemma testbit_add_mul_low : forall x y k j, 0 <= j < k -> Z.testbit (x + 2^k * y) j = Z.testbit x j.
Proof.
  intros x y k j Hj.
  rewrite <- (Z.mod_pow2_bits_low (x + 2^k * y) k j) by lia.
  rewrite <- (Z.mod_pow2_bits_low x k j) by lia.
  f_equal. rewrite Z.mul_comm. apply Z.mod_add. lia.
Qed.

Lemma testbit_add_mul_high : forall x y k j, 0 <= x < 2^k -> 0 <= k -> 0 <= j ->
  Z.testbit (x + 2^k * y) (j + k) = Z.testbit y j.
Proof.
  intros x y k j Hx Hk Hj. apply b2z_inj. rewrite !Z.testbit_spec' by lia.
  rewrite Z.pow_add_r by lia. rewrite (Z.mul_comm (2^j) (2^k)).
  rewrite <- Z.div_div by lia.
  replace ((x + 2 ^ k * y) / 2 ^ k) with y; [reflexivity|].
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint vl (l : list Z) : Z := match l with [] => 0 | b :: l' => b + 2^8 * vl l' end.
Fixpoint cA (n : nat) : Z := match n with O => 0 | S n' => 70 + 2^8 * cA n' end.        (* [comment removed for export] *)
Fixpoint cB (n : nat) : Z := match n with O => 1 | S n' => 208 + 2^8 * (cB n' - 1) end.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition byte_chk (b : Z) : bool :=
  implb (negb (Z.testbit (b + 70) 7) && negb (Z.testbit (b + 208) 7)) ((48 <=? b) && (b <=? 57)).

Lemma forallb_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall b, 0 <= b < Z.of_nat n -> f b = true.
Proof.
  intros f n H b Hb. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Lemma byte_chk_all : forall b, 0 <= b < 256 -> byte_chk b = true.
Proof.
  apply (forallb_range byte_chk 256). vm_compute. reflexivity.
Qed.

Lemma byte_dig : forall b, 0 <= b < 256 ->
  Z.testbit (b + 70) 7 = false -> Z.testbit (b + 208) 7 = false -> isdigZ b.
Proof.
  intros b Hb HA HB. pose proof (byte_chk_all b Hb) as H. unfold byte_chk in H.
  rewrite HA, HB in H. cbn in H. unfold isdigZ. lia.
Qed.

Lemma peel : forall l,
  Forall (fun b => 0 <= b < 256) l ->
  (forall i, (i < length l)%nat -> Z.testbit (vl l + cA (length l)) (8 * Z.of_nat i + 7) = false) ->
  (forall i, (i < length l)%nat -> Z.testbit (vl l + cB (length l)) (8 * Z.of_nat i + 7) = false) ->
  Forall isdigZ l.
Proof.
  induction l as [|b l IH]; intros HR HA HB; [constructor|].
  inversion HR as [|b' l' Hb Hl]; subst b' l'.
  cbn [vl cA cB length] in HA, HB.
  assert (DA : Z.testbit (b + 70) 7 = false).
  { specialize (HA O ltac:(lia)). change (8 * Z.of_nat 0 + 7) with 7 in HA.
    replace (b + 2 ^ 8 * vl l + (70 + 2 ^ 8 * cA (length l))) with ((b + 70) + 2^8 * (vl l + cA (length l))) in HA by lia.
    rewrite testbit_add_mul_low in HA by lia. exact HA. }
  assert (DB : Z.testbit (b + 208) 7 = false).
  { specialize (HB O ltac:(lia)). change (8 * Z.of_nat 0 + 7) with 7 in HB.
    replace (b + 2 ^ 8 * vl l + (208 + 2 ^ 8 * (cB (length l) - 1))) with ((b + 208) + 2^8 * (vl l + cB (length l) - 1)) in HB by lia.
    rewrite testbit_add_mul_low in HB by lia. exact HB. }
  pose proof (byte_dig b Hb DA DB) as D. unfold isdigZ in D.
  constructor; [exact D|].
  apply IH; [exact Hl| |].
  - intros i Hi. specialize (HA (S i) ltac:(cbn; lia)).
    replace (b + 2 ^ 8 * vl l + (70 + 2 ^ 8 * cA (length l))) with ((b + 70) + 2^8 * (vl l + cA (length l))) in HA by lia.
    rewrite Nat2Z.inj_succ in HA.
    replace (8 * Z.succ (Z.of_nat i) + 7) with ((8 * Z.of_nat i + 7) + 8) in HA by lia.
    rewrite testbit_add_mul_high in HA by lia. exact HA.
  - intros i Hi. specialize (HB (S i) ltac:(cbn; lia)).
    replace (b + 2 ^ 8 * vl l + (208 + 2 ^ 8 * (cB (length l) - 1))) with ((b - 48) + 2^8 * (vl l + cB (length l))) in HB by lia.
    rewrite Nat2Z.inj_succ in HB.
    replace (8 * Z.succ (Z.of_nat i) + 7) with ((8 * Z.of_nat i + 7) + 8) in HB by lia.
    rewrite testbit_add_mul_high in HB by lia. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_mask_bit : forall x M k, 0 <= k < 64 ->
  U (Z_to_bv 64 (Z.land x M)) = 0 -> Z.testbit M k = true -> Z.testbit x k = false.
Proof.
  intros x M k Hk H HM. rewrite unsigned_lit_wrap in H.
  assert (T : Z.testbit ((Z.land x M) mod 2^64) k = false) by (rewrite H; apply Z.bits_0).
  rewrite Z.mod_pow2_bits_low in T by lia. rewrite Z.land_spec, HM, andb_true_r in T. exact T.
Qed.

Lemma lor_bits_false : forall a b k, 0 <= k < 64 ->
  Z.testbit (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 a)) (U (Z_to_bv 64 b))))) k = false ->
  Z.testbit a k = false /\ Z.testbit b k = false.
Proof.
  intros a b k Hk H. rewrite !unsigned_lit_wrap in H.
  rewrite Z.mod_pow2_bits_low in H by lia. rewrite Z.lor_spec in H.
  rewrite !Z.mod_pow2_bits_low in H by lia.
  apply orb_false_iff in H. exact H.
Qed.

Lemma negb_eqb0_false : forall x, negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = false -> U (Z_to_bv 64 x) = 0.
Proof.
  intros x H. apply negb_false_iff in H. unfold bv_eqb in H. apply Z.eqb_eq in H.
  rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swar8_dig : forall V z0 z1 z2 z3 z4 z5 z6 z7,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
  V = v8 z0 z1 z2 z3 z4 z5 z6 z7 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (U (Z_to_bv 64 (Z.lor
          (U (Z_to_bv 64 (V + 5063812098665367110)))
          (U (Z_to_bv 64 (V + 14974415777481871312)))))) 9259542123273814144))
       (Z_to_bv 64 0)) = false ->
  isdigZ z0 /\ isdigZ z1 /\ isdigZ z2 /\ isdigZ z3 /\ isdigZ z4 /\ isdigZ z5 /\ isdigZ z6 /\ isdigZ z7.
Proof.
  intros V z0 z1 z2 z3 z4 z5 z6 z7 H0 H1 H2 H3 H4 H5 H6 H7 HV HC.
  apply negb_eqb0_false in HC.
  assert (VR : 0 <= V < 2^64) by (subst V; unfold v8, v4; lia).
  assert (BITS : forall i, (i < 8)%nat ->
     Z.testbit (V + 5063812098665367110) (8 * Z.of_nat i + 7) = false
     /\ Z.testbit (V + 14974415777481871312) (8 * Z.of_nat i + 7) = false).
  { intros i Hi.
    apply lor_bits_false; [lia|].
    apply (land_mask_bit _ 9259542123273814144); [lia | exact HC |].
    destruct i as [|[|[|[|[|[|[|[|]]]]]]]]; try lia; vm_compute; reflexivity. }
  assert (EV : V = vl [z0; z1; z2; z3; z4; z5; z6; z7]) by (subst V; cbn [vl]; unfold v8, v4; lia).
  assert (F : Forall isdigZ [z0; z1; z2; z3; z4; z5; z6; z7]).
  { apply peel.
    - repeat constructor; lia.
    - intros i Hi. cbn [length] in Hi |- *. change (cA 8) with 5063812098665367110. rewrite <- EV. apply (BITS i Hi).
    - intros i Hi. cbn [length] in Hi |- *. change (cB 8) with 14974415777481871312. rewrite <- EV. apply (BITS i Hi). }
  pose proof (Forall_inv F) as D0. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D1. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D2. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D3. apply Forall_inv_tail in F.
  try (pose proof (Forall_inv F) as D4; apply Forall_inv_tail in F;
       pose proof (Forall_inv F) as D5; apply Forall_inv_tail in F;
       pose proof (Forall_inv F) as D6; apply Forall_inv_tail in F;
       pose proof (Forall_inv F) as D7).
  unfold isdigZ in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_bits_low : forall x k, 0 <= k < 32 -> Z.testbit (bv_swrap 32 x) k = Z.testbit x k.
Proof.
  intros x k Hk. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite <- (Z.mod_pow2_bits_low (_ - _) 32 k) by lia.
  rewrite <- (Z.mod_pow2_bits_low x 32 k) by lia. f_equal.
  rewrite Zminus_mod_idemp_l.
  replace (x + 2 ^ 31 - 2 ^ 31) with x by lia. reflexivity.
Qed.

Lemma swar4_dig : forall V z0 z1 z2 z3,
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  0 <= V < 2^64 -> V mod 2^32 = v4 z0 z1 z2 z3 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (U (Z_to_bv 64 (Z.lor
          (U (Z_to_bv 64 (bv_swrap 32 (V + 1179010630))))
          (U (Z_to_bv 64 (bv_swrap 32 (V + 18446744072901087184))))))) 18446744071570489472))
       (Z_to_bv 64 0)) = false ->
  isdigZ z0 /\ isdigZ z1 /\ isdigZ z2 /\ isdigZ z3.
Proof.
  intros V z0 z1 z2 z3 H0 H1 H2 H3 VR HV HC.
  apply negb_eqb0_false in HC.
  assert (BITS : forall i, (i < 4)%nat ->
     Z.testbit (v4 z0 z1 z2 z3 + 1179010630) (8 * Z.of_nat i + 7) = false
     /\ Z.testbit (v4 z0 z1 z2 z3 + 3486502864) (8 * Z.of_nat i + 7) = false).
  { intros i Hi.
    assert (K : 0 <= 8 * Z.of_nat i + 7 < 32) by lia.
    destruct (lor_bits_false _ _ (8 * Z.of_nat i + 7) ltac:(lia)
               (land_mask_bit _ 18446744071570489472 (8 * Z.of_nat i + 7) ltac:(lia) HC
                  ltac:(destruct i as [|[|[|[|]]]]; try lia; vm_compute; reflexivity))) as [TA TB].
    rewrite swrap32_bits_low in TA, TB by lia.
    rewrite <- (Z.mod_pow2_bits_low _ 32) in TA by lia. rewrite <- (Z.mod_pow2_bits_low _ 32) in TB by lia.
    rewrite <- Zplus_mod_idemp_l, HV, Z.mod_pow2_bits_low in TA by lia.
    rewrite <- Zplus_mod_idemp_l, HV in TB. 
    replace ((v4 z0 z1 z2 z3 + 18446744072901087184) mod 2^32) with ((v4 z0 z1 z2 z3 + 3486502864) mod 2^32) in TB.
    2:{ replace (v4 z0 z1 z2 z3 + 18446744072901087184) with ((v4 z0 z1 z2 z3 + 3486502864) + 4294967295 * 2^32) by lia.
        rewrite Z.mod_add by lia. reflexivity. }
    rewrite Z.mod_pow2_bits_low in TB by lia.
    split; assumption. }
  assert (EV : v4 z0 z1 z2 z3 = vl [z0; z1; z2; z3]) by (cbn [vl]; unfold v4; lia).
  assert (F : Forall isdigZ [z0; z1; z2; z3]).
  { apply peel.
    - repeat constructor; lia.
    - intros i Hi. cbn [length] in Hi |- *. change (cA 4) with 1179010630. rewrite <- EV. apply (BITS i Hi).
    - intros i Hi. cbn [length] in Hi |- *. change (cB 4) with 3486502864.
      rewrite <- EV. apply (BITS i Hi). }
  pose proof (Forall_inv F) as D0. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D1. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D2. apply Forall_inv_tail in F.
  pose proof (Forall_inv F) as D3. apply Forall_inv_tail in F.
  unfold isdigZ in *. repeat split; lia.
Qed.
End Spf_swar.

Module AmoStep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_alignedW : forall a : word, (bv_unsigned a mod 4 = 0)%Z -> amo_aligned AW a = true.
Proof. intros a H. unfold amo_aligned. cbn [amo_bytes]. rewrite H. reflexivity. Qed.
Lemma amo_alignedD : forall a : word, (bv_unsigned a mod 8 = 0)%Z -> amo_aligned AD a = true.
Proof. intros a H. unfold amo_aligned. cbn [amo_bytes]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac amo_side := rewrite ?unsigned_lit by lia; first [ assumption | lia | Z.div_mod_to_equations; lia ].
Ltac amo_align :=
  repeat match goal with
  | |- context [amo_aligned AW ?a] => rewrite (amo_alignedW a) by amo_side
  | |- context [amo_aligned AD ?a] => rewrite (amo_alignedD a) by amo_side
  end;
  rewrite ?Z.eqb_refl; cbn [negb].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_st4 : forall v : bv 32, Z_to_le_bytes 4 (bv_unsigned v) = le4 (Z_to_bv 64 (bv_unsigned v)).
Proof.
  intros v. unfold le4. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  rewrite unsigned_lit by (cbn in R; lia). reflexivity.
Qed.
Lemma amo_st8 : forall v : bv 64, Z_to_le_bytes 8 (bv_unsigned v) = le8 v.
Proof. intros v. reflexivity. Qed.
Ltac amo_mem :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      lazymatch bs with
      | Z_to_le_bytes 4 (@bv_unsigned 32 ?v) => rewrite (amo_st4 v)
      | Z_to_le_bytes 8 (@bv_unsigned 64 ?v) => rewrite (amo_st8 v)
      | _ => idtac
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_old32 : forall c : word, bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 c))) = (bv_unsigned c mod 2^32)%Z.
Proof.
  intros c. rewrite bv_extract_unsigned, Z.shiftr_0_r. rewrite le_bytes_to_word_le4.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma amo_old64 : forall c : word, bv_extract 0 64 (le_bytes_to_word (le8 c)) = c.
Proof. exact load_u64. Qed.
Lemma low32_unsigned : forall s : word, bv_unsigned (low32 s) = (bv_unsigned s mod 2^32)%Z.
Proof. intros s. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.
Lemma amo_add32 : forall a b : bv 32, bv_unsigned (amo_val AMO_ADD a b) = ((bv_unsigned a + bv_unsigned b) mod 2^32)%Z.
Proof. intros a b. cbn [amo_val]. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma amo_add64 : forall a b : bv 64, bv_unsigned (amo_val AMO_ADD a b) = ((bv_unsigned a + bv_unsigned b) mod 2^64)%Z.
Proof. intros a b. cbn [amo_val]. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma amo_add64w : forall a b : bv 64, amo_val AMO_ADD a b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
  intros a b. cbn [amo_val]. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.
Lemma amo_or64w : forall a b : bv 64, amo_val AMO_OR a b = Z_to_bv 64 (Z.lor (bv_unsigned a) (bv_unsigned b)).
Proof.
  intros a b. cbn [amo_val]. apply bv_eq. rewrite bv_or_unsigned, Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 64 (bv_or a b)) as R. rewrite bv_or_unsigned in R. exact R.
Qed.
Lemma amo_swapN : forall n (a b : bv n), amo_val AMO_SWAP a b = b.
Proof. intros. reflexivity. Qed.
Lemma amo_or32 : forall a b : bv 32, bv_unsigned (amo_val AMO_OR a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. cbn [amo_val]. rewrite bv_or_unsigned. reflexivity. Qed.
Lemma unsigned_lit32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
(* [comment removed for export] *)
Ltac amo_vals :=
  rewrite ?amo_swapN in *;
  rewrite ?amo_add32, ?amo_add64, ?amo_or32 in *;
  rewrite ?amo_add64w, ?amo_or64w in *;
  rewrite ?amo_old32, ?amo_old64, ?low32_unsigned, ?le_bytes_to_word_le8 in *;
  repeat (rewrite unsigned_lit32 in * by lia);
  repeat (rewrite unsigned_lit in * by lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac step_amo :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with Some ?w =>
  let d := eval vm_compute in (decode_any w) in
  lazymatch d with Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; amo_align; vnorm_for i;
          try solve_load; try solve_store;
          first [reflexivity | match goal with |- ?g => idtac "step_amo: residual goal" g end; fail]
        | simp_regs; vnorm_for i; amo_mem; mem_after_store_opt; post_step i ]
  end end end.
End AmoStep.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition txb (bs : list byte) (k : Z) : word := zxb (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
(* [comment removed for export] *)
Definition tx (bs : list byte) (k : Z) : Z := bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0)).

Lemma txb_nth_error : forall bs k, (0 <= k < Z.of_nat (length bs))%Z ->
  nth_error bs (Z.to_nat k) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
Proof.
  intros bs k Hk. apply nth_error_nth'. lia.
Qed.

Lemma tx_range : forall bs k, (0 <= tx bs k < 256)%Z.
Proof.
  intros bs k. unfold tx. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) bs (Z_to_bv 8 0))) as H.
  unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma txb_unsigned : forall bs k, bv_unsigned (txb bs k) = tx bs k.
Proof.
  intros bs k. unfold txb, tx, zxb. pose proof (tx_range bs k) as H. unfold tx in H.
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma txb_range : forall bs k, (0 <= bv_unsigned (txb bs k) < 256)%Z.
Proof. intros bs k. rewrite txb_unsigned. apply tx_range. Qed.

Lemma txb_tx : forall bs k, txb bs k = Z_to_bv 64 (tx bs k).
Proof. intros bs k. rewrite <- txb_unsigned. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section WithSegs.
Variable segs : list MemImageType.Segment.
(* [comment removed for export] *)
#[using="Type"] Lemma txt_read : forall m P bs k,
  bytes_at segs m P bs -> (0 <= k < Z.of_nat (length bs))%Z ->
  ov_read_bytes segs m (wa (P + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m P bs k TXT Hk. eapply u8ro_read; [exact TXT | apply txb_nth_error; exact Hk | lia | reflexivity].
Qed.
End WithSegs.


Lemma wa_P0 : forall a : word, wa (bv_unsigned a + 0) = a.
Proof. intros a. unfold wa. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Ltac fold_tx bs k :=
  change (zxb (nth (Z.to_nat k) bs (Z_to_bv 8 0))) with (txb bs k); rewrite (txb_tx bs k).

(* [comment removed for export] *)
Definition isdig (z : Z) : Prop := (48 <= z <= 57)%Z.
(* [comment removed for export] *)
Definition digs (bs : list byte) (lo hi : Z) : Prop :=
  forall k, (lo <= k < hi)%Z -> isdig (tx bs k).

Lemma digs_nil : forall bs lo, digs bs lo lo.
Proof. intros bs lo k Hk. lia. Qed.
Lemma digs_snoc : forall bs lo hi, digs bs lo hi -> isdig (tx bs hi) -> digs bs lo (hi + 1).
Proof.
  intros bs lo hi H Hd k Hk. destruct (Z.eq_dec k hi) as [->|]; [exact Hd|]. apply H. lia.
Qed.
Lemma digs_sub : forall bs lo hi lo' hi', digs bs lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> digs bs lo' hi'.
Proof. intros bs lo hi lo' hi' H H1 H2 k Hk. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma dig_yes : forall t, (0 <= t < 256)%Z -> ((t + -48) mod 18446744073709551616 <= 9)%Z -> isdig t.
Proof.
  intros t Ht H. unfold isdig.
  destruct (Z_lt_le_dec t 48).
  - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma dig_no : forall t, (0 <= t < 256)%Z -> (9 < (t + -48) mod 18446744073709551616)%Z -> ~ isdig t.
Proof.
  intros t Ht H Hd. unfold isdig in Hd. rewrite Z.mod_small in H by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma dig_yes_m : forall t, (0 <= t < 256)%Z ->
  (Z.land ((t + -48) mod 18446744073709551616) 255 <= 9)%Z -> isdig t.
Proof.
  intros t Ht H. unfold isdig.
  change 255%Z with (2^8 - 1)%Z in H. rewrite zb_land_mask in H by lia.
  change 18446744073709551616%Z with (2^56 * 2^8)%Z in H.
  rewrite Zaux.Zmod_mod_mult in H by lia.
  destruct (Z_lt_le_dec t 48).
  - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma dig_no_m : forall t, (0 <= t < 256)%Z ->
  (9 < Z.land ((t + -48) mod 18446744073709551616) 255)%Z -> ~ isdig t.
Proof.
  intros t Ht H Hd. unfold isdig in Hd.
  change 255%Z with (2^8 - 1)%Z in H. rewrite zb_land_mask in H by lia.
  rewrite !Z.mod_small in H by lia. lia.
Qed.

Lemma land255_range : forall x, (0 <= Z.land x 255 <= 255)%Z.
Proof.
  intros x. change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia.
  pose proof (Z.mod_pos_bound x (2^8) ltac:(lia)). lia.
Qed.

Lemma signed_lit : forall z, (- 2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z_lt_le_dec z 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec0 (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 z (2^63)); lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_sign_mod : forall x, Z.lxor (x mod 18446744073709551616) 9223372036854775808
                                = ((x mod 18446744073709551616 + 9223372036854775808) mod 18446744073709551616)%Z.
Proof.
  intros x. change 9223372036854775808%Z with (2^63)%Z. change 18446744073709551616%Z with (2^64)%Z.
  apply zb_lxor_sign. apply Z.mod_pos_bound. lia.
Qed.
Lemma lxor_sign_small : forall x, (0 <= x < 18446744073709551616)%Z ->
  Z.lxor x 9223372036854775808 = ((x + 9223372036854775808) mod 18446744073709551616)%Z.
Proof.
  intros x Hx. change 9223372036854775808%Z with (2^63)%Z. change 18446744073709551616%Z with (2^64)%Z.
  apply zb_lxor_sign. exact Hx.
Qed.
Ltac unsign_chk H :=
  rewrite ?v_slt_b2z, ?v_slti_b2z, ?v_sltu_b2z, ?v_sltiu_b2z in H;
  rewrite ?unsigned_lit_wrap in H;
  rewrite ?lxor_sign_mod in H; rewrite ?lxor_sign_small in H by lia;
  rewrite ?zb_b2z_if in H.

Lemma b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. destruct b; cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac ms_leaf_eq :=
  first [ reflexivity
        | word_eq_tac
        | symmetry; word_eq_tac
        | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
        | lazymatch goal with
          | |- ?a = Z_to_bv 64 ?e =>
              transitivity (Z_to_bv 64 (bv_unsigned a)); [ symmetry; apply Z_to_bv_bv_unsigned | word_eq_tac ]
          | |- Z_to_bv 64 ?e = ?a =>
              transitivity (Z_to_bv 64 (bv_unsigned a)); [ word_eq_tac | apply Z_to_bv_bv_unsigned ]
          end ].
(* [comment removed for export] *)
Ltac ms_eq_tac :=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].
Tactic Notation "goto" tactic3(tac) := (eapply evt_eq; [ | tac ]; [ ms_eq_tac | .. ]).


(* [comment removed for export] *)
Definition zeros (bs : list byte) (lo hi : Z) : Prop :=
  forall k, (lo <= k < hi)%Z -> tx bs k = 48%Z.
Lemma zeros_nil : forall bs lo, zeros bs lo lo.
Proof. intros bs lo k Hk. lia. Qed.
Lemma zeros_snoc : forall bs lo hi, zeros bs lo hi -> tx bs hi = 48%Z -> zeros bs lo (hi + 1).
Proof.
  intros bs lo hi H Hd k Hk. destruct (Z.eq_dec k hi) as [->|]; [exact Hd|]. apply H. lia.
Qed.

(* [comment removed for export] *)
Fixpoint cnt48 (bs : list byte) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => cnt48 bs lo n' + (if (tx bs (lo + Z.of_nat n') =? 48)%Z then 1 else 0)
  end%Z.

Lemma cnt48_range : forall bs lo n, (0 <= cnt48 bs lo n <= Z.of_nat n)%Z.
Proof.
  intros bs lo n. induction n as [|n IH]; cbn [cnt48]; [lia|].
  rewrite Nat2Z.inj_succ. destruct (Z.eqb_spec (tx bs (lo + Z.of_nat n)) 48); lia.
Qed.

Lemma cnt48_split : forall bs lo a b,
  cnt48 bs lo (a + b) = (cnt48 bs lo a + cnt48 bs (lo + Z.of_nat a) b)%Z.
Proof.
  intros bs lo a b. induction b as [|b IH]; cbn [cnt48].
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. cbn [cnt48]. rewrite IH. rewrite Nat2Z.inj_add. rewrite <- Z.add_assoc.
    replace (lo + (Z.of_nat a + Z.of_nat b))%Z with (lo + Z.of_nat a + Z.of_nat b)%Z by lia. lia.
Qed.

Lemma cnt48_zeros : forall bs lo n, zeros bs lo (lo + Z.of_nat n) -> cnt48 bs lo n = Z.of_nat n.
Proof.
  intros bs lo n. induction n as [|n IH]; intros Hz; cbn [cnt48]; [reflexivity|].
  rewrite Nat2Z.inj_succ in *. rewrite IH.
  - rewrite (Hz (lo + Z.of_nat n)%Z) by lia. rewrite Z.eqb_refl. lia.
  - intros k Hk. apply Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma cnt48_step : forall bs lo n,
  cnt48 bs lo (S n) = (cnt48 bs lo n + (if (tx bs (lo + Z.of_nat n) =? 48)%Z then 1 else 0))%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma strip_contra : forall bs (L k3 kI fL ks dp : Z),
  (0 <= k3 <= kI)%Z -> (kI <= L)%Z -> (0 <= fL)%Z -> (k3 <= ks <= L)%Z ->
  zeros bs k3 kI ->
  (fL = 0 \/ (kI < L /\ tx bs kI = dp /\ (kI + 1 + fL <= L) /\ zeros bs (kI + 1) (kI + 1 + fL)))%Z ->
  (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = dp) ->
  (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> dp)) ->
  (20 <= (kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z -> False.
Proof.
  intros bs L k3 kI fL ks dp K3I KIL FL KS ZI SP SCAN EX T20.
  pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
  assert (HI : (kI <= ks)%Z).
  { destruct (Z_lt_le_dec ks kI) as [Hlt|]; [|lia]. exfalso.
    destruct EX as [->|[NE _]]; [lia|]. apply NE. apply ZI. lia. }
  destruct SP as [F0 | (KIL2 & DPk & FEND & ZF)].
  - (* [comment removed for export] *)
    replace (Z.to_nat (ks - k3)) with (Z.to_nat (kI - k3) + Z.to_nat (ks - kI))%nat in T20 by lia.
    rewrite cnt48_split in T20. rewrite cnt48_zeros in T20 by (intros k Hk; apply ZI; lia).
    pose proof (cnt48_range bs (k3 + Z.of_nat (Z.to_nat (kI - k3))) (Z.to_nat (ks - kI))). lia.
  - assert (HF : (kI + 1 + fL <= ks)%Z).
    { destruct (Z_lt_le_dec ks (kI + 1 + fL)) as [Hlt|]; [|lia]. exfalso.
      destruct EX as [->|[NE ND]]; [lia|].
      destruct (Z.eq_dec ks kI) as [->|]; [apply ND; exact DPk|].
      apply NE. apply ZF. lia. }
    replace (Z.to_nat (ks - k3)) with (Z.to_nat (kI - k3) + (Z.to_nat 1 + (Z.to_nat fL + Z.to_nat (ks - (kI + 1 + fL)))))%nat
      in T20 by lia.
    rewrite !cnt48_split in T20.
    rewrite (cnt48_zeros bs k3) in T20 by (intros k Hk; apply ZI; lia).
    rewrite (cnt48_zeros bs (k3 + Z.of_nat (Z.to_nat (kI - k3)) + Z.of_nat (Z.to_nat 1))) in T20
      by (intros k Hk; apply ZF; lia).
    pose proof (cnt48_range bs (k3 + Z.of_nat (Z.to_nat (kI - k3))) (Z.to_nat 1)).
    pose proof (cnt48_range bs (k3 + Z.of_nat (Z.to_nat (kI - k3)) + Z.of_nat (Z.to_nat 1) + Z.of_nat (Z.to_nat fL))
                  (Z.to_nat (ks - (kI + 1 + fL)))). lia.
Qed.

(* [comment removed for export] *)
Record spf_ctx : Type := SPF {
  r_ra : word; r_sp : word; r_gp : word; r_tp : word; r_t0 : word; r_t1 : word; r_t2 : word;
  r_s0 : word; r_s1 : word; r_a0 : word; r_a1 : word; r_a2 : word; r_a3 : word; r_a4 : word;
  r_a5 : word; r_a6 : word; r_a7 : word; r_s2 : word; r_s3 : word; r_s4 : word; r_s5 : word;
  r_s6 : word; r_s7 : word; r_s8 : word; r_s9 : word; r_s10 : word; r_s11 : word;
  r_t3 : word; r_t4 : word; r_t5 : word; r_t6 : word;
  r_F : bvmap 5 word; r_fc : bv 32; r_m0 : word -> option byte; r_bs : list byte; r_v : word }.

(* [comment removed for export] *)
Ltac txt_rd TXT k RD :=
  lazymatch type of TXT with bytes_at ?sg ?mm ?P ?bs =>
    pose proof (txt_read sg mm P bs k TXT ltac:(lia)) as RD end.
