(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land7_0 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x Hx. rewrite land7_mod. exact Hx. Qed.
Lemma land3_0 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hx. Qed.
Lemma land1_0 : forall x, x mod 2 = 0 -> Z.land x 1 = 0.
Proof. intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. exact Hx. Qed.

(* [comment removed for export] *)
Lemma mod8_of_16 : forall P k, P mod 16 = 0 -> k mod 8 = 0 -> (P + k) mod 8 = 0.
Proof. intros P k HP Hk. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_of_16 : forall P k, P mod 16 = 0 -> k mod 4 = 0 -> (P + k) mod 4 = 0.
Proof. intros P k HP Hk. Z.div_mod_to_equations. lia. Qed.
Lemma mod8_of_8 : forall P k, P mod 8 = 0 -> k mod 8 = 0 -> (P + k) mod 8 = 0.
Proof. intros P k HP Hk. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_of_8 : forall P k, P mod 8 = 0 -> k mod 4 = 0 -> (P + k) mod 4 = 0.
Proof. intros P k HP Hk. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_of_4 : forall P k, P mod 4 = 0 -> k mod 4 = 0 -> (P + k) mod 4 = 0.
Proof. intros P k HP Hk. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma lxor_allones : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  replace (18446744073709551615 - x) with ((Z.lnot x) mod 2^64) by (unfold Z.lnot; Z.div_mod_to_equations; lia).
  change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'; intros n Hn. rewrite Z.lxor_spec.
  destruct (Z_lt_le_dec n 64).
  - rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.lnot_spec by lia. apply Bool.xorb_true_r.
  - rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia.
    replace x with (x mod 2^64) by (apply Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Ltac ub_not := lazymatch goal with |- context [Z.lxor ?X 18446744073709551615] => rewrite (lxor_allones X) by lia end.

(* [comment removed for export] *)
Lemma ub_eqz_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Ltac ub_null_here :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?X) _ then _ else _) _ _ _ _) => if_false_by (ub_eqz_false X ltac:(lia))
  end.
Ltac ub_null := zstep; ub_null_here.

(* [comment removed for export] *)
Ltac ub_al K tac :=
  lazymatch goal with
  | |- context [Z.land ?X K] =>
      replace (Z.land X K) with 0%Z
        by (symmetry; first [apply land7_0 | apply land3_0 | apply land1_0]; tac)
  end.
(* [comment removed for export] *)
Lemma mod8_16 : forall P, P mod 16 = 0 -> P mod 8 = 0.
Proof. intros P HP. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_16 : forall P, P mod 16 = 0 -> P mod 4 = 0.
Proof. intros P HP. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_8 : forall P, P mod 8 = 0 -> P mod 4 = 0.
Proof. intros P HP. Z.div_mod_to_equations. lia. Qed.
Ltac al16 H := first [ apply (mod8_of_16 _ _ H); reflexivity | apply (mod4_of_16 _ _ H); reflexivity | exact (mod8_16 _ H) | exact (mod4_16 _ H) ].
Ltac al8 H := first [ apply (mod8_of_8 _ _ H); reflexivity | apply (mod4_of_8 _ _ H); reflexivity | exact H | exact (mod4_8 _ H) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ub_uns X :=
  first [ rewrite (unsigned_lit X) by lia
        | rewrite <- (Z_to_bv_mod64 X);
          let v := eval vm_compute in (X mod 2^64) in (change (X mod 2^64) with v; rewrite (unsigned_lit v) by lia) ].
(* [comment removed for export] *)
Ltac ub_ltu :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)) then _ else _) _ _ _ _) =>
      replace (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) with true
        by (symmetry; unfold bv_ltu; ub_uns a; ub_uns b; apply Z.ltb_lt; lia);
      cbn [negb]; cbv iota
  | |- evtF _ _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) then _ else _) _ _ _ _) =>
      replace (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) with false
        by (symmetry; unfold bv_ltu; ub_uns a; ub_uns b; apply Z.ltb_ge; lia);
      cbv iota
  end.
(* [comment removed for export] *)
Ltac ub_xnull :=
  lazymatch goal with
  | |- context [Z.lxor (Z.b2z (0 <? ?A)) (Z.b2z (?B <? 1))] =>
      replace (0 <? A)%Z with true by (symmetry; apply Z.ltb_lt; lia);
      replace (B <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia);
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1%Z;
      if_false_by (ub_eqz_false 1 ltac:(lia))
  end.
(* [comment removed for export] *)
Lemma ub_eqb_m1_false : forall x, (0 <= x < 2^64 - 1)%Z -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite (unsigned_lit x) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by (vm_compute; reflexivity). apply Z.eqb_neq. lia.
Qed.
Ltac ub_m1 :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?X) (Z_to_bv 64 (-1)) then _ else _) _ _ _ _) => if_false_by (ub_eqb_m1_false X ltac:(lia))
  end.
