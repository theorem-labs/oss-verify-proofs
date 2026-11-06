(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (Z.ones 64) = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha.
  assert (Hl : Z.land a (Z.lxor a (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a i); reflexivity.
    - assert (Z.testbit a i = false) as ->; [|reflexivity].
      destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia. }
  pose proof (Z.add_nocarry_lxor _ _ Hl) as E.
  rewrite <- Z.lxor_assoc in E. rewrite Z.lxor_nilpotent, Z.lxor_0_l in E.
  set (x := Z.lxor a (Z.ones 64)) in *. change (Z.ones 64) with (2 ^ 64 - 1) in E. lia.
Qed.

(* [comment removed for export] *)
Lemma u_not : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (v_xori (W a) (-1)) = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. unfold v_xori. rewrite (Wu a) by lia. change (bv_wrap 64 (-1)) with (Z.ones 64).
  rewrite lxor_ones64 by lia. apply Wu. lia.
Qed.

(* [comment removed for export] *)
Lemma u_andi_ones_W : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k < 64 ->
  bv_unsigned (v_andi (W a) (Z.ones k)) = a mod 2 ^ k.
Proof. intros a k Ha Hk. rewrite u_andi_ones by lia. rewrite Wu by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sltiu1_W : forall a, 0 <= a < 2 ^ 64 -> v_sltiu (W a) 1 = W (if Z.eqb a 0 then 1 else 0).
Proof.
  intros a Ha. unfold v_sltiu. rewrite (Wu a) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec a 0) as [->|Hn]; [reflexivity|].
  destruct (Z.ltb_spec a 1); [lia | reflexivity].
Qed.

Lemma sltu0_W : forall a, 0 <= a < 2 ^ 64 -> v_sltu (W 0) (W a) = W (if Z.eqb a 0 then 0 else 1).
Proof.
  intros a Ha. destruct (Z.eqb_spec a 0) as [->|Hn]; [reflexivity|].
  apply sltu0_nz. rewrite Wu by lia. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma mod8_sub : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a - k) mod 8 = 0.
Proof. intros a k Ha Hk. rewrite Zminus_mod, Ha, Hk. reflexivity. Qed.
Lemma mod8_add : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a + k) mod 8 = 0.
Proof. intros a k Ha Hk. rewrite Zplus_mod, Ha, Hk. reflexivity. Qed.
Lemma mod4_add : forall a k, a mod 4 = 0 -> k mod 4 = 0 -> (a + k) mod 4 = 0.
Proof. intros a k Ha Hk. rewrite Zplus_mod, Ha, Hk. reflexivity. Qed.
