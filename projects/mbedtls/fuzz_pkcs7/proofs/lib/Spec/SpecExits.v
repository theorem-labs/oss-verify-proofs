(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SrzHaltsB.
Import ListNotations.

Definition exits_in := SrzHaltsB.exits_in.
Definition evs_exits_in := SrzHaltsB.evs_exits_in.

(* [comment removed for export] *)
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma in_codes02_0 : In (exit_code 0) codes02.
Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (exit_code 2) codes02.
Proof. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma exits_in_emit : forall S evs T, evs_exits_in S evs -> exits_in S T -> exits_in S (t_emit evs T).
Proof. intros S evs T He HT. exact (SrzHaltsB.exits_in_emit S evs T He HT). Qed.
Lemma exits_in_exit : forall S code fs, In code S -> exits_in S (t_exit code fs).
Proof. intros S code fs Hin. exact (SrzHaltsB.exits_in_exit S code fs Hin). Qed.
Lemma exits_in_alt2 : forall S A B, exits_in S A -> exits_in S B -> exits_in S (t_alt2 A B).
Proof. intros S A B HA HB. exact (SrzHaltsB.exits_in_alt2 S A B HA HB). Qed.
Lemma exits_in_W : forall S ch msg T, exits_in S T -> exits_in S (t_emit (W ch msg) T).
Proof. intros S ch msg T HT. exact (SrzHaltsB.exits_in_writes S (Z_to_bv 64 ch) msg T HT). Qed.

Lemma exits_in_die : forall msg fs, exits_in codes02 (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply exits_in_W. apply exits_in_exit. apply in_codes02_2. Qed.

Lemma exits_in_body : forall data fs, exits_in codes02 (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply exits_in_die |].
  destruct (length data <? 6)%nat; [apply exits_in_die |].
  destruct (length data <? 6 + Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat;
    [apply exits_in_die |].
  destruct (length data - 6 - Z.to_nat ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768))%nat.
  - apply exits_in_W. apply exits_in_exit. apply in_codes02_0.
  - apply exits_in_alt2.
    + apply exits_in_exit.
      destruct (32768 <=? bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z;
        [apply in_codes02_0 | apply in_codes02_2].
    + apply exits_in_W. apply exits_in_exit. apply in_codes02_0.
Qed.

Theorem exits_in_spec : forall argv fs, exits_in codes02 (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [| a0 [| path [| a2 rest]]]; try apply exits_in_die.
  destruct (4096 <=? length path)%nat; [apply exits_in_die |].
  destruct (list_byte_eqb path []); [apply exits_in_die |].
  destruct (list_byte_eqb path dot_path).
  - apply exits_in_alt2; [apply exits_in_die | unfold t_opened_dir; apply exits_in_alt2; apply exits_in_die].
  - destruct (fs_lookup fs path); [| apply exits_in_die].
    apply exits_in_alt2; [apply exits_in_die | unfold t_opened; apply exits_in_alt2; [apply exits_in_die | apply exits_in_body]].
Qed.

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec, t_die, t_opened, t_opened_dir.
  destruct argv as [|a0 [|path [|x r]]]; try apply t_emit_has_nil.
  destruct (4096 <=? length path)%nat; [apply t_emit_has_nil|].
  destruct (list_byte_eqb path []); [apply t_emit_has_nil|].
  destruct (list_byte_eqb path dot_path); [left; apply t_emit_has_nil|].
  destruct (fs_lookup fs path); [left; apply t_emit_has_nil| apply t_emit_has_nil].
Qed.
