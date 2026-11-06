(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit HaltsAllowed.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN02 YN01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ex_tsafe : forall code fs, 0 <= code < 256 -> tsafe byte_codes (ex code fs).
Proof. intros code fs H. unfold ex. apply tsafe_bytes_exit. exact H. Qed.
Lemma wr_tsafe : forall ch bs T, tsafe byte_codes T -> tsafe byte_codes (wr ch bs T).
Proof. intros ch bs T HT. unfold wr. apply tsafe_writes. exact HT. Qed.
Lemma diag_tsafe : forall msg fs, tsafe byte_codes (diag msg fs).
Proof. intros msg fs. unfold diag. apply wr_tsafe. apply ex_tsafe. lia. Qed.
Lemma leaf_shape_tsafe : forall data fs r, tsafe byte_codes (leaf_shape data fs r).
Proof.
intros data fs [l a]. unfold leaf_shape. cbn [fst].
destruct l; try apply diag_tsafe.
- apply ex_tsafe. destruct (count_mode data); lia.
- apply wr_tsafe. apply ex_tsafe. lia.
Qed.
Lemma SPEC_loaded_tsafe : forall data fs, tsafe byte_codes (SPEC_loaded data fs).
Proof. intros data fs. unfold SPEC_loaded. apply tsafe_tset. intros a. apply leaf_shape_tsafe. Qed.
Lemma SPEC_dir_tsafe : forall p fs, tsafe byte_codes (SPEC_dir p fs).
Proof.
intros p fs. unfold SPEC_dir. apply tsafe_tset. intros [b a]. cbn [fst].
destruct b; apply diag_tsafe.
Qed.
Lemma SPEC_args_tsafe : forall argv fs, tsafe byte_codes (SPEC_args argv fs).
Proof.
intros argv fs. unfold SPEC_args.
destruct argv as [| a0 [| p [| x l]]]; try apply diag_tsafe.
destruct (classify_open p fs); [apply diag_tsafe | |];
apply tsafe_alt2; try apply diag_tsafe; [apply SPEC_dir_tsafe | apply SPEC_loaded_tsafe].
Qed.
Theorem SPEC_tsafe : forall inp, tsafe byte_codes (SPEC inp).
Proof. intros inp. unfold SPEC. apply SPEC_args_tsafe. Qed.
End c.
