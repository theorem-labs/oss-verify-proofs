(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 HaltsFO YP07 YP01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma shape_ok_ex02 : forall code fs, code = 0 \/ code = 2 -> shape_ok codes02 (ex code fs).
Proof. intros code fs [-> | ->]; unfold ex; apply shape_ok_exit; [apply in_codes02_0 | apply in_codes02_2]. Qed.
Lemma shape_ok_wr02 : forall ch bs T, shape_ok codes02 T -> shape_ok codes02 (wr ch bs T).
Proof.
  intros ch bs T H. unfold wr. apply shape_ok_emit; [|exact H].
  unfold trace_ok. apply Forall_forall. intros e He. apply in_map_iff in He as (b & <- & _). exact I.
Qed.
Lemma shape_ok_diag02 : forall msg fs, shape_ok codes02 (diag msg fs).
Proof. intros msg fs. unfold diag. apply shape_ok_wr02. apply shape_ok_ex02. right; reflexivity. Qed.
Lemma shape_ok_RUNS : forall data fs, shape_ok codes02 (RUNS data fs).
Proof. intros data fs. unfold RUNS. apply shape_ok_wr02. apply shape_ok_ex02. left; reflexivity. Qed.
Lemma shape_ok_POST : forall data fs, shape_ok codes02 (POST data fs).
Proof.
  intros data fs. unfold POST.
  destruct (dlen data <? HDR_MIN); [apply shape_ok_diag02|].
  destruct (dlen data <? HDR_MIN + config_len data); [apply shape_ok_diag02|].
  destruct (payload_len data =? 0); [apply shape_ok_RUNS|].
  apply shape_ok_alt2; [apply shape_ok_ex02; destruct (count_mode data); [left | right]; reflexivity | apply shape_ok_RUNS].
Qed.
Lemma shape_ok_CLOSED_loaded : forall data fs, shape_ok codes02 (CLOSED_loaded data fs).
Proof.
  intros data fs. unfold CLOSED_loaded. apply shape_ok_alt2; [apply shape_ok_diag02|].
  destruct (MAX_INPUT <=? dlen data); [apply shape_ok_diag02 | apply shape_ok_POST].
Qed.
Lemma shape_ok_CLOSED_dir : forall p fs, shape_ok codes02 (CLOSED_dir p fs).
Proof. intros p fs. unfold CLOSED_dir. apply shape_ok_alt2; apply shape_ok_diag02. Qed.
Theorem CLOSED_shape_ok : forall inp, shape_ok codes02 (CLOSED inp).
Proof.
  intros inp. unfold CLOSED, CLOSED_args.
  destruct (in_argv inp) as [| a0 [| p [| x l]]]; try apply shape_ok_diag02.
  destruct (classify_open p (in_fs inp)).
  - apply shape_ok_diag02.
  - apply shape_ok_alt2; [apply shape_ok_diag02 | apply shape_ok_CLOSED_dir].
  - apply shape_ok_alt2; [apply shape_ok_diag02 | apply shape_ok_CLOSED_loaded].
Qed.
(* [comment removed for export] *)
Lemma shape_ok_leaf_shape : forall data fs r, shape_ok codes02 (leaf_shape data fs r).
Proof.
  intros data fs [l a]. unfold leaf_shape. cbn [fst].
  destruct l; try apply shape_ok_diag02.
  - apply shape_ok_ex02. destruct (count_mode data); [left | right]; reflexivity.
  - apply shape_ok_wr02. apply shape_ok_ex02. left; reflexivity.
Qed.
End c.
