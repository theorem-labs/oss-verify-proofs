(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import ShapeAlg ShapeEFA HaltsBridge Spec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition spec_exits : list word := [exit_code 0; exit_code 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_die_kill_free : forall msg fs, kill_free (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply kill_free_emit.
  - apply forallb_not_kill_map_write.
  - apply kill_free_exit.
Qed.

Lemma t_body_kill_free : forall data fs, kill_free (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply t_die_kill_free|].
  destruct (length data <? 6)%nat; [apply t_die_kill_free|].
  cbv zeta.
  destruct (length data <? _)%nat; [apply t_die_kill_free|].
  apply kill_free_emit; [apply forallb_not_kill_map_write | apply kill_free_exit].
Qed.

Lemma spec_kill_free : forall argv fs, kill_free (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply t_die_kill_free.
  destruct (4096 <=? length path)%nat; [apply t_die_kill_free|].
  destruct (list_byte_eqb path []); [apply t_die_kill_free|].
  destruct (list_byte_eqb path dot_path).
  - apply kill_free_alt2; [apply t_die_kill_free|]. unfold t_opened_dir. apply t_die_kill_free.
  - destruct (fs_lookup fs path) as [data|]; [|apply t_die_kill_free].
    apply kill_free_alt2; [apply t_die_kill_free|]. unfold t_opened. apply t_body_kill_free.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_die_shape_good : forall msg fs, shape_good spec_exits (t_die msg fs).
Proof.
  intros msg fs. unfold t_die, W. apply shape_good_emit.
  - apply trace_good_writes.
  - apply shape_good_exit. unfold spec_exits. right. left. reflexivity.
Qed.

Lemma t_body_shape_good : forall data fs, shape_good spec_exits (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply t_die_shape_good|].
  destruct (length data <? 6)%nat; [apply t_die_shape_good|].
  cbv zeta.
  destruct (length data <? _)%nat; [apply t_die_shape_good|].
  unfold W. apply shape_good_emit; [apply trace_good_writes | apply shape_good_exit]. unfold spec_exits. left. reflexivity.
Qed.

Theorem spec_shape_good : forall argv fs, shape_good spec_exits (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply t_die_shape_good.
  destruct (4096 <=? length path)%nat; [apply t_die_shape_good|].
  destruct (list_byte_eqb path []); [apply t_die_shape_good|].
  destruct (list_byte_eqb path dot_path).
  - apply shape_good_alt2; [apply t_die_shape_good|]. unfold t_opened_dir. apply t_die_shape_good.
  - destruct (fs_lookup fs path) as [data|]; [|apply t_die_shape_good].
    apply shape_good_alt2; [apply t_die_shape_good|]. unfold t_opened. apply t_body_shape_good.
Qed.

(* [comment removed for export] *)
Corollary spec_shape_good_Z : forall argv fs, shape_good [Z_to_bv 64 0; Z_to_bv 64 2] (spec argv fs).
Proof. exact spec_shape_good. Qed.
