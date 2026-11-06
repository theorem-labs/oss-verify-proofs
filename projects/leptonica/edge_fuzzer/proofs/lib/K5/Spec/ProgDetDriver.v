(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim Stdio Canon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma concat_pieces_usage : forall a, concat (pieces_usage a) = msg_usage a.
Proof. intros a. unfold pieces_usage, msg_usage. cbn [concat]. rewrite !app_nil_l, app_nil_r. reflexivity. Qed.
Lemma concat_pieces_cannot_open : forall a, concat (pieces_cannot_open a) = msg_cannot_open a.
Proof. intros a. unfold pieces_cannot_open, msg_cannot_open. cbn [concat]. rewrite !app_nil_l. reflexivity. Qed.
Lemma concat_pieces_read_error : forall a, concat (pieces_read_error a) = msg_read_error a.
Proof. intros a. unfold pieces_read_error, msg_read_error. cbn [concat]. rewrite !app_nil_l. reflexivity. Qed.
