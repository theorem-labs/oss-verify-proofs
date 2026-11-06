(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Stdio Canon PrintfFormats.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma concat_pieces_usage : forall a, concat (pieces_usage a) = msg_usage a.
Proof. intros a. unfold pieces_usage, msg_usage. cbn [concat]. rewrite !app_nil_l, app_nil_r. reflexivity. Qed.

Lemma zlen_app : forall {A} (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros A l1 l2. unfold zlength. rewrite length_app. lia. Qed.

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlen_app, IH. unfold zlength. cbn [length]. lia.
Qed.
