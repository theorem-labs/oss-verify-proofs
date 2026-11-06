(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad Stdio Driver Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio ProgDetTarget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma concat_pieces_usage : forall a, concat (pieces_usage a) = msg_usage a.
Proof. intros a. unfold pieces_usage, msg_usage. cbn [concat]. rewrite !app_nil_l, app_nil_r. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Diag.
Context {St : Type}.
Variable sel : option bool.
Variable X : list event -> Prop.

(* [comment removed for export] *)

End Diag.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section ReadLoop.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable path : list Z.
Variable tr0 : list event.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ReadLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ReadAll.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable path : list Z.
Variable tr0 : list event.
Hypothesis Hpath : zlength path < 2^32.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ReadAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable tr0 : list event.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End Main.
