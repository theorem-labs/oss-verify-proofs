(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import UnwindA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Class UnwindRec {UK : UnwindKit} (f R : Z) (d : nat) : Type := mkUR {
  uk_ctxJ : nat -> list Z -> Prop;
  (* [comment removed for export] *)
  uk_ctxJ_enter : forall X0, uk_ctx f X0 -> uk_ctxJ 0%nat X0;
  (* [comment removed for export] *)
  uk_ctxJ_rec : forall j X0, uk_ctxJ j X0 -> (S j <= d)%nat -> uk_ctxJ (S j) X0;
  (* [comment removed for export] *)
  uk_ctxJ_call : forall j X0 r g, uk_call f r g -> r <> R -> uk_ctxJ j X0 -> uk_ctx g (r :: repeat R j ++ X0);
  (* [comment removed for export] *)
  uk_ctxJ_leaf : forall j X0 r, uk_leaf f r -> r <> R -> uk_ctxJ j X0 -> In (r :: repeat R j ++ X0) SITE_TRACES
}.

(* [comment removed for export] *)
Lemma repeat_cons_S : forall (R : Z) j (X0 : list Z), R :: (repeat R j ++ X0) = repeat R (S j) ++ X0.
Proof. intros. reflexivity. Qed.
