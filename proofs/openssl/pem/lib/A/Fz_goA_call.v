(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_gshacc RT_gap Fz_gochk Fz_callA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition go_b1 (p : Z * Z) : bool := go_exact1 p || ((fst p =? GAP_FILE) && (snd p =? GAP_FILE_SZ)).
Lemma go_b_sound : forall l : list (Z * Z), forallb go_b1 l = true -> Forall (fun p => B_GOBJ (fst p) (snd p)) l.
Proof.
  induction l as [|a l IH]; intros H; [constructor|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. constructor; [| exact (IH H2)].
  unfold go_b1 in H1. apply orb_prop in H1 as [H1|H1].
  - left. exact (Forall_inv (go_exact_sound [a] ltac:(cbn [forallb]; rewrite H1; reflexivity))).
  - right. apply andb_prop in H1 as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. split; assumption.
Qed.

Theorem go_call_A : Forall (fun p => B_GOBJ (fst p) (snd p)) CALLA_GOBJS.
Proof. apply go_b_sound. vm_compute. reflexivity. Qed.
