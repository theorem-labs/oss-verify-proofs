(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ABase.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import AsanCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition al_tight (L : alayout) : Prop := al_pat L = (fun _ => None) /\ al_spat L = (fun _ => None).

Lemma al_tight_pat : forall L p, al_tight L -> al_pat L p = None.
Proof. intros L p [H _]. rewrite H. reflexivity. Qed.
Lemma al_tight_spat : forall L mb, al_tight L -> al_spat L mb = None.
Proof. intros L mb [_ H]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma al_tight_eta : forall L, al_tight L -> mkALayout (al_V L) (al_w L) (al_U L) (fun _ => None) (fun _ => None) = L.
Proof. intros [V w U pat spat] [H1 H2]. cbn in *. subst. reflexivity. Qed.
