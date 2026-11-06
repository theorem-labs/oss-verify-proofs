(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint hs_lookup (h : nat) (l : list (nat * acs)) : option acs :=
  match l with
  | [] => None
  | (k, c) :: r => if Nat.eqb h k then Some c else hs_lookup h r
  end.

Lemma hs_lookup_In : forall h l c, hs_lookup h l = Some c -> In (h, c) l.
Proof.
  intros h l c. induction l as [|[k c'] r IH]; cbn [hs_lookup]; intros H; [discriminate H|].
  destruct (Nat.eqb h k) eqn:E.
  - apply PeanoNat.Nat.eqb_eq in E. subst k. injection H as ->. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma hs_lookup_cases : forall h l c, hs_lookup h l = Some c ->
  fold_right (fun kc (P : Prop) => (h = fst kc /\ c = snd kc) \/ P) False l.
Proof.
  intros h l c H. apply hs_lookup_In in H. induction l as [|[k c'] r IH]; cbn [fold_right fst snd In] in *; [exact H|].
  destruct H as [H|H]; [left; injection H as -> ->; split; reflexivity | right; apply IH; exact H].
Qed.
