(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanMainDefs AsanMain AsanTailAlist.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.

Definition tails_all_okb (KCm BFUELm FUELm : nat) (ITm : itab) (AL : list (nat * (acs * plan * shape))) : bool :=
  (AP.tails_okb ASEGS ITm ASAN NX0 AsanInit.LIMIT KCm (map snd AL) && tailsF_okb KCm BFUELm FUELm ITm (map snd AL))%bool.

Lemma tailsF_ok_of_alist : forall KCm BFUELm FUELm ITm AL,
  tailsF_okb KCm BFUELm FUELm ITm (map snd AL) = true -> tailsF_ok KCm BFUELm FUELm ITm (tt_of_alist AL).
Proof.
  intros KCm BFUELm FUELm ITm AL H t T p s Ht Hf. apply tt_of_alist_in in Ht.
  pose proof (proj1 (forallb_forall _ _) H (T, p, s) (in_map snd _ _ Ht)) as X. cbn beta iota in X. rewrite Hf in X.
  destruct (tailf_check KCm BFUELm FUELm ITm T p) as [s'|]; [|discriminate]. apply andb_prop in X as [X1 X2].
  apply APS.shape_eqb_eq in X1. subst s'. split; [reflexivity | exact X2].
Qed.
Lemma tails_all_ok_of_alist : forall KCm BFUELm FUELm ITm AL,
  tails_all_okb KCm BFUELm FUELm ITm AL = true -> tails_all_ok KCm BFUELm FUELm ITm (tt_of_alist AL).
Proof.
  intros KCm BFUELm FUELm ITm AL H. apply andb_prop in H as [H1 H2].
  split; [apply tails_ok_of_alist; exact H1 | apply tailsF_ok_of_alist; exact H2].
Qed.
Lemma tails_all_ok_alist_nil : forall KCm BFUELm FUELm ITm, tails_all_ok KCm BFUELm FUELm ITm (tt_of_alist []).
Proof. intros. split; intros t T p s H; discriminate H. Qed.
Lemma tails_all_ok_alist_app : forall KCm BFUELm FUELm ITm AL1 AL2,
  tails_all_ok KCm BFUELm FUELm ITm (tt_of_alist AL1) -> tails_all_ok KCm BFUELm FUELm ITm (tt_of_alist AL2) ->
  tails_all_ok KCm BFUELm FUELm ITm (tt_of_alist (AL1 ++ AL2)).
Proof.
  intros KCm BFUELm FUELm ITm AL1 AL2 [A1 F1] [A2 F2]. split; [apply tails_ok_alist_app; assumption|].
  intros t T p s Ht Hf. rewrite tt_of_alist_app in Ht. destruct (tt_of_alist AL1 t) as [e|] eqn:E1.
  - injection Ht as ->. exact (F1 t T p s E1 Hf).
  - exact (F2 t T p s Ht Hf).
Qed.
