(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree ITreeCfg Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad MSafe MSil MSuccTall.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Local Notation tsilC := (ImplRz.tsil node (nstep_cfg acfg) nexit nsafe).

(* [comment removed for export] *)
Lemma tsil_cfg_of_msil : forall {R} (t : itree node R) mo P,
  MSil.tsil t mo P -> tsilC t mo P.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as (Hs & Hx & Hk). split; [exact Hs|]. split; [exact Hx|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs (nstep_cfg_sub _ _ _ _ _ _ Hst)) as [He Ht].
  split; [exact He| apply IH; exact Ht].
Qed.

(* [comment removed for export] *)
Lemma tsil_cfg_tall : forall {R} (t : itree node R) mo P Q,
  tsilC t mo P -> tall (nstep_cfg acfg) t mo Q -> tsilC t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P Q H HQ; cbn in *; [split; assumption|].
  destruct H as (Hs & Hx & Hk). split; [exact Hs|]. split; [exact Hx|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as [He Ht].
  split; [exact He|]. apply IH; [exact Ht| exact (HQ _ _ _ Hst)].
Qed.

Lemma tsil_cfg_ctall : forall {A} (t : itree node (exc A)) mo (P : exc A -> Model -> Prop) (Q : A -> Model -> Prop),
  tsilC t mo P -> ctall t mo Q ->
  tsilC t mo (fun r mo' => P r mo' /\ match r with Unr => True | Ok a => Q a mo' end).
Proof. intros A t mo P Q H HQ. exact (tsil_cfg_tall t mo P _ H HQ). Qed.

(* [comment removed for export] *)
Lemma tsil_cfg_pack : forall {A} (t : itree node (exc A)) mo (P : exc A -> Model -> Prop) (Q : A -> Model -> Prop),
  MSil.tsil t mo P -> ctall t mo Q ->
  tsilC t mo (fun r mo' => match r with Unr => P Unr mo' | Ok a => P (Ok a) mo' /\ Q a mo' end).
Proof.
  intros A t mo P Q H HQ.
  eapply ImplRz.tsil_mono; [exact (tsil_cfg_ctall t mo P Q (tsil_cfg_of_msil t mo P H) HQ)|].
  intros [|a] mo'; cbn; tauto.
Qed.

End RC__.
