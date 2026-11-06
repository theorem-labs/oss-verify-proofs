(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
Import ListNotations.

Lemma in_map_WriteEv_no_exit : forall fd l code fs, ~ In (ExitEv code fs) (map (WriteEv fd) l).
Proof. intros fd l code fs Hin. apply in_map_iff in Hin as (x & Hx & _). discriminate Hx. Qed.

(* [comment removed for export] *)
Lemma nstep_no_exitev : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> forall code fs, ~ In (ExitEv code fs) evs.
Proof.
  intros n mo eff mo' evs Hst code fs.
  destruct n; cbn [nstep] in Hst.
  - (* [comment removed for export] *) destruct Hst as (k & _ & _ & _ & ->). apply in_map_WriteEv_no_exit.
  - (* [comment removed for export] *) destruct Hst as (_ & Hst).
    destruct (Z.of_nat (length (concat bufs)) =? 0)%Z.
    + destruct Hst as (_ & ->). intros [].
    + destruct Hst as (k & _ & _ & ->). apply in_map_WriteEv_no_exit.
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ttrace_exit_masked : forall {R : Type} (t : itree node R) mo tr,
  ttrace nstep nexit t mo tr ->
  forall code fs, In (ExitEv code fs) tr -> exists c : Z, code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).
Proof.
  intros R t. induction t as [r | n k IH]; intros mo tr Htr code fs Hin.
  - cbn in Htr. subst tr. destruct Hin.
  - cbn [ttrace] in Htr. destruct Htr as [(code' & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + destruct Hin as [E | []]. injection E as <- _.
      destruct n; cbn [nexit] in Hex; try contradiction. destruct Hex as [-> _]. eexists. reflexivity.
    + apply in_app_or in Hin as [Hin | Hin].
      * exfalso. exact (nstep_no_exitev _ _ _ _ _ Hst code fs Hin).
      * exact (IH rsp mo' tr' Htr' code fs Hin).
Qed.

(* [comment removed for export] *)
Lemma tree_traces_exit_masked : forall {R : Type} (t : itree node R) mo tr,
  tree_traces t mo tr ->
  forall code fs, In (ExitEv code fs) tr -> exists c : Z, code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).
Proof.
  intros R t mo tr (full & Hf & Hp) code fs Hin.
  exact (ttrace_exit_masked t mo full Hf code fs (in_is_prefix _ _ _ Hp Hin)).
Qed.

Lemma tree_traces_exit_any : forall {R : Type} (t : itree node R) mo tr code fs,
  tree_traces t mo (tr ++ [ExitEv code fs]) -> In code AnyExit.codes.
Proof.
  intros R t mo tr code fs H.
  destruct (tree_traces_exit_masked t mo _ H code fs ltac:(apply in_app_iff; right; left; reflexivity)) as [c ->].
  apply any_exit_covers.
Qed.

Lemma tree_traces_no_killev : forall {R : Type} (t : itree node R) mo tr sig fs,
  ~ tree_traces t mo (tr ++ [KillEv sig fs]).
Proof.
  intros R t mo tr sig fs H.
  exact (tree_traces_no_kill t mo _ H sig fs ltac:(apply in_app_iff; right; left; reflexivity)).
Qed.
