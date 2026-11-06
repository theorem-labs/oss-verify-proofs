(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import HaltsTrace.
Import ListNotations.

(* [comment removed for export] *)
Lemma ttrace_exit_S : forall (S : list word) {R : Type} (t : itree node R) mo tr,
  ttrace nstep nexit t mo tr -> texits nexit S t ->
  forall code fs, In (ExitEv code fs) tr -> In code S.
Proof.
  intros S R t. induction t as [r | n k IH]; intros mo tr Htr Hx code fs Hin.
  - cbn in Htr. subst tr. destruct Hin.
  - cbn [ttrace] in Htr. destruct Hx as [Hn Hk].
    destruct Htr as [(code' & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + destruct Hin as [E | []]. injection E as <- _. exact (Hn _ _ _ Hex).
    + apply in_app_or in Hin as [Hin | Hin].
      * exfalso. exact (nstep_no_exitev _ _ _ _ _ Hst code fs Hin).
      * exact (IH rsp mo' tr' Htr' (Hk rsp) code fs Hin).
Qed.

Lemma tree_traces_exit_S : forall (S : list word) {R : Type} (t : itree node R) mo tr code fs,
  texits nexit S t -> tree_traces t mo (tr ++ [ExitEv code fs]) -> In code S.
Proof.
  intros S R t mo tr code fs Hx (full & Hf & Hp).
  exact (ttrace_exit_S S t mo full Hf Hx code fs (in_is_prefix _ _ _ Hp ltac:(apply in_app_iff; right; left; reflexivity))).
Qed.
