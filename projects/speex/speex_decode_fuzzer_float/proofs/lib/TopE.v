(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Glue.
Variable T : ProcInput -> list event -> Prop.

Definition side_canon (img : Image) (lim : Z) : Prop :=
forall en inp, valid_entry img en inp -> valid_input_either inp ->
trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) img lim en inp)) (T inp)
/\ ~ bh_errors (run_scfg (alloc_only_cfg false) img lim en inp).

Definition T_nokill : Prop := forall inp tr sig fs, T inp tr -> ~ In (KillEv sig fs) tr.

Lemma side_unkilled : forall img lim, side_canon img lim -> T_nokill ->
forall en inp, valid_entry img en inp -> valid_input_either inp ->
error_free_unkilled (run_scfg (alloc_only_cfg false) img lim en inp).
Proof.
intros img lim H NK en inp He Hi. destruct (H en inp He Hi) as [Htr Herr]. split; [exact Herr|].
intros (tr & sig & fs & Hb & Hin). exact (NK inp tr sig fs (proj1 (Htr tr) Hb) Hin).
Qed.

Theorem glue_budgets_abort_at : forall imgS imgT limS limT,
side_canon imgS limS -> side_canon imgT limT -> T_nokill ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) limS limT imgS imgT.
Proof.
intros imgS imgT limS limT HS HT NK enS enT inp HeS HeT Hv _.
pose proof (valid_input_either_of_valid_input_abort _ Hv) as Hi.
split; [exact (side_unkilled _ _ HS NK enS inp HeS Hi)|]. split; [exact (side_unkilled _ _ HT NK enT inp HeT Hi)|].
intros tr. rewrite (proj1 (HS enS inp HeS Hi) tr). symmetry. exact (proj1 (HT enT inp HeT Hi) tr).
Qed.

End Glue.
