(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort RealizesHalts.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SPECH (inp : ProcInput) : TSet := spec (in_argv inp) (in_fs inp).

(* [comment removed for export] *)
Definition HALT_CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)

Definition EXS (T : TSet) : Prop :=
  forall tr code fs, T tr -> In (ExitEv code fs) tr -> In code HALT_CODES.

Lemma exs_exits_in : forall T, EXS T -> exits_in HALT_CODES T.
Proof.
  intros T H tr code fs Htr. apply (H _ code fs Htr). apply in_app_iff. right. left. reflexivity.
Qed.

Lemma prefix_in : forall {A} (l1 l2 : list A) x, is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|].
  destruct l2 as [|b l2]; [destruct H|]. destruct H as [-> H].
  destruct Hx as [->|Hx]; [left; reflexivity | right; exact (IH l2 x H Hx)].
Qed.

Lemma exs_emit : forall evs T,
  (forall code fs, In (ExitEv code fs) evs -> In code HALT_CODES) -> EXS T -> EXS (t_emit evs T).
Proof.
  intros evs T He HT tr code fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (He code fs (prefix_in tr evs _ Hp Hin)).
  - apply in_app_iff in Hin as [Hin|Hin]; [exact (He code fs Hin) | exact (HT tr' code fs Htr' Hin)].
Qed.

Lemma exs_nil : EXS t_nil.
Proof. intros tr code fs -> Hin. destruct Hin. Qed.

Lemma exs_exit : forall c fs, In c HALT_CODES -> EXS (t_exit c fs).
Proof.
  intros c fs Hc. unfold t_exit. apply exs_emit; [|exact exs_nil].
  intros code fs' [H|[]]. injection H as <- _. exact Hc.
Qed.

Lemma exs_alt2 : forall A B, EXS A -> EXS B -> EXS (t_alt2 A B).
Proof. intros A B HA HB tr code fs [H|H]; [exact (HA tr code fs H) | exact (HB tr code fs H)]. Qed.

Lemma exs_W : forall ch s code fs, ~ In (ExitEv code fs) (W ch s).
Proof. intros ch s code fs Hin. unfold W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb. Qed.

Lemma in_code0 : In (exit_code 0) HALT_CODES. Proof. left. reflexivity. Qed.
Lemma in_code2 : In (exit_code 2) HALT_CODES. Proof. right. left. reflexivity. Qed.

Lemma exs_die : forall msg fs, EXS (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply exs_emit; [| apply exs_exit; exact in_code2].
  intros code fs' Hin. exfalso. exact (exs_W _ _ _ _ Hin).
Qed.

Lemma exs_body : forall data fs, EXS (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply exs_die|].
  destruct (length data <? 6)%nat; [apply exs_die|].
  destruct (length data <? 6 + config_len data)%nat; [apply exs_die|].
  apply exs_emit; [| apply exs_exit; exact in_code0].
  intros code fs' Hin. exfalso. exact (exs_W _ _ _ _ Hin).
Qed.

Lemma exs_spec : forall argv fs0, EXS (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|a2 r]]]; try apply exs_die.
  destruct (4096 <=? length path)%nat; [apply exs_die|].
  destruct (path_eqb path []); [apply exs_die|].
  destruct (path_is_dirref path); [apply exs_alt2; apply exs_die|].
  destruct (fs_lookup fs0 path) as [data|]; [| apply exs_die].
  apply exs_alt2; [apply exs_die | apply exs_body].
Qed.

(* [comment removed for export] *)
Theorem spec_exits_in_SPECH : spec_exits_in HALT_CODES SPECH.
Proof. intros inp. apply exs_exits_in. apply exs_spec. Qed.

(* [comment removed for export] *)
Corollary spec_exit_code : forall argv fs0 tr code fs',
  spec argv fs0 (tr ++ [ExitEv code fs']) -> In code HALT_CODES.
Proof. intros argv fs0. exact (exs_exits_in _ (exs_spec argv fs0)). Qed.

(* [comment removed for export] *)

Definition NK (T : TSet) : Prop := forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.

Lemma nk_emit : forall evs T, (forall sig fs, ~ In (KillEv sig fs) evs) -> NK T -> NK (t_emit evs T).
Proof.
  intros evs T He HT tr sig fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (He sig fs (prefix_in tr evs _ Hp Hin)).
  - apply in_app_iff in Hin as [Hin|Hin]; [exact (He sig fs Hin) | exact (HT tr' sig fs Htr' Hin)].
Qed.
Lemma nk_nil : NK t_nil. Proof. intros tr sig fs -> Hin. destruct Hin. Qed.
Lemma nk_exit : forall c fs, NK (t_exit c fs).
Proof. intros c fs. apply nk_emit; [|exact nk_nil]. intros sig fs' [Hc|[]]. discriminate Hc. Qed.
Lemma nk_alt2 : forall A B, NK A -> NK B -> NK (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H]; [exact (HA tr sig fs H) | exact (HB tr sig fs H)]. Qed.
Lemma nk_W : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof. intros ch s sig fs Hin. unfold W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb. Qed.
Lemma nk_die : forall msg fs, NK (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply nk_emit; [apply nk_W | apply nk_exit]. Qed.
Lemma nk_body : forall data fs, NK (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply nk_die|].
  destruct (length data <? 6)%nat; [apply nk_die|].
  destruct (length data <? 6 + config_len data)%nat; [apply nk_die|].
  apply nk_emit; [apply nk_W | apply nk_exit].
Qed.
Lemma nk_spec : forall argv fs0, NK (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|a2 r]]]; try apply nk_die.
  destruct (4096 <=? length path)%nat; [apply nk_die|].
  destruct (path_eqb path []); [apply nk_die|].
  destruct (path_is_dirref path); [apply nk_alt2; apply nk_die|].
  destruct (fs_lookup fs0 path) as [data|]; [| apply nk_die].
  apply nk_alt2; [apply nk_die | apply nk_body].
Qed.

Theorem no_kill_SPECH : no_kill SPECH.
Proof. intros inp tr sig fs H. exact (nk_spec _ _ tr sig fs H). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shipped_lim_source_ge : 2 ^ 31 <= ShippedBudgets.lim_source.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
Theorem halts_of_realizes_SPECH : forall cfg segs pc ph lim,
  image_realizes_cfg_e cfg segs pc ph lim SPECH ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim HALT_CODES (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim HR.
  exact (halts_allowed_forced_only_of_realizes cfg segs pc ph lim HALT_CODES SPECH
           HR spec_exits_in_SPECH no_kill_SPECH).
Qed.
