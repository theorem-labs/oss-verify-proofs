(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1br X1bo X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel TopE.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r6 X1r7 X1nu X1r5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1pe X1ot.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgP := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgU := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) (only parsing).

Definition Tc : ProcInput -> list event -> Prop := X1nu.Tc.

Lemma Tc_eq : forall inp, Tc inp = canonT (argv_Z (in_argv inp)) (in_fs inp).
Proof. reflexivity. Qed.

Lemma Tc_nokill : T_nokill Tc.
Proof. intros inp tr sig fs H. exact (canonT_nokill _ _ tr sig fs H). Qed.

Definition impl_root (segs : list Segment) (pc : N) (ph : PhdrInfo) (rs : Z) : Prop :=
forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_core inp ->
impl segs (at_node segs) (prog segs rs (ceil_of en) (in_argv inp)) (epost (fun (_ : unit) (_ : machine_state) => True))
(ms0F segs pc ph en inp).

Theorem P_side_at : forall lim, X1pe.LBUDGET <= lim ->
impl_root Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs RSTAGE_plain ->
side_canon Tc imgP lim.
Proof.
intros lim Hlim HP en inp He Hi0. pose proof (valid_input_core_of_either _ Hi0) as Hi.
destruct (prog_plain_model_ok_at lim en inp Hlim He Hi) as [Hl Hs].
destruct (run_of_treeF _ _ _ lim _ _ en inp (HP en inp He Hi) Hl Hs) as (Htr & Herr & _).
split; [| exact Herr].
intros tr. rewrite (Htr tr). exact (prog_det_plain_at lim en inp Hlim He Hi tr).
Qed.

Theorem P_side :
impl_root Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs RSTAGE_plain ->
side_canon Tc imgP source_alloc_limit.
Proof. exact (P_side_at source_alloc_limit X1ot.LBUDGET_le_source). Qed.

Lemma LBUDGET_le_sanitizer : X1pe.LBUDGET <= SanitizerBudgets.lim_source.
Proof. unfold X1pe.LBUDGET, SanitizerBudgets.lim_source, sanitizer_source_limit. lia. Qed.

Theorem P_side_sanitizer :
impl_root Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs RSTAGE_plain ->
side_canon Tc imgP SanitizerBudgets.lim_source.
Proof. exact (P_side_at SanitizerBudgets.lim_source LBUDGET_le_sanitizer). Qed.

Theorem U_side :
impl_root Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs RSTAGE_ubsan ->
side_canon Tc imgU target_alloc_limit.
Proof.
intros HU en inp He Hi0. pose proof (valid_input_core_of_either _ Hi0) as Hi.
destruct (prog_ubsan_model_ok en inp He Hi) as [Hl Hs].
destruct (run_of_treeF _ _ _ target_alloc_limit _ _ en inp (HU en inp He Hi) Hl Hs) as (Htr & Herr & _).
split; [| exact Herr].
intros tr. rewrite (Htr tr). exact (prog_det_ubsan en inp He Hi tr).
Qed.

Theorem run_defined_of_valid : forall inp ok, valid_input_either inp -> run_defined (in_fs inp) (argv_Z (in_argv inp)) ok.
Proof. exact run_defined_valid. Qed.
