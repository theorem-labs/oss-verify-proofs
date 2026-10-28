(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.
Require OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.
Require OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.
Require OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Safety SafetyAbort.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitLayout.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require TopClosed.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require TopClosed.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require TopClosed.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require TopClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma Spec_no_kill : forall inp t, DriverSpec.Spec inp t ->
  forall sig fs, ~ List.In (LinuxProcessSemantics.LinuxProcessSem.State.KillEv sig fs) t.
Proof.
  intros inp t Ht sig fs Hin.
  destruct (DriverSpec.Spec_ends_in_exit inp t Ht) as (evs & c & -> & Hw).
  apply List.in_app_or in Hin. destruct Hin as [Hin | [Hin | []]].
  - apply (proj1 (List.Forall_forall _ _) Hw) in Hin. destruct Hin as (ch & b & E). discriminate E.
  - discriminate Hin.
Qed.


Theorem strong_universal_error_free_fuzz_tobj_c_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.phdrs).
Proof.
  intros [ssp sbrk smb srnd] [tsp tbrk tmb trnd] inp Hvs Hvt Hinp _.
  pose proof (LinuxProcessSemantics.LinuxProcessSem.Run.valid_input_either_of_valid_input_abort _ Hinp) as HinpE.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvs) as Hvs48.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvt) as Hvt48.
  destruct (P.TopClosed.top_closed_P_sanitizer ssp sbrk smb srnd inp Hvs48 HinpE) as (Ss & Cs & Es).
  destruct (A.TopClosed.top_closed_A tsp tbrk tmb trnd inp Hvt48 HinpE) as (St & Ct & Et).
  exact (SafetyAbort.strong_equiv_error_free_budgets_scfg_abort_of_facts_lim
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs) (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Asan.M.phdrs)
           (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry ssp sbrk smb srnd) (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry tsp tbrk tmb trnd) inp (DriverSpec.Spec inp) (Spec_no_kill inp) Ss Cs Es St Ct Et).
Qed.

Theorem strong_universal_error_free_fuzz_tobj_c_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.phdrs).
Proof.
  intros [ssp sbrk smb srnd] [tsp tbrk tmb trnd] inp Hvs Hvt Hinp _.
  pose proof (LinuxProcessSemantics.LinuxProcessSem.Run.valid_input_either_of_valid_input_abort _ Hinp) as HinpE.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvs) as Hvs48.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvt) as Hvt48.
  destruct (P.TopClosed.top_closed_P_sanitizer ssp sbrk smb srnd inp Hvs48 HinpE) as (Ss & Cs & Es).
  destruct (B.TopClosed.top_closed_A tsp tbrk tmb trnd inp Hvt48 HinpE) as (St & Ct & Et).
  exact (SafetyAbort.strong_equiv_error_free_budgets_scfg_abort_of_facts_lim
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs) (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.AsanUbsan.M.phdrs)
           (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry ssp sbrk smb srnd) (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry tsp tbrk tmb trnd) inp (DriverSpec.Spec inp) (Spec_no_kill inp) Ss Cs Es St Ct Et).
Qed.

Theorem strong_universal_error_free_fuzz_tobj_c_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.phdrs).
Proof.
  intros [ssp sbrk smb srnd] [tsp tbrk tmb trnd] inp Hvs Hvt Hinp _.
  pose proof (LinuxProcessSemantics.LinuxProcessSem.Run.valid_input_either_of_valid_input_abort _ Hinp) as HinpE.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvs) as Hvs48.
  pose proof (InitLayout.valid_entry48_of_input_abort _ _ _ Hinp Hvt) as Hvt48.
  destruct (P.TopClosed.top_closed_P ssp sbrk smb srnd inp Hvs48 HinpE) as (Ss & Cs & Es).
  destruct (U.TopClosed.top_closed_U tsp tbrk tmb trnd inp Hvt48 HinpE) as (St & Ct & Et).
  exact (SafetyAbort.strong_equiv_error_free_budgets_scfg_abort_of_facts_lim
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
           LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Plain.M.phdrs) (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.loaded_segments OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.init_pc OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images.Ubsan.M.phdrs)
           (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry ssp sbrk smb srnd) (LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry tsp tbrk tmb trnd) inp (DriverSpec.Spec inp) (Spec_no_kill inp) Ss Cs Es St Ct Et).
Qed.
