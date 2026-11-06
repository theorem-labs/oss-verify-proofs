(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.Asan.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec BaseGlueS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SRCM := OSSVerify.coturn.FuzzStunClient.images.Plain.M.
Module ASANM := OSSVerify.coturn.FuzzStunClient.images.Asan.M.
Module BOTHM := OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.

(* [comment removed for export] *)
Definition ref_spec_stmt_san : Prop :=
  forall sp brk mb rnd inp,
    valid_entry (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
    realizes SRCM.loaded_segments
      (init_config SRCM.loaded_segments SRCM.init_pc SRCM.phdrs sp brk mb rnd SanitizerBudgets.lim_source inp)
      (spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Definition asan_spec_stmt : Prop :=
  forall sp brk mb rnd inp,
    valid_entry (mkImage ASANM.loaded_segments ASANM.init_pc ASANM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
    srealizes ASANM.loaded_segments
      (init_config ASANM.loaded_segments ASANM.init_pc ASANM.phdrs sp brk mb rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Definition both_spec_stmt : Prop :=
  forall sp brk mb rnd inp,
    valid_entry (mkImage BOTHM.loaded_segments BOTHM.init_pc BOTHM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
    srealizes BOTHM.loaded_segments
      (init_config BOTHM.loaded_segments BOTHM.init_pc BOTHM.phdrs sp brk mb rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Theorem asan_base_of_specs : ref_spec_stmt_san -> asan_spec_stmt ->
  strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs)
    (mkImage ASANM.loaded_segments ASANM.init_pc ASANM.phdrs).
Proof.
  intros H1 H2.
  exact (base_of_realizes_s_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
           SRCM.loaded_segments SRCM.init_pc SRCM.phdrs ASANM.loaded_segments ASANM.init_pc ASANM.phdrs
           (fun inp => spec (in_argv inp) (in_fs inp)) H1 H2).
Qed.

Theorem both_base_of_specs : ref_spec_stmt_san -> both_spec_stmt ->
  strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs)
    (mkImage BOTHM.loaded_segments BOTHM.init_pc BOTHM.phdrs).
Proof.
  intros H1 H2.
  exact (base_of_realizes_s_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
           SRCM.loaded_segments SRCM.init_pc SRCM.phdrs BOTHM.loaded_segments BOTHM.init_pc BOTHM.phdrs
           (fun inp => spec (in_argv inp) (in_fs inp)) H1 H2).
Qed.
