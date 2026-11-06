(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractS1 S1Spec S1MainInst BaseSpecNk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBCore.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition as_realizes_spec (tsegs : list Segment) (tpc : N) (tph : PhdrInfo) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage tsegs tpc tph) en inp ->
    valid_input_either inp ->
    srealizes tsegs (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Theorem base_san_glue : forall tsegs tpc tph,
  lib_contract_S1 -> as_realizes_spec tsegs tpc tph ->
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage tsegs tpc tph).
Proof.
  intros tsegs tpc tph LIB AS. apply error_free_scfg_budgets_abort_sanitizer_of_pinned.
  intros en_s en_t inp Hvs Hvt Hinp.
  pose proof (AS en_t inp Hvt (valid_input_either_of_valid_input_abort inp Hinp)) as HA.
  pose proof (valid_input_abort_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hvs.
  destruct en_s as [rsp rbrk rmb rrnd]. destruct en_t as [asp abrk amb arnd].
  destruct Hvs as (Hsp1 & Hbrk1 & _ & Hfit1).
  pose proof Hinp as Hv. destruct Hv as (Hva & Hve & _).
  unfold strong_equiv_error_free_budgets_scfg_abort.
  exact (spin_shape_strong_equiv_ef_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp)) inp
           (s1_main_inst rsp rbrk rmb rrnd inp LIB Hsp1 Hbrk1 Hva Hve Hfit1) HA (spec_nokill _ _)).
Qed.

Definition as_realizes_spec_A : Prop :=
  as_realizes_spec Asan.M.loaded_segments
    Asan.M.init_pc Asan.M.phdrs.
Definition as_realizes_spec_B : Prop :=
  as_realizes_spec AsanUbsan.M.loaded_segments
    AsanUbsan.M.init_pc AsanUbsan.M.phdrs.

Theorem base_asan_glue : lib_contract_S1 -> as_realizes_spec_A ->
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments
             Asan.M.init_pc Asan.M.phdrs).
Proof. apply base_san_glue. Qed.

Theorem base_both_glue : lib_contract_S1 -> as_realizes_spec_B ->
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments
             AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. apply base_san_glue. Qed.

Theorem base_san_scfg : forall tsegs tpc tph,
  lib_contract_S1 -> as_realizes_spec tsegs tpc tph ->
  strong_universal_error_free_T_scfg CFG
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage tsegs tpc tph).
Proof.
  intros tsegs tpc tph LIB AS. apply spin_shape_universal_ef.
  intros en1 en2 inp Hen1 Hen2 Hvalid.
  pose proof (AS en2 inp Hen2 (valid_input_either_of_valid_input inp Hvalid)) as HA.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen1.
  destruct en1 as [rsp rbrk rmb rrnd].
  destruct Hen1 as (Hsp1 & Hbrk1 & _ & Hfit1).
  pose proof Hvalid as Hv. destruct Hv as (Hva & Hve & _).
  exists (spec (in_argv inp) (in_fs inp)). split; [|exact HA].
  exact (s1_main_inst rsp rbrk rmb rrnd inp LIB Hsp1 Hbrk1 Hva Hve Hfit1).
Qed.

Theorem base_asan_scfg : lib_contract_S1 -> as_realizes_spec_A ->
  strong_universal_error_free_T_scfg CFG
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments
             Asan.M.init_pc Asan.M.phdrs).
Proof. apply base_san_scfg. Qed.

Theorem base_both_scfg : lib_contract_S1 -> as_realizes_spec_B ->
  strong_universal_error_free_T_scfg CFG
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments
             AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. apply base_san_scfg. Qed.
