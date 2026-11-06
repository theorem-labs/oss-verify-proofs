(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Export BaseSpecNk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractDefs S1Spec S1MainInst U1MainInst.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem base_ubsan_scfg :
  lib_contract_S1 -> lib_contract_U1 ->
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments
             Ubsan.M.init_pc
             Ubsan.M.phdrs).
Proof.
  intros LIB1 LIB2.
  apply spin_shape_universal_ef.
  intros en1 en2 inp Hen1 Hen2 Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen1. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen2.
  destruct en1 as [rsp rbrk rmb rrnd]; destruct en2 as [asp abrk amb arnd].
  destruct Hen1 as (Hsp1 & Hbrk1 & _ & Hfit1); destruct Hen2 as (Hsp2 & Hbrk2 & _ & Hfit2).
  destruct Hvalid as (Hva & Hve & _).
  exists (spec (in_argv inp) (in_fs inp)). split.
  - exact (s1_main_inst rsp rbrk rmb rrnd inp LIB1 Hsp1 Hbrk1 Hva Hve Hfit1).
  - exact (u1_main_inst asp abrk amb arnd inp LIB2 Hsp2 Hbrk2 Hva Hve Hfit2).
Qed.

Theorem base_ubsan_abort :
  lib_contract_S1 -> lib_contract_U1 ->
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    source_alloc_limit target_alloc_limit
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments
             Ubsan.M.init_pc
             Ubsan.M.phdrs).
Proof.
  intros LIB1 LIB2.
  apply spin_shape_universal_ef_abort.
  intros en1 en2 inp Hen1 Hen2 Hvalid.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen1. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen2.
  destruct en1 as [rsp rbrk rmb rrnd]; destruct en2 as [asp abrk amb arnd].
  destruct Hen1 as (Hsp1 & Hbrk1 & _ & Hfit1); destruct Hen2 as (Hsp2 & Hbrk2 & _ & Hfit2).
  destruct Hvalid as (Hva & Hve & _).
  exists (spec (in_argv inp) (in_fs inp)). split; [| split].
  - exact (s1_main_inst rsp rbrk rmb rrnd inp LIB1 Hsp1 Hbrk1 Hva Hve Hfit1).
  - exact (u1_main_inst asp abrk amb arnd inp LIB2 Hsp2 Hbrk2 Hva Hve Hfit2).
  - apply spec_nokill.
Qed.
