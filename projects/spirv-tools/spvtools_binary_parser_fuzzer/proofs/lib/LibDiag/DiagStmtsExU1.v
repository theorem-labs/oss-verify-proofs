(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PmHypsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRepU1 DiagU1 DiagStmtsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Section StmtsEx.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.

  Definition exhausted_needs (G : grammar) (tc : tabl_consts) (idesc : Z -> Z -> Prop) : Prop :=
    tc_lookup_opcode tc = TC_LOOKUP_OPCODE /\ tc_idesc_name tc = TC_IDESC_NAME
    /\ tc_operand_type_str tc = TC_OPERAND_TYPE_STR /\ tc_strlen tc = TC_STRLEN
    /\ 0 <= tc_lookup_stack tc <= 64
    /\ lookup_opcode_stmt SEGS Ly.L G tc idesc
    /\ idesc_name_stmt SEGS Ly.L tc idesc
    /\ operand_type_str_stmt SEGS Ly.L tc
    /\ strlen_ro_stmt SEGS Ly.L tc

    /\ (forall d op, idesc d op -> 0x10000 <= d /\ d + 60 <= 2 ^ 40 /\ d mod 4 = 0).

  Definition diag_contract : Prop :=
    ds_rep_laws SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ pdiagP_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI) (dc_pdiag dcU1)
    /\ put_cstr_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ put_u16_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ put_u32_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ put_u64_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ put_int_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ put_chars_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI)
    /\ ds_dtor_stmt SEGS Ly.L MI ST dcU1 (ds_rep MI).

  Definition diag_main_goal : Prop := diag_needs MI ST -> diag_contract.

  Definition diag_exhausted_goal : Prop :=
    forall G tc idesc, diag_needs MI ST -> exhausted_needs G tc idesc -> exhaustedU_stmt SEGS Ly.L MI ST dcU1.
End StmtsEx.
