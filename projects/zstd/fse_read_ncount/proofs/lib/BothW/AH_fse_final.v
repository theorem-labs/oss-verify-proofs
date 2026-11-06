(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface
ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake5_iface AFake5_arep
AF_fse_iface AF_fse_prod AF_fse_leaf AF_fse_write_C AF_fse_rd_iface AF_fse_rd_closedF
AH_fse_Hiface AH_fse_Biface AH_fse_asmB AH_fse_asmBB AH_fse_asmD ARepQ ASec F_adepot AInstance AInstanceF AFreeAll.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section Inst.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
Hypothesis EC : aci AI = CI.
#[using="DI AQ ASEC HL CI CI_OK E EC"] Theorem fuzz_oneA_closedF : fuzz_oneA_stmt AI afake_rng.
Proof.
exact (fuzz_oneA_of_halves AI fflag afake_rng afake_rng_mono
(stack_malloc_5_AI DI AQ ASEC HL CI CI_OK AI E EC) (stack_free_5_AI DI AQ ASEC HL CI CI_OK AI E EC)
(fse_read_closedF DI AQ ASEC HL CI CI_OK AI E EC)
prod_u32r_proofA (prod_i32r_proofA prod_u32r_proofA) fse_wbound_proofA fse_write_proofA fse_iserror_proofA
(fz_BB_proof AI fflag) (fz_D_proof AI fflag afake_rng)).
Qed.
End Inst.
End CANSEC1.
Theorem fuzz_client_closed : forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) AFake_iface.afake_rng.
Proof.
intros rc.
exact (@fuzz_oneA_closedF rc adepot_iface AQUAR ASEC_of AH_laws (aci (AI_of AHI_free)) (AI_of_CI_OK AHI_free)
(AI_of AHI_free) (AI_of_E AHI_free) eq_refl).
Qed.
