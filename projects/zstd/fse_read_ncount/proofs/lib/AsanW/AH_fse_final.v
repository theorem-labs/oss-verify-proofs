(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ABase AMalloc_iface AHeapP AFake_iface AFake_arep AFake5_iface AFake5_arep
ADepot_iface F_adepot ARepQ ARepQP ASec ASecFrame AInstance AInstanceM AInstanceF AFreeAll AHarness_iface AF_fse_iface AF_fse_leaf AF_fse_prod AF_fse_write_C AF_fse_rd_iface
AF_fse_rd_closedF AH_fse_Hiface AH_fse_Biface AH_fse_asmBB AH_fse_asmD AH_fse_asmB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
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
Theorem fuzz_client_closed : forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) afake_rng.
Proof.
intros rc.
set (AI := AI_of (@AHI_free rc)).
assert (E : AHEAP AI = AHEAP_P (AH adepot_iface AQUAR ASEC_of)) by reflexivity.
assert (EC : aci AI = aci_I) by reflexivity.
apply (fuzz_oneA_of_halves AI AFake_iface.fflag afake_rng).
- exact afake_rng_mono.
- exact (stack_malloc_5_AI adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC).
- exact (stack_free_5_AI adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC).
- exact (fse_read_closedF adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC).
- exact prod_u32r_proofA.
- exact (prod_i32r_proofA prod_u32r_proofA).
- exact fse_wbound_proofA.
- exact fse_write_proofA.
- exact fse_iserror_proofA.
- exact (fz_BB_proof AI AFake_iface.fflag).
- exact (fz_D_proof AI AFake_iface.fflag afake_rng).
Qed.
