(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 D_iface D_defs Bi_pb_defs Bi_fz_defs Bi_fzkit Bi_fuzz_defs Bi_fuzz0 Bi_fuzz16.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_fuzz () := "C69OSSVerify5KrLib2K53A028Bi_fuzz09bi_fuzz_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029Bi_fuzz16:bi_fuzz_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<Bi_fuzz_defs@bi_fuzz_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FUZZTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis PCOPY : pixCopy_nn_cpsF RT.
Hypothesis PB : pixBilateral_cps2 RT.
Hypothesis PBBE : pixBlockBilateralExact_cps2 RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis PXDN : pixDestroy_null_cpsF RT.

Theorem bi_fuzz_ok : bi_fuzz_one_cps2 RT.
Proof using AF GP FKC DESER PCOPY PB PBBE PXD PXDN.
ltac2:(KReplay.run1 (kr_t_Bi_fuzz ()) ["FUZZTOP"] "p;:p;3g0000l:2Tg000nl:1Tg001nj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,5DESERR4p,5PCOPYR5p,2PBR6p,4PBBER7p,3PXDR8p,4PXDNR9M:2P0P1P2P3P4P5P6P7P8P9M:130o"). Qed.
End FUZZTOP.
