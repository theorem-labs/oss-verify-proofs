(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Gq_iface Gq_cmap_iface
  Gq_rmc_defs Gq_rmc_n0 Gq_rmc_n16 Gq_rmc_y0 Gq_rmc_y16.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RMC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis TOARR : pixcmapToArrays_cps RT.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.

Theorem pixRemoveColormap_gray_ok : pixRemoveColormap_gray_cps RT.
Proof using AF GP RC TOARR PCS PCR PCI.
  apply (pixRemoveColormap_of_cases RT).
  - exact (pixRemoveColormap_n0 RT AF GP RC).
  - exact (pixRemoveColormap_n16 RT AF GP RC).
  - exact (pixRemoveColormap_y0 RT AF GP RC TOARR PCS PCR PCI).
  - exact (pixRemoveColormap_y16 RT AF GP RC TOARR PCS PCR PCI).
Qed.
End RMC.
