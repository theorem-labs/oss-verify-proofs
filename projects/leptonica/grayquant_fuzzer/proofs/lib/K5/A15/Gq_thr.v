(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface D_iface D_defs Lept_iface
  Gm_iface Gq_iface Gq_cmap_iface Gq_thr_iface Gq_thr2_iface Gq_numa Gq_opcase Gq_thr_c0 Gq_thr_c16.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section THR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PARSE : parseStringForNumbers_gq_cps RT.
Hypothesis NSORT : numaSort_gq_cps RT.
Hypothesis QTAB : makeGrayQuantTableArb_gq_cps RT.
Hypothesis SETBW : pixcmapSetBlackAndWhite00_cps RT.
Hypothesis NDY : numaDestroy_cps RT.
Hypothesis SCM : pixSetColormap_cps RT.
Hypothesis RMC : pixRemoveColormap_gray_cps RT.
Hypothesis PDRC : pixDestroy_rc_cps RT.
Hypothesis PDY : pixDestroy_cps RT.

Theorem pixThresholdGrayArb_ok : pixThresholdGrayArb_cps RT.
Proof using AF GP RC RERR PCS PCR PCI PARSE NSORT QTAB SETBW NDY SCM RMC PDRC PDY.
  unfold pixThresholdGrayArb_cps.
  apply (gq_op_of_cases RT).
  - exact (thr_c0 RT AF GP RC RERR PCS PCR PCI PARSE NSORT QTAB SETBW NDY SCM RMC PDRC PDY).
  - exact (thr_c16 RT AF GP RC RERR PCS PCR PCI PARSE NSORT QTAB SETBW NDY SCM RMC PDRC PDY).
Qed.
End THR.
