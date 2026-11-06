(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface D_iface D_defs Lept_iface
  Gq_iface Gq_opcase Gq_band_c0 Gq_band_c16.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BAND.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PDR : pixDestroy_rc_cps RT.

Theorem pixGenerateMaskByBand_ok : pixGenerateMaskByBand_cps RT.
Proof using AF GP RERR PCS PCR PCI PDR.
  unfold pixGenerateMaskByBand_cps.
  apply (gq_op_of_cases RT).
  - exact (band_c0 RT AF GP RERR PCS PCR PCI PDR).
  - exact (band_c16 RT AF GP RERR PCS PCR PCI PDR).
Qed.
End BAND.
