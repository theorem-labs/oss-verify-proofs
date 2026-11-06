(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_gaps_iface D_iface D_defs D_libiface Lept_iface Lept_iface_nz
  Lept_stderr Lept_err Lept_hdr Lept_create LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_setcmap LeptM_destroy LeptC_padbits
  Lept_zero Lept_gmax Lept_deser.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gm_iface Gq_iface Gq_gaps Gq_obj Gq_numa Gq_nz Gq_cmap_iface Gq_thr_iface Gq_thr2_iface
  Gm_strrepl Gm_destroy_null Gm_cmapvalid Gm_cmapcopy Gm_copycmap Gm_copyres Gm_hdr_sure Gm_noinit Gm_tmplnoinit Gm_pixcopy
  Gq_create Gq_copyinf Gq_destroy_rc Gq_toarr Gq_rmc
  Ed_numa_create Ed_numa_destroy Ed_numa_addfast
  Gq_band Gq_band32 Gq_discr32 Gq_dither_low
  Gq_parse Gq_nsort Gq_qtab Gq_cmapbw Gq_cmaplin
  Gq_d2bpp_cmdefs Gq_d2bpp_cm Gq_dbin Gq_d2bpp Gq_thr
  Gq_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section TOP.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GG : gq_gaps RT.

Theorem gq_fuzz_top : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof using RC GP GG.
  pose proof (rc_facts RT RC) as AF.
  (* [comment removed for export] *)
  assert (SE : lept_stderr_cps RT) by (apply lept_stderr_ok; assumption).
  assert (REI : returnError_cps RT e_returnErrorInt) by (apply returnError_ok; first [assumption | left; reflexivity]).
  assert (REP : returnError_cps RT e_returnErrorPtr) by (apply returnError_ok; first [assumption | right; reflexivity]).
  assert (HDR : pixCreateHeader_cps RT) by (apply pixCreateHeader_ok; assumption).
  assert (ZERO : pixZero_cps RT) by (apply pixZero_ok; assumption).
  assert (GMAX : pixGetMaxColorIndex_cps RT) by (apply pixGetMaxColorIndex_ok; assumption).
  assert (CMDES : pixcmapDeserialize_cps RT) by (apply pixcmapDeserialize_ok; assumption).
  assert (CMD : pixcmapDestroy_cps RT) by (apply pixcmapDestroy_ok; first [assumption | exact (gp_free RT GP)]).
  assert (VALID : pixcmapIsValid_cps RT) by (apply pixcmapIsValid_ok; assumption).
  assert (SETCM : pixSetColormap_cps RT) by (apply pixSetColormap_ok; assumption).
  assert (DESTROY : pixDestroy_cps RT) by (apply pixDestroy_ok; assumption).
  assert (PAD : pixSetPadBits_cps RT) by (apply pixSetPadBits_ok; assumption).
  assert (CRE : pixCreate_cps RT) by (apply pixCreate_ok; assumption).
  assert (DESER : Gq_nz.pixDeserialize_nz_cps RT) by (exact (pixDeserialize_nz_ok RT AF RC GP SE REP HDR CRE DESTROY CMDES SETCM VALID)).
  (* [comment removed for export] *)
  assert (SRN : stringReplace_null_cps RT) by (apply stringReplace_null_ok; assumption).
  assert (DNULL : pixDestroy_null_cps RT) by (apply pixDestroy_null_ok; assumption).
  assert (IVN : pixcmapIsValid_null_cps RT) by (apply pixcmapIsValid_null_ok; assumption).
  assert (CMC : pixcmapCopy_cps RT) by (apply pixcmapCopy_ok; assumption).
  assert (CCM : pixCopyColormap_cps RT) by (apply pixCopyColormap_ok; assumption).
  assert (PCR : pixCopyResolution_cps RT) by (apply pixCopyResolution_ok; assumption).
  assert (HDRS : pixCreateHeader_sure_cps RT) by (apply pixCreateHeader_sure_ok; assumption).
  assert (NIS : pixCreateNoInit_sure_cps RT) by (apply pixCreateNoInit_sure_ok; assumption).
  assert (TNI : pixCreateTemplateNoInit_cps RT) by (apply pixCreateTemplateNoInit_ok; assumption).
  assert (PCOPY : pixCopy_cps RT) by (apply pixCopy_ok; assumption).
  assert (PCS : pixCreate_sure_cps RT) by (apply pixCreate_sure_ok; assumption).
  assert (PCI : pixCopyInputFormat_cps RT) by (apply pixCopyInputFormat_ok; assumption).
  assert (PDR : pixDestroy_rc_cps RT) by (apply pixDestroy_rc_ok; assumption).
  assert (TOARR : pixcmapToArrays_cps RT) by (apply pixcmapToArrays_ok; assumption).
  assert (RMC : pixRemoveColormap_gray_cps RT) by (apply pixRemoveColormap_gray_ok; assumption).
  assert (NUMAC : numaCreate_cps RT) by (apply numaCreate_ok; assumption).
  assert (NDY : numaDestroy_cps RT) by (apply numaDestroy_ok; assumption).
  assert (NADDF : numaAddNumber_fast_cps RT) by (apply numaAddNumber_fast_ok; assumption).
  (* [comment removed for export] *)
  assert (OP3 : pixGenerateMaskByBand_cps RT) by (apply pixGenerateMaskByBand_ok; assumption).
  assert (OP4 : pixGenerateMaskByBand32_cps RT) by (apply pixGenerateMaskByBand32_ok; assumption).
  assert (OP5 : pixGenerateMaskByDiscr32_cps RT) by (apply pixGenerateMaskByDiscr32_ok; assumption).
  assert (DLOW : ditherToBinaryLow_cps RT) by (apply ditherToBinaryLow_ok; assumption).
  assert (CML : pixcmapCreateLinear24_cps RT) by (apply pixcmapCreateLinear24_ok; assumption).
  (* [comment removed for export] *)
  assert (PARSE : parseStringForNumbers_gq_cps RT) by (apply parseStringForNumbers_ok; assumption).
  assert (NSORT : numaSort_gq_cps RT) by (apply numaSort_gq_ok; assumption).
  assert (QTAB : makeGrayQuantTableArb_gq_cps RT) by (apply makeGrayQuantTableArb_gq_ok; assumption).
  assert (SETBW : pixcmapSetBlackAndWhite00_cps RT) by (apply pixcmapSetBlackAndWhite00_ok; assumption).
  (* [comment removed for export] *)
  assert (DBIN : pixDitherToBinary_cps RT) by (apply pixDitherToBinary_ok; assumption).
  assert (CMF : d2_cmfree_cps RT) by (apply d2_cmfree_ok; assumption).   (* [comment removed for export] *)
  assert (D2BPP : pixDitherTo2bpp_cps RT) by (apply pixDitherTo2bpp_ok; assumption).
  assert (THR : pixThresholdGrayArb_cps RT) by (apply pixThresholdGrayArb_ok; assumption).
  (* [comment removed for export] *)
  apply fuzz_one_ok; assumption.
Qed.
End TOP.
