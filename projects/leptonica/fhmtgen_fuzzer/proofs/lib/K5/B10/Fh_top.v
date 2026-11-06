(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_gaps_iface D_iface D_defs D_libiface Lept_iface
  Lept_stderr Lept_err Lept_hdr Lept_create LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_setcmap LeptM_destroy LeptC_padbits
  Lept_zero Lept_gmax Lept_deser.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Gm_iface Gm_strrepl Gm_destroy_null Gm_hdr_sure Gm_noinit Gm_cmapvalid Gm_cmapcopy
  Gm_copycmap Gm_copyres Gm_copyspp Gm_tmplnoinit Gm_template Gm_pixcopy.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Fh_iface Fh_sel_iface Fh_rasterop1_top Fh_rmb1 Fh_rmborder_null Fh_addb1 Fh_addb1_wrap
  Fh_low Fh_gen Fh_gen_null Fh_hmt.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Fh_string Fh_selacreate Fh_selset Fh_selcreate Fh_brick Fh_seladd Fh_hm
  Fh_seldestroy Fh_seladestroy Fh_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section TOP.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GM : gm_gaps RT.
Hypothesis FH : fh_gaps RT.
Theorem fh_fuzz_top : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof using RC GP GM FH.
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
  assert (DESER : pixDeserialize_cps RT) by (apply pixDeserialize_ok; assumption).
  (* [comment removed for export] *)
  assert (SRN : stringReplace_null_cps RT) by (apply stringReplace_null_ok; assumption).
  assert (DNULL : pixDestroy_null_cps RT) by (apply pixDestroy_null_ok; assumption).
  assert (HDRS : pixCreateHeader_sure_cps RT) by (apply pixCreateHeader_sure_ok; assumption).
  assert (NIS : pixCreateNoInit_sure_cps RT) by (apply pixCreateNoInit_sure_ok; assumption).
  assert (IVN : pixcmapIsValid_null_cps RT) by (apply pixcmapIsValid_null_ok; assumption).
  assert (CMC : pixcmapCopy_cps RT) by (apply pixcmapCopy_ok; assumption).
  assert (CCM : pixCopyColormap_cps RT) by (apply pixCopyColormap_ok; assumption).
  assert (CRES : pixCopyResolution_cps RT) by (apply pixCopyResolution_ok; assumption).
  assert (CSPP : pixCopySpp_cps RT) by (apply pixCopySpp_ok; assumption).
  assert (TNI : pixCreateTemplateNoInit_cps RT) by (apply pixCreateTemplateNoInit_ok; assumption).
  assert (TPL : pixCreateTemplate_cps RT) by (apply pixCreateTemplate_ok; assumption).
  assert (PCOPY : pixCopy_cps RT) by (apply pixCopy_ok; assumption).
  (* [comment removed for export] *)
  assert (RCLR : pixRasterop_clr1_cps RT) by (apply pixRasterop_clr1_ok; assumption).
  assert (RSRC : pixRasterop_src1_cps RT) by (apply pixRasterop_src1_ok; assumption).
  (* [comment removed for export] *)
  assert (RMBG : pixRemoveBorder1_cps RT e_pixRemoveBorderGeneral) by (apply pixRemoveBorderGeneral1_ok; assumption).
  assert (RMB : pixRemoveBorder1_cps RT e_pixRemoveBorder) by (apply pixRemoveBorder1_ok; assumption).
  assert (RMNULL : fh_null_cps RT e_pixRemoveBorder) by (apply pixRemoveBorder_null_ok; assumption).
  assert (ADDBG : pixAddBorder1_cps RT e_pixAddBorderGeneral) by (apply pixAddBorderGeneral1_ok; assumption).
  assert (ADDB : pixAddBorder1_cps RT e_pixAddBorder) by (apply pixAddBorder1_of_general; assumption).
  (* [comment removed for export] *)
  assert (LOW : fhmtgen_low_1_cps RT) by (apply fhmtgen_low_1_ok; assumption).
  assert (GEN : pixFHMTGen_1_cps RT) by (apply pixFHMTGen_1_ok; assumption).
  assert (GENNULL : fh_null_cps RT e_pixFHMTGen_1) by (apply pixFHMTGen_1_null_ok; assumption).
  assert (HMT : pixHMTDwa_1_cps RT) by (apply pixHMTDwa_1_ok; assumption).
  (* [comment removed for export] *)
  assert (SN : stringNew_cps RT) by (apply stringNew_ok; assumption).
  assert (CRT : selaCreate_cps RT) by (apply selaCreate_ok; assumption).
  assert (SET : selSetElement_cps RT) by (apply selSetElement_ok; assumption).
  assert (SCR : selCreate_cps RT) by (apply selCreate_ok; assumption).
  assert (BRK : selCreateBrick_cps RT) by (apply selCreateBrick_ok; assumption).
  assert (ADD : selaAddSel_cps RT) by (apply selaAddSel_ok; assumption).
  assert (SAHM : selaAddHitMiss_cps RT) by (apply selaAddHitMiss_ok; assumption).
  assert (SDS : selDestroy_cps RT) by (apply selDestroy_ok; assumption).
  assert (SAD : selaDestroy_cps RT) by (apply selaDestroy_ok; assumption).
  (* [comment removed for export] *)
  apply fuzz_one_ok; assumption.
Qed.
End TOP.
