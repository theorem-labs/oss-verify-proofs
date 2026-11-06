(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_gaps_iface Lept_iface
  Lept_stderr Lept_err Lept_hdr Lept_create LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_setcmap LeptM_destroy LeptC_padbits
  Lept_zero Lept_gmax Lept_deser.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Gm_iface Gm_strrepl Gm_destroy_null Gm_hdr_sure Gm_noinit Gm_cmapvalid Gm_cmapcopy
  Gm_copycmap Gm_copyres Gm_copyspp Gm_tmplnoinit Gm_template Gm_pixcopy Gm_erode3 Gm_dilate3 Gm_open3 Gm_close3 Gm_fuzz.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Gm_e3h Gm_d3h Gm_e3h_null Gm_d3h_null Gm_addb Gm_rmb Gm_rmb_null.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Gm_roplow Gm_uni Gm_rasterop Gm_sbv Gm_sbv_null.

Theorem gm_fuzz_top : forall RT, rt_contracts RT -> rt_gaps RT -> gm_gaps RT -> Lept_iface.fuzz_one_cps RT.
Proof.
  intros RT RC GP GM.
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
  assert (ROPL : rasteropLow_cps RT) by (apply Gm_roplow.rasteropLow_ok; assumption).
  assert (ROPU : rasteropUniLow_cps RT) by (apply Gm_uni.rasteropUniLow_ok; assumption).
  assert (RUNI : pixRasterop_uni_cps RT) by (apply Gm_rasterop.pixRasterop_uni_ok; assumption).
  assert (RSRC : pixRasterop_src_cps RT) by (apply Gm_rasterop.pixRasterop_src_ok; assumption).
  assert (SBV : pixSetBorderVal_cps RT) by (apply Gm_sbv.pixSetBorderVal_ok; assumption).
  assert (SBVN : gm_null_cps RT e_pixSetBorderVal) by (apply Gm_sbv_null.pixSetBorderVal_null_ok; assumption).
  (* [comment removed for export] *)
  assert (E3H : gray3h_cps RT e_pixErodeGray3h) by (apply Gm_e3h.pixErodeGray3h_ok; assumption).
  assert (D3H : gray3h_cps RT e_pixDilateGray3h) by (apply Gm_d3h.pixDilateGray3h_ok; assumption).
  assert (E3HN : gm_null_cps RT e_pixErodeGray3h) by (apply Gm_e3h_null.pixErodeGray3h_null_ok; assumption).
  assert (D3HN : gm_null_cps RT e_pixDilateGray3h) by (apply Gm_d3h_null.pixDilateGray3h_null_ok; assumption).
  assert (ADDB : pixAddBorderGeneral_cps RT) by (apply Gm_addb.pixAddBorderGeneral_ok; assumption).
  assert (RMB : pixRemoveBorderGeneral_cps RT) by (apply Gm_rmb.pixRemoveBorderGeneral_ok; assumption).
  assert (RMBN : gm_null_cps RT e_pixRemoveBorderGeneral) by (apply Gm_rmb_null.pixRemoveBorderGeneral_null_ok; assumption).
  (* [comment removed for export] *)
  assert (GERODE : gray3_cps RT e_pixErodeGray3) by (apply pixErodeGray3_ok; assumption).
  assert (GDILATE : gray3_cps RT e_pixDilateGray3) by (apply pixDilateGray3_ok; assumption).
  assert (GOPEN : gray3_cps RT e_pixOpenGray3) by (apply pixOpenGray3_ok; assumption).
  assert (GCLOSE : gray3_cps RT e_pixCloseGray3) by (apply pixCloseGray3_ok; assumption).
  apply fuzz_one_ok; assumption.
Qed.
