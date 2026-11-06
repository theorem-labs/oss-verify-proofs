(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_gaps_iface D_iface D_defs D_libiface Lept_iface
  Lept_stderr Lept_err Lept_hdr Lept_create LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_setcmap LeptM_destroy LeptC_padbits
  Lept_zero Lept_gmax Lept_deser.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Ed_iface Ed_numa_destroy Ed_ext_closed Px_prof Ed_meas Ed_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section TOP.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.
Theorem ed_fuzz_top : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof using RC GP EG.
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
  assert (NDESTROY : numaDestroy_cps RT) by (apply numaDestroy_ok; assumption).
  assert (EXTREMA : numaFindExtrema_cps RT) by (apply numaFindExtrema_closed; assumption).
  assert (PROFILE : pixGetEdgeProfile_cps RT) by (apply pixGetEdgeProfile_ok; assumption).
  assert (MEASURE : pixMeasureEdgeSmoothness_cps RT) by (apply pixMeasureEdgeSmoothness_ok; assumption).
  (* [comment removed for export] *)
  apply fuzz_one_ok; assumption.
Qed.
End TOP.
