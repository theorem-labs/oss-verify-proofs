(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Pm_iface4 Pm_hdr2 Pm_strrepl Pm_noinit Pm_cmapvalid_stk Pm_cmapcopy Pm_addcolor Pm_tmpl Pm_copy.

Section PmTop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERRP : returnError_cps RT e_returnErrorPtr.
Hypothesis RERRI : returnError_cps RT e_returnErrorInt.
Hypothesis PAD : pixSetPadBits_cps RT.
Hypothesis CCM : pixCopyColormap_cps RT.

Theorem pixCreateNoInit_closed : pixCreateNoInit_nn_cps RT e_pixCreateNoInit PM_NOINIT_MALLOC.
Proof using AF GP PAD. exact (pixCreateNoInit_ok RT AF GP (pixCreateHeader_nn_ok RT AF GP) PAD). Qed.

Theorem pixcmapCopy_closed : pixcmapCopy_cps RT.
Proof using AF RC GP RERRP. exact (pixcmapCopy_ok RT AF RC GP (pixcmapIsValid_stk_ok RT AF GP) RERRP). Qed.

Theorem pixcmapAddColor_closed : pixcmapAddColor_cps RT.
Proof using AF GP RERRI. exact (pixcmapAddColor_ok RT AF GP RERRI). Qed.

Theorem pixCreateTemplateNoInit_closed : pixCreateTemplateNoInit_nn_cps RT.
Proof using AF GP PAD RERRI CCM.
  exact (pixCreateTemplateNoInit_ok RT AF GP pixCreateNoInit_closed CCM (stringReplace_null_ok RT AF GP) PAD RERRI).
Qed.

Theorem pixCopy_closed : pixCopy_nn_cps RT.
Proof using AF RC GP PAD RERRI CCM. exact (pixCopy_ok RT AF RC GP pixCreateTemplateNoInit_closed). Qed.
End PmTop.
