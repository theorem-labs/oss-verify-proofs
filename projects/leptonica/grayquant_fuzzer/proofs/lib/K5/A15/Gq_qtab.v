(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_gaps_iface Lept_iface Gq_numa Gq_gaps Gq_iface Gq_thr_iface Gq_thr2_iface
  Gq_qtab_defs Gq_qtab_addcolor Gq_qtab_create Gq_qtab_case Gq_qtab_c0 Gq_qtab_c16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section QTAB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem makeGrayQuantTableArb_gq_ok : makeGrayQuantTableArb_gq_cps RT.
Proof using AF GP.
  apply qtab_of_cases.
  - exact (qtab_c0 RT AF GP (pixcmapCreate8_ok RT AF GP) (pixcmapAddColor_gray_ok RT AF GP)).
  - exact (qtab_c16 RT AF GP (pixcmapCreate8_ok RT AF GP) (pixcmapAddColor_gray_ok RT AF GP)).
Qed.
End QTAB.
