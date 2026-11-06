(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Gq_iface Gq_destroy_rc_defs Gq_destroy_rc_c0 Gq_destroy_rc_c16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixDestroy_rc_ok : pixDestroy_rc_cps RT.
Proof using AF GP.
  apply pixDestroy_rc_of_cases.
  - exact (Gq_destroy_rc_c0.pixDestroy_rc_case_ok RT AF GP).
  - exact (Gq_destroy_rc_c16.pixDestroy_rc_case_ok RT AF GP).
Qed.
End RC.
