(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_gaps_iface Lept_iface Ed_iface Ed_ext_defs Ed_ext_pre_c0 Ed_ext_pre_c16 Ed_ext_main.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section EXT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.
Hypothesis NCR : numaCreate_cps RT.
Hypothesis NAF : numaAddNumber_fast_cps RT.
Hypothesis NA : numaAddNumber_cps RT.

Theorem numaFindExtrema_ok : numaFindExtrema_cps RT.
Proof using AF GP EG NCR NAF NA.
  exact (ext_cases RT (ext_pre_c0 RT AF GP EG NCR (ext_rest_ok RT AF GP NAF NA)) (ext_pre_c16 RT AF GP EG NCR (ext_rest_ok RT AF GP NAF NA))).
Qed.
End EXT.
