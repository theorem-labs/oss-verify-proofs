(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_gaps_iface Lept_iface Gq_numa Gq_gaps Gq_iface Gq_thr_iface
  Gq_parse_kit Gq_parse_defs Gq_parse_case Gq_str_new Gq_str_tok0 Gq_str_tok1 Gq_str_tok2 Gq_str_tok3 Gq_str_tokend Gq_parse_c0 Gq_parse_c16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PARSE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GG : gq_gaps RT.
Hypothesis NUMAC : numaCreate_cps RT.
Hypothesis NADDF : numaAddNumber_fast_cps RT.

Theorem parseStringForNumbers_ok : parseStringForNumbers_gq_cps RT.
Proof using AF RC GP GG NUMAC NADDF.
  apply parse_of_cases.
  - exact (parse_c0 RT AF GP RC GG NUMAC NADDF (stringNew_lit_ok RT AF RC GP)
             (strtokSafe_0_ok RT AF GP GG) (strtokSafe_1_ok RT AF GP GG) (strtokSafe_2_ok RT AF GP GG) (strtokSafe_3_ok RT AF GP GG)
             (strtokSafe_end_ok RT AF GP)).
  - exact (parse_c16 RT AF GP RC GG NUMAC NADDF (stringNew_lit_ok RT AF RC GP)
             (strtokSafe_0_ok RT AF GP GG) (strtokSafe_1_ok RT AF GP GG) (strtokSafe_2_ok RT AF GP GG) (strtokSafe_3_ok RT AF GP GG)
             (strtokSafe_end_ok RT AF GP)).
Qed.
End PARSE.
