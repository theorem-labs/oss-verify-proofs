(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_iface Sj_num_lm_defs Sj_num_lm_top Sj_num_pow5 Sj_num_memmove
  Sj_num_pm_defs Sj_num_pm_top Sj_num_pdc Sj_num_ndc Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_int Sj_num_ff_defs Sj_num_ff_top Sj_num_wrap Sj_num_wrap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NUMTOP.
  Hypothesis HCPY : memcpyZ_stmt_g psegs 0x71c40.
  Hypothesis HSET : memsetZ_stmt_g psegs 0x721c0.

  Lemma num_lm : lm_stmt_g psegs 0x3cbb0.
  Proof using HCPY HSET. exact (lm_spec HCPY HSET). Qed.
  Lemma num_p5 : p5_stmt_g psegs 0x3ca54 0xab000.
  Proof using HCPY HSET. exact (p5_spec num_lm). Qed.
  Lemma num_memmove : memmove_stmt_g psegs 0x72044.
  Proof using HCPY. exact (memmove_spec HCPY). Qed.
  Lemma num_pm : pm_stmt_g psegs 0x3b630 0xab000.
  Proof. exact pm_spec. Qed.
  Lemma num_pdc : pdc_stmt_g psegs 0x3c324 0xab000.
  Proof using HCPY HSET. exact (pdc_spec num_p5 num_memmove HSET). Qed.
  Lemma num_ndc : ndc_stmt_g psegs 0x3c688 0xab000.
  Proof using HCPY HSET. exact (ndc_spec num_p5 num_memmove HSET). Qed.
  Lemma num_spath : spath_stmt_g psegs 0x3a1d0 0xab000.
  Proof using HCPY HSET. exact (sp_spec HSET num_pm num_pdc num_ndc). Qed.
  Lemma num_ff : ff_stmt_g psegs 0x28d4c 0xab000.
  Proof using HCPY HSET. exact (ff_spec num_spath). Qed.

  Theorem num_slowf : slowf_stmt_g psegs 0x3cf38 0xab000.
  Proof using HCPY HSET. exact (slowf_spec num_ff). Qed.

  Theorem num_pff : pff_stmt_g psegs 0x3cfc0 0xab000.
  Proof using HCPY HSET. exact (pff_spec num_ff). Qed.
End NUMTOP.

Print Assumptions num_slowf.
Print Assumptions num_pff.
