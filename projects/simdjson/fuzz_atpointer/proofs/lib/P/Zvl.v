(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso Zsl Zt3 Ztf Zuz Ztj
  Zu5 Zut Zu2 Zu1 Zve Zvd Zvi Zsf Zsj Zvp Zvq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NUMTOP.
  Hypothesis HCPY : memcpyZ_stmt_g psegs 0x71d00.
  Hypothesis HSET : memsetZ_stmt_g psegs 0x72280.

  Lemma num_lm : lm_stmt_g psegs 0x3c800.
  Proof using HCPY HSET. exact (lm_spec HCPY HSET). Qed.
  Lemma num_p5 : p5_stmt_g psegs 0x3c6a4 0xab000.
  Proof using HCPY HSET. exact (p5_spec num_lm). Qed.
  Lemma num_memmove : memmove_stmt_g psegs 0x72104.
  Proof using HCPY. exact (memmove_spec HCPY). Qed.
  Lemma num_pm : pm_stmt_g psegs 0x3b280 0xab000.
  Proof. exact pm_spec. Qed.
  Lemma num_pdc : pdc_stmt_g psegs 0x3bf74 0xab000.
  Proof using HCPY HSET. exact (pdc_spec num_p5 num_memmove HSET). Qed.
  Lemma num_ndc : ndc_stmt_g psegs 0x3c2d8 0xab000.
  Proof using HCPY HSET. exact (ndc_spec num_p5 num_memmove HSET). Qed.
  Lemma num_spath : spath_stmt_g psegs 0x39e20 0xab000.
  Proof using HCPY HSET. exact (sp_spec HSET num_pm num_pdc num_ndc). Qed.
  Lemma num_ff : ff_stmt_g psegs 0x2899c 0xab000.
  Proof using HCPY HSET. exact (ff_spec num_spath). Qed.

  Theorem num_slowf : slowf_stmt_g psegs 0x3cb88 0xab000.
  Proof using HCPY HSET. exact (slowf_spec num_ff). Qed.

  Theorem num_pff : pff_stmt_g psegs 0x3cc10 0xab000.
  Proof using HCPY HSET. exact (pff_spec num_ff). Qed.
End NUMTOP.

Print Assumptions num_slowf.
Print Assumptions num_pff.
