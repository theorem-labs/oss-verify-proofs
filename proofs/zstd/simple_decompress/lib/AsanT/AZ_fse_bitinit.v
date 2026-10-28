(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AZ_huf_iface AZ_hft_iface AZ_fse_bitinit1 AZ_fse_bitinit2 AZ_fse_bitinit3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem fse_bit_init_proofA : bit_init_stmtA_at APFSE_BITINIT.
Proof.
  unfold bit_init_stmtA_at, APFSE_BITINIT.
  intros until junk. intros.
  destruct (Z_lt_le_dec n 2) as [L|L]; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec 7 n) as [L'|L']; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec n 5) as [L''|L'']; [eapply sbi_mid; try eassumption; lia|].
  eapply sbi_hi; try eassumption; lia.
Qed.
End CANSEC1.
