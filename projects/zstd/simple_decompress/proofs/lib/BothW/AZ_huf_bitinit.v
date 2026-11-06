(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg AZ_huf_iface AZ_huf_bitinit1 AZ_huf_bitinit2 AZ_huf_bitinit3.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem bit_init_proofA : bit_init_stmtA.
Proof.
  unfold bit_init_stmtA, bit_init_stmtA_at, APHUF_BITINIT.
  intros until junk. intros.
  destruct (Z_lt_le_dec n 2) as [L|L]; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec 7 n) as [L'|L']; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec n 5) as [L''|L'']; [eapply sbi_mid; try eassumption; lia|].
  eapply sbi_hi; try eassumption; lia.
Qed.
End CANSEC1.
