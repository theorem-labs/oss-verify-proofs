(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zsl Zsr Zsp Zqg Zve Zvd Zvi
  Zsf Zsj Zvp Zvq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NUMUTOP.
  Hypothesis HCPY : memcpyZ_stmt_g usegs 0x7c3dc.
  Hypothesis HSET : memsetZ_stmt_g usegs 0x7c95c.

  Lemma numu_spath : spathu_stmt_g usegs 0x43978 NUMU_GTOP.
  Proof using HCPY HSET. exact (spathu_spec HSET big_pmu (big_pdcu HCPY) (big_ndcu HCPY HSET)). Qed.
  Lemma numu_ff : ffu_stmt_g usegs 0x291c0 NUMU_GTOP.
  Proof using HCPY HSET. exact (ffu_spec numu_spath). Qed.

  Theorem numu_slowf : slowfu_stmt_g usegs 0x47214 0xb5000.
  Proof using HCPY HSET. exact (slowfu_spec numu_ff). Qed.

  Theorem numu_pff : pffu_stmt_g usegs 0x472c4 0xb5000.
  Proof using HCPY HSET. exact (pffu_spec numu_ff). Qed.
End NUMUTOP.

