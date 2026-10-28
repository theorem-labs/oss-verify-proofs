(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_iface Sj_num_kitu Sj_num_kitn Sj_num_bigtop Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_int
  Sj_num_ff_defs Sj_num_ff_top Sj_num_wrap Sj_num_wrap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NUMUTOP.
  Hypothesis HCPY : memcpyZ_stmt_g usegs 0xd06e8.
  Hypothesis HSET : memsetZ_stmt_g usegs 0xd0c68.

  Lemma numu_spath : spathu_stmt_g usegs 0x5b558 NUMU_GTOP.
  Proof using HCPY HSET. exact (spathu_spec HSET big_pmu (big_pdcu HCPY) (big_ndcu HCPY HSET)). Qed.
  Lemma numu_ff : ffu_stmt_g usegs 0x40da0 NUMU_GTOP.
  Proof using HCPY HSET. exact (ffu_spec numu_spath). Qed.

  Theorem numu_slowf : slowfu_stmt_g usegs 0x5edf4 0x111000.
  Proof using HCPY HSET. exact (slowfu_spec numu_ff). Qed.

  Theorem numu_pff : pffu_stmt_g usegs 0x5eea4 0x111000.
  Proof using HCPY HSET. exact (pffu_spec numu_ff). Qed.
End NUMUTOP.

