(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_num_iface Sj_num_kitu Sj_num_kitn Sj_num_bigtop Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_int
  Sj_num_ff_defs Sj_num_ff_top Sj_num_wrap Sj_num_wrap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NUMUTOP.
  Hypothesis HCPY : memcpyZ_stmt_g usegs 0xcb544.
  Hypothesis HSET : memsetZ_stmt_g usegs 0xcbac4.

  Lemma numu_spath : spathu_stmt_g usegs 0x56804 NUMU_GTOP.
  Proof using HCPY HSET. exact (spathu_spec HSET big_pmu (big_pdcu HCPY) (big_ndcu HCPY HSET)). Qed.
  Lemma numu_ff : ffu_stmt_g usegs 0x3c04c NUMU_GTOP.
  Proof using HCPY HSET. exact (ffu_spec numu_spath). Qed.

  Theorem numu_slowf : slowfu_stmt_g usegs 0x5a0a0 0x10b000.
  Proof using HCPY HSET. exact (slowfu_spec numu_ff). Qed.

  Theorem numu_pff : pffu_stmt_g usegs 0x5a150 0x10b000.
  Proof using HCPY HSET. exact (pffu_spec numu_ff). Qed.
End NUMUTOP.

