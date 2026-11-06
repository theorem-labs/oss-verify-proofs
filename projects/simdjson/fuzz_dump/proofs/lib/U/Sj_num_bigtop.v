(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_weak Sj_num_memmove Sj_num_shl Sj_num_memmoveN Sj_num_shlN Sj_num_lafN Sj_num_lmN
  Sj_num_pow5N Sj_num_hi64 Sj_num_pdc Sj_num_ndc Sj_num_pm_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BIGTOP.
  Hypothesis HCPY : memcpyZ_stmt_g usegs 0xcb544.
  Hypothesis HSET : memsetZ_stmt_g usegs 0xcbac4.

  Lemma big_lmuN : lmuN_stmt_g usegs 0x59a14.
  Proof using HCPY. exact (lmuN_spec HCPY lafuN_spec). Qed.
  Lemma big_p5uN : p5uN_stmt_g usegs 0x5981c NUMU_GTOP.
  Proof using HCPY. exact (p5uN_spec big_lmuN). Qed.
  Lemma big_shluN : shluN_stmt_g usegs 0x59f38.
  Proof using HCPY. exact (shluN_spec (memmoveN_spec HCPY)). Qed.

  Theorem big_pdcu : pdcu_stmt_g usegs 0x590f8 NUMU_GTOP.
  Proof using HCPY. exact (pdcu_spec big_p5uN big_shluN hi64u_spec). Qed.
  Theorem big_ndcu : ndcu_stmt_g usegs 0x592cc NUMU_GTOP.
  Proof using HCPY HSET. exact (ndcu_spec (p5uN_weak _ _ _ big_p5uN) (shlu_spec (memmove_spec HCPY)) HSET). Qed.
  Theorem big_pmu : pmu_stmt_g usegs 0x5815c NUMU_GTOP.
  Proof using. exact pmu_spec. Qed.
End BIGTOP.
