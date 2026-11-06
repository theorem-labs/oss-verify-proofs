(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Export Bo0_code_cc240_ccc64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xcc740%Z.
Definition Fo_000 := F_cc740.
Definition Do_000 := D_cc740.
Definition Fo_004 := F_cc744.
Definition Do_004 := D_cc744.
Definition Fo_008 := F_cc748.
Definition Do_008 := D_cc748.
Definition Fo_00c := F_cc74c.
Definition Do_00c := D_cc74c.
Definition Fo_010 := F_cc750.
Definition Do_010 := D_cc750.
Definition Fo_014 := F_cc754.
Definition Do_014 := D_cc754.
Definition Fo_018 := F_cc758.
Definition Do_018 := D_cc758.
Definition Fo_01c := F_cc75c.
Definition Do_01c := D_cc75c.
Definition Fo_020 := F_cc760.
Definition Do_020 := D_cc760.
Definition Fo_024 := F_cc764.
Definition Do_024 := D_cc764.
Definition Fo_028 := F_cc768.
Definition Do_028 := D_cc768.
Definition Fo_02c := F_cc76c.
Definition Do_02c := D_cc76c.
Definition Fo_030 := F_cc770.
Definition Do_030 := D_cc770.
Definition Fo_034 := F_cc774.
Definition Do_034 := D_cc774.
Definition Fo_038 := F_cc778.
Definition Do_038 := D_cc778.
Definition Fo_03c := F_cc77c.
Definition Do_03c := D_cc77c.
Definition Fo_040 := F_cc780.
Definition Do_040 := D_cc780.
Definition Fo_044 := F_cc784.
Definition Do_044 := D_cc784.
Definition Fo_048 := F_cc788.
Definition Do_048 := D_cc788.
Definition Fo_04c := F_cc78c.
Definition Do_04c := D_cc78c.
Definition Fo_050 := F_cc790.
Definition Do_050 := D_cc790.
Definition Fo_054 := F_cc794.
Definition Do_054 := D_cc794.
Definition Fo_058 := F_cc798.
Definition Do_058 := D_cc798.
Definition Fo_05c := F_cc79c.
Definition Do_05c := D_cc79c.
Definition Fo_060 := F_cc7a0.
Definition Do_060 := D_cc7a0.
Definition Fo_064 := F_cc7a4.
Definition Do_064 := D_cc7a4.
Definition Fo_068 := F_cc7a8.
Definition Do_068 := D_cc7a8.
Definition Fo_06c := F_cc7ac.
Definition Do_06c := D_cc7ac.
Definition Fo_070 := F_cc7b0.
Definition Do_070 := D_cc7b0.
Definition Fo_074 := F_cc7b4.
Definition Do_074 := D_cc7b4.
Definition Fo_078 := F_cc7b8.
Definition Do_078 := D_cc7b8.
Definition Fo_07c := F_cc7bc.
Definition Do_07c := D_cc7bc.
Definition Fo_080 := F_cc7c0.
Definition Do_080 := D_cc7c0.
Definition Fo_084 := F_cc7c4.
Definition Do_084 := D_cc7c4.
Definition Fo_088 := F_cc7c8.
Definition Do_088 := D_cc7c8.
Definition Fo_08c := F_cc7cc.
Definition Do_08c := D_cc7cc.
Definition Fo_090 := F_cc7d0.
Definition Do_090 := D_cc7d0.
Definition Fo_094 := F_cc7d4.
Definition Do_094 := D_cc7d4.
Definition Fo_098 := F_cc7d8.
Definition Do_098 := D_cc7d8.
Definition Fo_09c := F_cc7dc.
Definition Do_09c := D_cc7dc.
Definition Fo_0a0 := F_cc7e0.
Definition Do_0a0 := D_cc7e0.
Definition Fo_0a4 := F_cc7e4.
Definition Do_0a4 := D_cc7e4.
Definition Fo_0a8 := F_cc7e8.
Definition Do_0a8 := D_cc7e8.
Definition Fo_0ac := F_cc7ec.
Definition Do_0ac := D_cc7ec.
Definition Fo_0b0 := F_cc7f0.
Definition Do_0b0 := D_cc7f0.
Definition Fo_0b4 := F_cc7f4.
Definition Do_0b4 := D_cc7f4.
Definition Fo_0b8 := F_cc7f8.
Definition Do_0b8 := D_cc7f8.
Definition Fo_0bc := F_cc7fc.
Definition Do_0bc := D_cc7fc.
Definition Fo_0c0 := F_cc800.
Definition Do_0c0 := D_cc800.
Definition Fo_0c4 := F_cc804.
Definition Do_0c4 := D_cc804.
Definition Fo_0c8 := F_cc808.
Definition Do_0c8 := D_cc808.
Definition Fo_0cc := F_cc80c.
Definition Do_0cc := D_cc80c.
Definition Fo_0d0 := F_cc810.
Definition Do_0d0 := D_cc810.
Definition Fo_0d4 := F_cc814.
Definition Do_0d4 := D_cc814.
Definition Fo_0d8 := F_cc818.
Definition Do_0d8 := D_cc818.
Definition Fo_0dc := F_cc81c.
Definition Do_0dc := D_cc81c.
Definition Fo_0e0 := F_cc820.
Definition Do_0e0 := D_cc820.
Definition Fo_0e4 := F_cc824.
Definition Do_0e4 := D_cc824.
Definition Fo_0e8 := F_cc828.
Definition Do_0e8 := D_cc828.
Definition Fo_0ec := F_cc82c.
Definition Do_0ec := D_cc82c.
Definition Fo_0f0 := F_cc830.
Definition Do_0f0 := D_cc830.
Definition Fo_0f4 := F_cc834.
Definition Do_0f4 := D_cc834.
