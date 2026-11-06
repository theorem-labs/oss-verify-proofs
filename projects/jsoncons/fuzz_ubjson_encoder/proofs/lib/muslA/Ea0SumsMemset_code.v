(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export Ea0_code_rcb2e4_cbd08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x12b88c%Z.
Definition Fo_000 := F_12b848.
Definition Do_000 := D_12b848.
Definition Fo_004 := F_12b84c.
Definition Do_004 := D_12b84c.
Definition Fo_008 := F_12b850.
Definition Do_008 := D_12b850.
Definition Fo_00c := F_12b854.
Definition Do_00c := D_12b854.
Definition Fo_010 := F_12b858.
Definition Do_010 := D_12b858.
Definition Fo_014 := F_12b85c.
Definition Do_014 := D_12b85c.
Definition Fo_018 := F_12b860.
Definition Do_018 := D_12b860.
Definition Fo_01c := F_12b864.
Definition Do_01c := D_12b864.
Definition Fo_020 := F_12b868.
Definition Do_020 := D_12b868.
Definition Fo_024 := F_12b86c.
Definition Do_024 := D_12b86c.
Definition Fo_028 := F_12b870.
Definition Do_028 := D_12b870.
Definition Fo_02c := F_12b874.
Definition Do_02c := D_12b874.
Definition Fo_030 := F_12b878.
Definition Do_030 := D_12b878.
Definition Fo_034 := F_12b87c.
Definition Do_034 := D_12b87c.
Definition Fo_038 := F_12b880.
Definition Do_038 := D_12b880.
Definition Fo_03c := F_12b884.
Definition Do_03c := D_12b884.
Definition Fo_040 := F_12b888.
Definition Do_040 := D_12b888.
Definition Fo_044 := F_12b88c.
Definition Do_044 := D_12b88c.
Definition Fo_048 := F_12b890.
Definition Do_048 := D_12b890.
Definition Fo_04c := F_12b894.
Definition Do_04c := D_12b894.
Definition Fo_050 := F_12b898.
Definition Do_050 := D_12b898.
Definition Fo_054 := F_12b89c.
Definition Do_054 := D_12b89c.
Definition Fo_058 := F_12b8a0.
Definition Do_058 := D_12b8a0.
Definition Fo_05c := F_12b8a4.
Definition Do_05c := D_12b8a4.
Definition Fo_060 := F_12b8a8.
Definition Do_060 := D_12b8a8.
Definition Fo_064 := F_12b8ac.
Definition Do_064 := D_12b8ac.
Definition Fo_068 := F_12b8b0.
Definition Do_068 := D_12b8b0.
Definition Fo_06c := F_12b8b4.
Definition Do_06c := D_12b8b4.
Definition Fo_070 := F_12b8b8.
Definition Do_070 := D_12b8b8.
Definition Fo_074 := F_12b8bc.
Definition Do_074 := D_12b8bc.
Definition Fo_078 := F_12b8c0.
Definition Do_078 := D_12b8c0.
Definition Fo_07c := F_12b8c4.
Definition Do_07c := D_12b8c4.
Definition Fo_080 := F_12b8c8.
Definition Do_080 := D_12b8c8.
Definition Fo_084 := F_12b8cc.
Definition Do_084 := D_12b8cc.
Definition Fo_088 := F_12b8d0.
Definition Do_088 := D_12b8d0.
Definition Fo_08c := F_12b8d4.
Definition Do_08c := D_12b8d4.
Definition Fo_090 := F_12b8d8.
Definition Do_090 := D_12b8d8.
Definition Fo_094 := F_12b8dc.
Definition Do_094 := D_12b8dc.
Definition Fo_098 := F_12b8e0.
Definition Do_098 := D_12b8e0.
Definition Fo_09c := F_12b8e4.
Definition Do_09c := D_12b8e4.
Definition Fo_0a0 := F_12b8e8.
Definition Do_0a0 := D_12b8e8.
Definition Fo_0a4 := F_12b8ec.
Definition Do_0a4 := D_12b8ec.
Definition Fo_0a8 := F_12b8f0.
Definition Do_0a8 := D_12b8f0.
Definition Fo_0ac := F_12b8f4.
Definition Do_0ac := D_12b8f4.
Definition Fo_0b0 := F_12b8f8.
Definition Do_0b0 := D_12b8f8.
Definition Fo_0b4 := F_12b8fc.
Definition Do_0b4 := D_12b8fc.
Definition Fo_0b8 := F_12b900.
Definition Do_0b8 := D_12b900.
Definition Fo_0bc := F_12b904.
Definition Do_0bc := D_12b904.
Definition Fo_0c0 := F_12b908.
Definition Do_0c0 := D_12b908.
Definition Fo_0c4 := F_12b90c.
Definition Do_0c4 := D_12b90c.
Definition Fo_0c8 := F_12b910.
Definition Do_0c8 := D_12b910.
Definition Fo_0cc := F_12b914.
Definition Do_0cc := D_12b914.
Definition Fo_0d0 := F_12b918.
Definition Do_0d0 := D_12b918.
Definition Fo_0d4 := F_12b91c.
Definition Do_0d4 := D_12b91c.
Definition Fo_0d8 := F_12b920.
Definition Do_0d8 := D_12b920.
Definition Fo_0dc := F_12b924.
Definition Do_0dc := D_12b924.
Definition Fo_0e0 := F_12b928.
Definition Do_0e0 := D_12b928.
Definition Fo_0e4 := F_12b92c.
Definition Do_0e4 := D_12b92c.
Definition Fo_0e8 := F_12b930.
Definition Do_0e8 := D_12b930.
Definition Fo_0ec := F_12b934.
Definition Do_0ec := D_12b934.
Definition Fo_0f0 := F_12b938.
Definition Do_0f0 := D_12b938.
Definition Fo_0f4 := F_12b93c.
Definition Do_0f4 := D_12b93c.
