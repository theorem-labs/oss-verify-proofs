(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Export As0_code_cb62c_cc050.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xcbb2c%Z.
Definition Fo_000 := F_cbb2c.
Definition Do_000 := D_cbb2c.
Definition Fo_004 := F_cbb30.
Definition Do_004 := D_cbb30.
Definition Fo_008 := F_cbb34.
Definition Do_008 := D_cbb34.
Definition Fo_00c := F_cbb38.
Definition Do_00c := D_cbb38.
Definition Fo_010 := F_cbb3c.
Definition Do_010 := D_cbb3c.
Definition Fo_014 := F_cbb40.
Definition Do_014 := D_cbb40.
Definition Fo_018 := F_cbb44.
Definition Do_018 := D_cbb44.
Definition Fo_01c := F_cbb48.
Definition Do_01c := D_cbb48.
Definition Fo_020 := F_cbb4c.
Definition Do_020 := D_cbb4c.
Definition Fo_024 := F_cbb50.
Definition Do_024 := D_cbb50.
Definition Fo_028 := F_cbb54.
Definition Do_028 := D_cbb54.
Definition Fo_02c := F_cbb58.
Definition Do_02c := D_cbb58.
Definition Fo_030 := F_cbb5c.
Definition Do_030 := D_cbb5c.
Definition Fo_034 := F_cbb60.
Definition Do_034 := D_cbb60.
Definition Fo_038 := F_cbb64.
Definition Do_038 := D_cbb64.
Definition Fo_03c := F_cbb68.
Definition Do_03c := D_cbb68.
Definition Fo_040 := F_cbb6c.
Definition Do_040 := D_cbb6c.
Definition Fo_044 := F_cbb70.
Definition Do_044 := D_cbb70.
Definition Fo_048 := F_cbb74.
Definition Do_048 := D_cbb74.
Definition Fo_04c := F_cbb78.
Definition Do_04c := D_cbb78.
Definition Fo_050 := F_cbb7c.
Definition Do_050 := D_cbb7c.
Definition Fo_054 := F_cbb80.
Definition Do_054 := D_cbb80.
Definition Fo_058 := F_cbb84.
Definition Do_058 := D_cbb84.
Definition Fo_05c := F_cbb88.
Definition Do_05c := D_cbb88.
Definition Fo_060 := F_cbb8c.
Definition Do_060 := D_cbb8c.
Definition Fo_064 := F_cbb90.
Definition Do_064 := D_cbb90.
Definition Fo_068 := F_cbb94.
Definition Do_068 := D_cbb94.
Definition Fo_06c := F_cbb98.
Definition Do_06c := D_cbb98.
Definition Fo_070 := F_cbb9c.
Definition Do_070 := D_cbb9c.
Definition Fo_074 := F_cbba0.
Definition Do_074 := D_cbba0.
Definition Fo_078 := F_cbba4.
Definition Do_078 := D_cbba4.
Definition Fo_07c := F_cbba8.
Definition Do_07c := D_cbba8.
Definition Fo_080 := F_cbbac.
Definition Do_080 := D_cbbac.
Definition Fo_084 := F_cbbb0.
Definition Do_084 := D_cbbb0.
Definition Fo_088 := F_cbbb4.
Definition Do_088 := D_cbbb4.
Definition Fo_08c := F_cbbb8.
Definition Do_08c := D_cbbb8.
Definition Fo_090 := F_cbbbc.
Definition Do_090 := D_cbbbc.
Definition Fo_094 := F_cbbc0.
Definition Do_094 := D_cbbc0.
Definition Fo_098 := F_cbbc4.
Definition Do_098 := D_cbbc4.
Definition Fo_09c := F_cbbc8.
Definition Do_09c := D_cbbc8.
Definition Fo_0a0 := F_cbbcc.
Definition Do_0a0 := D_cbbcc.
Definition Fo_0a4 := F_cbbd0.
Definition Do_0a4 := D_cbbd0.
Definition Fo_0a8 := F_cbbd4.
Definition Do_0a8 := D_cbbd4.
Definition Fo_0ac := F_cbbd8.
Definition Do_0ac := D_cbbd8.
Definition Fo_0b0 := F_cbbdc.
Definition Do_0b0 := D_cbbdc.
Definition Fo_0b4 := F_cbbe0.
Definition Do_0b4 := D_cbbe0.
Definition Fo_0b8 := F_cbbe4.
Definition Do_0b8 := D_cbbe4.
Definition Fo_0bc := F_cbbe8.
Definition Do_0bc := D_cbbe8.
Definition Fo_0c0 := F_cbbec.
Definition Do_0c0 := D_cbbec.
Definition Fo_0c4 := F_cbbf0.
Definition Do_0c4 := D_cbbf0.
Definition Fo_0c8 := F_cbbf4.
Definition Do_0c8 := D_cbbf4.
Definition Fo_0cc := F_cbbf8.
Definition Do_0cc := D_cbbf8.
Definition Fo_0d0 := F_cbbfc.
Definition Do_0d0 := D_cbbfc.
Definition Fo_0d4 := F_cbc00.
Definition Do_0d4 := D_cbc00.
Definition Fo_0d8 := F_cbc04.
Definition Do_0d8 := D_cbc04.
Definition Fo_0dc := F_cbc08.
Definition Do_0dc := D_cbc08.
Definition Fo_0e0 := F_cbc0c.
Definition Do_0e0 := D_cbc0c.
Definition Fo_0e4 := F_cbc10.
Definition Do_0e4 := D_cbc10.
Definition Fo_0e8 := F_cbc14.
Definition Do_0e8 := D_cbc14.
Definition Fo_0ec := F_cbc18.
Definition Do_0ec := D_cbc18.
Definition Fo_0f0 := F_cbc1c.
Definition Do_0f0 := D_cbc1c.
Definition Fo_0f4 := F_cbc20.
Definition Do_0f4 := D_cbc20.
