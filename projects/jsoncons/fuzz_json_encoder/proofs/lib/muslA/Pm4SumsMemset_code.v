(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Export Pm4_code_152000_153000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x152ea4%Z.
Definition Fo_000 := F_152e60.
Definition Do_000 := D_152e60.
Definition Fo_004 := F_152e64.
Definition Do_004 := D_152e64.
Definition Fo_008 := F_152e68.
Definition Do_008 := D_152e68.
Definition Fo_00c := F_152e6c.
Definition Do_00c := D_152e6c.
Definition Fo_010 := F_152e70.
Definition Do_010 := D_152e70.
Definition Fo_014 := F_152e74.
Definition Do_014 := D_152e74.
Definition Fo_018 := F_152e78.
Definition Do_018 := D_152e78.
Definition Fo_01c := F_152e7c.
Definition Do_01c := D_152e7c.
Definition Fo_020 := F_152e80.
Definition Do_020 := D_152e80.
Definition Fo_024 := F_152e84.
Definition Do_024 := D_152e84.
Definition Fo_028 := F_152e88.
Definition Do_028 := D_152e88.
Definition Fo_02c := F_152e8c.
Definition Do_02c := D_152e8c.
Definition Fo_030 := F_152e90.
Definition Do_030 := D_152e90.
Definition Fo_034 := F_152e94.
Definition Do_034 := D_152e94.
Definition Fo_038 := F_152e98.
Definition Do_038 := D_152e98.
Definition Fo_03c := F_152e9c.
Definition Do_03c := D_152e9c.
Definition Fo_040 := F_152ea0.
Definition Do_040 := D_152ea0.
Definition Fo_044 := F_152ea4.
Definition Do_044 := D_152ea4.
Definition Fo_048 := F_152ea8.
Definition Do_048 := D_152ea8.
Definition Fo_04c := F_152eac.
Definition Do_04c := D_152eac.
Definition Fo_050 := F_152eb0.
Definition Do_050 := D_152eb0.
Definition Fo_054 := F_152eb4.
Definition Do_054 := D_152eb4.
Definition Fo_058 := F_152eb8.
Definition Do_058 := D_152eb8.
Definition Fo_05c := F_152ebc.
Definition Do_05c := D_152ebc.
Definition Fo_060 := F_152ec0.
Definition Do_060 := D_152ec0.
Definition Fo_064 := F_152ec4.
Definition Do_064 := D_152ec4.
Definition Fo_068 := F_152ec8.
Definition Do_068 := D_152ec8.
Definition Fo_06c := F_152ecc.
Definition Do_06c := D_152ecc.
Definition Fo_070 := F_152ed0.
Definition Do_070 := D_152ed0.
Definition Fo_074 := F_152ed4.
Definition Do_074 := D_152ed4.
Definition Fo_078 := F_152ed8.
Definition Do_078 := D_152ed8.
Definition Fo_07c := F_152edc.
Definition Do_07c := D_152edc.
Definition Fo_080 := F_152ee0.
Definition Do_080 := D_152ee0.
Definition Fo_084 := F_152ee4.
Definition Do_084 := D_152ee4.
Definition Fo_088 := F_152ee8.
Definition Do_088 := D_152ee8.
Definition Fo_08c := F_152eec.
Definition Do_08c := D_152eec.
Definition Fo_090 := F_152ef0.
Definition Do_090 := D_152ef0.
Definition Fo_094 := F_152ef4.
Definition Do_094 := D_152ef4.
Definition Fo_098 := F_152ef8.
Definition Do_098 := D_152ef8.
Definition Fo_09c := F_152efc.
Definition Do_09c := D_152efc.
Definition Fo_0a0 := F_152f00.
Definition Do_0a0 := D_152f00.
Definition Fo_0a4 := F_152f04.
Definition Do_0a4 := D_152f04.
Definition Fo_0a8 := F_152f08.
Definition Do_0a8 := D_152f08.
Definition Fo_0ac := F_152f0c.
Definition Do_0ac := D_152f0c.
Definition Fo_0b0 := F_152f10.
Definition Do_0b0 := D_152f10.
Definition Fo_0b4 := F_152f14.
Definition Do_0b4 := D_152f14.
Definition Fo_0b8 := F_152f18.
Definition Do_0b8 := D_152f18.
Definition Fo_0bc := F_152f1c.
Definition Do_0bc := D_152f1c.
Definition Fo_0c0 := F_152f20.
Definition Do_0c0 := D_152f20.
Definition Fo_0c4 := F_152f24.
Definition Do_0c4 := D_152f24.
Definition Fo_0c8 := F_152f28.
Definition Do_0c8 := D_152f28.
Definition Fo_0cc := F_152f2c.
Definition Do_0cc := D_152f2c.
Definition Fo_0d0 := F_152f30.
Definition Do_0d0 := D_152f30.
Definition Fo_0d4 := F_152f34.
Definition Do_0d4 := D_152f34.
Definition Fo_0d8 := F_152f38.
Definition Do_0d8 := D_152f38.
Definition Fo_0dc := F_152f3c.
Definition Do_0dc := D_152f3c.
Definition Fo_0e0 := F_152f40.
Definition Do_0e0 := D_152f40.
Definition Fo_0e4 := F_152f44.
Definition Do_0e4 := D_152f44.
Definition Fo_0e8 := F_152f48.
Definition Do_0e8 := D_152f48.
Definition Fo_0ec := F_152f4c.
Definition Do_0ec := D_152f4c.
Definition Fo_0f0 := F_152f50.
Definition Do_0f0 := D_152f50.
Definition Fo_0f4 := F_152f54.
Definition Do_0f4 := D_152f54.
