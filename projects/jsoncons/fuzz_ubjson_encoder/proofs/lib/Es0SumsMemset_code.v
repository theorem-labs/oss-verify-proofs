(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export Es0_code_r58000_59000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Plain.M.loaded_segments.
Definition ms_base : Z := 0xaca0c%Z.
Definition Fo_000 := F_ac9c0.
Definition Do_000 := D_ac9c0.
Definition Fo_004 := F_ac9c4.
Definition Do_004 := D_ac9c4.
Definition Fo_008 := F_ac9c8.
Definition Do_008 := D_ac9c8.
Definition Fo_00c := F_ac9cc.
Definition Do_00c := D_ac9cc.
Definition Fo_010 := F_ac9d0.
Definition Do_010 := D_ac9d0.
Definition Fo_014 := F_ac9d4.
Definition Do_014 := D_ac9d4.
Definition Fo_018 := F_ac9d8.
Definition Do_018 := D_ac9d8.
Definition Fo_01c := F_ac9dc.
Definition Do_01c := D_ac9dc.
Definition Fo_020 := F_ac9e0.
Definition Do_020 := D_ac9e0.
Definition Fo_024 := F_ac9e4.
Definition Do_024 := D_ac9e4.
Definition Fo_028 := F_ac9e8.
Definition Do_028 := D_ac9e8.
Definition Fo_02c := F_ac9ec.
Definition Do_02c := D_ac9ec.
Definition Fo_030 := F_ac9f0.
Definition Do_030 := D_ac9f0.
Definition Fo_034 := F_ac9f4.
Definition Do_034 := D_ac9f4.
Definition Fo_038 := F_ac9f8.
Definition Do_038 := D_ac9f8.
Definition Fo_03c := F_ac9fc.
Definition Do_03c := D_ac9fc.
Definition Fo_040 := F_aca00.
Definition Do_040 := D_aca00.
Definition Fo_044 := F_aca04.
Definition Do_044 := D_aca04.
Definition Fo_048 := F_aca08.
Definition Do_048 := D_aca08.
Definition Fo_04c := F_aca0c.
Definition Do_04c := D_aca0c.
Definition Fo_050 := F_aca10.
Definition Do_050 := D_aca10.
Definition Fo_054 := F_aca14.
Definition Do_054 := D_aca14.
Definition Fo_058 := F_aca18.
Definition Do_058 := D_aca18.
Definition Fo_05c := F_aca1c.
Definition Do_05c := D_aca1c.
Definition Fo_060 := F_aca20.
Definition Do_060 := D_aca20.
Definition Fo_064 := F_aca24.
Definition Do_064 := D_aca24.
Definition Fo_068 := F_aca28.
Definition Do_068 := D_aca28.
Definition Fo_06c := F_aca2c.
Definition Do_06c := D_aca2c.
Definition Fo_070 := F_aca30.
Definition Do_070 := D_aca30.
Definition Fo_074 := F_aca34.
Definition Do_074 := D_aca34.
Definition Fo_078 := F_aca38.
Definition Do_078 := D_aca38.
Definition Fo_07c := F_aca3c.
Definition Do_07c := D_aca3c.
Definition Fo_080 := F_aca40.
Definition Do_080 := D_aca40.
Definition Fo_084 := F_aca44.
Definition Do_084 := D_aca44.
Definition Fo_088 := F_aca48.
Definition Do_088 := D_aca48.
Definition Fo_08c := F_aca4c.
Definition Do_08c := D_aca4c.
Definition Fo_090 := F_aca50.
Definition Do_090 := D_aca50.
Definition Fo_094 := F_aca54.
Definition Do_094 := D_aca54.
Definition Fo_098 := F_aca58.
Definition Do_098 := D_aca58.
Definition Fo_09c := F_aca5c.
Definition Do_09c := D_aca5c.
Definition Fo_0a0 := F_aca60.
Definition Do_0a0 := D_aca60.
Definition Fo_0a4 := F_aca64.
Definition Do_0a4 := D_aca64.
Definition Fo_0a8 := F_aca68.
Definition Do_0a8 := D_aca68.
Definition Fo_0ac := F_aca6c.
Definition Do_0ac := D_aca6c.
Definition Fo_0b0 := F_aca70.
Definition Do_0b0 := D_aca70.
Definition Fo_0b4 := F_aca74.
Definition Do_0b4 := D_aca74.
Definition Fo_0b8 := F_aca78.
Definition Do_0b8 := D_aca78.
Definition Fo_0bc := F_aca7c.
Definition Do_0bc := D_aca7c.
Definition Fo_0c0 := F_aca80.
Definition Do_0c0 := D_aca80.
Definition Fo_0c4 := F_aca84.
Definition Do_0c4 := D_aca84.
Definition Fo_0c8 := F_aca88.
Definition Do_0c8 := D_aca88.
Definition Fo_0cc := F_aca8c.
Definition Do_0cc := D_aca8c.
Definition Fo_0d0 := F_aca90.
Definition Do_0d0 := D_aca90.
Definition Fo_0d4 := F_aca94.
Definition Do_0d4 := D_aca94.
Definition Fo_0d8 := F_aca98.
Definition Do_0d8 := D_aca98.
Definition Fo_0dc := F_aca9c.
Definition Do_0dc := D_aca9c.
Definition Fo_0e0 := F_acaa0.
Definition Do_0e0 := D_acaa0.
Definition Fo_0e4 := F_acaa4.
Definition Do_0e4 := D_acaa4.
Definition Fo_0e8 := F_acaa8.
Definition Do_0e8 := D_acaa8.
Definition Fo_0ec := F_acaac.
Definition Do_0ec := D_acaac.
Definition Fo_0f0 := F_acab0.
Definition Do_0f0 := D_acab0.
Definition Fo_0f4 := F_acab4.
Definition Do_0f4 := D_acab4.
