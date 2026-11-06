(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Export Pm5_code_156000_157000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x1568bc%Z.
Definition Fo_000 := F_156880.
Definition Do_000 := D_156880.
Definition Fo_004 := F_156884.
Definition Do_004 := D_156884.
Definition Fo_008 := F_156888.
Definition Do_008 := D_156888.
Definition Fo_00c := F_15688c.
Definition Do_00c := D_15688c.
Definition Fo_010 := F_156890.
Definition Do_010 := D_156890.
Definition Fo_014 := F_156894.
Definition Do_014 := D_156894.
Definition Fo_018 := F_156898.
Definition Do_018 := D_156898.
Definition Fo_01c := F_15689c.
Definition Do_01c := D_15689c.
Definition Fo_020 := F_1568a0.
Definition Do_020 := D_1568a0.
Definition Fo_024 := F_1568a4.
Definition Do_024 := D_1568a4.
Definition Fo_028 := F_1568a8.
Definition Do_028 := D_1568a8.
Definition Fo_02c := F_1568ac.
Definition Do_02c := D_1568ac.
Definition Fo_030 := F_1568b0.
Definition Do_030 := D_1568b0.
Definition Fo_034 := F_1568b4.
Definition Do_034 := D_1568b4.
Definition Fo_038 := F_1568b8.
Definition Do_038 := D_1568b8.
Definition Fo_03c := F_1568bc.
Definition Do_03c := D_1568bc.
Definition Fo_040 := F_1568c0.
Definition Do_040 := D_1568c0.
Definition Fo_044 := F_1568c4.
Definition Do_044 := D_1568c4.
Definition Fo_048 := F_1568c8.
Definition Do_048 := D_1568c8.
Definition Fo_04c := F_1568cc.
Definition Do_04c := D_1568cc.
Definition Fo_050 := F_1568d0.
Definition Do_050 := D_1568d0.
Definition Fo_054 := F_1568d4.
Definition Do_054 := D_1568d4.
Definition Fo_058 := F_1568d8.
Definition Do_058 := D_1568d8.
Definition Fo_05c := F_1568dc.
Definition Do_05c := D_1568dc.
Definition Fo_060 := F_1568e0.
Definition Do_060 := D_1568e0.
Definition Fo_064 := F_1568e4.
Definition Do_064 := D_1568e4.
Definition Fo_068 := F_1568e8.
Definition Do_068 := D_1568e8.
Definition Fo_06c := F_1568ec.
Definition Do_06c := D_1568ec.
Definition Fo_070 := F_1568f0.
Definition Do_070 := D_1568f0.
Definition Fo_074 := F_1568f4.
Definition Do_074 := D_1568f4.
Definition Fo_078 := F_1568f8.
Definition Do_078 := D_1568f8.
Definition Fo_07c := F_1568fc.
Definition Do_07c := D_1568fc.
Definition Fo_080 := F_156900.
Definition Do_080 := D_156900.
Definition Fo_084 := F_156904.
Definition Do_084 := D_156904.
Definition Fo_088 := F_156908.
Definition Do_088 := D_156908.
Definition Fo_08c := F_15690c.
Definition Do_08c := D_15690c.
Definition Fo_090 := F_156910.
Definition Do_090 := D_156910.
Definition Fo_094 := F_156914.
Definition Do_094 := D_156914.
Definition Fo_098 := F_156918.
Definition Do_098 := D_156918.
Definition Fo_09c := F_15691c.
Definition Do_09c := D_15691c.
Definition Fo_0a0 := F_156920.
Definition Do_0a0 := D_156920.
Definition Fo_0a4 := F_156924.
Definition Do_0a4 := D_156924.
Definition Fo_0a8 := F_156928.
Definition Do_0a8 := D_156928.
Definition Fo_0ac := F_15692c.
Definition Do_0ac := D_15692c.
Definition Fo_0b0 := F_156930.
Definition Do_0b0 := D_156930.
Definition Fo_0b4 := F_156934.
Definition Do_0b4 := D_156934.
Definition Fo_0b8 := F_156938.
Definition Do_0b8 := D_156938.
Definition Fo_0bc := F_15693c.
Definition Do_0bc := D_15693c.
Definition Fo_0c0 := F_156940.
Definition Do_0c0 := D_156940.
Definition Fo_0c4 := F_156944.
Definition Do_0c4 := D_156944.
Definition Fo_0c8 := F_156948.
Definition Do_0c8 := D_156948.
Definition Fo_0cc := F_15694c.
Definition Do_0cc := D_15694c.
Definition Fo_0d0 := F_156950.
Definition Do_0d0 := D_156950.
Definition Fo_0d4 := F_156954.
Definition Do_0d4 := D_156954.
Definition Fo_0d8 := F_156958.
Definition Do_0d8 := D_156958.
Definition Fo_0dc := F_15695c.
Definition Do_0dc := D_15695c.
Definition Fo_0e0 := F_156960.
Definition Do_0e0 := D_156960.
Definition Fo_0e4 := F_156964.
Definition Do_0e4 := D_156964.
Definition Fo_0e8 := F_156968.
Definition Do_0e8 := D_156968.
Definition Fo_0ec := F_15696c.
Definition Do_0ec := D_15696c.
Definition Fo_0f0 := F_156970.
Definition Do_0f0 := D_156970.
Definition Fo_0f4 := F_156974.
Definition Do_0f4 := D_156974.
