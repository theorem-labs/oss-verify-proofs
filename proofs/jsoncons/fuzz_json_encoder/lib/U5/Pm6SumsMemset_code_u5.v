(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Export Pm6_code_ba000_bb000_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Ubsan.M.loaded_segments.
Definition ms_base : Z := 0xbe5c8%Z.
Definition Fo_000 := F_baba0.
Definition Do_000 := D_baba0.
Definition Fo_004 := F_baba4.
Definition Do_004 := D_baba4.
Definition Fo_008 := F_baba8.
Definition Do_008 := D_baba8.
Definition Fo_00c := F_babac.
Definition Do_00c := D_babac.
Definition Fo_010 := F_babb0.
Definition Do_010 := D_babb0.
Definition Fo_014 := F_babb4.
Definition Do_014 := D_babb4.
Definition Fo_018 := F_babb8.
Definition Do_018 := D_babb8.
Definition Fo_01c := F_babbc.
Definition Do_01c := D_babbc.
Definition Fo_020 := F_babc0.
Definition Do_020 := D_babc0.
Definition Fo_024 := F_babc4.
Definition Do_024 := D_babc4.
Definition Fo_028 := F_babc8.
Definition Do_028 := D_babc8.
Definition Fo_02c := F_babcc.
Definition Do_02c := D_babcc.
Definition Fo_030 := F_babd0.
Definition Do_030 := D_babd0.
Definition Fo_034 := F_babd4.
Definition Do_034 := D_babd4.
Definition Fo_038 := F_babd8.
Definition Do_038 := D_babd8.
Definition Fo_03c := F_babdc.
Definition Do_03c := D_babdc.
Definition Fo_040 := F_babe0.
Definition Do_040 := D_babe0.
Definition Fo_044 := F_babe4.
Definition Do_044 := D_babe4.
Definition Fo_048 := F_babe8.
Definition Do_048 := D_babe8.
Definition Fo_04c := F_babec.
Definition Do_04c := D_babec.
Definition Fo_050 := F_babf0.
Definition Do_050 := D_babf0.
Definition Fo_054 := F_babf4.
Definition Do_054 := D_babf4.
Definition Fo_058 := F_babf8.
Definition Do_058 := D_babf8.
Definition Fo_05c := F_babfc.
Definition Do_05c := D_babfc.
Definition Fo_060 := F_bac00.
Definition Do_060 := D_bac00.
Definition Fo_064 := F_bac04.
Definition Do_064 := D_bac04.
Definition Fo_068 := F_bac08.
Definition Do_068 := D_bac08.
Definition Fo_06c := F_bac0c.
Definition Do_06c := D_bac0c.
Definition Fo_070 := F_bac10.
Definition Do_070 := D_bac10.
Definition Fo_074 := F_bac14.
Definition Do_074 := D_bac14.
Definition Fo_078 := F_bac18.
Definition Do_078 := D_bac18.
Definition Fo_07c := F_bac1c.
Definition Do_07c := D_bac1c.
Definition Fo_080 := F_bac20.
Definition Do_080 := D_bac20.
Definition Fo_084 := F_bac24.
Definition Do_084 := D_bac24.
Definition Fo_088 := F_bac28.
Definition Do_088 := D_bac28.
Definition Fo_08c := F_bac2c.
Definition Do_08c := D_bac2c.
Definition Fo_090 := F_bac30.
Definition Do_090 := D_bac30.
Definition Fo_094 := F_bac34.
Definition Do_094 := D_bac34.
Definition Fo_098 := F_bac38.
Definition Do_098 := D_bac38.
Definition Fo_09c := F_bac3c.
Definition Do_09c := D_bac3c.
Definition Fo_0a0 := F_bac40.
Definition Do_0a0 := D_bac40.
Definition Fo_0a4 := F_bac44.
Definition Do_0a4 := D_bac44.
Definition Fo_0a8 := F_bac48.
Definition Do_0a8 := D_bac48.
Definition Fo_0ac := F_bac4c.
Definition Do_0ac := D_bac4c.
Definition Fo_0b0 := F_bac50.
Definition Do_0b0 := D_bac50.
Definition Fo_0b4 := F_bac54.
Definition Do_0b4 := D_bac54.
Definition Fo_0b8 := F_bac58.
Definition Do_0b8 := D_bac58.
Definition Fo_0bc := F_bac5c.
Definition Do_0bc := D_bac5c.
Definition Fo_0c0 := F_bac60.
Definition Do_0c0 := D_bac60.
Definition Fo_0c4 := F_bac64.
Definition Do_0c4 := D_bac64.
Definition Fo_0c8 := F_bac68.
Definition Do_0c8 := D_bac68.
Definition Fo_0cc := F_bac6c.
Definition Do_0cc := D_bac6c.
Definition Fo_0d0 := F_bac70.
Definition Do_0d0 := D_bac70.
Definition Fo_0d4 := F_bac74.
Definition Do_0d4 := D_bac74.
Definition Fo_0d8 := F_bac78.
Definition Do_0d8 := D_bac78.
Definition Fo_0dc := F_bac7c.
Definition Do_0dc := D_bac7c.
Definition Fo_0e0 := F_bac80.
Definition Do_0e0 := D_bac80.
Definition Fo_0e4 := F_bac84.
Definition Do_0e4 := D_bac84.
Definition Fo_0e8 := F_bac88.
Definition Do_0e8 := D_bac88.
Definition Fo_0ec := F_bac8c.
Definition Do_0ec := D_bac8c.
Definition Fo_0f0 := F_bac90.
Definition Do_0f0 := D_bac90.
Definition Fo_0f4 := F_bac94.
Definition Do_0f4 := D_bac94.
