(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Export Ba0_code_rcb2e4_cbd08_b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x129d04%Z.
Definition Fo_000 := F_127714.
Definition Do_000 := D_127714.
Definition Fo_004 := F_127718.
Definition Do_004 := D_127718.
Definition Fo_008 := F_12771c.
Definition Do_008 := D_12771c.
Definition Fo_00c := F_127720.
Definition Do_00c := D_127720.
Definition Fo_010 := F_127724.
Definition Do_010 := D_127724.
Definition Fo_014 := F_127728.
Definition Do_014 := D_127728.
Definition Fo_018 := F_12772c.
Definition Do_018 := D_12772c.
Definition Fo_01c := F_127730.
Definition Do_01c := D_127730.
Definition Fo_020 := F_127734.
Definition Do_020 := D_127734.
Definition Fo_024 := F_127738.
Definition Do_024 := D_127738.
Definition Fo_028 := F_12773c.
Definition Do_028 := D_12773c.
Definition Fo_02c := F_127740.
Definition Do_02c := D_127740.
Definition Fo_030 := F_127744.
Definition Do_030 := D_127744.
Definition Fo_034 := F_127748.
Definition Do_034 := D_127748.
Definition Fo_038 := F_12774c.
Definition Do_038 := D_12774c.
Definition Fo_03c := F_127750.
Definition Do_03c := D_127750.
Definition Fo_040 := F_127754.
Definition Do_040 := D_127754.
Definition Fo_044 := F_127758.
Definition Do_044 := D_127758.
Definition Fo_048 := F_12775c.
Definition Do_048 := D_12775c.
Definition Fo_04c := F_127760.
Definition Do_04c := D_127760.
Definition Fo_050 := F_127764.
Definition Do_050 := D_127764.
Definition Fo_054 := F_127768.
Definition Do_054 := D_127768.
Definition Fo_058 := F_12776c.
Definition Do_058 := D_12776c.
Definition Fo_05c := F_127770.
Definition Do_05c := D_127770.
Definition Fo_060 := F_127774.
Definition Do_060 := D_127774.
Definition Fo_064 := F_127778.
Definition Do_064 := D_127778.
Definition Fo_068 := F_12777c.
Definition Do_068 := D_12777c.
Definition Fo_06c := F_127780.
Definition Do_06c := D_127780.
Definition Fo_070 := F_127784.
Definition Do_070 := D_127784.
Definition Fo_074 := F_127788.
Definition Do_074 := D_127788.
Definition Fo_078 := F_12778c.
Definition Do_078 := D_12778c.
Definition Fo_07c := F_127790.
Definition Do_07c := D_127790.
Definition Fo_080 := F_127794.
Definition Do_080 := D_127794.
Definition Fo_084 := F_127798.
Definition Do_084 := D_127798.
Definition Fo_088 := F_12779c.
Definition Do_088 := D_12779c.
Definition Fo_08c := F_1277a0.
Definition Do_08c := D_1277a0.
Definition Fo_090 := F_1277a4.
Definition Do_090 := D_1277a4.
Definition Fo_094 := F_1277a8.
Definition Do_094 := D_1277a8.
Definition Fo_098 := F_1277ac.
Definition Do_098 := D_1277ac.
Definition Fo_09c := F_1277b0.
Definition Do_09c := D_1277b0.
Definition Fo_0a0 := F_1277b4.
Definition Do_0a0 := D_1277b4.
Definition Fo_0a4 := F_1277b8.
Definition Do_0a4 := D_1277b8.
Definition Fo_0a8 := F_1277bc.
Definition Do_0a8 := D_1277bc.
Definition Fo_0ac := F_1277c0.
Definition Do_0ac := D_1277c0.
Definition Fo_0b0 := F_1277c4.
Definition Do_0b0 := D_1277c4.
Definition Fo_0b4 := F_1277c8.
Definition Do_0b4 := D_1277c8.
Definition Fo_0b8 := F_1277cc.
Definition Do_0b8 := D_1277cc.
Definition Fo_0bc := F_1277d0.
Definition Do_0bc := D_1277d0.
Definition Fo_0c0 := F_1277d4.
Definition Do_0c0 := D_1277d4.
Definition Fo_0c4 := F_1277d8.
Definition Do_0c4 := D_1277d8.
Definition Fo_0c8 := F_1277dc.
Definition Do_0c8 := D_1277dc.
Definition Fo_0cc := F_1277e0.
Definition Do_0cc := D_1277e0.
Definition Fo_0d0 := F_1277e4.
Definition Do_0d0 := D_1277e4.
Definition Fo_0d4 := F_1277e8.
Definition Do_0d4 := D_1277e8.
Definition Fo_0d8 := F_1277ec.
Definition Do_0d8 := D_1277ec.
Definition Fo_0dc := F_1277f0.
Definition Do_0dc := D_1277f0.
Definition Fo_0e0 := F_1277f4.
Definition Do_0e0 := D_1277f4.
Definition Fo_0e4 := F_1277f8.
Definition Do_0e4 := D_1277f8.
Definition Fo_0e8 := F_1277fc.
Definition Do_0e8 := D_1277fc.
Definition Fo_0ec := F_127800.
Definition Do_0ec := D_127800.
Definition Fo_0f0 := F_127804.
Definition Do_0f0 := D_127804.
Definition Fo_0f4 := F_127808.
Definition Do_0f4 := D_127808.
