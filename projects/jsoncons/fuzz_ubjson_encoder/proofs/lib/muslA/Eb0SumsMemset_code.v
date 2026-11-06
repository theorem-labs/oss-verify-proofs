(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export Eb0_code_rcb2e4_cbd08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x130034%Z.
Definition Fo_000 := F_12fff0.
Definition Do_000 := D_12fff0.
Definition Fo_004 := F_12fff4.
Definition Do_004 := D_12fff4.
Definition Fo_008 := F_12fff8.
Definition Do_008 := D_12fff8.
Definition Fo_00c := F_12fffc.
Definition Do_00c := D_12fffc.
Definition Fo_010 := F_130000.
Definition Do_010 := D_130000.
Definition Fo_014 := F_130004.
Definition Do_014 := D_130004.
Definition Fo_018 := F_130008.
Definition Do_018 := D_130008.
Definition Fo_01c := F_13000c.
Definition Do_01c := D_13000c.
Definition Fo_020 := F_130010.
Definition Do_020 := D_130010.
Definition Fo_024 := F_130014.
Definition Do_024 := D_130014.
Definition Fo_028 := F_130018.
Definition Do_028 := D_130018.
Definition Fo_02c := F_13001c.
Definition Do_02c := D_13001c.
Definition Fo_030 := F_130020.
Definition Do_030 := D_130020.
Definition Fo_034 := F_130024.
Definition Do_034 := D_130024.
Definition Fo_038 := F_130028.
Definition Do_038 := D_130028.
Definition Fo_03c := F_13002c.
Definition Do_03c := D_13002c.
Definition Fo_040 := F_130030.
Definition Do_040 := D_130030.
Definition Fo_044 := F_130034.
Definition Do_044 := D_130034.
Definition Fo_048 := F_130038.
Definition Do_048 := D_130038.
Definition Fo_04c := F_13003c.
Definition Do_04c := D_13003c.
Definition Fo_050 := F_130040.
Definition Do_050 := D_130040.
Definition Fo_054 := F_130044.
Definition Do_054 := D_130044.
Definition Fo_058 := F_130048.
Definition Do_058 := D_130048.
Definition Fo_05c := F_13004c.
Definition Do_05c := D_13004c.
Definition Fo_060 := F_130050.
Definition Do_060 := D_130050.
Definition Fo_064 := F_130054.
Definition Do_064 := D_130054.
Definition Fo_068 := F_130058.
Definition Do_068 := D_130058.
Definition Fo_06c := F_13005c.
Definition Do_06c := D_13005c.
Definition Fo_070 := F_130060.
Definition Do_070 := D_130060.
Definition Fo_074 := F_130064.
Definition Do_074 := D_130064.
Definition Fo_078 := F_130068.
Definition Do_078 := D_130068.
Definition Fo_07c := F_13006c.
Definition Do_07c := D_13006c.
Definition Fo_080 := F_130070.
Definition Do_080 := D_130070.
Definition Fo_084 := F_130074.
Definition Do_084 := D_130074.
Definition Fo_088 := F_130078.
Definition Do_088 := D_130078.
Definition Fo_08c := F_13007c.
Definition Do_08c := D_13007c.
Definition Fo_090 := F_130080.
Definition Do_090 := D_130080.
Definition Fo_094 := F_130084.
Definition Do_094 := D_130084.
Definition Fo_098 := F_130088.
Definition Do_098 := D_130088.
Definition Fo_09c := F_13008c.
Definition Do_09c := D_13008c.
Definition Fo_0a0 := F_130090.
Definition Do_0a0 := D_130090.
Definition Fo_0a4 := F_130094.
Definition Do_0a4 := D_130094.
Definition Fo_0a8 := F_130098.
Definition Do_0a8 := D_130098.
Definition Fo_0ac := F_13009c.
Definition Do_0ac := D_13009c.
Definition Fo_0b0 := F_1300a0.
Definition Do_0b0 := D_1300a0.
Definition Fo_0b4 := F_1300a4.
Definition Do_0b4 := D_1300a4.
Definition Fo_0b8 := F_1300a8.
Definition Do_0b8 := D_1300a8.
Definition Fo_0bc := F_1300ac.
Definition Do_0bc := D_1300ac.
Definition Fo_0c0 := F_1300b0.
Definition Do_0c0 := D_1300b0.
Definition Fo_0c4 := F_1300b4.
Definition Do_0c4 := D_1300b4.
Definition Fo_0c8 := F_1300b8.
Definition Do_0c8 := D_1300b8.
Definition Fo_0cc := F_1300bc.
Definition Do_0cc := D_1300bc.
Definition Fo_0d0 := F_1300c0.
Definition Do_0d0 := D_1300c0.
Definition Fo_0d4 := F_1300c4.
Definition Do_0d4 := D_1300c4.
Definition Fo_0d8 := F_1300c8.
Definition Do_0d8 := D_1300c8.
Definition Fo_0dc := F_1300cc.
Definition Do_0dc := D_1300cc.
Definition Fo_0e0 := F_1300d0.
Definition Do_0e0 := D_1300d0.
Definition Fo_0e4 := F_1300d4.
Definition Do_0e4 := D_1300d4.
Definition Fo_0e8 := F_1300d8.
Definition Do_0e8 := D_1300d8.
Definition Fo_0ec := F_1300dc.
Definition Do_0ec := D_1300dc.
Definition Fo_0f0 := F_1300e0.
Definition Do_0f0 := D_1300e0.
Definition Fo_0f4 := F_1300e4.
Definition Do_0f4 := D_1300e4.
