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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export Eu0_code_r59000_5a000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Ubsan.M.loaded_segments.
Definition ms_base : Z := 0xae588%Z.
Definition Fo_000 := F_ae53c.
Definition Do_000 := D_ae53c.
Definition Fo_004 := F_ae540.
Definition Do_004 := D_ae540.
Definition Fo_008 := F_ae544.
Definition Do_008 := D_ae544.
Definition Fo_00c := F_ae548.
Definition Do_00c := D_ae548.
Definition Fo_010 := F_ae54c.
Definition Do_010 := D_ae54c.
Definition Fo_014 := F_ae550.
Definition Do_014 := D_ae550.
Definition Fo_018 := F_ae554.
Definition Do_018 := D_ae554.
Definition Fo_01c := F_ae558.
Definition Do_01c := D_ae558.
Definition Fo_020 := F_ae55c.
Definition Do_020 := D_ae55c.
Definition Fo_024 := F_ae560.
Definition Do_024 := D_ae560.
Definition Fo_028 := F_ae564.
Definition Do_028 := D_ae564.
Definition Fo_02c := F_ae568.
Definition Do_02c := D_ae568.
Definition Fo_030 := F_ae56c.
Definition Do_030 := D_ae56c.
Definition Fo_034 := F_ae570.
Definition Do_034 := D_ae570.
Definition Fo_038 := F_ae574.
Definition Do_038 := D_ae574.
Definition Fo_03c := F_ae578.
Definition Do_03c := D_ae578.
Definition Fo_040 := F_ae57c.
Definition Do_040 := D_ae57c.
Definition Fo_044 := F_ae580.
Definition Do_044 := D_ae580.
Definition Fo_048 := F_ae584.
Definition Do_048 := D_ae584.
Definition Fo_04c := F_ae588.
Definition Do_04c := D_ae588.
Definition Fo_050 := F_ae58c.
Definition Do_050 := D_ae58c.
Definition Fo_054 := F_ae590.
Definition Do_054 := D_ae590.
Definition Fo_058 := F_ae594.
Definition Do_058 := D_ae594.
Definition Fo_05c := F_ae598.
Definition Do_05c := D_ae598.
Definition Fo_060 := F_ae59c.
Definition Do_060 := D_ae59c.
Definition Fo_064 := F_ae5a0.
Definition Do_064 := D_ae5a0.
Definition Fo_068 := F_ae5a4.
Definition Do_068 := D_ae5a4.
Definition Fo_06c := F_ae5a8.
Definition Do_06c := D_ae5a8.
Definition Fo_070 := F_ae5ac.
Definition Do_070 := D_ae5ac.
Definition Fo_074 := F_ae5b0.
Definition Do_074 := D_ae5b0.
Definition Fo_078 := F_ae5b4.
Definition Do_078 := D_ae5b4.
Definition Fo_07c := F_ae5b8.
Definition Do_07c := D_ae5b8.
Definition Fo_080 := F_ae5bc.
Definition Do_080 := D_ae5bc.
Definition Fo_084 := F_ae5c0.
Definition Do_084 := D_ae5c0.
Definition Fo_088 := F_ae5c4.
Definition Do_088 := D_ae5c4.
Definition Fo_08c := F_ae5c8.
Definition Do_08c := D_ae5c8.
Definition Fo_090 := F_ae5cc.
Definition Do_090 := D_ae5cc.
Definition Fo_094 := F_ae5d0.
Definition Do_094 := D_ae5d0.
Definition Fo_098 := F_ae5d4.
Definition Do_098 := D_ae5d4.
Definition Fo_09c := F_ae5d8.
Definition Do_09c := D_ae5d8.
Definition Fo_0a0 := F_ae5dc.
Definition Do_0a0 := D_ae5dc.
Definition Fo_0a4 := F_ae5e0.
Definition Do_0a4 := D_ae5e0.
Definition Fo_0a8 := F_ae5e4.
Definition Do_0a8 := D_ae5e4.
Definition Fo_0ac := F_ae5e8.
Definition Do_0ac := D_ae5e8.
Definition Fo_0b0 := F_ae5ec.
Definition Do_0b0 := D_ae5ec.
Definition Fo_0b4 := F_ae5f0.
Definition Do_0b4 := D_ae5f0.
Definition Fo_0b8 := F_ae5f4.
Definition Do_0b8 := D_ae5f4.
Definition Fo_0bc := F_ae5f8.
Definition Do_0bc := D_ae5f8.
Definition Fo_0c0 := F_ae5fc.
Definition Do_0c0 := D_ae5fc.
Definition Fo_0c4 := F_ae600.
Definition Do_0c4 := D_ae600.
Definition Fo_0c8 := F_ae604.
Definition Do_0c8 := D_ae604.
Definition Fo_0cc := F_ae608.
Definition Do_0cc := D_ae608.
Definition Fo_0d0 := F_ae60c.
Definition Do_0d0 := D_ae60c.
Definition Fo_0d4 := F_ae610.
Definition Do_0d4 := D_ae610.
Definition Fo_0d8 := F_ae614.
Definition Do_0d8 := D_ae614.
Definition Fo_0dc := F_ae618.
Definition Do_0dc := D_ae618.
Definition Fo_0e0 := F_ae61c.
Definition Do_0e0 := D_ae61c.
Definition Fo_0e4 := F_ae620.
Definition Do_0e4 := D_ae620.
Definition Fo_0e8 := F_ae624.
Definition Do_0e8 := D_ae624.
Definition Fo_0ec := F_ae628.
Definition Do_0ec := D_ae628.
Definition Fo_0f0 := F_ae62c.
Definition Do_0f0 := D_ae62c.
Definition Fo_0f4 := F_ae630.
Definition Do_0f4 := D_ae630.
