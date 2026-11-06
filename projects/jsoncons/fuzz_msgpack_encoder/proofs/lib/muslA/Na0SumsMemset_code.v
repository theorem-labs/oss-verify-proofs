(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0017. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0017.Na0_code_rcb2e4_cbd08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x14916c%Z.
Definition Fo_000 := F_149128.
Definition Do_000 := D_149128.
Definition Fo_004 := F_14912c.
Definition Do_004 := D_14912c.
Definition Fo_008 := F_149130.
Definition Do_008 := D_149130.
Definition Fo_00c := F_149134.
Definition Do_00c := D_149134.
Definition Fo_010 := F_149138.
Definition Do_010 := D_149138.
Definition Fo_014 := F_14913c.
Definition Do_014 := D_14913c.
Definition Fo_018 := F_149140.
Definition Do_018 := D_149140.
Definition Fo_01c := F_149144.
Definition Do_01c := D_149144.
Definition Fo_020 := F_149148.
Definition Do_020 := D_149148.
Definition Fo_024 := F_14914c.
Definition Do_024 := D_14914c.
Definition Fo_028 := F_149150.
Definition Do_028 := D_149150.
Definition Fo_02c := F_149154.
Definition Do_02c := D_149154.
Definition Fo_030 := F_149158.
Definition Do_030 := D_149158.
Definition Fo_034 := F_14915c.
Definition Do_034 := D_14915c.
Definition Fo_038 := F_149160.
Definition Do_038 := D_149160.
Definition Fo_03c := F_149164.
Definition Do_03c := D_149164.
Definition Fo_040 := F_149168.
Definition Do_040 := D_149168.
Definition Fo_044 := F_14916c.
Definition Do_044 := D_14916c.
Definition Fo_048 := F_149170.
Definition Do_048 := D_149170.
Definition Fo_04c := F_149174.
Definition Do_04c := D_149174.
Definition Fo_050 := F_149178.
Definition Do_050 := D_149178.
Definition Fo_054 := F_14917c.
Definition Do_054 := D_14917c.
Definition Fo_058 := F_149180.
Definition Do_058 := D_149180.
Definition Fo_05c := F_149184.
Definition Do_05c := D_149184.
Definition Fo_060 := F_149188.
Definition Do_060 := D_149188.
Definition Fo_064 := F_14918c.
Definition Do_064 := D_14918c.
Definition Fo_068 := F_149190.
Definition Do_068 := D_149190.
Definition Fo_06c := F_149194.
Definition Do_06c := D_149194.
Definition Fo_070 := F_149198.
Definition Do_070 := D_149198.
Definition Fo_074 := F_14919c.
Definition Do_074 := D_14919c.
Definition Fo_078 := F_1491a0.
Definition Do_078 := D_1491a0.
Definition Fo_07c := F_1491a4.
Definition Do_07c := D_1491a4.
Definition Fo_080 := F_1491a8.
Definition Do_080 := D_1491a8.
Definition Fo_084 := F_1491ac.
Definition Do_084 := D_1491ac.
Definition Fo_088 := F_1491b0.
Definition Do_088 := D_1491b0.
Definition Fo_08c := F_1491b4.
Definition Do_08c := D_1491b4.
Definition Fo_090 := F_1491b8.
Definition Do_090 := D_1491b8.
Definition Fo_094 := F_1491bc.
Definition Do_094 := D_1491bc.
Definition Fo_098 := F_1491c0.
Definition Do_098 := D_1491c0.
Definition Fo_09c := F_1491c4.
Definition Do_09c := D_1491c4.
Definition Fo_0a0 := F_1491c8.
Definition Do_0a0 := D_1491c8.
Definition Fo_0a4 := F_1491cc.
Definition Do_0a4 := D_1491cc.
Definition Fo_0a8 := F_1491d0.
Definition Do_0a8 := D_1491d0.
Definition Fo_0ac := F_1491d4.
Definition Do_0ac := D_1491d4.
Definition Fo_0b0 := F_1491d8.
Definition Do_0b0 := D_1491d8.
Definition Fo_0b4 := F_1491dc.
Definition Do_0b4 := D_1491dc.
Definition Fo_0b8 := F_1491e0.
Definition Do_0b8 := D_1491e0.
Definition Fo_0bc := F_1491e4.
Definition Do_0bc := D_1491e4.
Definition Fo_0c0 := F_1491e8.
Definition Do_0c0 := D_1491e8.
Definition Fo_0c4 := F_1491ec.
Definition Do_0c4 := D_1491ec.
Definition Fo_0c8 := F_1491f0.
Definition Do_0c8 := D_1491f0.
Definition Fo_0cc := F_1491f4.
Definition Do_0cc := D_1491f4.
Definition Fo_0d0 := F_1491f8.
Definition Do_0d0 := D_1491f8.
Definition Fo_0d4 := F_1491fc.
Definition Do_0d4 := D_1491fc.
Definition Fo_0d8 := F_149200.
Definition Do_0d8 := D_149200.
Definition Fo_0dc := F_149204.
Definition Do_0dc := D_149204.
Definition Fo_0e0 := F_149208.
Definition Do_0e0 := D_149208.
Definition Fo_0e4 := F_14920c.
Definition Do_0e4 := D_14920c.
Definition Fo_0e8 := F_149210.
Definition Do_0e8 := D_149210.
Definition Fo_0ec := F_149214.
Definition Do_0ec := D_149214.
Definition Fo_0f0 := F_149218.
Definition Do_0f0 := D_149218.
Definition Fo_0f4 := F_14921c.
Definition Do_0f4 := D_14921c.
