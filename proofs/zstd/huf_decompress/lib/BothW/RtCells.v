(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RtCells () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW4BImgEref_find_segment_noneC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8no_imageK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegs".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x60f000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xb2118 [C8 (Z_to_bv 64 0x14be28); C8 (Z_to_bv 64 0xb7af8); C8 (Z_to_bv 64 0xba2f8);
                              C8 (Z_to_bv 64 0xbafe8); C8 (Z_to_bv 64 0xbaff0); C8 (Z_to_bv 64 0xbafe0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0xb2c90 [C8 (Z_to_bv 64 0xbafd9)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0xbafd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0xbafe0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0xb3fa0 [C8 (Z_to_bv 64 0xab458); C8 (Z_to_bv 64 0xab85c)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]).
Notation rt_real_read m := (rw_cells bsegs m 0xb3e78 [C8 (Z_to_bv 64 0xb0b5c)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xb3e98 [C8 (Z_to_bv 64 0xaada8); C8 (Z_to_bv 64 0xa7c98)]).
