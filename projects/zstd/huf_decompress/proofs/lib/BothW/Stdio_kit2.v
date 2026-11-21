(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (rw_cells_recast3, fmt_bytes_at)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_kit2 () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Common<F_fmt_fp_lib9zb_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStepAro_cells_bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_recast3 : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv bsegs m -> ro_bytes_b bsegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at bsegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at bsegs m A _ (ro_cells_image bsegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

End CANSEC1.
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
