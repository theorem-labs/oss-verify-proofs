(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_fin AZ_seq_l_xat AZ_seq_l_exit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_at_err20 (P : slq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 (l_FF P)) x12 x13 (Z_to_bv 64 18446744073709551596) x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a8) (l_fc P) None m1 (seg_rom bsegs)).

Lemma sql_err20_at : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_err20 P OEND LLO LEND LOCV.
Proof. intros P OEND LLO LEND LOCV ST FIN. exact (sql_err20_ok P OEND LLO LEND LOCV ST FIN). Qed.

(* [comment removed for export] *)
Definition sql_at_e70 (P : slq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 (l_FF P)) x12 x13 (Z_to_bv 64 18446744073709551546) x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a8) (l_fc P) None m1 (seg_rom bsegs)).

Lemma sql_e70_at : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_e70 P OEND LLO LEND LOCV.
Proof. intros P OEND LLO LEND LOCV ST FIN. exact (sql_e70_ok P OEND LLO LEND LOCV ST FIN). Qed.

(* [comment removed for export] *)
Definition sql_at_err20d (P : slq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 x25 x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e79c) (l_fc P) None m1 (seg_rom bsegs)).

Lemma sql_err20d_at : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_err20d P OEND LLO LEND LOCV.
Proof. intros P OEND LLO LEND LOCV ST FIN. exact (sql_err20d_ok P OEND LLO LEND LOCV ST FIN). Qed.

(* [comment removed for export] *)
Definition sql_at_err20c (P : slq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a0) (l_fc P) None m1 (seg_rom bsegs)).

Lemma sql_err20c_at : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_fin P -> sql_at_err20c P OEND LLO LEND LOCV.
Proof. intros P OEND LLO LEND LOCV ST FIN. exact (sql_err20c_ok P OEND LLO LEND LOCV ST FIN). Qed.

End CANSEC1.
