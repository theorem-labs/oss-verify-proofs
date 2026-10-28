(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_xat RZ_seq_s_exit RZ_seq_s_none RZ_seq_s_ibase RZ_seq_s_ient RZ_seq_s_ient2 RZ_seq_s_ibit RZ_seq_s_ifse RZ_seq_s_irl RZ_seq_s_a1_at RZ_seq_s_a2_at RZ_seq_s_a1_loop RZ_seq_s_a2_loop RZ_seq_s_tr3.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_static_oend : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> v_DST P <= OEND <= v_DST P + v_CAP P /\ 1 <= zlen (v_sq P).
Proof.
  intros P OEND LLO LEND LOCV ST. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_static v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *. sd_static_open ST. lia.
Qed.

Theorem zd_seq_split_proof : zd_execend_stmt -> zd_execend_split_stmt -> zd_seq_split_stmt.
Proof.
  intros EXE EXS. unfold zd_seq_split_stmt, zd_seq_split_stmt_at.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws.
  intros DCX LIT R1 R2 R3 SQB AB R4 R5 R6 TB BUF R7 R8 PF R9 R10 R11 LOCK R12 R13 R14 LRD PLACED STK R15 R16 R17 O1 O2 O3 O4 OT A1 A2 AT A3 A4 ATR SP16 ALT MI.
  intros -> -> -> -> -> ->.
  set (P := mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws).
  assert (MEM : seqs_mem P) by (cbn [seqs_mem P]; repeat (split; [assumption|]); assumption).
  assert (RG : seqs_ranges P) by (cbn [seqs_ranges P]; repeat (split; [assumption|]); assumption).
  assert (SIDE : seqs_side P) by (cbn [seqs_side P]; repeat (split; [assumption|]); assumption).
  assert (SEP : seqs_sep P) by (cbn [seqs_sep P]; repeat (split; [assumption|]); assumption).
  assert (LV : v_LOC P = 2) by (cbn [P v_LOC]; exact LOCK).
  destruct (Z.eq_dec nbSeq 0) as [NB0|NZ].
  - exact (seqs_none P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0 LV).
  - assert (TBL : seqs_tables P).
    { cbn [seqs_tables P]. destruct (TB NZ) as (T1 & T2 & T3 & T4 & T5 & T6). destruct (OT NZ) as (T7 & T8 & T9). destruct (AT NZ) as (T10 & T11 & T12).
      destruct (ATR NZ) as (T13 & T14 & T15). destruct (ALT NZ) as (T16 & T17 & T18). repeat (split; [assumption|]). assumption. }
    assert (HLBE : wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 (v_LBE P)) by (cbn [P v_ws v_LBE]; destruct LIT as (_ & L2 & _); exact L2).
    assert (HLP : v_LITP P <= v_LITP P <= v_LBE P) by (cbn [P v_LITP v_LBE]; lia).
    apply (seqs_entry P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ LV). intros OEND ST1.
    destruct (seqs_static_oend P _ _ _ _ ST1) as (HOE & HN1).
    pose proof (seqs_static_intro2 P OEND RG SIDE SEP TBL NZ HN1 HOE) as ST2.
    pose proof (seqs_at_err_ok P OEND (v_LITP P) (v_LBE P) 2 RG) as A_err1.
    pose proof (seqs_at_err_ok P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 RG) as A_err2.
    pose proof (seqs_at_lexit_ok P _ _ _ _ ST1 RG SEP) as A_lexit1.
    pose proof (seqs_at_lexit_ok P _ _ _ _ ST2 RG SEP) as A_lexit2.
    pose proof (a2_loop EXE P _ _ _ _ ST2 A_err2 A_lexit2) as A_loop2.
    pose proof (tr_all EXE P OEND (v_LITP P) (v_LBE P) ST1 ST2 A_err1 A_err2 A_lexit2 A_loop2) as A_brk.
    pose proof (a1_loop EXS P _ _ _ _ ST1 A_err1 A_lexit1 HLBE eq_refl A_brk) as A_loop1.
    apply (seqs_bitinit P _ _ _ _ ST1 RG).
    apply (seqs_ifse_LL P _ _ _ _ ST1). apply (seqs_irl_LL P _ _ _ _ ST1).
    apply (seqs_ifse_OF P _ _ _ _ ST1). apply (seqs_irl_OF P _ _ _ _ ST1).
    apply (seqs_ifse_ML P _ _ _ _ ST1). apply (seqs_irl_ML P _ _ _ _ ST1).
    apply (seqs_ihead P _ _ _ _ ST1 HLP).
    apply A_loop1. cbn [v_nbSeq P]. lia.
Qed.

