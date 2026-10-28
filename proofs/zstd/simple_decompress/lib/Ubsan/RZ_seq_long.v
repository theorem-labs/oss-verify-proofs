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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_exit RZ_seq_l_none RZ_seq_l_null RZ_seq_l_ibase RZ_seq_l_ient RZ_seq_l_ient2 RZ_seq_l_ibit3 RZ_seq_l_ifse RZ_seq_l_irl RZ_seq_l_irl2 RZ_seq_l_irl3 RZ_seq_l_ihead RZ_seq_l_la_at RZ_seq_l_lf_at RZ_seq_l_la_loop.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_static_oend : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> y_DST P <= OEND <= y_DST P + y_CAP P /\ 1 <= zlen (y_sq P).
Proof.
  intros P OEND LLO LEND LOCV ST. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_static y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *. sd_static_open ST. lia.
Qed.

Theorem zd_seq_long_proof : zd_execend_stmt -> zd_execend_split_stmt -> zd_seq_long_stmt.
Proof.
  intros EXE EXS. unfold zd_seq_long_stmt, zd_seq_long_stmt_at.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws.
  intros DCX LIT R1 R2 R3 SQB AB R4 R5 R6 TB BUF R8 PF R9 R10 R11 NUL NNUL LOCK R12 R13 R14 LRD PLACED STK R15 R16 R17 O1 O2 O3 O4 OT A1 A2 AT A3 A4 ATR SP16 TAL MI.
  intros -> -> -> -> -> ->.
  set (P := mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws).
  assert (MEM : seql_mem P) by (cbn [seql_mem P]; repeat (split; [assumption|]); assumption).
  assert (SIDE : seql_side P) by (cbn [seql_side P]; repeat (split; [assumption|]); assumption).
  assert (SEP : seql_sep P) by (cbn [seql_sep P]; repeat (split; [assumption|]); assumption).
  destruct (Z.eq_dec DST 0) as [D0|DN].
  - (* [comment removed for export] *)
    destruct (NUL D0) as (C0 & NB0).
    exact (seql_null P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM SIDE SEP NB0 D0 C0 R1 R2 R12 R13 R14 R16 R17 R15).
  - pose proof (NNUL DN) as R7.
    assert (RG : seql_ranges P) by (cbn [seql_ranges P]; repeat (split; [assumption|]); assumption).
    destruct (Z.eq_dec nbSeq 0) as [NB0|NZ].
    + exact (seql_none P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0).
    + assert (TBL : seql_tables P).
      { cbn [seql_tables P]. destruct (TB NZ) as (T1 & T2 & T3 & T4 & T5 & T6). destruct (OT NZ) as (T7 & T8 & T9). destruct (AT NZ) as (T10 & T11 & T12).
        destruct (ATR NZ) as (T13 & T14 & T15). destruct (TAL NZ) as (T16 & T17 & T18). repeat (split; [assumption|]). assumption. }
      assert (HLBE : wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 (y_LBE P)) by (cbn [P y_ws y_LBE]; destruct LIT as (_ & L2 & _); exact L2).
      assert (HLP : y_LITP P <= y_LITP P <= y_LBE P) by (cbn [P y_LITP y_LBE]; lia).
      apply (seql_entry P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ). intros OEND ST1.
      destruct (Z.eq_dec (zlen (y_sq P)) 0) as [HZ0|HZN].
      { apply (seql_bitinit0 P OEND _ _ _ RG SEP); [cbn [P y_SPV]; exact SP16 | exact HZ0]. }
      assert (HZ1 : 1 <= zlen (y_sq P)) by (clear - HZN; lia).
      specialize (ST1 HZ1).
      destruct (seql_static_oend P _ _ _ _ ST1) as (HOE & HN1).
      pose proof (seql_at_err_ok P OEND (y_LITP P) (y_LBE P) (y_LOC P) RG) as A_err1.
      pose proof (seql_lf_end_ok P _ _ _ _ ST1 RG SEP) as A_end1.
      assert (A_loop : la_head P OEND (y_LITP P) (y_LBE P) (y_LOC P) (y_nbSeq P)).
      { assert (HKN : 1 <= y_nbSeq P <= y_nbSeq P) by (cbn [P y_nbSeq]; lia).
        destruct (Z.eq_dec (y_LOC P) 2) as [L2|LN2].
        - pose proof (seql_static_x P OEND RG SIDE SEP TBL NZ HN1 HOE) as ST2.
          pose proof (seql_at_err_ok P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 RG) as A_err2.
          pose proof (seql_lf_end_ok P _ _ _ _ ST2 RG SEP) as A_end2.
          revert ST1 A_err1 A_end1. rewrite L2. intros ST1 A_err1 A_end1.
          exact (seql_loops_s EXE EXS P OEND (y_LITP P) (y_LBE P) ST1 ST2 HLBE A_err1 A_err2 A_end1 A_end2 (y_nbSeq P) HKN).
        - exact (seql_loops_n EXE P _ _ _ _ ST1 LN2 A_err1 A_end1 (y_nbSeq P) HKN). }
      apply (seql_bitinit P _ _ _ _ ST1 RG).
      apply (seql_ifse_LL P _ _ _ _ ST1). apply (seql_irl_LL P _ _ _ _ ST1).
      apply (seql_ifse_OF P _ _ _ _ ST1). apply (seql_irl_OF P _ _ _ _ ST1).
      apply (seql_ifse_ML P _ _ _ _ ST1). apply (seql_irl_ML P _ _ _ _ ST1).
      apply (seql_ihead P _ _ _ _ ST1 HLP).
      exact A_loop.
Qed.

