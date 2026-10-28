(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_none RZ_seq_d_lbase RZ_seq_d_ibase RZ_seq_d_ient RZ_seq_d_ient2 RZ_seq_d_ibit RZ_seq_d_ifse RZ_seq_d_irl RZ_seq_d_loop.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem zd_seq_default_proof : zd_execend_stmt -> zd_seq_default_stmt.
Proof.
  intros EXE. unfold zd_seq_default_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws.
  intros DCX LIT R1 R2 R3 SQB AB R4 R5 R6 TB BUF R7 PF R8 R9 R10 DZ DNZ LOCD R11 R12 R13 LRD INDST NOTIN STK R14 R15 R16 O1 O2 O3 O4 OT A1 A2 AT A3 A4 ATR AL16 AL4 MI.
  intros -> -> -> -> -> ->.
  set (P := mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws).
  assert (MEM : seqd_mem P) by (cbn [seqd_mem P]; repeat (split; [assumption|]); assumption).
  assert (RG : seqd_ranges P) by (cbn [seqd_ranges P]; repeat (split; [assumption|]); assumption).
  assert (SIDE : seqd_side P) by (cbn [seqd_side P]; repeat (split; [assumption|]); assumption).
  assert (SEP : seqd_sep P) by (cbn [seqd_sep P]; repeat (split; [assumption|]); assumption).
  destruct (Z.eq_dec nbSeq 0) as [NB0|NZ].
  - exact (seq_none P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0).
  - assert (TBL : seqd_tables P).
    { cbn [seqd_tables P]. destruct (TB NZ) as (T1 & T2 & T3 & T4 & T5 & T6). destruct (OT NZ) as (T7 & T8 & T9). destruct (AT NZ) as (T10 & T11 & T12).
      destruct (ATR NZ) as (T13 & T14 & T15). repeat (split; [assumption|]). assumption. }
    apply (seqd_entry P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ AL16 (AL4 NZ)). intros OEND LEND ST.
    apply (seqd_bitinit P OEND LEND ST RG).
    apply (seqd_ifse_LL P OEND LEND ST). apply (seqd_irl_LL P OEND LEND ST).
    apply (seqd_ifse_OF P OEND LEND ST). apply (seqd_irl_OF P OEND LEND ST).
    apply (seqd_ifse_ML P OEND LEND ST). apply (seqd_irl_ML P OEND LEND ST).
    apply (seqd_i7ac P OEND LEND ST).
    apply (seqd_loop EXE P OEND LEND ST RG SEP). cbn [q_nbSeq P]. lia.
Qed.
