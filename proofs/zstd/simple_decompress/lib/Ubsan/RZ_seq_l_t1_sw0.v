(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_lsw RZ_seq_l_t1_at RZ_seq_l_e1_at seqL3_kit_t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t1_sw0_ok : forall P OEND LLO LEND K, seql_static P OEND LLO LEND 2 -> 1 <= K <= y_nbSeq P ->
  e1_exec P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K -> t1_sw0 P OEND LLO LEND 2 K.
Proof.
  intros P OEND LLO LEND K ST HK CONT. unfold t1_sw0.
  intros m1 c0 c128 c176 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro OP llv mlv ofs sn cidx dll dml dof raddr x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 INV LF HO HL HM HSN HCI HDL HDM HDO HRING HRA HRL HRM HRO.
  unfold e1_exec in CONT.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, HK, HSN, HRA, CONT |- *.
  assert (SR : 896 <= SPV < 2^47 /\ SPV mod 16 = 0) by (clear - ST; sd_static_open ST; split; [exact S17 | exact AL4]).
  destruct SR as (SR1 & SR2).
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst cidx; subst raddr llv mlv ofs;
  [ seql_ring_open 0 FR | seql_ring_open 1 FR | seql_ring_open 2 FR | seql_ring_open 3 FR
  | seql_ring_open 4 FR | seql_ring_open 5 FR | seql_ring_open 6 FR | seql_ring_open 7 FR ].
  all: hold CONT; hold INV; hold LF; hold ST; hold HRING; hold HK; hold HSN.
  all: kx_autoLx [0x18b3c; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: unfold held in CONT, INV, LF, ST, HRING, HK, HSN.
  all: eapply CONT; [exact INV | exact LF | ..].
  all: seql_yred.
  all: first [exact HRING | lia].
Qed.
