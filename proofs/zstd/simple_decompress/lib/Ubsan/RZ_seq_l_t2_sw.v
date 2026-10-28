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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_lsw RZ_seq_l_t2_at seqL3_kit_t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t2_sw_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  t2_sw0 P OEND LLO LEND LOCV K -> t2_sw P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT. unfold t2_sw.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs lft idx cidx raddr x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x27 x28 x29 x30 x31 INV LF HO HL HM HLF HLT HOE HIDX HRING HCI HRA HRL HRM HRO.
  unfold t2_sw0 in CONT.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as (LF1 & LF2 & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, HK, HIDX, HRA, CONT, TRANS, LF1, LF2 |- *.
  assert (SR : 896 <= SPV < 2^47 /\ SPV mod 16 = 0 /\ 4096 <= DCTX /\ DCTX + 30372 + 65536 < 2^47 /\ 4096 <= OP /\ OEND < 2^47).
  { clear - ST LF1. sd_static_open ST. split; [exact S17|]. split; [exact AL4|]. split; [exact S19|]. split; [clear - S20; lia|]. clear - LF1 S1 S2 S3 S4 S5 S6 S7; lia. }
  destruct SR as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst cidx; subst raddr;
  [ seql_ring_open_eq 0 FR HRL HRM HRO | seql_ring_open_eq 1 FR HRL HRM HRO | seql_ring_open_eq 2 FR HRL HRM HRO | seql_ring_open_eq 3 FR HRL HRM HRO
  | seql_ring_open_eq 4 FR HRL HRM HRO | seql_ring_open_eq 5 FR HRL HRM HRO | seql_ring_open_eq 6 FR HRL HRM HRO | seql_ring_open_eq 7 FR HRL HRM HRO ].
  all: hold CONT; hold TRANS; hold INV; hold LF; hold ST; hold HRING; hold HK; hold HIDX; hold HRL; hold HRM; hold HRO.
  all: kx_autoLx [0x1a074; 0x1ac04] 30%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange DCTX 4096 (2^47); KZRange OP 4096 (2^47); KZRange lft 1 (2^18); KZRange llv 1 (2^18); KZRange (llv - lft) 0 (2^18);
     KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  all: kx_mem.
  all: unfold held in CONT, TRANS, INV, LF, ST, HRING, HK, HIDX, HRL, HRM, HRO.
  all: seql_ring_close_any FR.
  all: lazymatch type of FR with context [ring_upd _ ?k _] =>
    eapply CONT with (cidx := k) (mlv := mlv) (ofs := ofs);
    [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
    | unfold seql_lfacts in LF |- *; destruct LF as (Q1 & Q2 & Q3); split; [lia|]; split; [lia| exact Q3]
    | .. ] end.
  all: seql_yred.
  all: first [ eapply seql_ring_ok_upd; [exact HRING | lia | lia | lia] | (unfold ring_upd; cbn [Z.eqb Pos.eqb]; lia) | lia ].
Qed.
