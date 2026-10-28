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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_lsw RZ_seq_l_t2_at RZ_seq_l_e2_at seqL3_kit_t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t2_sw0_ok : forall P OEND LLO LEND K, seql_static P OEND LLO LEND 2 -> 1 <= K <= y_nbSeq P ->
  e2_exec P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 K -> t2_sw0 P OEND LLO LEND 2 K.
Proof.
  intros P OEND LLO LEND K ST HK CONT. unfold t2_sw0.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro OP llv mlv ofs idx cidx raddr x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 INV LF HO HL HM HIDX HRING HCI HRA HRL HRM HRO.
  unfold e2_exec in CONT.
  pose proof (seql_linv_switch P OEND LLO LEND m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as SWI.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & (H5V & H5L) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, H5V, HK, HIDX, HRA, CONT, SWI |- *.
  unfold h5_vcells in H5V, SWI.
  assert (SR : 896 <= SPV < 2^47 /\ SPV mod 16 = 0 /\ 4096 <= DCTX /\ DCTX + 30372 + 65536 < 2^47 /\
               (SPV - 688 + 688 <= DCTX + 30096 \/ DCTX + 30096 + 276 <= SPV - 688)).
  { clear - ST. sd_static_open ST. unfold held in S27. split; [exact S17|]. split; [exact AL4|]. split; [exact S19|]. split; [clear - S20; lia|]. clear - S27 S18; lia. }
  destruct SR as (SR1 & SR2 & SR3 & SR4 & DJD).
  assert (MUL : munch [(DCTX + 30368, DCTX + 30368 + 4); (SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst cidx; subst raddr llv mlv ofs;
  [ seql_ring_open 0 FR | seql_ring_open 1 FR | seql_ring_open 2 FR | seql_ring_open 3 FR
  | seql_ring_open 4 FR | seql_ring_open 5 FR | seql_ring_open 6 FR | seql_ring_open 7 FR ].
  all: hold CONT; hold SWI; hold INV; hold LF; hold ST; hold HRING; hold HK; hold HIDX; hold H5L.
  all: kx_autoLx [0x1a080; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange DCTX 4096 (2^47); KZWr (SPV - 688) 688; KZWr (DCTX + 30096) 276; KZDisj (SPV - 688) 688 (DCTX + 30096) 276]
    [(SPV - 688, 688)].
  all: kx_mem.
  all: unfold held in CONT, SWI, INV, LF, ST, HRING, HK, HIDX, H5L.
  all: seql_ring_unopen_any FR.
  all: eapply CONT;
    [ eapply SWI; [exact MUL | exact WMl | exact KXMI | exact FR | exact H5V]
    | unfold seql_lfacts in LF |- *; destruct LF as (Q1 & _ & Q3); split; [exact Q1|]; split; [lia| exact Q3]
    | .. ].
  all: seql_yred.
  all: first [exact HRING | lia].
Qed.
