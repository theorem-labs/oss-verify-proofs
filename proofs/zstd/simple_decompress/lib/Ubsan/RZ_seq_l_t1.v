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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_lsw RZ_seq_l_t1_at seqL3_kit_t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t1_lfacts_op : forall P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML,
  seql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> y_DST P <= OP' <= OEND ->
  seql_lfacts P OEND LLO LEND B OP' LP bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML (L1 & L) H. split; [exact H| exact L]. Qed.

Lemma t1_brk_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  seql_at_err P OEND LLO LEND LOCV -> t1_sw0 P OEND LLO LEND LOCV K -> t1_sw P OEND LLO LEND LOCV K -> t1_brk P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 CONT2 CONT3. subst LOCV. unfold t1_brk.
  intros m1 c0 c128 c176 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs sn cidx dll dml dof raddr x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 INV LF HO HL HM HB HSN HCI HDL HDM HDO HRING HRA HRL HRM HRO.
  unfold seql_at_err in CONT1. unfold t1_sw0 in CONT2. unfold t1_sw in CONT3.
  pose proof (seql_linv_switch P OEND LLO LEND m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as SWI.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & (H5V & H5L) & _).
  pose proof LF as (LF1 & LF2 & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, H5V, HK, HSN, HRA, CONT1, CONT2, CONT3, SWI, LF1, LF2 |- *.
  unfold h5_vcells in H5V, SWI.
  assert (SR : 896 <= SPV < 2^47 /\ SPV mod 16 = 0 /\ 4096 <= DCTX /\ DCTX + 30372 + 65536 < 2^47 /\
               (SPV - 688 + 688 <= DCTX + 30096 \/ DCTX + 30096 + 276 <= SPV - 688) /\ 4096 <= OP /\ OEND < 2^47 /\ 4096 <= LP /\ LEND < 2^47).
  { clear - ST LF1 LF2. sd_static_open ST. unfold held in S27. split; [exact S17|]. split; [exact AL4|]. split; [exact S19|]. split; [clear - S20; lia|]. split; [clear - S27 S18; lia|]. clear - LF1 LF2 S1 S2 S3 S4 S5 S6 S7 S9 S11; lia. }
  destruct SR as (SR1 & SR2 & SR3 & SR4 & DJD & SR5 & SR6 & SR7 & SR8).
  assert (MUL : munch [(DCTX + 30368, DCTX + 30368 + 4); (SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  hold CONT1; hold CONT2; hold CONT3; hold SWI; hold INV; hold LF; hold ST; hold ST0; hold HRING; hold HK; hold HSN; hold H5L; hold HRL; hold HRM; hold HRO.
  kx_autoLx [0x1abb4; 0x18b34; 0x1dd78; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange DCTX 4096 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47); KZRange llv 0 (2^18); KZRange raddr 568 (2^47);
     KZWr (SPV - 688) 688; KZWr (DCTX + 30096) 276; KZDisj (SPV - 688) 688 (DCTX + 30096) 276]
    [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  all: kx_mem.
  all: unfold held in CONT1, CONT2, CONT3, SWI, INV, LF, ST, ST0, HRING, HK, HSN, H5L, HRL, HRM, HRO.
  all: sd_diffs.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => eapply CONT1; [exact INV | ..]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18b34) _ _ _ _) =>
        eapply CONT2 with (cidx := cidx) (mlv := mlv) (ofs := ofs);
        [ eapply SWI; [exact MUL | exact WMl | exact KXMI | exact FR | exact H5V]
        | unfold seql_lfacts in LF |- *; destruct LF as (Q1 & _ & Q3); split; [exact Q1|]; split; [seql_yred; lia| exact Q3]
        | .. ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dd78) _ _ _ _) =>
        eapply evt_cut;
        [ eapply seql_dbs_spec; [exact ST0 | exact INV | ..]
        | seql_dbs_intro INV'; eapply CONT3 with (llv := llv) (mlv := mlv) (ofs := ofs) (cidx := cidx); [exact INV' | exact LF | ..] ]
    end.
  all: seql_yred.
  all: first [exact HRING | reflexivity | (left; reflexivity) | (match goal with H : ?a <> ?b |- 0 < _ < _ => clear - H LF2 HB; lia end) | lia].
Qed.
