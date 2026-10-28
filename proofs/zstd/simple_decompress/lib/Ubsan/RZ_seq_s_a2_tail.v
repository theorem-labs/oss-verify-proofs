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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_xat RZ_seq_s_a2_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma a2_tail_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  seqs_at_err P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> a2_head P OEND LLO LEND LOCV K') -> seqs_at_lexit P OEND LLO LEND LOCV -> a2_tail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3. unfold a2_tail.
  intros m1 c0 c8 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x27 x28 x29 x30 x31 INV HR RES.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seqs_at_err in CONT1. unfold seqs_at_lexit in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> a2_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold a2_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, RES, HK, CONT1, CONT2, CONT3 |- *.
  sd_static_open ST.
  assert (RG : 1 <= K <= 98047 /\ 0 <= r <= 18446744073709551615) by (clear - S16 HK HR; lia).
  assert (RX : 2^64 - 120 < r \/ (4096 <= OP < 2^47 /\ 0 <= r /\ OP + r < 2^47)) by (clear - RES HR S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; destruct RES as [RE|((L1 & _) & NE)]; [left; apply zd_is_error_true_iff in RE; lia | right; cbn [v_DST] in L1; lia]).
  clear AL1 AL2 AL3 AL4.
  ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c6fc; 0x1bc38; 0x1c664] 40%nat
    [KZRange SPV 592 (2^47); KZRange K 1 98047; KZRange r 0 18446744073709551615; KZWr (SPV - 384) 384]
    [(SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6fc) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc38) _ _ _ _) => (destruct RES as [RE|(LF & NE)]; [apply zd_is_error_true_iff in RE; exfalso; lia|]; destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7); cbn [v_DST v_nbSeq] in L1, L2, L6; eapply (CONT2 (K - 1)); [lia | lia | exact INV | unfold seqs_lfacts; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq v_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7]])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c664) _ _ _ _) => (destruct RES as [RE|(LF & NE)]; [apply zd_is_error_true_iff in RE; exfalso; lia|]; destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7); cbn [v_DST v_nbSeq] in L1, L2, L6; eapply CONT3; [exact INV | cbn [v_DST]; lia | exact L2 | lia])
      end).
Qed.
