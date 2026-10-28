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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_xat RZ_seq_s_a1_at RZ_seq_s_a2_at RZ_seq_s_tr_at RZ_seq_s_et_at RZ_seq_s_tr RZ_seq_s_tr2 RZ_seq_s_et_exlit RZ_seq_s_et_exmat RZ_seq_s_et_exclose RZ_seq_s_et_slow.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma tr_sw_ok : forall P OEND LLO LEND K, seqs_static P OEND LLO LEND 2 -> 1 <= K <= v_nbSeq P ->
  et_exec P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 K -> tr_sw P OEND LLO LEND 2 K.
Proof.
  intros P OEND LLO LEND K ST HK CONT. unfold tr_sw.
  intros m1 c0 c8 c40 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 INV LF HO HL HM.
  unfold et_exec in CONT.
  pose proof (seqs_linv_switch P OEND LLO LEND m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as SWI.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & (H5V & H5L) & _).
  pose proof LF as LF0.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, H5V, CONT, SWI |- *.
  unfold h5_vcells in H5V, SWI.
  sd_static_open ST.
  assert (RG : 4096 <= DCTX < 2^47 /\ 4096 <= OEND < 2^47 /\ 4000 <= OEND - 32 < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20; lia).
  assert (DJD : SPV - 384 + 384 <= DCTX + 30096 \/ DCTX + 30096 + 276 <= SPV - 384) by (unfold held in S27; clear - S27 S18; lia).
  assert (MUL : munch [(DCTX + 30368, DCTX + 30368 + 4); (SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  ((try hold CONT; try hold SWI; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold H5L; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bacc] 40%nat
    [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47); KZRange OEND 4096 (2^47); KZRange (OEND - 32) 4000 (2^47);
     KZWr (SPV - 384) 384; KZWr (DCTX + 30096) 276; KZDisj (SPV - 384) 384 (DCTX + 30096) 276]
    [(SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT; try unfold held in SWI; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in H5L; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bacc) _ _ _ _) => (replace (OEND + -32) with (OEND - 32) in FR by (clear; lia); eapply CONT; [ eapply SWI; [exact MUL | exact WMl | exact KXMI | exact FR | exact H5V] | unfold seqs_lfacts in LF0 |- *; destruct LF0 as (Q1 & _ & Q3); split; [exact Q1|]; split; [cbn [v_DCTX]; lia| exact Q3] | exact HO | lia | exact HM | lia | reflexivity | cbn [v_DCTX]; lia])
      end).
Qed.

Lemma et_tail_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  seqs_at_err P OEND LLO LEND LOCV -> et_tail2 P OEND LLO LEND LOCV K -> et_tail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold et_tail.
  intros m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 INV HR RES.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seqs_at_err in CONT1. unfold et_tail2 in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, RES, HK, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 0 <= r <= 18446744073709551615) by (clear - HR; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold INV; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c6fc; 0x1bc14] 40%nat
    [KZRange SPV 592 (2^47); KZRange r 0 18446744073709551615]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6fc) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc14) _ _ _ _) => (destruct RES as [RE|(LF & NE)]; [apply zd_is_error_true_iff in RE; exfalso; lia|]; eapply CONT2; [exact INV | exact LF | lia | lia])
      end).
Qed.

Lemma et_stail_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  seqs_at_err P OEND LLO LEND LOCV -> et_tail2 P OEND LLO LEND LOCV K -> et_stail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold et_stail.
  intros m1 c0 c8 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 INV HR RES.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seqs_at_err in CONT1. unfold et_tail2 in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, RES, HK, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 0 <= r <= 18446744073709551615) by (clear - HR; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold INV; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c6fc; 0x1bc14] 40%nat
    [KZRange SPV 592 (2^47); KZRange r 0 18446744073709551615]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6fc) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc14) _ _ _ _) => (destruct RES as [RE|(LF & NE)]; [apply zd_is_error_true_iff in RE; exfalso; lia|]; eapply CONT2; [exact INV | exact LF | lia | lia])
      end).
Qed.

Lemma et_tail2_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  (forall K', 1 <= K' < K -> a2_head P OEND LLO LEND LOCV K') -> seqs_at_lexit P OEND LLO LEND LOCV -> et_tail2 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT2 CONT3. unfold et_tail2.
  intros m1 c0 c8 c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP r x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 INV LF HR0 HR1.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seqs_at_lexit in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> a2_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold a2_head in CONT2.
  pose proof ST as ST0. pose proof LF as (LFa & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, HK, LFa, CONT2, CONT3 |- *.
  sd_static_open ST.
  assert (RG : 1 <= K <= 98047 /\ 0 <= r <= 2^47 /\ 4096 <= OP < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR0 HR1 LFa; lia).
  ((try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold LF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bc38; 0x1c664] 40%nat
    [KZRange SPV 592 (2^47); KZRange K 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in LF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc38) _ _ _ _) => (replace (Z_to_bv 64 18446744073709551599) with (Z_to_bv 64 (-17)) by (apply Z_to_bv_eqm; reflexivity); eapply (CONT2 (K - 1)); [lia | lia | exact INV | destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7); unfold seqs_lfacts; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq v_nbSeq] in *; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7]])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c664) _ _ _ _) => (destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7); cbn [v_DST v_nbSeq] in L1, L6; eapply CONT3; [exact INV | cbn [v_DST]; lia | exact L2 | lia])
      end).
Qed.

(* [comment removed for export] *)
Theorem tr_all : zd_execend_stmt -> forall P OEND LLO LEND,
  seqs_static P OEND LLO LEND 2 -> seqs_static P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 ->
  seqs_at_err P OEND LLO LEND 2 -> seqs_at_err P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 -> seqs_at_lexit P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 ->
  (forall K, 1 <= K <= v_nbSeq P -> a2_head P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 K) ->
  forall K, 1 <= K <= v_nbSeq P -> a1_brk P OEND LLO LEND 2 K.
Proof.
  intros EXE P OEND LLO LEND ST1 ST2 A_err1 A_err2 A_lexit2 A_head2 K HK.
  assert (A_tail2 : et_tail2 P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 K) by (apply (et_tail2_ok P _ _ _ _ K ST2 HK); [intros K' HK'; apply A_head2; lia | exact A_lexit2]).
  pose proof (et_tail_ok P _ _ _ _ K ST2 HK A_err2 A_tail2) as A_tail.
  pose proof (et_stail_ok P _ _ _ _ K ST2 HK A_err2 A_tail2) as A_stail.
  pose proof (et_closeloop_ok P _ _ _ _ K ST2 HK A_tail) as A_closeloop.
  pose proof (et_exec7 P _ _ _ _ K ST2 HK A_tail A_closeloop) as A_close8.
  pose proof (et_exec6 P _ _ _ _ K ST2 HK A_close8) as A_close.
  pose proof (et_matloop_ok P _ _ _ _ K ST2 HK A_tail) as A_matloop.
  pose proof (et_exec3 P _ _ _ _ K ST2 HK eq_refl A_err2 A_tail A_matloop A_close) as A_match.
  pose proof (et_litloop_ok P _ _ _ _ K ST2 HK eq_refl A_match) as A_litloop.
  pose proof (et_exec1 P _ _ _ _ K ST2 HK eq_refl A_match A_litloop) as A_lit1.
  pose proof (et_slow_ok EXE P _ _ _ _ K ST2 HK A_stail) as A_slow.
  pose proof (et_exec0 P _ _ _ _ K ST2 HK A_slow A_lit1) as A_exec.
  pose proof (tr_sw_ok P OEND LLO LEND K ST1 HK A_exec) as A_sw.
  pose proof (tr_w1_ok P _ _ _ _ K ST1 HK A_sw) as A_w1.
  exact (tr_brk_ok P _ _ _ _ K ST1 HK A_err1 A_sw A_w1).
Qed.
