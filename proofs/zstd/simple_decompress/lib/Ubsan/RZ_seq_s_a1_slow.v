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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_skit RZ_seq_s_xat RZ_seq_s_a1_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma a1_slow_ok : zd_execend_split_stmt -> forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LOCV = 2 ->
  a1_tail P OEND LLO LEND LOCV K -> a1_slow P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK HLOC CONT1. unfold a1_slow.
  intros m1 c0 c8 c40 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ow x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x28 x29 x30 x31 INV LF HO HL HM HOW HLE.
  pose proof (seqs_linv_frame P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqs_frame4_merge P OEND) as MERGE.
  pose proof (fun m0 INV0 => seqs_linv_slow P OEND LLO LEND LOCV m0 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV0) as SLOW.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold a1_tail in CONT1. unfold zd_execend_split_stmt in EXE.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_frame4 seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, L1, L2, CONT1, TRANS, MERGE, SLOW |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 0 <= llv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL; lia).
  subst ow. assert (LE32 : LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML; try hold AL1; try hold AL2; try hold AL3; try hold AL4);
    kx_autoLx [0x1e5d0] 40%nat
    [KZRange SPV 592 (2^47); KZRange OP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange PFX 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange LP 4096 (2^47); KZRange llv 0 262143; KZWr (SPV - 384) 384]
    [(SPV - 384, 384)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1e5d0) _ _ _ _) => (edestruct MERGE as (jseq2 & FRM); [exact FR|];
      pose proof (TRANS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MUL WMl KXMI FRM) as INV0;
      pose proof INV0 as (_ & _ & _ & _ & _ & LIT0 & _ & _ & XI0); cbn [seqs_xinv v_B0 v_B1 v_lo v_SPV] in XI0, LIT0; destruct XI0 as (_ & _ & BUF0 & STK0 & _);
      pose proof FR as FRS;
      change (rw_cells usegs m0 (SPV + -384) ([C8 c0; C8 c8; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 DCTX); C8 c40; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (DCTX + 29896)); C8 (Z_to_bv 64 (2^60)); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 K); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2] ++ [C8 (Z_to_bv 64 LP)] ++ [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ++ [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FRS;
      apply rw_cells_app in FRS; destruct FRS as (_ & FRS); apply rw_cells_app in FRS; destruct FRS as (LPC & FRS); apply rw_cells_app in FRS; destruct FRS as (SQC & _);
      cbn [cells_size csize Nat.add] in LPC, SQC;
      replace (SPV + -384 + Z.of_nat 248) with (SPV + -136) in LPC, SQC by lia; replace (SPV + -136 + Z.of_nat 8) with (SPV + -128) in SQC by lia;
      unfold held in S12, S24, S26;
      eapply evt_cut;
      [ eapply (EXE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (SPV + -384) lo OP OEND (LP + llv - 32) (SPV + -128) (SPV + -136) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
        [ exact BUF0 | lia | lia | lia | lia | lia | lia | exact SQC | exact LPC | lia | lia | lia | lia | lia
        | eapply rdbl_sub; [exact LIT0 | lia | lia]
        | unfold apart; destruct S12 as [A|[A|A]]; [right; lia | left; lia | left; lia]
        | lia | lia | lia | lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart; lia
        | exact STK0 | lia | lia
        | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia
        | clear - AL4; try unfold held in AL4; lia | clear - AL4; try unfold held in AL4; lia
        | exact KXMI | reflexivity | reflexivity | first [reflexivity | f_equal; lia] | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned ]
      | ];
      intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & lp2 & -> & MUc & WMc & MIc & STKc & BUFc & SQCc & LPCc & HR2 & RES);
      lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end;
      pose proof (SLOW m0 INV0 jpad llv mlv ofs OP m2 lp2 208 FR ltac:(lia) ltac:(lia) MUc WMc MIc STKc BUFc SQCc LPCc) as INV2;
      clear MUc WMc STKc BUFc SQCc LPCc LPC SQC LIT0 BUF0 STK0 FRM INV0 KXMI MUL WMl FR;
      pose proof INV2 as ((jpad2 & jseq3 & FR) & _); cbn [seqs_frame v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in FR;
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold INV2; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1b3a8] 20%nat
    [KZRange SPV 592 (2^47); KZRange r 0 18446744073709551615]
    [(SPV - 384, 384)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in INV2; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1b3a8) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | destruct RES as [RE|(RE1 & RE2 & RE3 & RE4)]; [left; exact RE | right; split; [destruct LF0 as (_ & _ & LFR); split; [cbn [v_DST]; exact L1|]; split; [lia| exact LFR] | lia]]])
      end))
      end).
Qed.
