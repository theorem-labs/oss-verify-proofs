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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_skit RZ_seq_l_xat RZ_seq_l_s1_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac s1s_split FR :=
  lazymatch type of FR with rw_cells ?s ?mm ?A ?L =>
    let pre := eval cbv [firstn] in (firstn 47%nat L) in
    let rest := eval cbv [skipn] in (skipn 47%nat L) in
    let lpc := eval cbv [firstn] in (firstn 1%nat rest) in
    let rest2 := eval cbv [skipn] in (skipn 1%nat rest) in
    let sqc := eval cbv [firstn] in (firstn 3%nat rest2) in
    let post := eval cbv [skipn] in (skipn 3%nat rest2) in
    change (rw_cells s mm A (pre ++ lpc ++ sqc ++ post)) in FR
  end.

Lemma s1_slow_ok : zd_execend_split_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  s1_tail P OEND LLO LEND LOCV K -> seql_at_err P OEND LLO LEND LOCV -> s1_slow P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK HLOC CONT1 CONT2. unfold s1_slow.
  intros m1 c0 c128 c176 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ow sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x19 x21 x23 x28 x29 x30 x31 INV LF HO HL HM HOW HLE HSN HCI HDL HDM HDO HRING.
  pose proof (seql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_frame4_merge P OEND) as MERGE.
  pose proof (fun m0 INV0 => seql_linv_slow P OEND LLO LEND LOCV m0 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV0) as SLOW.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold s1_tail in CONT1. unfold seql_at_err in CONT2. unfold zd_execend_split_stmt in EXE.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_frame4 seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, TRANS, MERGE, SLOW |- *.
  sd_static_open ST. hold AL1; hold AL2; hold AL3; hold AL4.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 0 <= llv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL; lia).
  subst ow. assert (LE32 : LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x19038; 0x1abb4; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange PFX 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange LP 4096 (2^47); KZRange llv 0 262143; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1e5d0) _ _ _ _) => (edestruct MERGE as (jseq2 & FRM); [exact FR|];
      pose proof (TRANS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MUL WMl KXMI FRM) as INV0;
      pose proof INV0 as (_ & _ & _ & _ & _ & LIT0 & _ & _ & XI0); cbn [seql_xinv y_B0 y_B1 y_lo y_SPV] in XI0, LIT0; destruct XI0 as (_ & _ & BUF0 & STK0 & _);
      pose proof FR as FRS;
      s1s_split FRS;
      apply rw_cells_app in FRS; destruct FRS as (_ & FRS); apply rw_cells_app in FRS; destruct FRS as (LPC & FRS); apply rw_cells_app in FRS; destruct FRS as (SQC & _);
      cbn [cells_size csize Nat.add] in LPC, SQC;
      replace (SPV + -688 + Z.of_nat 552) with (SPV + -136) in LPC, SQC by lia; replace (SPV + -136 + Z.of_nat 8) with (SPV + -128) in SQC by lia;
      unfold held in S12, S24, S26, AL4;
      eapply evt_cut;
      [ eapply (EXE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (SPV + -688) lo OP OEND (LP + llv - 32) (SPV + -128) (SPV + -136) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
        [ exact BUF0 | lia | lia | lia | lia | lia | lia | exact SQC | exact LPC | lia | lia | lia | lia | lia
        | eapply rdbl_sub; [exact LIT0 | lia | lia]
        | unfold apart; destruct S12 as [A|[A|A]]; [right; lia | left; lia | left; lia]
        | lia | lia | lia | lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart; lia
        | exact STK0 | lia | lia
        | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia
        | clear - AL4; lia | clear - AL4; lia
        | exact KXMI | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | symmetry; apply Z_to_bv_bv_unsigned ]
      | ];
      intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & lp2 & -> & MUc & WMc & MIc & STKc & BUFc & SQCc & LPCc & HR2 & RES);
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end;
      pose proof (SLOW m0 INV0 jpad llv mlv ofs OP m2 lp2 208 FR ltac:(lia) ltac:(lia) MUc WMc MIc STKc BUFc SQCc LPCc) as INV2;
      clear MUc WMc STKc BUFc SQCc LPCc LPC SQC LIT0 BUF0 STK0 FRM INV0 KXMI MUL WMl FR;
      pose proof INV2 as ((jpad2 & jseq3 & FR) & _); cbn [seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR;
    ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold INV2; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x19038; 0x1abb4; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZRange r 0 18446744073709551615]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in INV2; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19038) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | destruct RES as [RE|(RE1 & RE2 & RE3 & RE4)]; [apply zd_is_error_true_iff in RE; exfalso; lia | split; [destruct LF0 as (_ & _ & LFR); split; [cbn [y_DST]; exact L1|]; split; [lia| exact LFR] | lia]] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT2; [exact INV2 | lia | left; apply zd_is_error_true_iff; lia])
      end))
      end).
Qed.
