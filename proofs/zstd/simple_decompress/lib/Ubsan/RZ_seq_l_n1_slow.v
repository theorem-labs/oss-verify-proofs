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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_skit RZ_seq_l_xat RZ_seq_l_n1_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma n1_frame4_cells : forall P OEND (m : fmem) c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad llv mlv ofs,
  rw_cells usegs m (y_SPV P + -688) (seql_frame4 P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad llv mlv ofs) ->
  rw_cells usegs m (y_SPV P + -136) [C8 (Z_to_bv 64 LP)] /\ rw_cells usegs m (y_SPV P + -128) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)].
Proof.
  intros P OEND m c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad llv mlv ofs FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_frame4 y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR.
  apply rw_cells_app in FR. destruct FR as (_ & REST). apply rw_cells_app in REST. destruct REST as (LPC & REST).
  apply rw_cells_app in REST. destruct REST as (SQC & _).
  cbn [cells_size csize Nat.add app] in LPC, SQC.
  match type of LPC with rw_cells _ _ ?a _ => replace a with (SPV + -136) in LPC by lia end.
  match type of SQC with rw_cells _ _ ?a _ => replace a with (SPV + -128) in SQC by lia end.
  split; [exact LPC | exact SQC].
Qed.

Lemma n1_slow_ok : zd_execend_stmt -> forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  n1_tail P OEND LLO LEND LOCV K -> seql_at_err P OEND LLO LEND LOCV -> n1_slow P OEND LLO LEND LOCV K.
Proof.
  intros EXE P OEND LLO LEND LOCV K ST HK  CONT1 CONT2. unfold n1_slow.
  intros m1 c0 c128 c176 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x28 x29 x30 x31 INV LF HO HL HM  HSN HCI HDL HDM HDO HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_frame4_merge P OEND) as MERGE. pose proof (n1_frame4_cells P OEND) as F4C.
  pose proof (fun m0 INV0 => seql_linv_slow P OEND LLO LEND LOCV m0 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV0) as SLOW.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold n1_tail in CONT1. unfold seql_at_err in CONT2. unfold zd_execend_stmt in EXE.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_frame4 seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, TRANS, MERGE, F4C, SLOW |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 0 <= llv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL; lia).
  
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold F4C; try hold SLOW; try hold L2; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x19038; 0x1abb4; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange OP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange PFX 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange LP 4096 (2^47); KZRange llv 0 262143; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in F4C; try unfold held in SLOW; try unfold held in L2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dfe4) _ _ _ _) => (edestruct MERGE as (jseq2 & FRM); [exact FR|];
      pose proof (TRANS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MUL WMl KXMI FRM) as INV0;
      pose proof INV0 as (_ & _ & _ & _ & _ & LIT0 & _ & _ & XI0); cbn [seql_xinv y_B0 y_B1 y_lo y_SPV] in XI0, LIT0; destruct XI0 as (_ & _ & BUF0 & STK0 & _);
      edestruct F4C as (LPC & SQC); [exact FR|];
      unfold held in S12, S24, S26;
      eapply evt_cut;
      [ eapply (EXE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (SPV + -688) lo OP OEND (SPV + -128) (SPV + -136) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
        [ exact BUF0 | lia | lia | lia | lia | exact SQC | exact LPC | lia | lia | lia | lia | unfold WILDCOPY_OVERLENGTH; lia
        | eapply rdbl_sub; [exact LIT0 | lia | unfold WILDCOPY_OVERLENGTH; lia]
        | unfold apart, WILDCOPY_OVERLENGTH; destruct S12 as [A|[A|A]]; [right; lia | left; lia | left; lia]
        | lia | lia | lia | lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart, WILDCOPY_OVERLENGTH; lia
        | exact STK0 | lia | lia
        | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack; lia | unfold off_stack, WILDCOPY_OVERLENGTH; lia
        | clear - AL4; lia | clear - AL4; lia
        | exact KXMI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned ]
      | ];
      intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & lp2 & -> & MUc & WMc & MIc & STKc & BUFc & SQCc & LPCc & HR2 & RES);
      replace (ret_pc (Z_to_bv 64 0x190c0)) with (Z_to_bv 64 0x190c0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]);
      pose proof (SLOW m0 INV0 jpad llv mlv ofs OP m2 lp2 192 FR ltac:(lia) ltac:(lia) MUc WMc MIc STKc BUFc SQCc LPCc) as INV2;
      clear MUc WMc STKc BUFc SQCc LPCc LPC SQC LIT0 BUF0 STK0 FRM INV0 KXMI MUL WMl FR F4C;
      pose proof INV2 as ((jpad2 & jseq3 & FR) & _); cbn [seql_frame y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR;
    ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold TRANS; try hold EXE; try hold MERGE; try hold SLOW; try hold L2; try hold INV2; try hold RES; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x19038; 0x1abb4; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange r 0 18446744073709551615]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in EXE; try unfold held in MERGE; try unfold held in SLOW; try unfold held in L2; try unfold held in INV2; try unfold held in RES; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19038) _ _ _ _) => (eapply CONT1; [exact INV2 | lia | destruct RES as [RE|(RE1 & RE2 & RE3 & RE4)]; [apply zd_is_error_true_iff in RE; lia | split; [destruct LF0 as (_ & _ & LFR); split; [cbn [y_DST]; exact L1|]; split; [lia| exact LFR] | lia]] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT2; [exact INV2 | lia | left; apply zd_is_error_true_iff; lia])
      end))
      end).
Qed.
