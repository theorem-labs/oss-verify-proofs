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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_xat RZ_seq_s_et_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma et_exec6 : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  et_close8 P OEND LLO LEND LOCV K -> et_close P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold et_close.
  intros m1 c0 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs mtc dpx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 INV LF MF HO HOF HM HD.
  pose proof (seqs_linv_buf P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  unfold et_close8 in CONT1.
  pose proof LF as LF0. pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, M1, HOF, HD, BUF, CONT1, STEP |- *.
  sd_static_open ST.
  assert (MUL : munch [(ole, ole + 8)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= mtc < 2^47 /\ B0 <= mtc /\ ole + 8 <= B1 /\ DST <= ole /\ ole + 8 <= OEND)
    by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; lia).
  assert (CASES : ofs = 0 \/ ofs = 1 \/ ofs = 2 \/ ofs = 3 \/ ofs = 4 \/ ofs = 5 \/ ofs = 6 \/ ofs = 7 \/ 8 <= ofs <= 15) by (clear - HO; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 0) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole, 8)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 1) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 1) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 1, 9)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 2) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 2) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 2, 10)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 3) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 3) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 3, 11)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 4) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 4) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 4, 12)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 5) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 5) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 5, 13)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 6) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 6) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 6, 14)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 7) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 7) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 7, 15)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
  - (* [comment removed for export] *)
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c93c] 80%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange mtc 4096 (2^47); KZRange ofs 8 15;
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(mtc, 8)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c93c) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
Qed.

Lemma et_exec7 : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  et_tail P OEND LLO LEND LOCV K -> et_closeloop P OEND LLO LEND LOCV K -> et_close8 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold et_close8.
  intros m1 c0 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs dpx rip8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 INV LF MF HO HD HR1 HR2.
  unfold et_tail in CONT1. unfold et_closeloop in CONT2.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & _). pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, L1, M1, HR1, HD, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= ole < 2^47 /\ 4000 <= rip8 < 2^47 /\ 8 <= ole - rip8 <= 15 /\ 0 <= dpx < 2^47 /\ 0 <= ofs < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HR1 HR2 HO HD; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bc00; 0x1c990] 40%nat
    [KZRange SPV 592 (2^47); KZRange ole 4096 (2^47); KZRange rip8 4000 (2^47); KZRange mlv 0 262143; KZRange (ole - rip8) 8 15; KZRange dpx 0 (2^47); KZRange ofs 0 (2^47)]
    [(SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc00) _ _ _ _) => (eapply CONT1; [exact INV | lia | right; split; [exact LF0 | lia]])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c990) _ _ _ _) => (eapply CONT2 with (ole := ole) (mlv := mlv); [exact INV | exact LF0 | exact MF0 | lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia | cbn [v_PFX]; lia])
      end).
Qed.

Lemma et_closeloop_aux : forall (k : nat) P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  et_tail P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl -> ome = ole + mlv -> ole + 8 <= cur < ome -> v_PFX P <= rsrc -> 8 <= cur - rsrc <= 15 ->
  ome - cur <= 8 * (Z.of_nat k + 1) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 cur) (Z_to_bv 64 9) (Z_to_bv 64 rsrc) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 (Z_to_bv 64 rsrc) x22 (Z_to_bv 64 ome) x24 x25 x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c990) (v_fc P) None m1 (seg_rom usegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK CONT1 m1 c0 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl cur rsrc ome x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV LF MF EM HC HS HD HM.
  all: pose proof CONT1 as CONT0; unfold et_tail in CONT1.
  all: pose proof (seqs_linv_buf P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  all: pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  all: pose proof INV as ((jpad & jseq & FR) & _).
  all: pose proof LF as LF0; destruct LF as (L1 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqs_static seqs_frame seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, L1, M1, HS, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (MUL : munch [(cur, cur + 8)] m1 m1) by apply munch_refl; assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= rsrc < 2^47 /\ 4096 <= ome < 2^47 /\ B0 <= rsrc /\ rsrc + 8 <= B1 /\ B0 <= cur /\ cur + 8 <= B1 /\ DST <= cur /\ cur + 8 <= OEND)
         by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 EM HC HS HD; lia).
  all: assert (DJF : cur + 8 <= SPV - 384 \/ SPV - 384 + 384 <= cur) by (unfold held in S24; clear - S24 S18 RG; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c990; 0x1bc00] 60%nat
    [KZRange SPV 592 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8;
     KZDisj cur 8 (SPV - 384) 384]
    [(rsrc, 8); (SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c990) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc00) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia]])
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c990; 0x1bc00] 60%nat
    [KZRange SPV 592 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8;
     KZDisj cur 8 (SPV - 384) 384]
    [(rsrc, 8); (SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c990) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK CONT0) with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | lia | lia | cbn [v_PFX]; lia | lia | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc00) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia]])
      end).
Qed.

Lemma et_closeloop_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  et_tail P OEND LLO LEND LOCV K -> et_closeloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold et_closeloop.
  intros m1 c0 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl cur rsrc ome x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV LF MF EM HC HS HD.
  eapply (et_closeloop_aux (Z.to_nat (ome - cur)) P OEND LLO LEND LOCV K ST HK CONT1); try eassumption. lia.
Qed.
