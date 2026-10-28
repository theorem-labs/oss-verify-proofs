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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_s2_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma s2_exec6 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s2_close8 P OEND LLO LEND LOCV K -> s2_close P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold s2_close.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl ofs mtc q idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 INV LF MF HO HOF HM HQ0 HQ HIDX HRING.
  pose proof (seql_linv_buf P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & _).
  unfold s2_close8 in CONT1.
  pose proof LF as LF0. pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, M1, HOF, BUF, CONT1, STEP |- *.
  sd_static_open ST.
  assert (MUL : munch [(ole, ole + 8)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= mtc < 2^47 /\ B0 <= mtc /\ ole + 8 <= B1 /\ DST <= ole /\ ole + 8 <= OEND)
    by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; lia).
  assert (CASES : ofs = 0 \/ ofs = 1 \/ ofs = 2 \/ ofs = 3 \/ ofs = 4 \/ ofs = 5 \/ ofs = 6 \/ ofs = 7 \/ 8 <= ofs <= 15) by (clear - HO; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 0) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole, 8)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 1) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 1) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 1, 9)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 2) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 2) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 2, 10)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 3) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 3) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 3, 11)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 4) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 4) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 4, 12)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 5) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 5) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 5, 13)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 6) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 6) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 6, 14)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 7) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 7) 4096 (2^47);
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 7, 15)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - (* [comment removed for export] *)
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a814; 0x1ac04] 120%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange mtc 4096 (2^47); KZRange ofs 8 15;
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(mtc, 8)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a814) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma s2_exec7 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s2_stail P OEND LLO LEND LOCV K -> s2_closeloop P OEND LLO LEND LOCV K -> s2_close8 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold s2_close8.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl rip8 ofs q idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 INV LF MF HR1 HR2 HO HQ0 HQ HIDX HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  unfold s2_stail in CONT1. unfold s2_closeloop in CONT2.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & _). pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, M1, HR1, HQ, CONT1, CONT2, TRANS |- *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4000 <= rip8 < 2^47 /\ 8 <= ole - rip8 <= 15 /\ 4096 <= PFX < 2^47 /\ 0 <= q < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HR1 HR2 HQ0 HQ; lia).
  ((try hold CONT1; try hold CONT2; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a1a4; 0x1a86c; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZRange ole 4096 (2^47); KZRange rip8 4000 (2^47); KZRange mlv 0 (2^18); KZRange (ole - rip8) 8 15;
     KZRange PFX 4096 (2^47); KZRange q 0 (2^47); KZRange ofs 0 15; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1a4) _ _ _ _) => (eapply CONT1; [exact INV | lia | right; split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a86c) _ _ _ _) => (eapply CONT2 with (ole := ole) (mlv := mlv); [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact LF0 | exact MF0 | lia | lia | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- _ => (exfalso; lia)
      end).
Qed.

Lemma s2_closeloop_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s2_stail P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (idx : Z) (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl -> ome = ole + mlv -> ole + 8 <= cur < ome -> y_PFX P <= rsrc -> 8 <= cur - rsrc <= 15 ->
  idx = y_nbSeq P - K -> seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro -> ome - cur <= 8 * (Z.of_nat k + 1) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) (Z_to_bv 64 rsrc) x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 cur) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 ome) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a86c) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK CONT1 m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl cur rsrc ome idx x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 INV LF MF EM HC HS HD HIDX HRING HM.
  all: pose proof CONT1 as CONT0; unfold s2_stail in CONT1.
  all: pose proof (seql_linv_buf P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  all: pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (BUF & _).
  all: pose proof INV as ((jpad & jseq & FR) & _).
  all: pose proof LF as LF0; destruct LF as (L1 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, M1, HS, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (MUL : munch [(cur, cur + 8)] m1 m1) by apply munch_refl; assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= rsrc < 2^47 /\ 4096 <= ome < 2^47 /\ B0 <= rsrc /\ rsrc + 8 <= B1 /\ B0 <= cur /\ cur + 8 <= B1 /\ DST <= cur /\ cur + 8 <= OEND)
         by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 EM HC HS HD; lia).
  all: assert (DJF : cur + 8 <= SPV - 688 \/ SPV - 688 + 688 <= cur) by (unfold held in S24; clear - S24 S18 RG; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a86c; 0x1a1a4; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8;
     KZDisj cur 8 (SPV - 688) 688]
    [(rsrc, 8); (SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a86c) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1a4) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1a86c; 0x1a1a4; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8;
     KZDisj cur 8 (SPV - 688) 688]
    [(rsrc, 8); (SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a86c) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK CONT0) with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | lia | lia | cbn [y_PFX]; lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1a4) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma s2_closeloop_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s2_stail P OEND LLO LEND LOCV K -> s2_closeloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold s2_closeloop.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl cur rsrc ome idx x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 INV LF MF EM HC HS HD HIDX HRING.
  eapply (s2_closeloop_aux (Z.to_nat (ome - cur)) P OEND LLO LEND LOCV K ST HK CONT1); try eassumption. lia.
Qed.
