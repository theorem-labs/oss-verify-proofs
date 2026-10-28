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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_rkit RZ_seq_l_xat RZ_seq_l_md_at RZ_seq_l_lm_at RZ_seq_l_n1_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma lm_mode_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  lm_msplit P OEND LLO LEND LOCV K -> lm_mnorm P OEND LLO LEND LOCV K -> md_exec P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2. unfold md_exec.
  intros m1 c0 c128 c176 c232 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs sn x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 INV LF HO HL HM HSN HRING.
  unfold lm_msplit in CONT1. unfold lm_mnorm in CONT2.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & (H5C & H5L) & _).
  pose proof LF as LF0.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, H5C, HK, HSN, CONT1, CONT2, TRANS |- *.
  unfold h5_vcells in H5C.
  sd_static_open ST.
  assert (RG : 4096 <= DCTX < 2^47 /\ 0 <= LOCV <= 2 /\ 0 <= sn <= 98047) by (clear - S16 S19 S20 S41 HK HSN; lia).
  assert (DJD : SPV - 688 + 688 <= DCTX \/ DCTX + 95992 <= SPV - 688) by (unfold held in S27; clear - S27 S18; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold TRANS; try hold HRING; try hold HSN; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x188d8; 0x18e84; 0x1ac04] 30%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange DCTX 4096 (2^47); KZRange LOCV 0 2; KZRange sn 0 98047; KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992]
    [(SPV - 688, 688); (DCTX + 30096, 276)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in HSN; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x188d8) _ _ _ _) => (eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact LF0 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18e84) _ _ _ _) => (eapply CONT2; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | exact LF0 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma lm_mnorm_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  n1_exec P OEND LLO LEND LOCV K -> lm_mnorm P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT. unfold lm_mnorm.
  intros m1 c0 c128 c176 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP sn cidx dll dml dof x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 INV LF HSN HCI HDL HDM HDO HRING HCL HNLOC.
  unfold n1_exec in CONT.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, HK, HSN, CONT |- *.
  sd_static_open ST.
  clear HCL.
  match type of FR with rw_cells _ _ _ ?l => replace l with (firstn 46 l ++ nth 46 l (C8 c0) :: skipn 47 l) in FR by reflexivity end. cbn [firstn skipn nth] in FR.
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HCI; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
  - subst cidx. pose proof (HRING 0 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_0 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 0); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 1 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_1 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 1); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 2 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_2 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 2); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 3 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_3 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 3); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 4 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_4 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 4); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 5 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_5 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 5); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 6 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_6 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 6); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
  - subst cidx. pose proof (HRING 7 ltac:(lia)) as (RR1 & RR2 & RR3). apply (seql_ring_open_7 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    ((try hold CONT; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold HRING; try hold HSN; try hold HNLOC; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18eb8; 0x1ac04] 20%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in HRING; try unfold held in HSN; try unfold held in HNLOC; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18eb8) _ _ _ _) => (eapply CONT with (cidx := 7); [exact INV | exact LF0 | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.
