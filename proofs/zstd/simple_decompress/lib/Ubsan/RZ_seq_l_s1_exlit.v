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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_xat RZ_seq_l_s1_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma s1_exec0 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P -> LOCV = 2 ->
  s1_slow P OEND LLO LEND LOCV K -> s1_lit1 P OEND LLO LEND LOCV K -> s1_exec P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 CONT2. unfold s1_exec.
  intros m1 c0 c128 c176 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 INV LF HO HL HM EI HI HSN HCI HDL HDM HDO HRING.
  unfold s1_slow in CONT1. unfold s1_lit1 in CONT2.
  pose proof (seql_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, L1, L2, CONT1, CONT2, TRANS |- *.
  sd_static_open ST. hold AL1; hold AL2; hold AL3; hold AL4.
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
  subst ile.
  assert (LE32 : LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  ((try hold CONT1; try hold CONT2; try hold TRANS; try hold HK; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold LF0; try hold ST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x190d8] 40%nat
    [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange llv 0 262143; KZRange mlv 0 262143; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in TRANS; try unfold held in HK; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in LF0; try unfold held in ST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x190d8) _ _ _ _) => (eapply CONT1; [exact INV | exact LF0 | exact HO | exact HL | exact HM | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV'; eapply CONT2; [exact INV' | exact LF0 | exact HO | unfold seql_fast; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end).
Qed.

Lemma s1_exec1 : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s1_match P OEND LLO LEND LOCV K -> s1_litloop P OEND LLO LEND LOCV K -> s1_lit1 P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK  CONT1 CONT2. unfold s1_lit1.
  intros m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sl ole sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3  HSN HCI HDL HDM HDO HRING.
  
  unfold s1_match in CONT1. unfold s1_litloop in CONT2.
  pose proof LF as LF0. destruct LF as (L1 & L2 & _). pose proof FAST as FAST0. destruct FAST as (F1 & F2 & F3 & F4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, CONT1, CONT2 |- *.
  sd_static_open ST. hold AL1; hold AL2; hold AL3; hold AL4.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= ole < 2^47 /\ 4096 <= DCTX < 2^47) by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 S19 S20 F1 F2 F3 F4 E3; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange llv 0 262143; KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18a0c) _ _ _ _) => (eapply CONT1; [exact INV | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV';
    ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange llv 0 262143; KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18a0c) _ _ _ _) => (eapply CONT1; [exact INV' | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1943c) _ _ _ _) => (eapply CONT2; [exact INV' | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end).
Qed.

Lemma s1_litloop_aux : forall (k : nat) P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s1_match P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 -> seql_fast OEND LEND OP LP llv mlv -> ile = LP + llv -> sl = llv + mlv -> ole = OP + llv -> 
  OP + 32 <= cur < ole -> src = LP + (cur - OP) + 16 -> sn = y_nbSeq P - K -> 0 <= cidx <= 7 -> 0 <= dll < 2^18 -> 0 <= dml < 2^18 -> 0 <= dof < 2^64 -> seql_ring_ok 8 rl rm ro -> ole - cur <= 32 * (Z.of_nat k + 1) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 cur) (Z_to_bv 64 mlv) (Z_to_bv 64 src) x22 (Z_to_bv 64 ile) (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1943c) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK  CONT1 m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sl ole cur src sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3  HC ES HSN HCI HDL HDM HDO HRING HM.
  all: pose proof CONT1 as CONT0; unfold s1_match in CONT1.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _); pose proof FAST as FAST0; destruct FAST as (F1 & F2 & F3 & F4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, L1, L2, CONT1 |- *.
  all: sd_static_open ST. all: hold AL1; hold AL2; hold AL3; hold AL4.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= ole < 2^47) by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 F1 F2 F3 F4 E3 HC ES; lia).
  - pose proof I as IHk. clear CONT0.
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1943c) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18a0c) _ _ _ _) => (eapply CONT1; [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) => (eapply evt_cut; [eapply seql_copy_spec; [exact ST0 | exact INV1 | cbn [y_DST]; lia | lia | lia | left; cbn [y_B0 y_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x18a0c; 0x1943c; 0x1ac04] 40%nat
    [KZRange SPV 896 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1943c) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK  CONT0); [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18a0c) _ _ _ _) => (eapply CONT1; [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      end))
      end))
      end).
Qed.

Lemma s1_litloop_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  s1_match P OEND LLO LEND LOCV K -> s1_litloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK  CONT1. unfold s1_litloop.
  intros m1 c0 c128 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ile sl ole cur src sn cidx dll dml dof x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3  HC ES HSN HCI HDL HDM HDO HRING.
  eapply (s1_litloop_aux (Z.to_nat (ole - cur)) P OEND LLO LEND LOCV K ST HK  CONT1); try eassumption. lia.
Qed.
