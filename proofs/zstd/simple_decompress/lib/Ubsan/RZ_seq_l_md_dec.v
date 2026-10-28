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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_md_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma md_decode : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  md_dec P OEND LLO LEND LOCV K -> md_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT. unfold md_head.
  intros m1 c0 c128 c176 c216 c224 c232 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP sn x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x29 INV LF HSN HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  destruct (seql_linv_cells P OEND LLO LEND LOCV _ m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OP ST INV LF) as (nLL & aLL & bLL & vLL & nOF & aOF & bOF & vOF & nML & aML & bML & vML & WLL & WOF & WML & CF).
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold md_dec in CONT.
  destruct INV as ((jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct CF as (NX & N1 & N2 & N3 & A1 & A2 & A3 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST.
  destruct WLL as (WLL0 & WLL1 & WLL2 & WLL3). destruct WOF as (WOF0 & WOF1 & WOF2 & WOF3). destruct WML as (WML0 & WML1 & WML2 & WML3).
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  assert (RS : 0 <= sLL <= 511 /\ 0 <= sOF <= 511 /\ 0 <= sML <= 511 /\ 0 <= bc <= 9900000) by (clear - L3 L4 L5 L6 PLL POF PML HK S16; lia).
  assert (RV : 0 <= vLL <= 131072 /\ 0 <= vML <= 131075 /\ 0 <= vOF <= 4294967294 /\ 0 <= vLL < 2^17 /\ 0 <= vML + 2^aML < 2^18 /\ 0 < 2^aML).
  { clear - V1 V2 V3 V4 V5 V6 A1 A2 A3. pose proof (Z.pow_pos_nonneg 2 aLL). pose proof (Z.pow_pos_nonneg 2 aOF). pose proof (Z.pow_pos_nonneg 2 aML). lia. }
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (CASES : (aOF = 0 /\ vOF = 0) \/ (aOF = 1 /\ vOF = 1) \/ 2 <= aOF) by (clear - A2 V7 V8; lia).
  try hold TRANS. try hold CONT. try hold LF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold L7. try hold NX. try hold V1. try hold V2. try hold V3. try hold V4. try hold V5. try hold V6. try hold V7. try hold V8. try hold NX3. try hold NX6. try hold NX9. try hold PLL. try hold POF. try hold PML.
  destruct CASES as [[C C']|[[C C']|C]].
  - kx_autoLx [0x185f0; 0x1ac04] 240%nat
    [KZRange SPV 896 (2^47); KZRange LLT 4096 (2^47); KZRange OFT 4096 (2^47); KZRange MLT 4096 (2^47); KZAlign LLT 4; KZAlign OFT 4; KZAlign MLT 4; KZAlign SPV 16;
     KZRange sLL 0 511; KZRange sOF 0 511; KZRange sML 0 511; KZRange bc 0 9900000;
     KZRange nLL 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange vLL 0 131072;
     KZRange nOF 0 511; KZRange aOF 0 0; KZRange bOF 0 9; KZRange vOF 0 0;
     KZRange nML 0 511; KZRange aML 0 16; KZRange bML 0 9; KZRange vML 0 131075;
     KZWord (LLT + 8 * sLL + 8) 2 nLL; KZWord (LLT + 8 * sLL + 10) 1 aLL; KZWord (LLT + 8 * sLL + 11) 1 bLL; KZWord (LLT + 8 * sLL + 12) 4 vLL;
     KZWord (OFT + 8 * sOF + 8) 2 nOF; KZWord (OFT + 8 * sOF + 10) 1 aOF; KZWord (OFT + 8 * sOF + 11) 1 bOF; KZWord (OFT + 8 * sOF + 12) 4 vOF;
     KZWord (MLT + 8 * sML + 8) 2 nML; KZWord (MLT + 8 * sML + 10) 1 aML; KZWord (MLT + 8 * sML + 11) 1 bML; KZWord (MLT + 8 * sML + 12) 4 vML;
     KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: sd_rbf.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in LF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX; try unfold held in V1; try unfold held in V2; try unfold held in V3; try unfold held in V4; try unfold held in V5; try unfold held in V6; try unfold held in V7; try unfold held in V8; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in PLL; try unfold held in POF; try unfold held in PML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | eapply seql_lfacts_bc; [exact LF0 | lia]
      | exact NX | lia | lia | lia | lia | lia  | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]).

  - kx_autoLx [0x185f0; 0x1ac04] 240%nat
    [KZRange SPV 896 (2^47); KZRange LLT 4096 (2^47); KZRange OFT 4096 (2^47); KZRange MLT 4096 (2^47); KZAlign LLT 4; KZAlign OFT 4; KZAlign MLT 4; KZAlign SPV 16;
     KZRange sLL 0 511; KZRange sOF 0 511; KZRange sML 0 511; KZRange bc 0 9900000;
     KZRange nLL 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange vLL 0 131072;
     KZRange nOF 0 511; KZRange aOF 1 1; KZRange bOF 0 9; KZRange vOF 1 1;
     KZRange nML 0 511; KZRange aML 0 16; KZRange bML 0 9; KZRange vML 0 131075;
     KZWord (LLT + 8 * sLL + 8) 2 nLL; KZWord (LLT + 8 * sLL + 10) 1 aLL; KZWord (LLT + 8 * sLL + 11) 1 bLL; KZWord (LLT + 8 * sLL + 12) 4 vLL;
     KZWord (OFT + 8 * sOF + 8) 2 nOF; KZWord (OFT + 8 * sOF + 10) 1 aOF; KZWord (OFT + 8 * sOF + 11) 1 bOF; KZWord (OFT + 8 * sOF + 12) 4 vOF;
     KZWord (MLT + 8 * sML + 8) 2 nML; KZWord (MLT + 8 * sML + 10) 1 aML; KZWord (MLT + 8 * sML + 11) 1 bML; KZWord (MLT + 8 * sML + 12) 4 vML;
     KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: sd_rbf.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in LF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX; try unfold held in V1; try unfold held in V2; try unfold held in V3; try unfold held in V4; try unfold held in V5; try unfold held in V6; try unfold held in V7; try unfold held in V8; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in PLL; try unfold held in POF; try unfold held in PML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | eapply seql_lfacts_bc; [exact LF0 | lia]
      | exact NX | lia | lia | lia | lia | lia  | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]).

  - kx_autoLx [0x185f0; 0x1ac04] 240%nat
    [KZRange SPV 896 (2^47); KZRange LLT 4096 (2^47); KZRange OFT 4096 (2^47); KZRange MLT 4096 (2^47); KZAlign LLT 4; KZAlign OFT 4; KZAlign MLT 4; KZAlign SPV 16;
     KZRange sLL 0 511; KZRange sOF 0 511; KZRange sML 0 511; KZRange bc 0 9900000;
     KZRange nLL 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange vLL 0 131072;
     KZRange nOF 0 511; KZRange aOF 2 31; KZRange bOF 0 9; KZRange vOF 0 4294967294;
     KZRange nML 0 511; KZRange aML 0 16; KZRange bML 0 9; KZRange vML 0 131075;
     KZWord (LLT + 8 * sLL + 8) 2 nLL; KZWord (LLT + 8 * sLL + 10) 1 aLL; KZWord (LLT + 8 * sLL + 11) 1 bLL; KZWord (LLT + 8 * sLL + 12) 4 vLL;
     KZWord (OFT + 8 * sOF + 8) 2 nOF; KZWord (OFT + 8 * sOF + 10) 1 aOF; KZWord (OFT + 8 * sOF + 11) 1 bOF; KZWord (OFT + 8 * sOF + 12) 4 vOF;
     KZWord (MLT + 8 * sML + 8) 2 nML; KZWord (MLT + 8 * sML + 10) 1 aML; KZWord (MLT + 8 * sML + 11) 1 bML; KZWord (MLT + 8 * sML + 12) 4 vML;
     KZWr (SPV - 688) 688]
    [(SPV - 688, 688)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: sd_rbf.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in LF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX; try unfold held in V1; try unfold held in V2; try unfold held in V3; try unfold held in V4; try unfold held in V5; try unfold held in V6; try unfold held in V7; try unfold held in V8; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in PLL; try unfold held in POF; try unfold held in PML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | eapply seql_lfacts_bc; [exact LF0 | lia]
      | exact NX | lia | lia | lia | lia | lia  | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..]).

Qed.
