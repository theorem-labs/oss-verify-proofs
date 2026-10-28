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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_lf_at RZ_seq_l_n2_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac n2t_hold t := lazymatch t with (?a, ?b) => n2t_hold a; n2t_hold b | ?h => try hold h end.
Ltac n2t_unhold t := lazymatch t with (?a, ?b) => n2t_unhold a; n2t_unhold b | ?h => try unfold held in h end.

Lemma n2_tail_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> lf_head P OEND LLO LEND LOCV K') -> lf_end P OEND LLO LEND LOCV -> n2_tail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3. unfold n2_tail.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP r idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 INV HR RES HIDX HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold lf_end in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> lf_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold lf_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, RES, HK, HIDX, CONT1, CONT2, CONT3, TRANS |- *.
  sd_static_open ST.
  assert (RG : 0 <= idx <= 98047 /\ 1 <= nbSeq <= 98047 /\ 0 <= r <= 18446744073709551615) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR HIDX; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  destruct RES as [RE|(LF & NE)].
  - apply zd_is_error_true_iff in RE.
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x1a1b0; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 18446744073709551615; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1b0) _ _ _ _) => (exfalso; lia)
      end).
  - destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [y_DST y_nbSeq] in L1, L2, L6.
    assert (RR : 0 <= r < 2^47 /\ 4096 <= OP < 2^47) by (clear - L1 NE HR S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; try hold L3; try hold L4; try hold L5; try hold L7; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x19d58; 0x1ab34; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L7; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19d58) _ _ _ _) => (eapply (CONT2 (K - 1) ltac:(lia) (K - 1) eq_refl); [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7] | lia | exact HRING])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab34) _ _ _ _) => (eapply CONT3; [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | cbn [y_DST]; lia | exact L2 ])
      end).
Qed.

Lemma n2_mtail_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> lf_head P OEND LLO LEND LOCV K') -> lf_end P OEND LLO LEND LOCV -> n2_mtail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3. unfold n2_mtail.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP r idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 INV HR RES HIDX HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold lf_end in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> lf_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold lf_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, RES, HK, HIDX, CONT1, CONT2, CONT3, TRANS |- *.
  sd_static_open ST.
  assert (RG : 0 <= idx <= 98047 /\ 1 <= nbSeq <= 98047 /\ 0 <= r <= 18446744073709551615) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR HIDX; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  destruct RES as [RE|(LF & NE)].
  - apply zd_is_error_true_iff in RE.
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x1a1b0; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 18446744073709551615; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1b0) _ _ _ _) => (exfalso; lia)
      end).
  - destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [y_DST y_nbSeq] in L1, L2, L6.
    assert (RR : 0 <= r < 2^47 /\ 4096 <= OP < 2^47) by (clear - L1 NE HR S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; try hold L3; try hold L4; try hold L5; try hold L7; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x19d58; 0x1ab34; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L7; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19d58) _ _ _ _) => (eapply (CONT2 (K - 1) ltac:(lia) (K - 1) eq_refl); [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7] | lia | exact HRING])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab34) _ _ _ _) => (eapply CONT3; [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | cbn [y_DST]; lia | exact L2 ])
      end).
Qed.

Lemma n2_stail_ok : forall P OEND LLO LEND LOCV K, seql_static P OEND LLO LEND LOCV -> 1 <= K <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> (forall K', 1 <= K' < K -> lf_head P OEND LLO LEND LOCV K') -> lf_end P OEND LLO LEND LOCV -> n2_stail P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3. unfold n2_stail.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP r idx x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 INV HR RES HIDX HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1. unfold lf_end in CONT3.
  assert (CONT2' : forall K', 1 <= K' < K -> forall Ks, Ks = K' -> lf_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold lf_head in CONT2.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, RES, HK, HIDX, CONT1, CONT2, CONT3, TRANS |- *.
  sd_static_open ST.
  assert (RG : 0 <= idx <= 98047 /\ 1 <= nbSeq <= 98047 /\ 0 <= r <= 18446744073709551615) by (clear - S1 S2 S3 S4 S5 S6 S7 S16 HK HR HIDX; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  destruct RES as [RE|(LF & NE)].
  - apply zd_is_error_true_iff in RE.
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x1a1b0; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 18446744073709551615; KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; apply zd_is_error_true_iff; lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1b0) _ _ _ _) => (exfalso; lia)
      end).
  - destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [y_DST y_nbSeq] in L1, L2, L6.
    assert (RR : 0 <= r < 2^47 /\ 4096 <= OP < 2^47) by (clear - L1 NE HR S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
    ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold HIDX; try hold L3; try hold L4; try hold L5; try hold L7; n2t_hold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML));
    kx_autoLx [0x1abb4; 0x19d58; 0x1ab34; 0x1ac04] 60%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange idx 0 98047; KZRange nbSeq 1 98047; KZRange r 0 (2^47); KZRange OP 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in HIDX; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L7; n2t_unhold (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, OKLL, OKOF, OKML); repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19d58) _ _ _ _) => (eapply (CONT2 (K - 1) ltac:(lia) (K - 1) eq_refl); [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | unfold seql_lfacts; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq]; split; [lia|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia| exact L7] | lia | exact HRING])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab34) _ _ _ _) => (eapply CONT3; [ first [ exact INV | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] ] | cbn [y_DST]; lia | exact L2 ])
      end).
Qed.
