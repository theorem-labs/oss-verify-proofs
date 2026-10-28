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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat RZ_seq_l_la_at2 RZ_seq_l_md_at RZ_seq_l_lf_at seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma la_done_ok : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> 1 <= y_nbSeq P ->
  seql_at_err P OEND LLO LEND LOCV -> (forall K, 1 <= K <= y_nbSeq P -> lf_head P OEND LLO LEND LOCV K) -> (forall K, 1 <= K <= y_nbSeq P -> md_head P OEND LLO LEND LOCV K) -> la_done P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HK0 CONT1 CONT2 CONT3. unfold la_done.
  intros m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 INV LF HOPD HRING.
  pose proof (seql_linv_frame P OEND LLO LEND LOCV m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold seql_at_err in CONT1.
  assert (CONT2' : forall K, 1 <= K <= y_nbSeq P -> forall Ks, Ks = K -> lf_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT2; exact HK').
  clear CONT2. rename CONT2' into CONT2. unfold lf_head in CONT2.
  assert (CONT3' : forall K, 1 <= K <= y_nbSeq P -> forall Ks, Ks = K -> md_head P OEND LLO LEND LOCV Ks) by (intros K' HK' Ks ->; apply CONT3; exact HK').
  clear CONT3. rename CONT3' into CONT3. unfold md_head in CONT3.
  pose proof INV as ((jpad & jseq & FR) & _).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_frame seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in ST, FR, HK0, HRING, HOPD, CONT1, CONT2, CONT3, TRANS |- *.
  sd_static_open ST. subst OP.
  assert (RG : 1 <= nbSeq <= 98047 /\ 1 <= Z.min nbSeq 8 <= 8 /\ 4096 <= DCTX < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= OEND < 2^47 /\ 4000 <= OEND - 32 < 2^47 /\ 4096 <= SEQ < 2^47)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S13 S14 S15 S16 S19 S20 HK0; lia).
  assert (RB : 0 <= bc <= 2147483647) by (unfold seql_lfacts in LF; cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in LF; clear - LF RG; lia).
  assert (MUL : munch [(SPV - 688, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK0; try hold ST0; try hold INV; try hold TRANS; try hold HRING; try hold LF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1abb4; 0x19d58; 0x1ab30; 0x18464; 0x1ac04] 80%nat
    [KZRange SPV 896 (2^47); KZAlign SPV 16; KZRange nbSeq 1 98047; KZRange (Z.min nbSeq 8) 1 8; KZRange bc 0 2147483647; KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange OEND 4096 (2^47); KZRange (OEND - 32) 4000 (2^47);
     KZRange SEQ 4096 (2^47); KZWr (SPV - 688) 688]
    [(SPV - 688, 688)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => seql_ck end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK0; try unfold held in ST0; try unfold held in INV; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ab30) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x19d58) _ _ _ _) => (replace (Z_to_bv 64 18446744073709551599) with (Z_to_bv 64 (-17)) by (apply Z_to_bv_eqm; reflexivity); eapply (CONT2 nbSeq ltac:(lia) nbSeq eq_refl); [ replace (OEND + -32) with (OEND - 32) in FR by (clear; lia); try replace (Z_to_bv 64 18446744073709486079) with (Z_to_bv 64 (-65537)) in FR by (apply Z_to_bv_eqm; reflexivity); eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | unfold seql_lfacts in LF |- *; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq] in LF |- *; destruct LF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7); split; [lia|]; split; [exact Q2|]; split; [exact Q3|]; split; [exact Q4|]; split; [exact Q5|]; split; [lia | exact Q7] | lia | exact HRING])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18464) _ _ _ _) => (replace (Z_to_bv 64 18446744073709551599) with (Z_to_bv 64 (-17)) by (apply Z_to_bv_eqm; reflexivity); eapply (CONT3 (nbSeq - 8) ltac:(lia) (nbSeq - 8) eq_refl); [ replace (OEND + -32) with (OEND - 32) in FR by (clear; lia); replace (-1 * SPV + 327) with (- (SPV - 328) - 1) in FR by (clear; lia); replace (Z_to_bv 64 18446744073709486079) with (Z_to_bv 64 (-65537)) in FR by (apply Z_to_bv_eqm; reflexivity); eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | replace (nbSeq - (nbSeq - 8)) with (Z.min nbSeq 8) by lia; unfold seql_lfacts in LF |- *; cbn [y_DST y_tLL y_tOF y_tML y_SEQ y_sq y_nbSeq] in LF |- *; destruct LF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7); split; [lia|]; split; [exact Q2|]; split; [exact Q3|]; split; [exact Q4|]; split; [exact Q5|]; split; [lia | exact Q7] | lia | replace 8 with (Z.min nbSeq 8) by lia; exact HRING])
      end).
Qed.
