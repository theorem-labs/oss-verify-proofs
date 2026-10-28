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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_xat RZ_seq_s_a1_at RZ_seq_s_tr_at seqL3_kit_dbs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma tr_brk_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  seqs_at_err P OEND LLO LEND LOCV -> tr_sw P OEND LLO LEND LOCV K -> tr_w1 P OEND LLO LEND LOCV K -> a1_brk P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2 CONT3. unfold a1_brk.
  intros m1 c0 c8 c40 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x25 x28 x29 x30 x31 INV LF HO HL HM HB.
  unfold seqs_at_err in CONT1. unfold tr_sw in CONT2. unfold tr_w1 in CONT3.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & LIT & _).
  pose proof INV as ((jpad & jseq & FR) & _ & _ & _ & _ & _ & _ & _ & XI).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_post seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, FR, XI, BUF, HK, L1, L2, CONT1, CONT2, CONT3 |- *.
  sd_static_open ST. destruct XI as (_ & _ & _ & STK & _).
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 1 <= K < 2^31)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 S16 HK; lia).
  assert (MUL : munch [(SPV - 384, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  ((try hold CONT1; try hold CONT2; try hold CONT3; try hold HK; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold LF0; try hold ST0; try hold INV; try hold BUF; try hold LIT; try hold STK; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1c6fc; 0x1ba7c; 0x1dd78] 60%nat
    [KZRange SPV 592 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47); KZRange llv 0 (2^18); KZRange mlv 0 (2^18); KZRange K 1 (2^31); KZWr (SPV - 384) 384]
    [(SPV - 384, 384)];
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => kx_trap_fast end);
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in HK; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in BUF; try unfold held in LIT; try unfold held in STK; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1c6fc) _ _ _ _) => (eapply CONT1; [exact INV | lia | left; reflexivity])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ba7c) _ _ _ _) => (sd_diffs; eapply CONT2; [exact INV | exact LF0 | exact HO | lia | exact HM])
      | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A0) (Z_to_bv 64 ?A1) (Z_to_bv 64 ?A2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x1dd78) _ _ _ _) =>
          (sd_diffs; unfold held in S24, S26; eapply evt_cut;
           [ eapply zd_safecopy_dbs_proof with (SPV := SPV + -384) (lo := lo) (OP := A0) (IP := A1) (LEN := A2) (B0 := B0) (B1 := B1) (R0 := LLO) (R1 := LEND + 32);
             [ exact BUF | lia | lia | lia | lia | lia | exact LIT | lia | lia | lia | lia | exact STK | lia | lia | unfold off_stack; lia | unfold off_stack; lia | exact MI | reflexivity | reflexivity | reflexivity ]
           | intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & BUF' & _);
             lazymatch goal with
             | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                 replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
             end;
             eapply CONT3; [ eapply seqs_linv_call; [exact ST0 | exact INV | exact MU | exact WM | exact MI' | exact STK' | exact BUF' | cbn [v_DST]; lia | lia | lia] | exact LF0 | exact HO | exact HL | exact HM | lia | lia | lia ] ])
      end).
Qed.
