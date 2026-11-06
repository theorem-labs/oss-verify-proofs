(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2 RZ_seq_s_xat RZ_seq_s_tr_at RZ_seq_s_et_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_lfacts_op : forall P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML,
  seqs_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> v_DST P <= OP' <= OEND ->
  seqs_lfacts P OEND LLO LEND B OP' LP bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP OP' LP bc ptr sLL sOF sML (L1 & L) H. split; [exact H| exact L]. Qed.

Lemma tr_cpA_aux : forall (k : nat) P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LOCV = 2 ->
  tr_sw P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML -> 0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  lft = LEND - LP -> 0 < lft < llv -> en = OP + lft -> en <= OEND ->
  OP <= cur < en -> src = LP + (cur - OP) -> en - cur <= Z.of_nat k + 1 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 en) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) (Z_to_bv 64 OEND) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 cur) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a6d8) (v_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs lft en cur src x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES HMk.
  all: pose proof CONT1 as CONT0; unfold tr_sw in CONT1.
  all: pose proof (seqs_linv_buf P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  all: pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, L1, L2, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  all: assert (MUL : munch [(cur, cur + 1)] m1 m1) by apply munch_refl; assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= en < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= llv <= 262143 /\
                   B0 <= src /\ src + 1 <= B1 /\ B0 <= cur /\ cur + 1 <= B1 /\ DST <= cur /\ cur + 1 <= OEND)
         by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 LE32 HL ELF HLF EEN HEN HC ES; lia).
  - pose proof I as IHk. clear CONT0.
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1a6d8; 0x1a72c] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a6d8) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a72c) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply seqs_lfacts_op; [exact LF0 | cbn [v_DST]; lia] | exact HO | lia | exact HM])
      end).
  - ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1a6d8; 0x1a72c] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a6d8) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK HLOC CONT0) with (OP := OP); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a72c) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply seqs_lfacts_op; [exact LF0 | cbn [v_DST]; lia] | exact HO | lia | exact HM])
      end).
Qed.

Lemma tr_cpA_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LOCV = 2 ->
  tr_sw P OEND LLO LEND LOCV K -> tr_cpA P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1. unfold tr_cpA.
  intros m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs lft en cur src x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES.
  eapply (tr_cpA_aux (Z.to_nat (en - cur)) P OEND LLO LEND LOCV K ST HK HLOC CONT1); try eassumption. lia.
Qed.

Lemma tr_cpB_aux : forall (k : nat) P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LOCV = 2 ->
  tr_sw P OEND LLO LEND LOCV K ->
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src rem : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML -> 0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  lft = LEND - LP -> 0 < lft < llv -> en = OP + lft -> en <= OEND ->
  OP <= cur < en -> src = LP + (cur - OP) -> rem = en - cur -> en - cur <= Z.of_nat k + 1 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 en) (Z_to_bv 64 rem) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) (Z_to_bv 64 OEND) (Z_to_bv 64 K) (Z_to_bv 64 llv) x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a70c) (v_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK HLOC CONT1 m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs lft en cur src rem x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES ER HMk.
  all: pose proof CONT1 as CONT0; unfold tr_sw in CONT1.
  all: pose proof (seqs_linv_buf P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  all: pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seqs_copy_facts P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in ST, L1, L2, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (LE32 : B0 <= LLO /\ LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  all: assert (MUL : munch [(cur, cur + 1)] m1 m1) by apply munch_refl; assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= en < 2^47 /\ 1 <= lft <= 262143 /\ 0 <= llv <= 262143 /\
                   B0 <= src /\ src + 1 <= B1 /\ B0 <= cur /\ cur + 1 <= B1 /\ DST <= cur /\ cur + 1 <= OEND)
         by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 LE32 HL ELF HLF EEN HEN HC ES ER; lia).
  - pose proof I as IHk. clear CONT0.
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1a70c; 0x1a72c] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZRange rem 1 (2^47); KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a70c) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a72c) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply seqs_lfacts_op; [exact LF0 | cbn [v_DST]; lia] | exact HO | lia | exact HM])
      end).
  - ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold INV; try hold STEP; try hold HMk; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1a70c; 0x1a72c] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange en 4096 (2^47); KZRange lft 1 262143; KZRange llv 0 262143;
     KZRange rem 1 (2^47); KZWr cur 1]
    [(src, 1)];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in INV; try unfold held in STEP; try unfold held in HMk; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a70c) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK HLOC CONT0) with (OP := OP); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact HO | exact HL | exact HM | exact ELF | exact HLF | exact EEN | exact HEN | lia | lia | lia | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a72c) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | eapply seqs_lfacts_op; [exact LF0 | cbn [v_DST]; lia] | exact HO | lia | exact HM])
      end).
Qed.

Lemma tr_cpB_ok : forall P OEND LLO LEND LOCV K, seqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LOCV = 2 ->
  tr_sw P OEND LLO LEND LOCV K -> tr_cpB P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLOC CONT1. unfold tr_cpB.
  intros m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs lft en cur src rem x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 INV LF HO HL HM ELF HLF EEN HEN HC ES ER.
  eapply (tr_cpB_aux (Z.to_nat (en - cur)) P OEND LLO LEND LOCV K ST HK HLOC CONT1); try eassumption. lia.
Qed.
