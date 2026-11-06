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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_lkit2 RZ_seq_d_lbase3.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma seqd_exec6 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_be28 P OEND LEND K -> at_bca4 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1. unfold at_bca4.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs mtc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 INV LF MF HO HOF HM.
  pose proof (seqd_linv_buf P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seqd_copy_facts P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  unfold at_be28 in CONT1.
  pose proof LF as LF0. pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, M1, HOF, BUF, CONT1, STEP |- *.
  sd_static_open ST.
  assert (MUL : munch [(ole, ole + 8)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= mtc < 2^47 /\ B0 <= mtc /\ ole + 8 <= B1 /\ DST <= ole /\ ole + 8 <= OEND)
    by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; lia).
  assert (CASES : ofs = 0 \/ ofs = 1 \/ ofs = 2 \/ ofs = 3 \/ ofs = 4 \/ ofs = 5 \/ ofs = 6 \/ ofs = 7 \/ 8 <= ofs <= 15) by (clear - HO; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 0) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole, 8)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 1) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 1) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 1, 9)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 2) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 2) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 2, 10)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 3) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 3) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 3, 11)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 4) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 4) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 4, 12)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 5) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 5) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 5, 13)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 6) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 6) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 6, 14)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 7) by (clear - HM; lia). subst mtc.
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange (ole - 7) 4096 (2^47); 
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(ole - 7, 15)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
  - (* [comment removed for export] *)
    ((try hold CONT1; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bef4] 80%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange mtc 4096 (2^47); KZRange ofs 8 15;
     KZWr ole 8; KZImg 0x10000 0x14000]
    [(mtc, 8)];
    kx_mem; (try unfold held in CONT1; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bef4) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia])
      end).
Qed.

Lemma seqd_exec7 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K -> at_be48 P OEND LEND K -> at_be28 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2. unfold at_be28.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl rip8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31 INV LF MF HR1 HR2.
  unfold at_bb64 in CONT1. unfold at_be48 in CONT2.
  pose proof LF as LF0. destruct LF as (L1 & _). pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, L1, M1, HR1, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= ole < 2^47 /\ 4000 <= rip8 < 2^47 /\ 8 <= ole - rip8 <= 15) by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HR1 HR2; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bc30; 0x1bf14] 40%nat
    [KZRange SPV 496 (2^47); KZRange ole 4096 (2^47); KZRange rip8 4000 (2^47); KZRange mlv 0 262143; KZRange (ole - rip8) 8 15]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc30) _ _ _ _) => (eapply CONT1; [exact INV | lia | right; split; [exact LF0 | lia]])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bf14) _ _ _ _) => (eapply CONT2 with (ole := ole) (mlv := mlv); [exact INV | exact LF0 | exact MF0 | lia | lia | cbn [q_PFX]; lia | lia])
      end).
Qed.

Lemma seqd_closeloop_aux : forall (k : nat) P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K ->
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x23 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl -> ome = ole + mlv -> ole + 8 <= cur < ome -> q_PFX P <= rsrc -> 8 <= cur - rsrc <= 15 ->
  ome - cur <= 8 * (Z.of_nat k + 1) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 ome) x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 OP) x25 (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bf14) (q_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LEND K ST HK CONT1 m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl cur rsrc ome x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x23 x25 x27 x28 x29 x30 x31 INV LF MF EM HC HS HD HM.
  all: pose proof CONT1 as CONT0; unfold at_bb64 in CONT1.
  all: pose proof (seqd_linv_buf P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  all: pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  all: pose proof (seqd_copy_facts P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & _).
  all: pose proof LF as LF0; destruct LF as (L1 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, L1, M1, HS, BUF, CONT1, STEP |- *.
  all: sd_static_open ST.
  all: assert (MUL : munch [(cur, cur + 8)] m1 m1) by apply munch_refl; assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= rsrc < 2^47 /\ 4096 <= ome < 2^47 /\ B0 <= rsrc /\ rsrc + 8 <= B1 /\ B0 <= cur /\ cur + 8 <= B1 /\ DST <= cur /\ cur + 8 <= OEND)
         by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 EM HC HS HD; lia).
  - pose proof I as IHk.
    ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bf14; 0x1bc30] 60%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8]
    [(rsrc, 8)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bf14) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc30) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia]])
      end).
  - ((try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold INV; try hold STEP; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_auto [0x1bf14; 0x1bc30] 60%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange rsrc 4096 (2^47); KZRange ome 4096 (2^47); KZWr cur 8]
    [(rsrc, 8)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in INV; try unfold held in STEP; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bf14) _ _ _ _) => (eapply (IHk _ OEND LEND K ST0 HK CONT0) with (ole := ole) (mlv := mlv); [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | exact LF0 | exact MF0 | lia | lia | cbn [q_PFX]; lia | lia | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc30) _ _ _ _) => (eapply CONT1; [ eapply STEP; [exact MUL | exact WMl | exact KXMI | exact BUF | lia | lia] | lia | right; split; [exact LF0 | lia]])
      end).
Qed.

Lemma seqd_closeloop : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K -> at_be48 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1. unfold at_be48.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl cur rsrc ome x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x23 x25 x27 x28 x29 x30 x31 INV LF MF EM HC HS HD.
  eapply (seqd_closeloop_aux (Z.to_nat (ome - cur)) P OEND LEND K ST HK CONT1); try eassumption. lia.
Qed.
