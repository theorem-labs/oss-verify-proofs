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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_lkit2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma seqd_exec0 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb80 P OEND LEND K -> at_baac P OEND LEND K -> at_ba80 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2. unfold at_ba80.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x26 x28 x29 x30 x31 INV LF HL HM.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold at_bb80 in CONT1. unfold at_baac in CONT2.
  pose proof INV as ((j0 & jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  rewrite <- (Z_to_bv_bv_unsigned ofs). pose proof (kx_u64_range ofs) as HO. remember (bv_unsigned ofs) as ofz eqn:Eofz. clear Eofz ofs.
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, L1, L2, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S9 S11; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold LF0; try hold ST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bc4c] 40%nat
    [KZRange SPV 496 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange llv 0 262143; KZRange mlv 0 262143; KZWr (SPV - 304) 304]
    [(SPV - 304, 304)];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in LF0; try unfold held in ST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bc4c) _ _ _ _) => (eapply CONT1; [exact INV | exact LF0 | exact HO | exact HL | exact HM])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV'; eapply CONT2; [exact INV' | exact LF0 | exact HO | unfold seqd_fast; lia | lia | lia | lia])
      end).
Qed.

Lemma seqd_exec1 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bab4 P OEND LEND K -> at_bc74 P OEND LEND K -> at_baac P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2. unfold at_baac.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ile sl ole x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3.
  unfold at_bab4 in CONT1. unfold at_bc74 in CONT2.
  pose proof LF as LF0. destruct LF as (L1 & L2 & _). pose proof FAST as FAST0. destruct FAST as (F1 & F2 & F3 & F4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, L1, L2, CONT1, CONT2 |- *.
  sd_static_open ST.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= ole < 2^47) by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S9 S11 F1 F2 F3 F4 E3; lia).
  ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange llv 0 262143; KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bb80) _ _ _ _) => (eapply CONT1; [exact INV | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV';
    ((try hold CONT1; try hold CONT2; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange llv 0 262143; KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bb80) _ _ _ _) => (eapply CONT1; [exact INV' | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bd40) _ _ _ _) => (eapply CONT2; [exact INV' | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | lia | lia])
      end))
      end).
Qed.

Lemma seqd_litloop_aux : forall (k : nat) P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bab4 P OEND LEND K ->
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 -> seqd_fast OEND LEND OP LP llv mlv -> ile = LP + llv -> sl = llv + mlv -> ole = OP + llv ->
  OP + 32 <= cur < ole -> src = LP + (cur - OP) + 16 -> ole - cur <= 32 * (Z.of_nat k + 1) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 ofs) (Z_to_bv 64 ile) (Z_to_bv 64 src) (Z_to_bv 64 BITMASK) (Z_to_bv 64 cur) (Z_to_bv 64 OP) (Z_to_bv 64 mlv) (Z_to_bv 64 sl) (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bd40) (q_fc P) None m1 (seg_rom psegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LEND K ST HK CONT1 m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ile sl ole cur src x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3 HC ES HM.
  all: pose proof CONT1 as CONT0; unfold at_bab4 in CONT1.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _); pose proof FAST as FAST0; destruct FAST as (F1 & F2 & F3 & F4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, L1, L2, CONT1 |- *.
  all: sd_static_open ST.
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= ole < 2^47) by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S9 S11 F1 F2 F3 F4 E3 HC ES; lia).
  - pose proof I as IHk. clear CONT0.
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV1 | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bd40) _ _ _ _) => (exfalso; lia)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bb80) _ _ _ _) => (eapply CONT1; [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3])
      end))
      end))
      end).
  - ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV1;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2f530) _ _ _ _) => (eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV1 | cbn [q_DST]; lia | lia | lia | left; cbn [q_LITP q_B0 q_B1]; lia]|]; sd_copy_intro INV2;
    ((try hold CONT1; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold HM; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML);
    kx_autoLx [0x1bb80; 0x1bd40] 40%nat
    [KZRange SPV 496 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ole 4096 (2^47)]
    [];
    kx_mem; (try unfold held in CONT1; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end);
    lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bd40) _ _ _ _) => (eapply (IHk _ OEND LEND K ST0 HK CONT0); [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3 | lia | lia | lia])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1bb80) _ _ _ _) => (eapply CONT1; [exact INV2 | exact LF0 | exact HO | exact FAST0 | exact E1 | exact E2 | exact E3])
      end))
      end))
      end).
Qed.

Lemma seqd_litloop : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bab4 P OEND LEND K -> at_bc74 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1. unfold at_bc74.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ile sl ole cur src x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3 HC ES.
  eapply (seqd_litloop_aux (Z.to_nat (ole - cur)) P OEND LEND K ST HK CONT1); try eassumption. lia.
Qed.
