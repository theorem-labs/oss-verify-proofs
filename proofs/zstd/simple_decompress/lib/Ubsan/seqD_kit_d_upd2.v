(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 huf411_kit_rs seqS_kit_al.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land_mask_lt2 : forall x nb, 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma land_mask_lt3 : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (2^nb - 1) by lia. apply land_mask_lt2. lia.
Qed.
Ltac sd_land :=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  end.
Ltac sd_rbf2 :=
  repeat match goal with
  | |- context [bv_unsigned ?w / 2 ^ (((-1 * ?a) mod 2 ^ 64) mod 64)] =>
      let H := fresh "RBF" in pose proof (rbf_bound_w w a ltac:(lia)) as H;
      let v := fresh "rv" in set (v := bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64)) in *; clearbody v
  end.

Lemma seqd_update_k2 : forall P OEND LEND K, seqd_static P OEND LEND -> 2 <= K <= q_nbSeq P ->
  at_b93c P OEND LEND K -> at_b898 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1. unfold at_b898.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP nLL aLL bLL vLL nOF bOF nML bML mlv ofs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 INV LF NX HA1 HV HM.
  pose proof (seqd_linv_frame P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold at_b93c in CONT1.
  destruct INV as ((j0 & jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  assert (RS : 0 <= bc <= 9900000 /\ 2 <= K <= 98047) by (clear - L6 HK S16; lia).
  assert (RP : 1 <= 2^bLL <= 512 /\ 1 <= 2^bOF <= 512 /\ 1 <= 2^bML <= 512 /\ nLL <= 511 /\ nOF <= 511 /\ nML <= 511).
  { clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 PLL POF PML.
    pose proof (Z.pow_pos_nonneg 2 bLL). pose proof (Z.pow_pos_nonneg 2 bOF). pose proof (Z.pow_pos_nonneg 2 bML). lia. }
  pose proof (bitmask_know m1 bLL MI ltac:(clear - NX1; lia)) as BK1.
  pose proof (bitmask_know m1 bOF MI ltac:(clear - NX4; lia)) as BK2.
  pose proof (bitmask_know m1 bML MI ltac:(clear - NX7; lia)) as BK3.
  unfold BITMASK in BK1, BK2, BK3.
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (PA : 0 < 2^aLL <= 65536) by (clear - HA1; split; [apply Z.pow_pos_nonneg; lia | change 65536 with (2^16); apply Z.pow_le_mono_r; lia]).
  assert (HV' : 0 <= vLL <= 131071) by (clear - HV; lia). assert (HM' : 0 <= mlv <= 262143) by (clear - HM; lia).
  try hold TRANS. try hold CONT1. try hold LF0. try hold NX. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold L7. try hold NX3. try hold NX6. try hold NX9. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1ce4c] 120%nat
    [KZRange SPV 544 (2^47); KZRange bc 0 9900000; KZRange K 2 98047;
     KZRange nLL 0 511; KZRange nOF 0 511; KZRange nML 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange bOF 0 9; KZRange bML 0 9;
     KZRange vLL 0 131071; KZRange mlv 0 262143;
     KZRange (2^bLL) 1 512; KZRange (2^bOF) 1 512; KZRange (2^bML) 1 512;
     KZWord (BITMASK + 4 * bLL) 4 (2^bLL - 1); KZWord (BITMASK + 4 * bOF) 4 (2^bOF - 1); KZWord (BITMASK + 4 * bML) 4 (2^bML - 1);
     KZWr (SPV - 352) 352; KZImg 0x10000 0x14000]
    [(SPV - 352, 352)].
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => first [kx_trap_fast | seqs_land_close] | _ => idtac end.
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_rbf2.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT1; try unfold held in LF0; try unfold held in NX; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML).
  all: eapply CONT1;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; sd_land;
        split; [exact L1|]; split; [exact L2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
        eapply bit_ok_mono; [exact L7 | lia]
      | lia | lia ].
Qed.
