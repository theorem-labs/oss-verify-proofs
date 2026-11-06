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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase RZ_seq_s_a1_at.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seqs_ifse_LL : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i2 P OEND LLO LEND LOCV -> ai_i1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i1.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c96 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 jpad jseq cw bc ptr d x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 INV IB HF0.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i2 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 LLT K_LL tLL TLL OKLL) as RL. pose proof (seq_tl_range K_LL tLL OKLL) as RT.
  remember (st_log tLL) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 336, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 336 + 336 <= DCTX \/ DCTX + 32 <= SPV - 336) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 336 + 336 <= LLT \/ LLT + 8 <= SPV - 336) by (unfold held in S28; clear - S28 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x19b34] 60%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange LLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (LLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 DCTX 32; KZDisj (SPV - 336) 336 LLT 8; KZImg 0x10000 0x14000]
    [(SPV - 336, 336)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqs_ifse_OF : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i4 P OEND LLO LEND LOCV -> ai_i3 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i3.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c96 w_c136 w_c144 w_c152 w_c160 w_c168 jpad jseq cw bc ptr sLL x1 x5 x6 x7 x8 x9 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 INV IB HF0.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i4 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 OFT K_OF tOF TOF OKOF) as RL. pose proof (seq_tl_range K_OF tOF OKOF) as RT.
  remember (st_log tOF) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 336, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 336 + 336 <= DCTX \/ DCTX + 32 <= SPV - 336) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 336 + 336 <= OFT \/ OFT + 8 <= SPV - 336) by (unfold held in S29; clear - S29 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x19c90] 60%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange OFT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (OFT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 DCTX 32; KZDisj (SPV - 336) 336 OFT 8; KZImg 0x10000 0x14000]
    [(SPV - 336, 336)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqs_ifse_ML : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV -> ai_i5 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i5.
  intros m1 p0 p1 p2 w_c0 w_c16 w_c24 w_c32 w_c40 w_c96 w_c152 w_c160 w_c168 jpad jseq cw bc ptr sLL sOF x1 x5 x6 x7 x8 x9 x15 x17 x19 x20 x21 x22 x27 x28 x29 x31 INV IB HF0 HF1.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i6 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 MLT K_ML tML TML OKML) as RL. pose proof (seq_tl_range K_ML tML OKML) as RT.
  remember (st_log tML) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 336, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 336 + 336 <= DCTX \/ DCTX + 32 <= SPV - 336) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 336 + 336 <= MLT \/ MLT + 8 <= SPV - 336) by (unfold held in S30; clear - S30 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x19dd4] 60%nat
    [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange MLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (MLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 336) 336; KZDisj (SPV - 336) 336 DCTX 32; KZDisj (SPV - 336) 336 MLT 8; KZImg 0x10000 0x14000]
    [(SPV - 336, 336)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | exact HF1 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqs_ihead : forall P OEND LLO LEND LOCV, seqs_static P OEND LLO LEND LOCV -> LLO <= v_LITP P <= LEND ->
  a1_head P OEND LLO LEND LOCV (v_nbSeq P) -> ai_i7 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLP CONT. unfold ai_i7.
  intros m1 p0 p1 p2 w_c0 w_c16 w_c24 w_c40 w_c168 jpad jseq cw bc ptr sLL sOF sML x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 INV IB HF0 HF1 HF2.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold a1_head in CONT.
  destruct INV as (FR & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 336, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= MLT < 2^47 /\ 4096 <= DCTX < 2^47 /\ 4096 <= DST < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20 S23; lia).
  try hold TRANS. try hold CONT. try hold IB2. try hold HF0. try hold HF1. try hold HF2. try hold HLP. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x19e94] 20%nat
    [KZRange SPV 544 (2^47); KZRange OEND 4096 (2^47); KZRange MLT 4096 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZWr (SPV - 336) 336]
    [(SPV - 336, 336)].
  kx_mem. (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in HLP; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  eapply CONT with (LP := LITP);
    [ eapply seqs_iinv_linv; eapply seqs_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [seqs_frame]; repeat f_equal; lia]
    | unfold seqs_lfacts; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq v_nbSeq];
      split; [lia|]; split; [exact HLP|]; split; [exact HF0|]; split; [exact HF1|]; split; [exact HF2|]; split; [lia| exact IB2] ].
Qed.
