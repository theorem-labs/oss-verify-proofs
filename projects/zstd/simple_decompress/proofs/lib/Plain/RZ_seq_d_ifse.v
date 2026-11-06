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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_upd RZ_seq_d_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_iinv_eq : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_LL : forall P OEND LEND, seqd_static P OEND LEND -> ai_43c P OEND LEND -> ai_408 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_408.
  intros m1 p0 p1 p2 j0 jpad jseq j_c16 j_c48 j_cbc j_c96 j_c104 j_c112 j_c120 j_c128 j_c136 cw bc ptr d x1 x5 x6 x7 x16 x17 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 INV IB HF0.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_43c in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 LLT K_LL tLL TLL OKLL) as RL. pose proof (seq_tl_range K_LL tLL OKLL) as RT.
  remember (st_log tLL) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= DCTX \/ DCTX + 32 <= SPV - 304) by (unfold held in S27; clear - S27 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1b508] 60%nat
    [KZRange SPV 496 (2^47); KZRange DCTX 4096 (2^47); KZRange LLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (LLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 DCTX 32; KZImg 0x10000 0x14000]
    [(SPV - 304, 304)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_OF : forall P OEND LEND, seqd_static P OEND LEND -> ai_56c P OEND LEND -> ai_538 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_538.
  intros m1 p0 p1 p2 j0 jpad jseq j_c16 j_c48 j_cbc j_c104 j_c112 j_c120 j_c128 j_c136 cw bc ptr sLL x1 x5 x6 x7 x15 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB HF0.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_56c in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 OFT K_OF tOF TOF OKOF) as RL. pose proof (seq_tl_range K_OF tOF OKOF) as RT.
  remember (st_log tOF) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= DCTX \/ DCTX + 32 <= SPV - 304) by (unfold held in S27; clear - S27 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1b638] 60%nat
    [KZRange SPV 496 (2^47); KZRange DCTX 4096 (2^47); KZRange OFT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (OFT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 DCTX 32; KZImg 0x10000 0x14000]
    [(SPV - 304, 304)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_ML : forall P OEND LEND, seqd_static P OEND LEND -> ai_6a8 P OEND LEND -> ai_66c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_66c.
  intros m1 p0 p1 p2 j0 jpad jseq j_c16 j_c48 j_cbc j_c120 j_c128 j_c136 cw bc ptr sLL sOF x1 x5 x6 x7 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB HF0 HF1.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold ai_6a8 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 MLT K_ML tML TML OKML) as RL. pose proof (seq_tl_range K_ML tML OKML) as RT.
  remember (st_log tML) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 304 + 304 <= DCTX \/ DCTX + 32 <= SPV - 304) by (unfold held in S27; clear - S27 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1b774] 60%nat
    [KZRange SPV 496 (2^47); KZRange DCTX 4096 (2^47); KZRange MLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (MLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 304) 304; KZDisj (SPV - 304) 304 DCTX 32; KZImg 0x10000 0x14000]
    [(SPV - 304, 304)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | exact HF1 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seqd_i7ac : forall P OEND LEND, seqd_static P OEND LEND -> at_head P OEND LEND (q_nbSeq P) -> ai_7ac P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_7ac.
  intros m1 p0 p1 p2 j0 jpad jseq j_c48 j_c136 cw bc ptr sLL sOF sML x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 INV IB HF0 HF1 HF2.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  unfold at_head in CONT.
  destruct INV as (FR & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST.
  assert (MUL : munch [(SPV - 304, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= MLT < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S23; lia).
  try hold TRANS. try hold CONT. try hold IB2. try hold HF0. try hold HF1. try hold HF2. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x1b890] 20%nat
    [KZRange SPV 496 (2^47); KZRange OEND 4096 (2^47); KZRange MLT 4096 (2^47); KZWr (SPV - 304) 304]
    [(SPV - 304, 304)].
  kx_mem. (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in HF0; try unfold held in HF1; try unfold held in HF2; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  repeat match goal with |- context [Z_to_bv 64 (?a + -32)] => replace (a + -32) with (a - 32) by lia end.
  eapply CONT with (LP := LITP);
    [ eapply seqd_iinv_linv; eapply seqd_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [seqd_frame]; repeat f_equal; lia]
    | unfold seqd_lfacts; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq q_nbSeq];
      split; [lia|]; split; [lia|]; split; [exact HF0|]; split; [exact HF1|]; split; [exact HF2|]; split; [lia| exact IB2] ].
Qed.
