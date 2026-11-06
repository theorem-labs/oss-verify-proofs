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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Lemma seql_ifse_LL : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i2 P OEND LLO LEND LOCV -> ai_i1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i1.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c144 w_c152 w_c160 w_c176 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 jpad jseq rl rm ro cw bc ptr d x1 x6 x7 x15 x16 x17 x21 x22 x23 x25 x26 x27 x28 x29 x31 INV IB HF0.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i2 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 LLT K_LL tLL TLL OKLL) as RL. pose proof (seq_tl_range K_LL tLL OKLL) as RT.
  remember (st_log tLL) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 608 + 608 <= DCTX \/ DCTX + 32 <= SPV - 608) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 608 + 608 <= LLT \/ LLT + 8 <= SPV - 608) by (unfold held in S28; clear - S28 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x17590] 60%nat
    [KZRange SPV 816 (2^47); KZRange DCTX 4096 (2^47); KZRange LLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (LLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 DCTX 32; KZDisj (SPV - 608) 608 LLT 8; KZImg 0x10000 0x14000]
    [(SPV - 608, 608)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seql_ifse_OF : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i4 P OEND LLO LEND LOCV -> ai_i3 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i3.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c152 w_c160 w_c176 w_c216 w_c224 w_c232 w_c240 w_c248 jpad jseq rl rm ro cw bc ptr sLL x1 x6 x7 x12 x21 x22 x23 x25 x26 x27 x28 x29 x31 INV IB HF0.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i4 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 OFT K_OF tOF TOF OKOF) as RL. pose proof (seq_tl_range K_OF tOF OKOF) as RT.
  remember (st_log tOF) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 608 + 608 <= DCTX \/ DCTX + 32 <= SPV - 608) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 608 + 608 <= OFT \/ OFT + 8 <= SPV - 608) by (unfold held in S29; clear - S29 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x176ec] 60%nat
    [KZRange SPV 816 (2^47); KZRange DCTX 4096 (2^47); KZRange OFT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (OFT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 DCTX 32; KZDisj (SPV - 608) 608 OFT 8; KZImg 0x10000 0x14000]
    [(SPV - 608, 608)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | subst tl; lia ]).
Qed.

(* [comment removed for export] *)
Lemma seql_ifse_ML : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV -> ai_i5 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i5.
  intros m1 p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c152 w_c176 w_c232 w_c240 w_c248 jpad jseq rl rm ro cw bc ptr sLL sOF x1 x6 x16 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 INV IB HF0 HF1.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  unfold ai_i6 in CONT.
  destruct INV as (FR & PT & TLL & TOF & TML & _). destruct IB as (IB1 & IB2).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_post y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold dctx_ptrs in PT.
  pose proof (seq_rdn_log psegs m1 MLT K_ML tML TML OKML) as RL. pose proof (seq_tl_range K_ML tML OKML) as RT.
  remember (st_log tML) as tl eqn:Etl.
  pose proof (bitmask_know m1 tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MUL : munch [(SPV - 608, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono psegs m1 m1) by apply wmono_refl.
  assert (DJ : SPV - 608 + 608 <= DCTX \/ DCTX + 32 <= SPV - 608) by (unfold held in S27; clear - S27 S18; lia).
  assert (DJT : SPV - 608 + 608 <= MLT \/ MLT + 8 <= SPV - 608) by (unfold held in S30; clear - S30 S18; lia).
  clear TLL TOF TML.
  try hold TRANS. try hold CONT. try hold IB2. try hold Etl. try hold HF0. try hold HF1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoLx [0x17838] 60%nat
    [KZRange SPV 816 (2^47); KZRange DCTX 4096 (2^47); KZRange MLT 4096 (2^47); KZRange bc 0 100; KZRange tl 0 9; KZRange (2^tl) 1 512;
     KZWord (MLT + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
     KZWr (SPV - 608) 608; KZDisj (SPV - 608) 608 DCTX 32; KZDisj (SPV - 608) 608 MLT 8; KZImg 0x10000 0x14000]
    [(SPV - 608, 608)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: kx_mem.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in IB2; try unfold held in Etl; try unfold held in HF0; try unfold held in HF1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: (eapply CONT; [ first [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seql_iinv_eq; [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | repeat f_equal; lia] ] | (split; [lia | eapply bit_ok_mono; [exact IB2 | lia]]) | exact HF0 | exact HF1 | subst tl; lia ]).
Qed.
