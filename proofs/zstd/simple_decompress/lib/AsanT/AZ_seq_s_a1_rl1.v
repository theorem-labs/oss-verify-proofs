(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_a1_at AZ_seq_s_lkit2 AZ_seq_s_rkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

Lemma a1_reload1 : forall P OEND LLO LEND LOCV K, sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LEND + 32 <= OEND ->
  a1_rl1 P OEND LLO LEND LOCV K -> a1_dec P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK HLBE HL32  CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold a1_dec. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 c0 c8 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv ofs x10 x12 x19 x22 x24 x28 x30 INV LF NX HA1 HA2 HA3 HV HM.
  unfold a1_rl1 in CONT. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in HK, CONT.
  pose proof (sqs_linv_frame _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (DCTX + 30360)) (Z_to_bv 64 (2147450880 + D8 + 3795)) (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in TRANS.
  
  apply (sqs_lopen_k _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (DCTX + 30360)) (Z_to_bv 64 (2147450880 + D8 + 3795)) (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqs_frame sqs_ffr] in FR, FRF. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FR, FRF.
  apply (sqs_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. sd_static_open ST. unfold held in RGB.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En. try rewrite <- En in USEQ. try rewrite <- En in RSQ. try rewrite <- En in RSQS.
  assert (DJF : FF + 256 <= SEQ \/ SEQ + n <= FF) by (unfold held in S56; clear - S56 En; lia). assert (DJR : FRB + 280 <= SEQ \/ SEQ + n <= FRB) by (unfold held in S25; clear - S25 S18 S47 En; lia).
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (RS : 0 <= bc <= 9900000) by (clear - L6 HK S16; lia).
  assert (DJ : SPV - 280 + 280 <= SEQ \/ SEQ + n <= SPV - 280) by (unfold held in S25; clear - S25 S18; lia). clear DJ.
  
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ ptr = SEQ) \/ (bc <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8)).
  { unfold bit_ok in L7. clear - L7. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (L7 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia| right; right; right; lia]. }
  clear L7.
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *)
    hold TRANS. hold ST0. hold CONT. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold NX. hold HV. hold HM. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp SEQ n] [0x9002c; 0x90c84; 0x90470] 468%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 65 9900000;
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, HK, L1, L2, L3, L4, L5, L6, En, Esqb, NX, HV, HM, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9002c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    hold TRANS. hold ST0. hold CONT. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold NX. hold HV. hold HM. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp SEQ n] [0x9002c; 0x90c84; 0x90470] 468%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 0 64;
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, HK, L1, L2, L3, L4, L5, L6, En, Esqb, NX, HV, HM, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9002c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    hold TRANS. hold ST0. hold CONT. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold NX. hold HV. hold HM. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp SEQ n] [0x9002c; 0x90c84; 0x90470] 468%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 17); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, HK, L1, L2, L3, L4, L5, L6, En, Esqb, NX, HV, HM, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9002c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3 & C4).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 C4 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + hold TRANS. hold ST0. hold CONT. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold NX. hold HV. hold HM. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp SEQ n] [0x9002c; 0x90c84; 0x90470] 468%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 10); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, HK, L1, L2, L3, L4, L5, L6, En, Esqb, NX, HV, HM, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9002c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      end.

    + hold TRANS. hold ST0. hold CONT. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold NX. hold HV. hold HM. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp SEQ n] [0x9002c; 0x90c84; 0x90470] 468%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 10); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, HK, L1, L2, L3, L4, L5, L6, En, Esqb, NX, HV, HM, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9002c) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts, bit_ok; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      end.

Qed.

End CANSEC1.
