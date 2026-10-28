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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_a2_at AZ_seq_s_a2_deca.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma a2_decode_c1 : forall P OEND LLO LEND LOCV K, sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  a2_dec P OEND LLO LEND LOCV K -> a2_head_sel (fun a => a = 1) P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold a2_head_sel. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 c0 c8 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x28 x29 x30 x31 INV LF (O8s & aOFs & EO8s & RDs & RAs & SELs).
  unfold a2_dec in CONT. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in HK, CONT.
  apply (sqs_lopen_k _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros jpad jseq FR FRF0 L16F LJF SQB MI UFL USEQ RSQ RSQS.
  pose proof LF as LF0. apply (sqs_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  apply (sqs_dec_k _ _ _ _ _ K _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP jpad ST INV LF); [cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; clear; lia | exact HK | exact FRF0 |]; cbn [sqs_ffr8 v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1];
    intros L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML EL8 EO8 EM8 GL8 GO8 GM8 WLL0 WLL1 WLL2 WLL3 WOF0 WOF1 WOF2 WOF3 WML0 WML1 WML2 WML3 ZLL ZOF ZML RWLL RWOF RWML RZLL RZOF RZML FRF
           NX NXB1 NXB2 NXB3 N1 N2 N3 NB1 NB2 NB3 A1 A2 A3 RV1 RV2 RV3 RV4 RV5 RV6 V7 V8 PLL POF PML RS1 RS2 RS3 RS4.
  assert (EQA : aOFs = aOF).
  { clear - EO8 EO8s RDs WOF1 A2 RAs. assert (EO : O8s = O8) by lia. subst O8s. rewrite WOF1 in RDs.
    rewrite !kxl_w1 in RDs. pose proof (f_equal (fun o => match o with Some (b :: _) => bv_unsigned b | _ => 0 end) RDs) as RD2; cbv beta iota in RD2.
    rewrite !b8_lit in RD2 by lia. symmetry; exact RD2. }
  cbn beta in SELs. rewrite EQA in SELs. clear EQA EO8s RDs RAs aOFs.
  clear FRF0. cbv delta [sqs_ffr8] in FRF. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FRF.
  pose proof (sqs_linv_frame8 _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP L8 O8 M8 ST INV EL8 EO8 EM8) as TRANS. cbn [sqs_frame sqs_ffr8 v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in TRANS.
  cbv delta [sqs_frame] in FR. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FR.     (* [comment removed for export] *)
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (CASES : aOF = 1 /\ vOF = 1) by (clear - A2 V7 V8 SELs; lia). clear SELs.
  hold TRANS. hold CONT. hold LF0. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold L7. hold NX. hold NXB1. hold NXB2. hold NXB3. hold V7. hold V8. hold PLL. hold POF. hold PML. hold EL8. hold EO8. hold EM8. hold L16F. hold LJF.
  destruct CASES as [C C'].
  kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256] [0x912b4] 291%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange L8 512 (2^44); KZRange O8 512 (2^44); KZRange M8 512 (2^44);
     KZRange sLL 0 511; KZRange sOF 0 511; KZRange sML 0 511; KZRange bc 0 9900000;
     KZRange nLL 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange vLL 0 131072;
     KZRange nOF 0 511; KZRange aOF 1 1; KZRange bOF 0 9; KZRange vOF 1 1;
     KZRange nML 0 511; KZRange aML 0 16; KZRange bML 0 9; KZRange vML 0 131075;
     KZWord (8 * L8 + 8 * sLL + 8) 2 nLL; KZWord (8 * L8 + 8 * sLL + 10) 1 aLL; KZWord (8 * L8 + 8 * sLL + 11) 1 bLL; KZWord (8 * L8 + 8 * sLL + 12) 4 vLL;
     KZWord (8 * O8 + 8 * sOF + 8) 2 nOF; KZWord (8 * O8 + 8 * sOF + 10) 1 aOF; KZWord (8 * O8 + 8 * sOF + 11) 1 bOF; KZWord (8 * O8 + 8 * sOF + 12) 4 vOF;
     KZWord (8 * M8 + 8 * sML + 8) 2 nML; KZWord (8 * M8 + 8 * sML + 10) 1 aML; KZWord (8 * M8 + 8 * sML + 11) 1 bML; KZWord (8 * M8 + 8 * sML + 12) 4 vML;
     KZWord (2147450880 + L8 + sLL + 1) 1 0; KZWord (2147450880 + O8 + sOF + 1) 1 0; KZWord (2147450880 + M8 + sML + 1) 1 0;
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (8 * L8 + 8 * sLL + 8, 8); (8 * O8 + 8 * sOF + 8, 8); (8 * M8 + 8 * sML + 8, 8);
     (2147450880 + L8 + sLL + 1, 1); (2147450880 + O8 + sOF + 1, 1); (2147450880 + M8 + sML + 1, 1)].
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqs_aclose.
    all: kx_mem.
    all: sd_rbf.
    all: (unfold held in TRANS, CONT, LF0, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML, HK, L1, L2, L3, L4, L5, L6, L7, NX, NXB1, NXB2, NXB3, V7, V8, PLL, POF, PML, EL8, EO8, EM8, L16F, LJF; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqs_lfacts_bc; [exact LF0 | lia]
      | exact NX | lia | lia | lia | lia | lia ]).
Qed.

End CANSEC1.
