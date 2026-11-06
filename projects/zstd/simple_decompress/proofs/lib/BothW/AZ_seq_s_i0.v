(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_fin.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_i0_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> sqs_bit_init_stmtG APZD_BITINIT ->
  sqs_at_ierr P OEND LLO LEND LOCV -> ai_I1 P OEND LLO LEND LOCV -> ai_I0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST BI IERR CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [ai_I0 sqs_iregs sqs_ifrI sqs_imidA sqs_iffA]. cbn [app v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 ja jb j128 j152 j176 jd jseq jbd j72 p0 p1 p2 T40 T48 T56 T64 T120 T160 T168 T192 A6 T32 x5 x6 x7 x13 x14 x15 x16 x17 x18 x25 x27 x28 x29 x30 x31
         INV E40 E48 E56 E64 E120 E160 E168 E192 EA6 ET32.
  subst T40 T48 T56 T64 T120 T160 T168 T192 A6 T32.
  cbv delta [ai_I1 sqs_iregs sqs_ifrN sqs_ifrI sqs_imidA sqs_iffB] in CONT. cbn [app v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in CONT.
  cbv delta [sqs_at_ierr] in IERR. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in IERR.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (sqs_bitinit_ispec (mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND LLO LEND LOCV m1 _ jbd j72 p0 p1 p2 (DCTX + 26692) (2147450880 + D8 + 3336)); [exact ST | exact BI | exact INV]. }
  clear INV. cbv delta [sqs_bitinit_ipost sqs_iregs sqs_iffA sqs_iffB]. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros ms2 (m2 & r & t0_ & t1_ & t2_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & -> & RES).
  replace (ret_pc (Z_to_bv 64 591384)) with (Z_to_bv 64 591384) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  remember (zlen sq) as n eqn:En.
  assert (HN : 1 <= n < 2^47).
  { pose proof (st13 _ _ _ _ _ ST) as X13. pose proof (st14 _ _ _ _ _ ST) as X14. pose proof (st15 _ _ _ _ _ ST) as X15. cbv beta iota in X13, X14, X15. clear - X13 X14 X15 En. lia. }
  destruct RES as [(-> & cw & bc & jpad & HBC & INV2) | (ER & HR & jbd2 & INV2)].
  - (* [comment removed for export] *)
  pose proof (sqs_iinv_frame _ _ _ _ _ m2 _ _ ST INV2) as TRANS. cbn [v_FRB v_FF] in TRANS.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV2); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros FR FRF PT SQB MI UFL USEQ RSQ RSQS UD RD RDS.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. AZ_seq_s_lkit.sd_static_open ST. unfold held in RGB.
  unfold dctx_ptrs in PT. unfold DCTX_SIZEOF in UD, RD, RDS.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m2 m2) by apply munch_refl. assert (WMl : wmono bsegs m2 m2) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 0 <= D8 /\ 8 * D8 + 95992 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ DCTX = 8 * D8 /\
               4096 <= LLT /\ LLT + 4104 <= 2^47 /\ 4096 <= OFT /\ OFT + 2056 <= 2^47 /\ 4096 <= MLT /\ MLT + 4104 <= 2^47)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20 S21 S22 S23 S61; destruct S61 as (_ & _ & _ & _ & ED8 & _); lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & ED8 & RG7 & RG8 & RG9 & RG10 & RG11 & RG12).
  assert (DJD1 : FRB + 280 <= DCTX \/ DCTX + 95992 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX \/ DCTX + 95992 <= FF) by (unfold held in S54; clear - S54; lia).
  clear SQB UFL USEQ RSQ RSQS.
  hold CONT. hold En. hold HBC. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF, PT) [KAApp FRB 280; KAApp FF 256; KAUnp DCTX 95992] [0x96148; 0x92f8c] 40%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6459392 (2^47); KZAlign SPV 16;
     KZRange OEND 4096 (2^47); KZRange D8 0 (2^44); KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange DST 4096 (2^47);
     KZRange LLT 4096 (2^47 - 4104); KZRange OFT 4096 (2^47 - 2056); KZRange MLT 4096 (2^47 - 4104); KZRange n 1 (2^47);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (DCTX, 32)].
  all: try sqs_aclose.
  all: kx_mem.
  all: (unfold held in CONT, En, HBC, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96148) _ _ _ _) =>
        (eapply CONT;
         [ eapply sqs_iinv_eq2; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; sqs_cells_eq | cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; subst n; reflexivity ]
         | clear; lia
         | clear - HBC; lia
         | subst n; apply sqs_bitd_ptr_ok ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal:" UNEXPECTED
    end.

  - (* [comment removed for export] *)
    apply zd_is_error_true_iff in ER. unfold ZE_maxCode in ER.
  pose proof (sqs_iinv_frame _ _ _ _ _ m2 _ _ ST INV2) as TRANS. cbn [v_FRB v_FF] in TRANS.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV2); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros FR FRF PT SQB MI UFL USEQ RSQ RSQS UD RD RDS.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. AZ_seq_s_lkit.sd_static_open ST. unfold held in RGB.
  unfold dctx_ptrs in PT. unfold DCTX_SIZEOF in UD, RD, RDS.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m2 m2) by apply munch_refl. assert (WMl : wmono bsegs m2 m2) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 0 <= D8 /\ 8 * D8 + 95992 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ DCTX = 8 * D8 /\
               4096 <= LLT /\ LLT + 4104 <= 2^47 /\ 4096 <= OFT /\ OFT + 2056 <= 2^47 /\ 4096 <= MLT /\ MLT + 4104 <= 2^47)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20 S21 S22 S23 S61; destruct S61 as (_ & _ & _ & _ & ED8 & _); lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & ED8 & RG7 & RG8 & RG9 & RG10 & RG11 & RG12).
  assert (DJD1 : FRB + 280 <= DCTX \/ DCTX + 95992 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX \/ DCTX + 95992 <= FF) by (unfold held in S54; clear - S54; lia).
  clear SQB UFL USEQ RSQ RSQS.
  hold IERR. hold En. hold ER. hold HR. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF, PT) [KAApp FRB 280; KAApp FF 256; KAUnp DCTX 95992] [0x96148; 0x92f8c] 40%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6459392 (2^47); KZAlign SPV 16;
     KZRange OEND 4096 (2^47); KZRange D8 0 (2^44); KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange DST 4096 (2^47);
     KZRange LLT 4096 (2^47 - 4104); KZRange OFT 4096 (2^47 - 2056); KZRange MLT 4096 (2^47 - 4104); KZRange r (2^64 - 119) (2^64 - 1);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (DCTX, 32)].
  all: try sqs_aclose.
  all: kx_mem.
  all: (unfold held in IERR, En, ER, HR, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - ER HR; lia end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x92f8c) _ _ _ _) =>
        (sqs_blob_seg FR 11%nat 28%nat; sqs_blob_seg FR 0%nat 8%nat; sqs_blob_seg FRF 0%nat 7%nat;
         eapply IERR; eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal:" UNEXPECTED
    end.

Qed.

End CANSEC1.
