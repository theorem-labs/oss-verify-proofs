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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_a1_at AZ_seq_s_akit3.
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

Ltac sd_land ::=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  | _ : context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] |- _ =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  end.

Lemma a1_update : forall P OEND LLO LEND LOCV K, sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LEND + 32 <= OEND ->
  a1_upd P OEND LLO LEND LOCV K -> a1_execb P OEND LLO LEND LOCV K -> a1_slow P OEND LLO LEND LOCV K -> a1_brk P OEND LLO LEND LOCV K -> a1_rl1 P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK HLBE HL32  CONT1 CONT2 CONTS CONTK.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold a1_rl1. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 c0 c8 c208 cw bc ptr sLL sOF sML p0 p1 p2 LP OP nLL aLL bLL vLL nOF bOF nML bML mlv ofs x6 x7 x10 x12 x19 x22 x24 x28 x30 INV LF NX HA1 HV HM.
  unfold a1_upd in CONT1. unfold a1_execb in CONT2. unfold a1_slow in CONTS. unfold a1_brk in CONTK.  cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in HK, CONT1, CONT2, CONTS, CONTK.
  pose proof (sqs_linv_frame _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (DCTX + 30360)) (Z_to_bv 64 (2147450880 + D8 + 3795)) (Z_to_bv 64 LEND) c208 ofs cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in TRANS.
  
  pose proof (sqs_bm_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (UBM & RBM & RBMS). cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in UBM, RBM, RBMS.
  pose proof (sqs_lbe_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ED8 & D8L & D8H & RDZ & RZ1 & RH8 & _). cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in ED8, D8L, D8H, RDZ, RZ1, RH8.
  pose proof (sqs_linv_lbe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEND INV HLBE) as LBK. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in LBK.
  apply (sqs_lopen_k _ _ _ _ _ m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (DCTX + 30360)) (Z_to_bv 64 (2147450880 + D8 + 3795)) (Z_to_bv 64 LEND) c208 ofs cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqs_frame sqs_ffr] in FR, FRF. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sqs_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  unfold sqs_next in NX. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in NX. pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  rewrite <- (Z_to_bv_bv_unsigned ofs) in INV, FR |- *. pose proof (kx_u64_range ofs) as HO. remember (bv_unsigned ofs) as ofz eqn:Eofz. clear Eofz ofs.
  sd_static_open ST. unfold held in RGB.
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  assert (RS : 0 <= bc <= 9900000 /\ 1 <= K <= 98047) by (clear - L6 HK S16; lia).
  assert (RP : 1 <= 2^bLL <= 512 /\ 1 <= 2^bOF <= 512 /\ 1 <= 2^bML <= 512 /\ nLL <= 511 /\ nOF <= 511 /\ nML <= 511).
  { clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 PLL POF PML.
    pose proof (Z.pow_pos_nonneg 2 bLL). pose proof (Z.pow_pos_nonneg 2 bOF). pose proof (Z.pow_pos_nonneg 2 bML). lia. }
  pose proof (bitmask_know m1 bLL MI ltac:(clear - NX1; lia)) as BK1.
  pose proof (bitmask_know m1 bOF MI ltac:(clear - NX4; lia)) as BK2.
  pose proof (bitmask_know m1 bML MI ltac:(clear - NX7; lia)) as BK3.
  unfold BITMASK in BK1, BK2, BK3.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (PA : 0 < 2^aLL <= 65536) by (clear - HA1; split; [apply Z.pow_pos_nonneg; lia | change 65536 with (2^16); apply Z.pow_le_mono_r; lia]).
  assert (HV' : 0 <= vLL <= 131071) by (clear - HV; lia). assert (HM' : 0 <= mlv <= 262143) by (clear - HM; lia).
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= OEND < 2^47)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11; lia).
  assert (RGD : 4096 <= DCTX /\ DCTX + 95992 < 2^47) by (clear - RG S19 S20; lia).
  assert (DJD1 : FRB + 280 <= DCTX + 30360 \/ DCTX + 30360 + 8 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX + 30360 \/ DCTX + 30360 + 8 <= FF) by (unfold held in S54; clear - S54; lia).
  
  hold TRANS. hold CONT1. hold CONT2. hold CONTS. hold CONTK. hold LF0. hold NX. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold L7. hold NX3. hold NX6. hold NX9. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold S72. hold S73. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 280; KAApp FF 256; KAUnp 0x22180 128] [0x90164; 0x902a0; 0x903c4; 0x90db8; 0x90b28; 0x90b38; 0x90b48] 470%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange bc 0 9900000; KZRange K 1 98047;
     KZRange nLL 0 511; KZRange nOF 0 511; KZRange nML 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange bOF 0 9; KZRange bML 0 9;
     KZRange vLL 0 131071; KZRange mlv 0 262143;
     KZRange (2^bLL) 1 512; KZRange (2^bOF) 1 512; KZRange (2^bML) 1 512;
     KZWord (BITMASK + 4 * bLL) 4 (2^bLL - 1); KZWord (BITMASK + 4 * bOF) 4 (2^bOF - 1); KZWord (BITMASK + 4 * bML) 4 (2^bML - 1);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZImg 0x22180 0x22220;
     KZRange OP 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange DCTX 4096 (2^47 - 95992); KZRange D8 512 (2^44 - 11999);
     KZWord (DCTX + 30360) 8 LEND; KZWord (2147450880 + D8 + 3795) 1 0;
     KZDisj FRB 280 (DCTX + 30360) 8; KZDisj FF 256 (DCTX + 30360) 8]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (0x22180, 128); (DCTX + 30360, 8); (2147450880 + D8 + 3795, 1)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: try sqs_aclose.
  all: kx_mem.
  all: sd_rbf2.
  all: sd_land.
  all: (unfold held in TRANS, CONT1, CONT2, CONTS, CONTK, LF0, NX, HK, L1, L2, L3, L4, L5, L6, L7, NX3, NX6, NX9, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90164) _ _ _ _) => (eapply CONT1;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqs_lfacts; cbn [v_DST v_tLL v_tOF v_tML v_SEQ v_sq];
        split; [exact L1|]; split; [exact L2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
        eapply bit_ok_mono; [exact L7 | lia]
      | exact HO | lia | lia ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x902a0) _ _ _ _) => (eapply CONT2;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqs_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia | first [reflexivity | lia] | lia | first [reflexivity | lia] ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x903c4) _ _ _ _) => (eapply CONTS;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqs_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia | first [reflexivity | lia] | first [reflexivity | lia] | lia ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x90db8) _ _ _ _) => (eapply CONTK;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqs_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia | lia | first [reflexivity | lia] ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
    | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
    end.
Qed.

End CANSEC1.
