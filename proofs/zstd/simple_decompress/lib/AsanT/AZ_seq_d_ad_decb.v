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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ad_at AZ_seq_d_ad_deca.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma ad_decode_c1 : forall P OEND LLO LEND LOCV K, sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P ->
  ad_dec P OEND LLO LEND LOCV K -> ad_head_sel (fun a => a = 1) P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold ad_head_sel. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x27 x28 x29 x30 INV LF (O8s & aOFs & EO8s & RDs & RAs & SELs).
  unfold ad_dec in CONT. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in HK, CONT.
  apply (sqd_lopen_k _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF0 L16F LJF SQB MI UFL USEQ RSQ RSQS.
  pose proof LF as LF0. apply (sqd_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  apply (sqd_dec_k _ _ _ _ _ K _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP jpad ST INV LF); [cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; clear; lia | exact HK | exact FRF0 |]; cbn [sqd_ffr8 w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1];
    intros L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML EL8 EO8 EM8 GL8 GO8 GM8 WLL0 WLL1 WLL2 WLL3 WOF0 WOF1 WOF2 WOF3 WML0 WML1 WML2 WML3 ZLL ZOF ZML RWLL RWOF RWML RZLL RZOF RZML FRF
           NX NXB1 NXB2 NXB3 N1 N2 N3 NB1 NB2 NB3 A1 A2 A3 RV1 RV2 RV3 RV4 RV5 RV6 V7 V8 PLL POF PML RS1 RS2 RS3 RS4.
  assert (EQA : aOFs = aOF).
  { clear - EO8 EO8s RDs WOF1 A2 RAs. assert (EO : O8s = O8) by lia. subst O8s. rewrite WOF1 in RDs.
    rewrite !kxl_w1 in RDs. pose proof (f_equal (fun o => match o with Some (b :: _) => bv_unsigned b | _ => 0 end) RDs) as RD2; cbv beta iota in RD2.
    rewrite !b8_lit in RD2 by lia. symmetry; exact RD2. }
  cbn beta in SELs. rewrite EQA in SELs. clear EQA EO8s RDs RAs aOFs.
  clear FRF0. cbv delta [sqd_ffr8] in FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FRF.
  pose proof (sqd_linv_frame8 _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP L8 O8 M8 ST INV EL8 EO8 EM8) as TRANS. cbn [sqd_frame sqd_ffr8 w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS.
  cbn [sqd_frame w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR.     (* [comment removed for export] *)
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (CASES : aOF = 1 /\ vOF = 1) by (clear - A2 V7 V8 SELs; lia). clear SELs.
  hold TRANS. hold CONT. hold LF0. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold L7. hold NX. hold NXB1. hold NXB2. hold NXB3. hold V7. hold V8. hold PLL. hold POF. hold PML. hold EL8. hold EO8. hold EM8. hold L16F. hold LJF.
  destruct CASES as [C C'].
  kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256] [0x93b4c] 320%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange L8 512 (2^44); KZRange O8 512 (2^44); KZRange M8 512 (2^44);
     KZRange sLL 0 511; KZRange sOF 0 511; KZRange sML 0 511; KZRange bc 0 9900000;
     KZRange nLL 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange vLL 0 131072;
     KZRange nOF 0 511; KZRange aOF 1 1; KZRange bOF 0 9; KZRange vOF 1 1;
     KZRange nML 0 511; KZRange aML 0 16; KZRange bML 0 9; KZRange vML 0 131075;
     KZWord (8 * L8 + 8 * sLL + 8) 2 nLL; KZWord (8 * L8 + 8 * sLL + 10) 1 aLL; KZWord (8 * L8 + 8 * sLL + 11) 1 bLL; KZWord (8 * L8 + 8 * sLL + 12) 4 vLL;
     KZWord (8 * O8 + 8 * sOF + 8) 2 nOF; KZWord (8 * O8 + 8 * sOF + 10) 1 aOF; KZWord (8 * O8 + 8 * sOF + 11) 1 bOF; KZWord (8 * O8 + 8 * sOF + 12) 4 vOF;
     KZWord (8 * M8 + 8 * sML + 8) 2 nML; KZWord (8 * M8 + 8 * sML + 10) 1 aML; KZWord (8 * M8 + 8 * sML + 11) 1 bML; KZWord (8 * M8 + 8 * sML + 12) 4 vML;
     KZWord (2147450880 + L8 + sLL + 1) 1 0; KZWord (2147450880 + O8 + sOF + 1) 1 0; KZWord (2147450880 + M8 + sML + 1) 1 0;
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (8 * L8 + 8 * sLL + 8, 8); (8 * O8 + 8 * sOF + 8, 8); (8 * M8 + 8 * sML + 8, 8);
     (2147450880 + L8 + sLL + 1, 1); (2147450880 + O8 + sOF + 1, 1); (2147450880 + M8 + sML + 1, 1)].
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: sd_rbf.
    all: (unfold held in TRANS, CONT, LF0, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML, HK, L1, L2, L3, L4, L5, L6, L7, NX, NXB1, NXB2, NXB3, V7, V8, PLL, POF, PML, EL8, EO8, EM8, L16F, LJF; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: (eapply (CONT _ _ c32 c40 c208);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqd_lfacts_bc; [exact LF0 | lia]
      | exact NX | lia | lia | lia | lia | lia ]).
Qed.

End CANSEC1.
