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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ad_at.
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

Lemma ad_update : forall P OEND LLO LEND LOCV K, sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P ->
  ad_upd P OEND LLO LEND LOCV K -> ad_exec P OEND LLO LEND LOCV K -> ad_rl1 P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK  CONT1 CONT2 .
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold ad_rl1. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP nLL aLL bLL vLL nOF bOF nML bML mlv ofs x1 x6 x7 x10 x12 x22 x28 x29 x30 INV LF NX HA1 HV HM.
  unfold ad_upd in CONT1. unfold ad_exec in CONT2.  cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in HK, CONT1, CONT2.
  pose proof (sqd_linv_frame _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS.
  
  pose proof (sqd_bm_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (UBM & RBM & RBMS). cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in UBM, RBM, RBMS.
  apply (sqd_lopen_k _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqd_frame sqd_ffr] in FR, FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sqd_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  unfold sqd_next in NX. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in NX. pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  rewrite <- (Z_to_bv_bv_unsigned ofs). pose proof (kx_u64_range ofs) as HO. remember (bv_unsigned ofs) as ofz eqn:Eofz. clear Eofz ofs.
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
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (PA : 0 < 2^aLL <= 65536) by (clear - HA1; split; [apply Z.pow_pos_nonneg; lia | change 65536 with (2^16); apply Z.pow_le_mono_r; lia]).
  assert (HV' : 0 <= vLL <= 131071) by (clear - HV; lia). assert (HM' : 0 <= mlv <= 262143) by (clear - HM; lia).
  
  hold TRANS. hold CONT1. hold CONT2. hold LF0. hold NX. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold L7. hold NX3. hold NX6. hold NX9. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp 0x22180 128] [0x93c34; 0x93d44; 0x945c4; 0x945d4; 0x945e4] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange bc 0 9900000; KZRange K 1 98047;
     KZRange nLL 0 511; KZRange nOF 0 511; KZRange nML 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange bOF 0 9; KZRange bML 0 9;
     KZRange vLL 0 131071; KZRange mlv 0 262143;
     KZRange (2^bLL) 1 512; KZRange (2^bOF) 1 512; KZRange (2^bML) 1 512;
     KZWord (BITMASK + 4 * bLL) 4 (2^bLL - 1); KZWord (BITMASK + 4 * bOF) 4 (2^bOF - 1); KZWord (BITMASK + 4 * bML) 4 (2^bML - 1);
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZImg 0x22180 0x22220]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (0x22180, 128)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: try sqd_aclose.
  all: kx_mem.
  all: sd_rbf2.
  all: sd_land.
  all: (unfold held in TRANS, CONT1, CONT2, LF0, NX, HK, L1, L2, L3, L4, L5, L6, L7, NX3, NX6, NX9, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: first
    [ eapply (CONT1 _ _ c32 c40 c208);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq];
        split; [exact L1|]; split; [exact L2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
        eapply bit_ok_mono; [exact L7 | lia]
      | exact HO | lia | lia ]
    | eapply (CONT2 _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | eapply sqd_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia ] ].
Qed.

End CANSEC1.
