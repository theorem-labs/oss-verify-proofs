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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase AZ_seq_d_iat AZ_seq_d_ikit AZ_seq_d_ickit.
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

Lemma sqd_i1_ok : forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> zd_initfse_stmtA ->
  (w_LLT P + 4104 < 2^47 /\ w_OFT P + 2056 < 2^47 /\ w_MLT P + 4104 < 2^47) ->
  ai_I3 P OEND LLO LEND LOCV -> ai_I1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST IFS TST CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [ai_I1 sqd_iregs sqd_ifrN sqd_ifrI sqd_imidA sqd_ic176A sqd_iffB]. cbn [app w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 jb j48 jm jc144 jc168 j176 jd jseq jpad j72 p0 p1 p2 cw A0 bc ptr x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 INV EA0 HBC BOK.
  subst A0.
  cbv delta [ai_I3 sqd_iregs sqd_ifrN sqd_ifrI sqd_imidC sqd_ic176A sqd_iffC] in CONT. cbn [app w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in CONT.
  (* [comment removed for export] *)
  pose proof INV as (FR0 & FRF0 & IREST).
  destruct (sqd_cbst48 m1 FF [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] j72 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FRF0) as (u1 & u2 & j88 & FRF1).
  cbn [app] in FRF1.
  assert (INV1 : sqd_iinv (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND LLO LEND LOCV m1 _ _) by (exact (conj FR0 (conj FRF1 IREST))).
  clear INV FR0 FRF0 FRF1 IREST.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (sqd_initfse_ispec (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND LLO LEND LOCV m1 _ cw bc jpad ptr [] u1 u2 [CB 32 j88; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] LLT tLL K_LL 64 (FF + 72) (DCTX + 26692) (2147450880 + D8 + 3336));
      [ exact ST | exact IFS | exact INV1 | cbn [w_LLT w_OFT w_MLT w_tLL w_tOF w_tML]; left; split; [reflexivity | split; reflexivity] | exact TST
      | cbn [cells_size csize Nat.add length w_FF]; clear; lia | cbn [cells_size csize Nat.add length]; clear; lia | cbn [cells_size csize Nat.add length]; clear; lia
      | clear - HBC; lia | clear; lia | exact BOK ]. }
  clear INV1. cbv delta [sqd_initfse_ipost sqd_iregs]. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros ms2 (m2 & cw2 & bc2 & jpad2 & ptr2 & sv & t0_ & t1_ & t2_ & a0_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & -> & INV2 & HST & HBC2 & BOK2).
  replace (ret_pc (Z_to_bv 64 606496)) with (Z_to_bv 64 606496) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  cbv delta [sbd_cells] in INV2. cbn [app] in INV2.
  pose proof (sqd_iinv_frame _ _ _ _ _ m2 _ _ ST INV2) as TRANS. cbn [w_FRB w_FF] in TRANS.
  apply (sqd_iopen_k _ _ _ _ _ _ _ _ ST INV2); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros FR FRF PT SQB MI UFL USEQ RSQ RSQS UD RD RDS.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. AZ_seq_d_lkit.sd_static_open ST. unfold held in RGB.
  unfold dctx_ptrs in PT. unfold DCTX_SIZEOF in UD, RD, RDS.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m2 m2) by apply munch_refl. assert (WMl : wmono bsegs m2 m2) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 0 <= D8 /\ 8 * D8 + 95992 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ DCTX = 8 * D8 /\
               4096 <= LLT /\ LLT + 4104 <= 2^47 /\ 4096 <= OFT /\ OFT + 2056 <= 2^47 /\ 4096 <= MLT /\ MLT + 4104 <= 2^47)
    by (clear - S1 S2 S3 S4 S5 S6 S7 S19 S20 S21 S22 S23 S61; destruct S61 as (_ & _ & _ & _ & ED8 & _); lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & ED8 & RG7 & RG8 & RG9 & RG10 & RG11 & RG12).
  assert (DJD1 : FRB + 280 <= DCTX \/ DCTX + 95992 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX \/ DCTX + 95992 <= FF) by (unfold held in S54; clear - S54; lia).
  clear SQB UFL USEQ RSQ RSQS.
  hold CONT. hold HBC2. hold BOK2. hold HST. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF, PT) [KAApp FRB 280; KAApp FF 256; KAUnp DCTX 95992] [0x96148] 40%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6459392 (2^47); KZAlign SPV 16;
     KZRange OEND 4096 (2^47); KZRange D8 0 (2^44); KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange DST 4096 (2^47);
     KZRange LLT 4096 (2^47 - 4104); KZRange OFT 4096 (2^47 - 2056); KZRange MLT 4096 (2^47 - 4104);
     KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj FRB 280 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256); (DCTX, 32)].
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611744) _ _ _ _) => kx_trap_fast end).
  all: try sqd_aclose.
  all: kx_mem.
  all: (unfold held in CONT, HBC2, BOK2, HST, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96148) _ _ _ _) =>
        (eapply CONT;
         [ eapply sqd_iinv_eq2; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; sqd_cells_eq | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; reflexivity ]
         | clear; lia
         | clear - HBC2; lia
         | exact BOK2
         | exact HST ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal:" UNEXPECTED
    end.
Qed.

End CANSEC1.
