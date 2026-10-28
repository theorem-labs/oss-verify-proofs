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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2 AZ_seq_d_skit AZ_seq_d_xat AZ_seq_d_ad_at.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Lemma ad_slow_ok : forall P OEND LLO LEND LOCV K, sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P ->
  ad_tail2 P OEND LLO LEND LOCV K -> sqd_at_err P OEND LLO LEND LOCV -> ad_slow P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1 CONT2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold ad_slow. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 INV LF HO HL HM.
  unfold ad_tail2 in CONT1. unfold sqd_at_err in CONT2. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in HK, CONT1, CONT2.
  pose proof ST as ST0.
  pose proof (sqd_linv_frame _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS.
  apply (sqd_lopen_k _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqd_frame sqd_ffr] in FR, FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sqd_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 0 <= llv <= 262143 /\ 0 <= mlv <= 262143)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 HL HM; lia).
  (try hold CONT1; try hold CONT2; try hold TRANS; try hold HK; try hold LF; try hold LF0; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold ST0; try hold HO; try hold INV; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256] [] 80%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange OP 4096 (2^47);
     KZRange LP 4096 (2^47);
     KZRange LEND 4096 (2^47);
     KZRange OEND 4096 (2^47);
     KZRange PFX 4096 (2^47);
     KZRange llv 0 262143;
     KZRange mlv 0 262143;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in TRANS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in ST0; try unfold held in HO; try unfold held in INV; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x950d4) _ _ _ _) => (destruct (sqd_fr26_seq _ (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 LP llv mlv ofs FR L16F) as (LPC & SQC & F22 & FR24);
      pose proof (TRANS _ _ c32 c40 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MUL WMl KXMI FR24 FRF) as INV0;
      eapply evtF_cut;
      [ eapply (sqd_slow_spec (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND LLO LEND LOCV K); [exact ST0 | exact HK | exact INV0 | exact SQC | exact LF0 | exact HO | exact HL | exact HM]
      | ];
      clear FR FRF KXMI MUL WMl LPC SQC F22 FR24 INV0;
      intros ms2 (mc2 & r & lp2 & (t0_ & t1_ & t2_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & ->) & INV2 & HR2 & RES);
      replace (ret_pc (Z_to_bv 64 606588)) with (Z_to_bv 64 606588) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]);
      apply (sqd_lopen_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad2 jseq2 FR FRF L16F2 LJF2 SQB2 MI2 UFL2 USEQ2 RSQ2 RSQS2;
      pose proof (sqd_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2) as TRANS2; cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS2;
      assert (MUL2 : munch [(FRB, FRB + 216); (FF, FF + 256)] mc2 mc2) by apply munch_refl; assert (WMl2 : wmono bsegs mc2 mc2) by apply wmono_refl;
      clear SQB2 UFL2 USEQ2 RSQ2 RSQS2;
    (try hold CONT1; try hold CONT2; try hold TRANS; try hold HK; try hold LF; try hold LF0; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold ST0; try hold HO; try hold INV; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML; try hold INV2; try hold TRANS2; try hold RES; try hold L16F2; try hold LJF2;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256] [0x93e5c; 0x94748] 80%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange r 0 (2^64 - 1);
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in TRANS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in ST0; try unfold held in HO; try unfold held in INV; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in INV2; try unfold held in TRANS2; try unfold held in RES; try unfold held in L16F2; try unfold held in LJF2; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93e5c) _ _ _ _) => (destruct RES as [RE|(R1 & R2 & R3 & R4)]; [apply zd_is_error_true_iff in RE; exfalso; clear - RE KXBR HR2; lia|]; eapply (CONT1 _ _ c32 c40) with (r := r); [eapply TRANS2; [exact MUL2 | exact WMl2 | first [exact KXMI | exact MI2] | exact FR | exact FRF] | eapply sqd_lfacts_lp; [exact LF0 | clear - R3 R4 L2 HL; lia] | clear - HR2; lia | exact R2])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94748) _ _ _ _) => (eapply (CONT2 _ _ c32 c40) with (r := r); [eapply TRANS2; [exact MUL2 | exact WMl2 | first [exact KXMI | exact MI2] | exact FR | exact FRF] | exact HR2 | left; apply zd_is_error_true_iff; clear - KXBR HR2; lia])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end))
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
Qed.

End CANSEC1.
