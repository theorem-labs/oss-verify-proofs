(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM KXCell.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_z4m AF_huf_w4m AF_huf_w4sb AF_huf_w4skx AF_huf_w4skx1 AF_huf_w4s01k AF_huf_w4skx2 AF_huf_w4s02k AF_huf_w4s04k.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_w4s1k AF_huf_w4s1r AF_huf_w4s1x AF_huf_w4s1c.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_tbl_iface2 AF_huf_bitd AF_huf_w4s12_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_w4s31z AF_huf_w4s31c AF_huf_w4s3_iface AF_huf_w4s3_iface2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_w4s3b AF_huf_w4s3_iface3 AF_huf_w4s34z AF_huf_w4s34z2 AF_huf_w4s34c.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_w4s0f AF_huf_w4s1 AF_huf_w4s31 AF_huf_w4s32 AF_huf_w4s33 AF_huf_w4s34.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_dec4x1A AF_huf_afa6.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4sf () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s34;w4s34_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWBAF_huf_w4s3_iface3:w4s34_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s33;w4s33_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWBAF_huf_w4s3_iface2:w4s33_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s32;w4s32_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_w4s3_iface:w4s32_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s31;w4s31_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWBAF_huf_w4s12_iface9w4s2_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_w4s1:w4s1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWBAF_huf_w4s12_iface9w4s1_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s0f9w4s0_slowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW=AMalloc_iface<AMallocIface00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5AsanW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC59OSSVerify5KrLib5AsanW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K59OSSVerify5KrLib5AsanW5ABase6abkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface<DTABLE_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX1;x1_table_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5Plain<RF_huf_iface8x1_bytesC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5AsanW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW;AF_huf_w4sf9w4sf_slowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW@AF_huf_w4s_iface=w4_slow_stmtAC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec=HufPure_HufX16deltX100C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface?HUF_DEC_STACK_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_afa6@fast_args_proofAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AF_huf_dec4x1A>dec_4x1_proofAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW;AF_huf_w4sf>w4_slow_proofAC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4SFIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -496).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WB l := (l AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
                      cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3
                      LOA LOS SPT SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS).
  Notation W4S := (AF_huf_w4s_iface.W4S ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation W4SF' mm sa sb bd4 := (W4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm sa sb bd4).

  Lemma w4sf_slow : w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4sf ()) ["CANSEC1"; "W4SFIN"] "h04LOOPh13S2Gh23S32h33S33h43S34p;yp;Rp;zp;{p-1p10000p4p710R0p8p1000Gp4p70P0p8g001>ly:Tg002AlR9Tg003Ilz0Tg004LlR1Tg005Tlz8Tg006WlR2Tg007^lz3Tg008alR4Tg009hlz5Tg00:ilR6Tg00<0l{7Tp,2rcR0p,2AIR1p,1LR2p,3RNGR3p,2stR4p,2LBR5p,6rng_fsR6p,2raR7p,2spR8p,2gpR9p,2tpR:p,2s0R;p,2s1R<p,2s2R=p,2s3R>p,2s4R?p,2s5R@p,2s6RAp,2s7RBp,2s8RCp,2s9RDp,3s10REp,3s11RFp,2FRRGp,2fcRHp,2m0RIp,3DSTRJp,4dcapRKp,2SSRLp,2DTRMp,3mtlRNp,2tlROp,2loRPp,3srcRQp,5cellsRRp,3cbsRSp,3pdtRTp,3SBLRUp,3SBHRVp,4rstkRWp,2AHRXp,3NFKRYp,3ABLRZp,3MTLR[p,3TLMR\p,3HDTR]p,3TOKR^p,3ECBR_p,3LCBR`p,4DSTFRap,2DCRbp,3BYSRcp,3NSMRdp,3S16Rep,4SRCBRfp,3DJ1Rgp,3DJ2Rhp,3DJ3Rip,3LOARjp,3LOSRkp,3SPTRlp,4SP16Rmp,3TPARnp,4HINVRop,3RCLRpp,3RLORqp,3RHIRrp,3RRLRsp,3RRSRtp,3WSKRup,3WIMRvp,3WISRwp,3WFSRxMy:P0P1P2P3P4P5P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPSMR9P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgPhPiPjPkPlPmPnPoPpPqPrPsPtPuPvPwPxf0RyMz0P0P1P2P3P4P5P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPSMR1P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgPhPiPjPkPlPmPnPoPpPqPrPsPtPuPvPwPxPyMz8P0P1P2P3P4P5P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPSMR2P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgPhPiPjPkPlPmPnPoPpPqPrPsPtPuPvPwPxPyMz3P0P1P2P3P4P5P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPSMR4P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgPhPiPjPkPlPmPnPoPpPqPrPsPtPuPvPwPxPyMz5P0P1P2P3P4P5P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPSMR6P0P1P2P3P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgPhPiPjPkPlPmPnPoPpPqPrPsPtPuPvPwPxPyf1M{7b0b1b2b3b4o"). Qed.

End W4SFIN.

Theorem w4_slow_proofA : w4_slow_stmtA.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4sf ()) ["CANSEC1"] "h03ABLh12AHh22AIh33BYSh42DCh53DJ1h63DJ2h73DJ3h83DSTh94DSTFh:2DTh;3ECBh<1Fh=2FRh>3HDTh?4HINVh@1LhA2LBhB3LCBhC3LOAhD3LOShE3MTLhF3NFKhG3NSMhH3RCLhI3RHIhJ3RLOhK3RNGhL3RRLhM3RRShN3S16hO3SBHhP3SBLhQ4SP16hR3SPThS4SRCBhT2SShU3TLMhV3TOKhW3TPAhX3WFShY3WIMhZ3WISh[3WSKh\1bh]1ch^3cbsh_5cellsh`4dcapha2fchb2gphc1khd2lohe2m0hf3mtlhg1phh2pbhi3pdthj2rahk6rng_fshl4rstkhm2s0hn2s1ho3s10hp3s11hq2s2hr2s3hs2s4ht2s5hu2s6hv2s7hw2s8hx2s9hy2sphz3srch{2sth|2tlh}2tpp;1p;2p;7p;3p;xg00=1j1fTg00>8j1@Tg00>Xj10Tg00?=j1>Tg00?[j1FTg00@>j12Tg00@cj2WTg00AOj1UTg00B1j7RTg00Boj1PTg00Chj3<Tg00Daj38Tg00E8j1eTg00EQj1cTg00FIj1]Tg00GAj24Tg00G^j3XTg00HSj13Tg00I1j21Tg00IMj26Tg00Ihj1LTg00Jaj1ETg00Kej2VTg00Lhj2=Tg00MEj2KTg00Mbj1TTg00NBj1STg00OBj3QTg00Oaj3?Tg00P;j29Tg00P[j17Tg00Q;j2ITg00QUj2ATg00Qoj2:Tg00RKj3OTg00Rlj2DTg00SIj1NTg00T?j2BTg00Tij1MTg00U`j2dTg00V@j2bTg00Vfj1_Tg00Wlj2^Tg00Xgj1\Tg00Y`j1ZTg00ZYj1[Tg00[Sj2YTg00\Lj3GTg00]?lx`Tg00^?j1aTf0R0#0#0p=Jg00_HR1g00_fR27?0p=C%00#0#0#0p=5%20#2p=H%20#2#2#2p=;p,2rcR3#fg00`DR4g00a>R5g00b7g00c2R6#@p-0\5\4g00ckR4#0R5#JR7#0R8#0R9#0R:#>R;#FR<%25#>/W<%>9#F%>7#FR7#U\<%@1g00dP#@%@7R=g000GR>g00ePP3fVR?fUR@fTRAfSRBfRRCf>RDFR%P2f1RE;<0=86@#e^c1^<1A860@%cERF%]E,4F5X3[^\6%34RFf<RG'1%24RH#0RI#0#3,1G'6f=RJ/4F,1Gf8RF#Lf?RK%ED3<fWRL586f;RM/VD%35R51=5K'K#T%SG5Q79?=M197G#7f@R7,=5,K55?1fFR=#CfERN#C'6%L0ROfGRP;<=f\RQ586Xh>,I>'A112=%39,=5,:='61120%J:R:#3,:0'6X]1fAR95O1fBRR,91#7%2I#0#3,=5':%38R8fHR5'1fDRI,91#7,:21D9R9<ORfbRO586fKR6,1R191=#7,46R2/19'6'6Xg>,I>[fIR>%E5'4fJRS'1191N#7,4S/1>'AfMRTfLRU'4/16112T'A%ES,46fNR2'1142T/16'A%N3RV%5:R:#3'4/1>1B;Og00fM'D,1SfcRW,B;/48fiRX#M':fdRY,B;/d8#Cg00gT,b;9?<W%_@1^?5%\>fPR8'11B;X%ZS'1%[6,1VfpRV/YUfqR;frRZ#M/DA7GA%5:#3%04#2#H#;#0#2#5#5#5#35GZfsR:%HH#;#;#;#0#2#0#5#5#5#3%04#2#H#;#0#2#0#5#5#33GP;fuR4ftRHO2fwfvP4PHP:PZP;PVfofnfmflfkfjPXfhfgfffePYPWPOfaf`f_f^f]PQf[fZfYfXPLP?P@PAPBPCfQP8fOP2PTPUP6PSP>P5PPP=PNPIfCPRP9P7PKPDPJPGPMf:f9PFf7f6f5f4f3f2PEP0Mx`WXWZWYW[WMWLWIWJWHW?WWWQWRWDWCW7W6W5WSWNWGW3W4W9WBW;WVW>WUWEW0WFW1WlXO1XP1WiW^W_WzXd1X|1Xf1X:1XT1X`1X81WeWaW=Xp<Xo<Xx<Xw<Xv<Xu<Xt<Xs<Xr<Xq<Xn<Xm<X}<Xb<Xy<WjWkWAW{WKW@W2%a3eo"). Qed.

Theorem dec_4x1_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  dec4_int_stmtA AI rng_fs x1_tabA AHUF_DX1_4X.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4sf ()) ["CANSEC1"] "h02AIh16rng_fsp;1p;5g00=1j12Tg00hHj11Tg00iOj50Tp,2rcR0#2g00`Dg00a>p-0[[P0f1f0g00jW%10D0W1W0o"). Qed.

End CANSEC1.
