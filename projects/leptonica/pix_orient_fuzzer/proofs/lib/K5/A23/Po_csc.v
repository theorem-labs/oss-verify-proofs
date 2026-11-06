(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface RT_fk RT_fk_iface Bi_fktw D_iface D_defs Po_rows
     Po_dilate_defs Po_morph2_defs Po_null_defs Po_pmcs_defs Po_csc_defs
     Po_csc_front_c0 Po_csc_front_c16 Po_csc_t30_c0 Po_csc_t30_c16 Po_csc_t8_c0 Po_csc_t8_c16 Po_csc_end_c0 Po_csc_end_c16 Po_csc_r_c0 Po_csc_r_c16 Po_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_csc () := "C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A23;Po_csc_defs7csc_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_csc_defs5csc_QC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_csc_end_c09csc_end_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_csc_r_c09csc_r30_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_csc_t30_c09csc_t30_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_csc_r_c08csc_r8_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_csc_t8_c08csc_t8_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23?Po_csc_front_c0;csc_front_0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_csc_end_c16:csc_end_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_csc_r_c16:csc_r30_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_csc_t30_c16:csc_t30_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_csc_r_c169csc_r8_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_csc_t8_c169csc_t8_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23@Po_csc_front_c16<csc_front_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_csc_defsLpixCloseSafeCompBrick3_of_alC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_cscIpixCloseSafeCompBrick3_c0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_cscJpixCloseSafeCompBrick3_c16C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CSC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
(* [comment removed for export] *)
Hypothesis CSELS : selectComposableSels_cps RT.          (* [comment removed for export] *)
Hypothesis ADDB : pixAddBorder32_rows_cps RT.             (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis DIL : pixDilate2_cps RT.                       (* [comment removed for export] *)
Hypothesis ERO : pixErode_given2_cps RT.                  (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis PDES : pixDestroy_cpsF RT.                     (* [comment removed for export] *)
Hypothesis PDN : pixDestroy_null_cpsF RT.                 (* [comment removed for export] *)
Hypothesis REMB : pixRemoveBorder32_rows_cps RT.          (* [comment removed for export] *)
Hypothesis COPYG : pixCopy_given_cps RT.                  (* [comment removed for export] *)
Hypothesis SELD : selDestroy_cps RT.                      (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis DILN : pixDilate_null0_cps RT.                 (* [comment removed for export] *)
Hypothesis ERON : pixErode_null0_cps RT.                  (* [comment removed for export] *)
Hypothesis REMBN : pixRemoveBorder_null_cps RT.           (* [comment removed for export] *)
Hypothesis CPYN : pixCopy_srcnull_cps RT.                 (* [comment removed for export] *)

Theorem pixCloseSafeCompBrick3_c0 : pixCloseSafeCompBrick3_case RT 0.
Proof using AF GP FKC CSELS ADDB DIL ERO PDES PDN REMB COPYG SELD DILN ERON REMBN CPYN.
ltac2:(KReplay.run1 (kr_t_Po_csc ()) ["CSC"] "h03CTXh11Fh23PMch32cvh42gph52hsh62loh71mh84pix1h92rah:3rash;2s0h<2s1h=3s10h>3s11h?2s2h@2s3hA2s4hB2s5hC2s6hD2s7hE2s8hF2s9hG3usphH1vhI2vshJ2Σp;1p;2p;>p;Hp;Tp;Up;8g0000j1?Tg000hj10Tg001Mj11Tg001kj12Tg002Nj1>Tg0033j2:Tg003_j17Tg004Aj14Tg004al>5Tg005`lH6Tg006]lT3Tg007`lU8Tg008alT9Tg009dlU=Tg00:dlT<Tg00;ej8;Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,5CSELSp,4ADDB%?0R4g00<lp-0[R5g00=b#0R6#0#0R7#0#0#0#1#2R8%>6#1/:8R6g00>GR9%17#2#7\8R7g00>eR:g00?bR;%49R<P0fIR=fHR>fGR?fFR@f8RAf7RBf6RCf5RDf4REf3RFf2RGf1RHf0RIM>5RJP0P1P2P3p,3DILRKp,3ERORLfJRMP=P>P?P@fERNfDROfCRPfBRQfARRf@RSf?RTf>RUf=RVf<RWf;RXf:RYf9RZPAPBPCPDPEPFPGPHPIP0PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPFPGMH6R[P0P1P2P3p,4PDESp,3PDNR\p,4REMBp,5COPYGp,4SELDR]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMT3R^P0P1P2P3p,4DILNR_p,4ERONR`P\p,5REMBNRap,4CPYNRbP]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMU8MT9W0W:W3WHXI9X59X89W7X69WGW1X48X>8X=8XF8XE8XD8XC8XB8XA8X@8X?8X<8X;8W9W2WJP0P1P2P3PKPLPMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIP[P^P0P1P2P3P_P`P\PaPbP]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMU=MT<X0JX:<X3;XH:XI9X59X89X77X69XG9X16X48X>8X=8XF8XE8XD8XC8XB8XA8X@8X?8X<8X;8X98X25XJ4G;o"). Qed.

Theorem pixCloseSafeCompBrick3_c16 : pixCloseSafeCompBrick3_case RT 16.
Proof using AF GP FKC CSELS ADDB DIL ERO PDES PDN REMB COPYG SELD DILN ERON REMBN CPYN.
ltac2:(KReplay.run1 (kr_t_Po_csc ()) ["CSC"] "h03CTXh11Fh23PMch32cvh42gph52hsh62loh71mh84pix1h92rah:3rash;2s0h<2s1h=3s10h>3s11h?2s2h@2s3hA2s4hB2s5hC2s6hD2s7hE2s8hF2s9hG3usphH1vhI2vshJ2Σp;1p;2p;>p;Hp;Tp;Up;8g0000j1?Tg000hj10Tg001Mj11Tg001kj12Tg002Nj1>Tg0033j2:Tg003_j17Tg004Aj14Tg004al>5Tg005`lH6Tg00@`lT3Tg00AelU8Tg00BhlT9Tg00CmlU=Tg00DolT<Tg00F2j8;Tp,2RTR0p,2AFR1p,2GPR2p,3FKCR3p,5CSELSp,4ADDB%?0R4g00<lp-0[R5g00=b#0R6#0#0R7#0#0#0#1#2R8%>6#1/:8R6g00>GR9%17#2#7\8R7g00>eR:g00?bR;%49R<P0fIR=fHR>fGR?fFR@f8RAf7RBf6RCf5RDf4REf3RFf2RGf1RHf0RIM>5RJP0P1P2P3p,3DILRKp,3ERORLfJRMP=P>P?P@fERNfDROfCRPfBRQfARRf@RSf?RTf>RUf=RVf<RWf;RXf:RYf9RZPAPBPCPDPEPFPGPHPIP0PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPFPGMH6R[P0P1P2P3p,4PDESp,3PDNR\p,4REMBp,5COPYGp,4SELDR]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMT3R^P0P1P2P3p,4DILNR_p,4ERONR`P\p,5REMBNRap,4CPYNRbP]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMU8MT9W0W:W3WHXI9X59X89W7X69WGW1X48X>8X=8XF8XE8XD8XC8XB8XA8X@8X?8X<8X;8W9W2WJP0P1P2P3PKPLPMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIP[P^P0P1P2P3P_P`P\PaPbP]PMP=P>P?P@PNPOPPPQPRPSPTPUPVPWPXPYPZPAPBPCPDPEPFPGPHPIMU=MT<X0JX:<X3;XH:XI9X59X89X77X69XG9X16X48X>8X=8XF8XE8XD8XC8XB8XA8X@8X?8X<8X;8X98X25XJ4G;o"). Qed.

(* [comment removed for export] *)
Theorem pixCloseSafeCompBrick3_ok : pixCloseSafeCompBrick3_cps RT.
Proof using AF GP FKC CSELS ADDB DIL ERO PDES PDN REMB COPYG SELD DILN ERON REMBN CPYN.
ltac2:(KReplay.run1 (kr_t_Po_csc ()) ["CSC"] "p;3g00G;j30Tp,2RTg00HOg00I[30o"). Qed.
End CSC.
