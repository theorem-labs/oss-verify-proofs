(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require ExitBase StdioDefs Exit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2StdioDefs V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require R23Code FuncsOnExit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2R23Code.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Exit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs;exit_common00I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;exit_common00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs<atexit_stateC5ARocqVerifyHarness?AgentSubmission2V2:V2ExitBase=stdio_globalsC5ARocqVerifyHarness?AgentSubmission2V2:V2ExitBase:file_cleanK6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;exit_common01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocK47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;foe_variant00I5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs>stdout_pending00I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs>stdout_pending00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs9ssp_cellsK6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs>stdout_pending01C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission2V2;V2StdioDefs8exit_preK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltac5ARocqVerifyHarness?AgentSubmission2V26V2Exit=exit_common_GK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission2V26V2Exit@stdout_pending_GK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs8exit_preC6ARocqVerifyHarness?AgentSubmission6Common4Musl8ExitBase:file_cleanI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c5ARocqVerifyHarness?AgentSubmission2V26V2Exit5FOE23C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_exitI5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_cleanC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocMusl5v2_rwc5ARocqVerifyHarness?AgentSubmission2V26V2Exit5CXF23I47Corelib7Numbers7BinNums1N00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec1WC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_emitC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_flushC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit?t_emit_nil_exitc5ARocqVerifyHarness?AgentSubmission2V26V2Exit:exit_pre_GC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit8ref_exitC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit:ref_exit_Z".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exit_common_G : forall regs mem sp tp code tid wp2 rp2,
  exit_common regs mem sp tp code tid wp2 rp2 ->
  @StdioDefs.exit_common v2_reloc regs mem sp tp code tid wp2 rp2.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) [] "p'0h01Hh14codeh23dsoh32f1h43f10h53f11h63f12h73f13h83f14h93f15h:3f16h;3f17h<3f18h=3f19h>2f2h?3f20h@3f21hA2f3hB2f4hC2f5hD2f6hE2f7hF2f8hG2f9hH3memhI4regshJ3rp2hK2sphL3tidhM2tphN1vhO3wp2i005ec_a0i019ec_atexiti027ec_compi036ec_dsoi046ec_erri055ec_fai065ec_fei075ec_fsi085ec_g1i095ec_g2i0:7ec_globi0;7ec_locki0<7ec_mtidi0=6ec_soki0>5ec_spi0?7ec_sphii0@7ec_sploi0A6ec_tidi0B5ec_tpi0C7ec_tphii0D7ec_tplop;1p;2p;8p;9p;3p;4p;Ng0000j10Tg000Uj12Tg001:j1ITg001Xj1OTg002;j2[Tg002gj1LTg003IR0j8XTg004Jl9UTg005Rj1;Tg0060j3HTg006Sj2FTg007Lj3?Tg007fj2ATg008Pj2JTg008mj2DTg009Ij2@Tg009oj11Tg00:Nj4TTg00;Nj2KTg00;jj2STg00<Ej1RTg00<ej1QTg00=Ej3aTg00=ej2PTg00>Gj2NTg00>aj2_Tg00?aj1^Tg00@aj4]Tg00A^lN\Tg00Bfj4MTg00C^j2ZTf0R1#0#0p=3%01#0#0#0p=6%21#0#0#0p=E%01#;p=C%11#1p=Y%11#1#1#1p=W%11#1#1#1#1#1#1#1p=V%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=7f6R2g00DfR3f5R4f4R5f3R6CMf2R7f1R8/Z1'P3?p=9%21#2#0#2p=>%21#0p=5%01#2p=<%01#0#2#2p=G%01#2#0#0p==%01#0#;,@8p=4%21#2#2#0p=8%21#2p=:%01#0#0#2p=BP3P6P7P8CM=?51p=`g00F8R9#0R:#2R;#IR<%0:R=#0R>#0#3R?#IR@#ORA'[%I>R>#ORB#L\Ag00F]f7RCP2P4P5P6P7P8P1GXP0f8R0PCP2P4P5P6P7P8g00G;RDf9REP0PCP2P4P5P6P7M9UP1fM%;:g00H3R:5H<'FfKRF5?AfNRG%;==H<:'F=?AFfORH%0;R;#;=H<:'F=?AF%0?#6#6#6#6#6#6R?#0RF#;R:1A@G%E=#CR='J'D1A@H%3F#6#6#6#C'Dg00HOP3fQR3fPRF,A@RH/J=,@@g00Ho#1R=#1#YRG#WR<#V#7#7#7#7#7#7#7#7CTg00IN3?%2;#3#CR;/DH1A@3/D:g00InR:/KF%;?,KF'S%RBRF#LR?fUfS,A@/J;,@@PGPFPG1@@3F9P?fV%>9#5#<#G#=,4@PGPFPG1@@:RGF9P?fW%39#=#8#:#=,4@P<PFP<%39#=#8#G#3,4@F9P?fX%39#=#8#>#5,4@P<PFP<%B9#G#E#5#5,4@R3F9P?fYP3P<PFP<%<9#>#:#>#5,4@F9P?fZR3%B9#5#B#<#5#5,4@P=1@>:%QB5aB,PFD`P?f[RB%39#=#8#<#:#3,4@P<PFP<%29#5#:#>#>#:,4@F9P?f\R:%39#=#8#<#8,4@P<PFP<PGF9P?f^R?%B9#<#8#:#E,4@P<PFP<P1F9X2A,NAg00JLR<f_RF/_1XN<'N%^Ff`R<%09#3#5#:#8#<#E#CPBP3C]PDfbfaP<PFP?f]P:PBfDRBfCR:fBR?fARFf@R<f?RDf>R3f=R9f<R@f;RGf:R>PEP0PCP2P4P5P6P7P8P1MN\W@W?W=W<W;W:W9W8W7W6W5W4WGWFWEWDWCWBWAW>W3PBP:P?PFP<PDP3P9P@PGP>PEP0PCP2P4P5P6P7P8P1OEn80000000010000001E110>10B10010@10?10=10D10C10A10<10;10610710510210810910310110:104W0XJAXOAWLX1AXMAXKAWHWIo"). Qed.

Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v2_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) [] "p'0h01Hh14bufph25bufszh33canh42f1h53f10h63f11h73f12h83f13h93f14h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC7pendinghD3rp1hE2wbhF2wpi006sp_bszi016sp_bufi028sp_bytesi035sp_fdi046sp_leni057sp_locki066sp_maxi078sp_rangei087sp_rendi097sp_rposi0:6sp_sspi0;8sp_wbasei0<7sp_wposi0=8sp_writep;1p;8p;9p;2p;3p;Gp;4g0000j10Tg001:j1FTg001Xj1ETg002gj1HTg00<Ej1STg00KTR0j8RTg00LXl9QTg000Uj11Tg009oj15Tg005Rj17Tg009Ij29Tg008mj2?Tg00;Nj2PTg00;jj2DTg008Pj2OTg00Mcj2@Tg00NCj1CTg007Lj3<Tg00Ncj2MTg00=ej2BTg00O@j2KTg00P=lGJTg00C^j2NTg00QHj2ITg00Bfj4GTf0R1#0#0p=8%11#1p=;%01#0#0#0p==%01#1p=>%01#0#0#7p=4%11#0p=:%01#7p=A%11#1#1#1p=3f2R2f1R3/N1'Bp=6f6R4g00DfR5f5R6f4R7f3R8/I2'9P3CG;<1p=2P5P8P2P3CG=<71p=Lg00F8R5#0R9#0R:#0R;#0R<#8#FR=#ER>%F;#ER?#H[g00F]R@%S?RAf7RBP4P6P7P8P2P3P1GRP0f8R0PBP4P6P7P8P2P3g00G;RCf9RDP0PBP4P6P7P8P2M9QP1%HAREfFP=%05#8#;#8#=#>#8#4RF%1;#:#Ag00Ho#5#5#5#5RG%15RH#1RI#1RJ#3#3#3#3#3#3#3#7,9=96AGF2PEfGRKP=PF%19RL#4%5G#5#5#5RMfE,9=96AMF2PEfHRNP=PF%4IPM19=K96AMF2PEfIRIP=PF%1:#4PM%35#8#>#:#3#:#A,9=96AMF2PEfJR:P=PF%1L#4PMA6AMKRKF2PEfKRLP=PF%8H#4PMPKF2PEfLP=PF%0JRJ#0#APG%75,9=96AGF2PEfMRGP=PF%7;PMA6AMNF2PEfNRNP=PF%7<PMA6AMIF2%15#:#;#8#:#>#;#8#4/?N1PNG'D%15#:#;#:#=#=#4,?G'DfOR5,ON1@?I#C5<@1@?:#C%79%7J'M'?PEfRREfQRJ,9=1@?L1BALDLfSRL/KGPCfTPLPEPJfPP5PNPGf=RGf<RNf;R5f:RJPDP0PBP4P6P7P8P2P3P1MGJW9W8W7W6W5WAW@W?W>W=W<W;W:W4PGPNP5PJPDP0PBP4P6P7P8P2P3P1O>n80000000010000001>110510<10;10=10110010310910810710410610210:W0WCX3>XD>X2>X1>XF@WEWBo"). Qed.

Lemma exit_pre_G : forall regs mem model code pending,
  exit_pre regs mem model code pending -> @StdioDefs.exit_pre v2_reloc regs mem model code pending.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) [] "p'0h03rp1h13canh25bufszh34bufph42wph53wp1h62wbh71Hh83rp2h93wp2h:3tidh;2tph<2sph=5CASESh>1Eh?2ECh@2F1hA3HfdhB2HhhC5HlazyhD2SPhE4codehF3memhG5modelhH7pendinghI4regsi001xp;1p;2p;5p;8p;4p;3p;9p;6g0000j1@Tg000Uj1>Tg001:j1JTg001Xj1WTg002;j2aTg002gj1MTg00<Ej1STg00Qej5\Tg003Ij8<Tg00Raj1[Tg00SCj2YTg00<ej1RTg005Rj1PTg00@aj45Tg00>GR0j20Tg00KTj83Tg009Ij2_Tg00Scj1^Tg00=ej2]Tg00T[j1GTg00URj2ZTg00QHj2XTg00;jR1j22Tg007Lj3:Tg00VRl9hTg00WNj4DTg00Wij3gTg00XCl9fTg00YBj3eTg00Y\j4OTg00Z6j1UTg00Zjj2TTg00[bR2j2NTg00\<j1QTg00]4j6`Tg004Jl9bTg00^7j5cTg00LXl9dTf0R3#@#@p==%>3#@p=Cf4R4f3R5f2R6#Uf1R7'T;:3'2p=4g00F]R8/03p=1f5R9?:451067'21083'Np=6f7R:f6R;%G9;:4%Q6=:57/23'2'2p=9g00G;R<P4P5P6P7P3E`p=?%Q;=::9A:456/27/N3'2p=FA:567/23p=I%G7=:63p=K%Q7=:63p=LP<P:P;P9P4P5P6P7P3M9bp=B%>3#>p=EP<P5P6P7P3Dcp=8P<P:P;P9P4P5P6P7P3M9dp=7%U6/T7=:53p=;1067,25/N3p=H1073,26p=VP;P9P4P5P6P7P3COCOp=Ag00F8R=#@R>#>#J%@>R>#@R?#@#=#JR@#WRA'a%J?#WR?#M\Ag00_;%S?RBP4P5P6P7P3D\P0PAf:RCf9RDP4P5P:P6P7P3G<%MAREf8RF%[ARG1YAARH#SRIPF%RHRHPBP;%R?R?PAf;RJ%@=#=#>#C#=#=#=#C#=#=#PRKP7P3C5X0A,0AX5Af?RLP9P4P5P6P7P3f<RMG3g00`1RN#MROf>RP%P=,_@R@%^@,]NRND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP;P9P4P5P6D?P3PMPJP4P5PDP6P7P3G<PEPCPGPIPCPHPBPFP?PAf=RQPKP7P3C5X0A,0AX5AfARRP9P4P5P6P7P3PPG3POf@RSP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AP0PAPQPMP9P5PCP6P7P3G<PEPJPGPIPJPHPBPDP?PAPPPKP7P3C5X0A,0AX5AfBRTP9P4P5P6P7P3PLG3POPRP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;APCPDPFP:P;D?P3PLPPP:P5PMP6P7P3G<PEPQPGPIPQPHPBPJP?PAPSPKP7P3C5X0A,0AX5AfDRUP9P4P5P6P7P3PRG3POfCRVP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1P0P8PSPLPFP4PQP6P7P3G<PEPPPGPIPPPHPBPMP?PAPRPKP7P3C5X0A,0AX5AfERWP9P4P5P6P7P3PTG3POPUP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8PPPQPMPJPCD?P3PTPRPCP;PLP6P7P3G<PEPSPGPIPSPHPBPPP?PAPVPKP7P3C5X0A,0AX5AfGRXP9P4P5P6P7P3PUG3POfFRYP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AP0PAPVPTPJP:PSP5P7P3G<PEPRPGPIPRPHPBPLP?PAPUPKP7P3C5X0A,0AX5AfHRZP9P4P5P6P7P3PWG3POPXP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9APTPRPSPLPPD?P3PWPUPQPDPTP9P7P3G<PEPVPGPIPVPHPBPRP?PAPYPKP7P3C5X0A,0AX5AfJR[P9P4P5P6P7P3PXG3POfIR\P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AP0PAPYPWPPPCPVP;P6P3G<PEPUPGPIPUPHPBPTP?PAPXPKP7P3C5X0A,0AX5AfKR]P9P4P5P6P7P3PZG3POP[P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8APYPWPUPVPTD?P3PZPXPSPMPWPFP4P3G<PEPYPGPIPYPHPBPUP?PAP\PKP7P3C5X0A,0AX5AfMR^P9P4P5P6P7P3P[G3POfLR_P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9P1P\PZPRPQPYPDP9P7G<PE%GXPGPIPXPHPBPWP?P[PKP7P3C5X0A,0AX5A,0AfNR`P9P4P5P6P7P3P]G3POP^P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GFCIP[P\PZPXPYD?P3P]P[PVPLPZPJP:P5G<PE%G[PGPIP[PHPBPZP?P^PKP7P3C5X0A,0AX5A,0AfQRaP9P4P5P6P7P3P`G3POfPRbP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GFCIP1AKE]GPIP]PHPBP\P?P`PKP7P3C5X0A,0AX5A,0AfRRcP9P4P5P6P7P3fORdG3POPaP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GFP`P^P_P]P[D?P3AKE^GPIP`PHPBP_P?PaPKP7P3C5X0A,0AX5A,0AfUReP9P4P5P6P7P3PcG3POfTRfP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GFP1ALIdHPBP^P?PAPcPKP7P3C5X0A,0AX5AfVRgP9P4P5P6P7P3fSRhG3POPeP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PcPaPbPdP`D?P3ALIaHPBPbP?PAPePKP7P3C5X0A,0AX5AfYRiP9P4P5P6P7P3PgG3POfXRjP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PAfZRkPiP4P5fWRlP6P7P3GBPEPjPGPIPjPHPBPgP?PAf[Rm%>=#E#C#C#>#=#E#=#=#P%>>#E#=#>#C#E,Z<'XR<P7P3C8X0A,0AX5Af_R>P9P4P5P6P7P3f\R=G7POf^RnP@PNC;Ro'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP^PAPiPjPaP5PgP6P7P3GBPEPlPGPIPlPHA:Be?RpPAPkP<P7P3C8X0A,0AX5APnP9P4P5P6P7P3PmG7POf]RqP@PNC;Rr'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CHG9X8A,0AX9A,0AX:8#1X;AP\P8PjPlPbP_PeP6P7P3GBPEPgPGPIPgPHPBPfP?PAPiP<P7P3C8X0A,0AX5APqP9P4P5P6P7P3PkG7POP=P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RbG9X8A,0AX9A,0AX:8PWPAPlPgPdP]PfPXP7P3GBPEPePGPIPePHA:Bh?RdPAPjP<P7P3C8X0A,0AX5AP=P9P4P5P6P7P3PiG7POPmP@PNC;Rs'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CHG9X8A,0AX9APRPAPgPeP`P[PhPYPTP3GBPEPfPGPIPfPHA:Bc?RtPAPlP<P7P3C8X0A,0AX5APmP9P4P5P6P7P3PjG7POPkP@PNC;Ru'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CHRvG9X8APQPePfP^P\PcPWPRPQGBAKEhGRGALIhHRhA:Ba?RaPAPgP<P7P3C8X0A,0AX5APkP9P4P5P6P7P3PlG7POPiP@PNC;RH'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CHRI'2RE'2PePfP^P\PcPWPRPQPDM9hPGPEP9PhPIP7P2PgPKP7P3C5X0A,0AX5A9VaAPkP9P4P5P6P7P3PlG3/2HX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PvP3PlPKP7P3C5X0A,0AX5A9VtAP1PdPjPKP7P3C5X0A,0AX5A,0APbP3PmPKP7P3C5X0A,0AX5A,0AP0PAP=PKP7P3C5X0A,0AX5APBPjP?PAPqP<P7P3C8X0A,0AX5AfaRqP9P4P5P6P7P3PnG7POf`RdP@PNC;Rt'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RlP3PnPKP7P3C5X0A,0AP0PAP>PKP6P3C5X0APBP=P?PAPqP<P7P3C8X0A,0AX5AfeRvP9P4P5P6P7P3fbRHG7POfdRkP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RgP3PqPKP4P3C5A:B>?RKPkP<P7P3C8X0A,0AX5AR2,0ARI'2fhRhP9P4P5P6P7P3PvG7POfgREP@PNC;RG'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PKPIPDPAP2P9PAfcR2P<P;P3C8X0AP7P3FACD3gW@X0AP7P3O2n2001000010121100000W7X5AP7P3O2n2001000010121100000W7X>pP7P3O2n2001000010121000000W7P3O1PmP9P4P5P6P7P3PjG3/2uX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1P0P8P=P9P4P5P6P7P3PiG3/2sX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68PbP3PnP9P4P5P6P7P3PmG3/2rX1A,0AX0A,0AX2A,0AX3A,0AX48#1P0P8P>P;P4P5P6P7P3P=G3/2oX1A,0AX0A,0AX2A,0AX3A,0AX48PlP3PqPFP4P5P6P7P3PnG3/2tX1A,0AX0A,0AX2A,0AX3A,0AP0PAPHPDP9P5P6P7P3P>G3POPqP@PND4X1A,0AX0A,0AX2A,0AX3APgP3PkPJP:P5P6P7P3PqG3POP2P@PND4X1A,0AX0A,0AX2A,0AP0PAPvPMPFP4P6P7P3PHG3/2aX1A,0AX0A,0AX2APBPdP?PAPvP<P7P3C8X0A,0AX5AfiRdP9P4P5P6P7P3ffRaG7POPhP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PEPPPCP;P6P7P3PkG3POPaP@PND4X1A,0AX0A,0AP0PAPhPLPJP:P5P7P3PvG3/2GX1A,0AX0APBPkP?PAPdP<P7P3C8X0A,0AX5AfmRkP9P4P5P6P7P3fjRGG7POflRvP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PGPRPQPDP9P7P3PEG3POPdP@PND4X1A,0AP0PAfkR0PTPPPCP;P6P3PhG3POPGP@PND4X1APBPhP?PAPkP<P7P3C8X0A,0AX5AfqRhP9P4P5P6P7P3fnR;G7POfpRdP@PNC;RE'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PkPUPSPMPFP4P3PGG3/2aP1P;PWPRPQPDP9P7P0G3POPkP@PNC;PBPvP?PAPhP<P7P3C8X0A,0AX5AfuRvP9P4P5P6P7P3frR0G7POftR;P@PNC;R1'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PdPXPVPLPJP:P5PkG3PBfoRBP?P;P<P7P3C8X0A,0AX5A,0ACIfxP9P4P5P6P7P3PvG7POfwR<P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68R?#1P8P?P\P8P<P`P4P5P6P7P3P;G7POfvR4P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48PWPAP4P^P\P5P6P7P3fsR5G7POPvP@PND4X1A,0AX0A,0AX2A,0AX3APRPAPvP_PZPUP6P7P3P0G7/21X1A,0AX0A,0AX2APQPAP;P]PXPVPLP7P3PhG7POP5P@PND4X1A,0AX0APDPAP5P[PYPTPPPCP3PdG7POP0P@PND4X1AP9P0P\PWPRPQPDP9PBG7POPhP@PNC;P0P\PWPRPQPDP9PBP7M9fP3CDFAFAFA3eXAEWDP7P3O2n2001000010121000000W7X1AP7P3O2n2001000010121100000W7X0AP7P3O2n2001000010121100000W7X2AP7P3O2n2001000010121100000W7X3AP7P3O2n2001000010121100000W7X48P7P3O2n2001000010121100000W7X68P7P3O2n2001000010121100000W7P3O1n200100001021100011000CDCDCDCOFAFAW=WCP7P3O2n2011000000121000000W7WBP7P3O2n2011000000121000000W7W?P7P3O2n2011000000121000000W7X8AP7P3O2n2011000000121100000W7X9AP7P3O2n2011000000121100000W7X:8P7P3O2n2011000000121100000W7X;AP7P3O2n2011000000121100000W7X<AP7P3O2n2011000000121100000W7WHXEAWGWFWIo"). Qed.


(* [comment removed for export] *)
Definition FOE23 {fx : FPState} : @StdioDefs.funcs_on_exit_spec v2_reloc fx :=
  @FuncsOnExit.funcs_on_exit fx v2_reloc v2_code v2_sites v2_data v2_rw v2_r23code.
Definition CXF23 : @ExitBase.cxa_finalize_ret v2_reloc := @R23Code.F23_13198 v2_reloc v2_data v2_r23code.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x46020 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x3bef8 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP1"] "h01Hh12b1h22b2h31nh42ECh52F1h62Hhh75Hlazyh83RLTh91bh:4codeh;3memh<5modelh=4regsh>3rp1h?3rp2h@2sphA3tidhB2tphC3wp1hD3wp2p;1p;2p;8p;4p;3p;9p;5p;6p;Gg0000j11Tg000Uj14Tg001:j18Tg001Xj15Tg002;j2STg002gj1>Tg003Ij8HTg005Rj17Tg00@aj4ETg00T[j1CTg00Raj1BTg007Lj33Tg00SCj2UTg00<Ej1TTg00\<j1RTg00<ej1MTg00`ij1LTg00VRl9KTg00a]j1ITg00URj2GTg00b\j2FTg00cVj1=Tg00dRj5<Tg00eKj2?Tg009Ij2:Tg00f@j3;Tg00fej19Tg00gXj2@Tg00hSj3ATg007fj26Tg00iRj3DTg0060j3NTg00j6j2OTg00jPj6PTg00jllGQTf0R0#1#1p=0%40#4p=2P0g00G;R1g00l0g00lkg00mhg00nbf1R2g00o[f2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAMGQp=Jg00F8RB#1RC#4RD#8%0CRC#1#0RE#8RF#5RG'S%8C#5#>\Gg00_;g00F]RCP;P:P8P7P6P5P4P3GHP;%1B#0#2#1#0#0#0#4#1#0#0#7P3P2CE%>G%C;%BG331UGGRH#T%R<%MH33p,2fxRH%LHP?P>P=P<P;P:P9P8P7P6P5P?P>P<P;P:P9P8P7P4M9KP3P2P0MAJ%I1R7PHP?%0E#2,G1%1D#2#1#0#0#0#0#0#7'FP>%=7D</?=%4B#2#2#2#7,:FR79;F:%9='@3Ag010OR:%50R>%52RDg00;j%53?3201643164253CR1[1632163053C%54?332[RE%55?343\1AD320P0n2001000000120000000W2W1W3PE^2D^1>^3:P0PF%2B#1#4#2#2#1#4#2#2#1#0#7RB,:FR:g00H39NFBR>1OCB16F:16F>53CdO4b0A3G:>PGP:g00DfR:PHfAP0PA%=:D</?@A;F=7%9@'@3AX9GP2P>P0EPb0b8W7W6W5W4X>GXCGX?GXDGWAX:GXBGX@GW<W;W=o"). Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x3bef8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP2"] "h01Hh12b1h22b2h31nh42ECh53Hfdh62Hhh75Hlazyh83RLTh92SPh:1bh;4bufph<5bufszh=3canh>4codeh?3memh@5modelhA7pendinghB4regshC3rp1hD3rp2hE2sphF3tidhG2tphH2wbhI2wphJ3wp2p;1p;2p;8p;3p;9p;5p;6p;Mg0000j13Tg000Uj16Tg001:j18Tg001Xj14Tg002;j2TTg002gj19Tg00<Ej1?Tg003Ij8LTg00KTj8GTg00T[j1FTg00Raj1ETg007Lj31Tg00SCj2\Tg00\<j1VTg00<ej1UTg00Z6j1STg005Rj17Tg009Ij2:Tg00Zjj2RTg00Scj1QTg00=ej2PTg00`ij1OTg00VRl9NTg00XCl9MTg00a]j1JTg00URj2HTg00b\j2ITg00cVj1=Tg00dRj5<Tg00eKj2>Tg010mj2CTg00f@j3ATg00fej1BTg00gXj2@Tg011ij2;Tg00hSj3DTg007fj25Tg00iRj3[Tg0060j3ZTg00j6j2YTg00jPj6WTg012dlMXTf0R0#3#3p=2P0g00G;R1g00l0g00lkg00mhg00nbf1R2g00o[f2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAfARBfBRCfCRDfDREfERFfFRGMMXp=K%60#6p=0g00F8RH#3RI#6RJ#8%2IRI#3#2RK#8RL#4RM'T%8I#4RI#9\Mg00_;g00F]RN%?IP@P?P=P<P;P:P9P8GLP@P8P7P6P5P4P3P2GG%9M%F@%EM311\MMRI#?%VA%UI31g00`1RI#9%SB%7HRO,:LRP'R%QP,PI31p,2fxRI%OIPEPDPCPBPAP@P?P>P=P<P;P:P9P8P7P6PEPDPBPAP@P?P>P=P5M9NPDP<P;P:P9P8P7P6P4M9MP3P2P0MGK%J1R7PIPE%2K#0,H1%3J#0#3#2#2#2#2#2#7'IPD%=7D</>C1CO6%6H#0#0#0#7,:LR69AL@%BC'@';3Dg010OR@%40R7%42RDg00;j%43?1201543154251NRJ[1532153051N%44?132[R1%45?143\JA[320P0n2001000000120000000W2W1W3P1^2D^17^3@P0PL%0H#3#6#0#0#3#6#0#0#3#2#7RH,:LR@g00H39ZLHR71YNH15L@15L751NdO4b0A1M@7PMP@g00DfR@PIfGP0PG%=@D</>F1CO9AALC6%BF'@';3DX:MP2P7P0EWb0b8W5W7W6W9W4WAX=MXCMX<MX;MXINXHNXDMXJMWFX>MXGMXEMW@W?WBo"). Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP3"] "g013ho"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x3bef8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP4"] "h01Hh12b1h22b2h31nh43PREh53RLTh61bh74codeh83memh95modelh:7pendingh;4regsp;1p;2p;5p;6p;3p;>g0000j11Tg000Uj16Tg001:j18Tg001Xj13Tg002;j2PTg002gj1LTg00<Ej1ITg00Qej5HTg00`ij1GTg014mj6FTg00a]j1CTg00URj2QTg005Rj17Tg00b\j2OTg00cVj1BTg00dRj5ATg00eKj2@Tg010mj2:Tg009Ij29Tg00f@j3?Tg00fej1>Tg00gXj2;Tg011ij2=Tg00hSj3<Tg007Lj34Tg007fj25Tg00iRj3JTg0060j3KTg00j6j2ETg00jPj6MTg015fl>NTf0R0#1#1p=2f7R1g00G;R2g00l0g00lkg00mhg00nbf6R3g00o[f5R4f4R5f3R6f2R7f1R8P0M>Np=D%60#6p=0g00F8R9#1R:#6R;#8%2:R:#1#2R<#8R=#3R>'P%8:#3R:#L\>g00_;%I:P5P6P7P8P0DHp,2fxR:%G:P4P5P6P7P8P4P5P6P7P8P0EFGD%C2R?P:P4%2<#0,Q2%1;#0#1#2#2#2#2#2#7'OP5%B?DA/@6%79R?/:8%69#0#0#0#7,9=R;9?=7%>6';'=3<g010OR2%30R<%38R@g00;j%37?480g00F]RA1567156834RB[1578157054A%36?478[RC%35?467\BAJ780P0n2001000000120000000W2W1W3PC^2@^1<^32P0P=%09#1#6#0#0#1#6#0#0#1#2#7R9,9=R2g00H39K=9R<1EA915=215=<54AdO4b0A4>2<P>P2g00DfR2P:f8P0P1%B2DA/@31:?5A?=4;%>3';'=3<X6>P8P<P0EMb0b5W4W:X7>W9W8W;o"). Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x3bef8) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP5"] "h03PREh13RLTh24codeh33memh45modelh57pendingh64regsp;1p;2p;5p;6p;3p;>g0000j11Tg000Uj13Tg001:j14Tg001Xj16Tg002;j2JTg002gj1>Tg00<Ej1=Tg00Qej5;Tg00`ij1:Tg014mj67Tg00a]j19Tg00URj2KTg005Rj15Tg00b\j2ITg00cVj1HTg00dRj5BTg00eKj2?Tg010mj2@Tg009Ij2ATg00f@j3<Tg00fej1CTg00gXj2DTg011ij2ETg00hSj3FTg016dl>GTf0R0#1#1p=0f7g00G;R1g00l0g00lkg00mhg00nbf6g00o[f5R2f4R3f3R4f2R5f1R6P0M>Gp=8%30#3p=2g00F8R7#1R8#3R9#4%08R8#1#0R:#4R;#6R<'J%48#6R8#>\<g00_;%=8P3P4P5P6P0D;p,2fxR8%:8P2P3P4P5P6P2P3P4P5P6P0E7G8%91R=P8P2%0:#2,K1%19#2#1#0#0#0#0#0#5'IP3%H=DB/?4%57/@6%37#2#2#2#5,A;9<;5%C4'D'E3FP0b1W0W5X2<W4W3W6o"). Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
