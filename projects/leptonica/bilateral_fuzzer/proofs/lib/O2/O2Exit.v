(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require ExitBase StdioDefs Exit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2StdioDefs O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocMusl.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require R23Code FuncsOnExit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2R23Code.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Exit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib2O2;O2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib2O2;O2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2O2;O2StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2O2;O2StdioDefs8exit_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit=exit_common_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib2O26O2Exit@stdout_pending_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common4Musl9StdioDefs8exit_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib2O26O2Exit5FOE23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_cleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2RelocSites8o2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocMusl5o2_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit5CXF23C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_flushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit:exit_pre_GC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit8ref_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exit_common_G : forall regs mem sp tp code tid wp2 rp2,
  exit_common regs mem sp tp code tid wp2 rp2 ->
  @StdioDefs.exit_common o2_reloc regs mem sp tp code tid wp2 rp2.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) [] "p'0h01Hh14codeh23dsoh32f1h43f10h53f11h63f12h73f13h83f14h93f15h:3f16h;3f17h<3f18h=3f19h>2f2h?3f20h@3f21hA2f3hB2f4hC2f5hD2f6hE2f7hF2f8hG2f9hH3memhI4regshJ3rp2hK2sphL3tidhM2tphN1vhO3wp2i005ec_a0i019ec_atexiti027ec_compi036ec_dsoi046ec_erri055ec_fai065ec_fei075ec_fsi085ec_g1i095ec_g2i0:7ec_globi0;7ec_locki0<7ec_mtidi0=6ec_soki0>5ec_spi0?7ec_sphii0@7ec_sploi0A6ec_tidi0B5ec_tpi0C7ec_tphii0D7ec_tplop;1p;2p;8p;9p;3p;4p;Ng0000j10Tg000Uj12Tg001:j1HTg001Xj1OTg002;j2[Tg002gj1LTg003IR0j8YTg004Jl9UTg005Rj1;Tg0060j3GTg006Sj2FTg007Lj3=Tg007fj2@Tg008Pj2ITg008mj2CTg009Ij2>Tg009oj11Tg00:Nj4TTg00;Nj2JTg00;jj2STg00<Ej1RTg00<ej1QTg00=Ej3aTg00=ej2PTg00>Gj2NTg00>aj2_Tg00?aj1^Tg00@aj4]Tg00A^lN\Tg00Bfj4MTg00C^j2ZTf0R1#0#0p=:%01#0#0#0#0#0#0#0p=?%21#0#0#0p=8%01#;p=D%01#0#0#0p=K%11#1p=X%11#1#1#1p=W%11#1#1#1#1#1#1#1p=V%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=7f6R2g00DfR3f5R4f4R5f3R6CMf2R7f1R8/Z1'P3=p=6%21#0#2#0p=A%01#2p=<%21#0p=3%01#0#;,>8p=4%01#2#0#0p=9%21#2p=5%21#2#0p=B%01#0#0#2p=EP3P6P7P8CM==51p=`g00FLR9#0R:#2R;#HR<%0:R=#0R>#0#:R?#HR@#ORA'[%H>R>#ORB#L\Ag00G1f7RCP2P4P5P6P7P8P1GYP0f8R0PCP2P4P5P6P7P8g00GORDf9REP0PCP2P4P5P6P7M9UP1fM%;:g00HGR:5G<'FfKRF5=AfNRG%;==G<:'F==AFfORH%0;R;#;=G<:'F==AF%0?#?#?#?R?#0RF#;R:1@@G%8=#DR='I'C1@@H%:F#K#?#D'Cg00HcP3fQR3fPRF,@@RH/I=,>@g00IC#1R=#1#XRG#WR<#V#7#7#7#7#7#7#7#7CTg00Ib3=%2;#:#DR;/CH1@@3/C:g00JBR:/JF%;?,JF'S%RBRF#LR?fUfS,@@/I;,>@PGPFPG1>@3F6P?fV%A9#<#3#A#8,4@PGPFPG1>@:RGF6P?fW%29#8#9#3#A,4@P<PFP<%29#8#9#K#3,4@F6P?fX%29#8#9#3#5#:,4@P<PFP<%B9#E#?,4@R3F6P?fYP3P<PFP<%<9#5#<#<#8#3,4@F6P?fZR3%B9#<#<#5#:#5#3,4@P=1>>:%QB5aB,PFD`P?f[RB%29#8#9#9#3,4@P<PFP<%09#5#5#:#5#3#5#3,4@F6P?f\R:%B9#E#E#9,4@P<PFP<PGF6P?f^R?%B9#<#9#3#5#3,4@P<PFP<P1F6X2A,NAg00J`R<f_RF/_1XN<'N%^Ff`R<%59#:#A#8#9#DPBP3C]PDfbfaP<PFP?f]P:PBfDRBfCR:fBR?fARFf@R<f?RDf>R3f=R9f<R@f;RGf:R>PEP0PCP2P4P5P6P7P8P1MN\W@W?W=W<W;W:W9W8W7W6W5W4WGWFWEWDWCWBWAW>W3PBP:P?PFP<PDP3P9P@PGP>PEP0PCP2P4P5P6P7P8P1OEn80000000010000001E110>10B10010@10?10=10D10C10A10<10;10610710510210810910310110:104W0XJAXOAWLX1AXMAXKAWHWIo"). Qed.

Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o2_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) [] "p'0h01Hh14bufph25bufszh33canh42f1h53f10h63f11h73f12h83f13h93f14h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC7pendinghD3rp1hE2wbhF2wpi006sp_bszi016sp_bufi028sp_bytesi035sp_fdi046sp_leni057sp_locki066sp_maxi078sp_rangei087sp_rendi097sp_rposi0:6sp_sspi0;8sp_wbasei0<7sp_wposi0=8sp_writep;1p;8p;9p;2p;3p;Gp;4g0000j11Tg001:j1CTg001Xj1ETg002gj1GTg00<Ej1RTg00KhR0j8QTg00Lll9NTg000Uj10Tg009oj17Tg005Rj16Tg009Ij2:Tg008mj2>Tg00;Nj2PTg00;jj2DTg008Pj2MTg00N7j2?Tg00NWj1BTg007Lj3=Tg00O7j2LTg00=ej2ATg00OTj2KTg00PQlGITg00C^j2HTg00Q\j2OTg00Bfj4@Tf0R1#1#1p=2%01#0p=<%01#1p=8%01#0#0#0p=9%11#1#1#6p=3%11#6p=Ff2R2f1R3/H1'Ap=5f6R4g00DfR5f5R6f4R7f3R8/O2':P3C@;=1p=4%11#0p=;P5P8P2P3C@==71p=Jg00FLR5#1R9#1R:#1R;#1R<#2#CR=#ER>%C;#ER?#G[g00G1R@%R?RAf7RBP4P6P7P8P2P3P1GQP0f8R0PBP4P6P7P8P2P3g00GORCf9RDP0PBP4P6P7P8P2M9NP1%GAREfFP=%<5#2#8#8#<#9#3RF%0;#8#Fg00IC#7#7#7#7RG%05RH#0RI#0RJ#9#9#9#9#9#9#9#6,:=95AGF4PEfGRKP=PF%09RL#3%7G#7#7#7RMfE,:=95AMF4PEfHRNP=PF%3IPM1:=K95AMF4PEfIRIP=PF%0:#3PM%85#2#<#2#8#8#<#3,:=95AMF4PEfJR:P=PF%0L#3PMA5AMKRKF4PEfKRLP=PF%2H#3PMPKF4PEfLP=PF%1JRJ#1#FPG%65,:=95AGF4PEfMRGP=PF%6;PMA5AMNF4PEfNRNP=PF%6<PMA5AMIF4%05#;#2#<#;#;#;#8#3/>N1PNG'D%05#;#;#8#2#2#2#2#3,>G'DfOR5,MN1??I#B5=@1??:#B%69%6J'L'>PEfRREfQRJ,:=1??L1AALDJfSRL/KGPCfTPLPEPJfPP5PNPGf=RGf<RNf;R5f:RJPDP0PBP4P6P7P8P2P3P1MGIW9W8W7W6W5WAW@W?W>W=W<W;W:W4PGPNP5PJPDP0PBP4P6P7P8P2P3P1O>n80000000010000001>110510<10;10=10110010310910810710410610210:W0WCX3>XD>X2>X1>XF@WEWBo"). Qed.

Lemma exit_pre_G : forall regs mem model code pending,
  exit_pre regs mem model code pending -> @StdioDefs.exit_pre o2_reloc regs mem model code pending.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) [] "p'0h03rp1h13canh25bufszh34bufph42wph53wp1h62wbh71Hh83rp2h93wp2h:3tidh;2tph<2sph=5CASESh>1Eh?2ECh@2F1hA3HfdhB2HhhC5HlazyhD2SPhE4codehF3memhG5modelhH7pendinghI4regsi001xp;1p;2p;5p;8p;4p;3p;9p;6g0000j1>Tg000Uj1CTg001:j1MTg001Xj1XTg002;j2cTg002gj1PTg00<Ej1TTg00R9j5]Tg003Ij8<Tg00S5j1\Tg00SWj2[Tg00<ej1STg005Rj1NTg00@aj45Tg00>GR0j20Tg00Khj83Tg009Ij2`Tg00T7j1_Tg00=ej2^Tg00Toj1HTg00Ufj2ZTg00Q\j2YTg00;jR1j22Tg007Lj3:Tg00Vfl9iTg00Wbj4ETg00X=j3hTg00XWl9gTg00YVj3fTg00Z0j4OTg00ZJj1VTg00[>j2UTg00\6R2j2RTg00\Pj1QTg00]Hj6bTg004Jl9aTg00^Kj5dTg00Lll9eTf0R3#>#>p=D%C3#>p=F%>3#Cp=B%C3#Cp=?f4R4f3R5f2R6#Vf1R7'U;:3'2p=4g00G1R8/03p=1f5R9?:451067'21083'Rp=6f7R:f6R;%H9;:4%Q6=:57/23'2'2p=9g00GOR<P4P5P6P7P3Ebp==%Q;=::9A:456/27/R3'2p=GA:567/23p=L%H7=:63p=K%Q7=:63p=JP<P:P;P9P4P5P6P7P3M9ap=AP<P5P6P7P3Ddp=8P<P:P;P9P4P5P6P7P3M9ep=7%V6/U7=:53p=;1067,25/R3p=I1073,26p=WP;P9P4P5P6P7P3COCOp=@g00FLR=#>R>#C#M%>>R>#>R?#>#D#MR@#XRA'c%M?#XR?#P\Ag00_O%T?RBP4P5P6P7P3D]P0PAf:RCf9RDP4P5P:P6P7P3G<%PAREf8RF%\ARG1[AARH#TRIPF%SHRHPBP;%S?R?PAf;RJ%C=#F#B#B#B#?#?#F#D#NRKP7P3C5X0A,0AX5Af?RLP9P4P5P6P7P3f<RMG3g00`ERN#PROf>RP%N=,`@R@%_@,^NRND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP;P9P4P5P6D=P3PMPJP4P5PDP6P7P3G<PEPCPGPIPCPHPBPFP?PAf=RQPKP7P3C5X0A,0AX5AfARRP9P4P5P6P7P3PPG3POf@RSP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AP0PAPQPMP9P5PCP6P7P3G<PEPJPGPIPJPHPBPDP?PAPPPKP7P3C5X0A,0AX5AfBRTP9P4P5P6P7P3PLG3POPRP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;APCPDPFP:P;D=P3PLPPP:P5PMP6P7P3G<PEPQPGPIPQPHPBPJP?PAPSPKP7P3C5X0A,0AX5AfDRUP9P4P5P6P7P3PRG3POfCRVP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1P0P8PSPLPFP4PQP6P7P3G<PEPPPGPIPPPHPBPMP?PAPRPKP7P3C5X0A,0AX5AfERWP9P4P5P6P7P3PTG3POPUP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8PPPQPMPJPCD=P3PTPRPCP;PLP6P7P3G<PEPSPGPIPSPHPBPPP?PAPVPKP7P3C5X0A,0AX5AfGRXP9P4P5P6P7P3PUG3POfFRYP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AP0PAPVPTPJP:PSP5P7P3G<PEPRPGPIPRPHPBPLP?PAPUPKP7P3C5X0A,0AX5AfHRZP9P4P5P6P7P3PWG3POPXP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9APTPRPSPLPPD=P3PWPUPQPDPTP9P7P3G<PEPVPGPIPVPHPBPRP?PAPYPKP7P3C5X0A,0AX5AfJR[P9P4P5P6P7P3PXG3POfIR\P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AP0PAPYPWPPPCPVP;P6P3G<PEPUPGPIPUPHPBPTP?PAPXPKP7P3C5X0A,0AX5AfKR]P9P4P5P6P7P3PZG3POP[P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8APYPWPUPVPTD=P3PZPXPSPMPWPFP4P3G<PEPYPGPIPYPHPBPUP?PAP\PKP7P3C5X0A,0AX5AfMR^P9P4P5P6P7P3P[G3POfLR_P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9P1P\PZPRPQPYPDP9P7G<PE%HXPGPIPXPHPBPWP?P[PKP7P3C5X0A,0AX5A,0AfNR`P9P4P5P6P7P3P]G3POP^P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGCLP[P\PZPXPYD=P3P]P[PVPLPZPJP:P5G<PE%H[PGPIP[PHPBPZP?P^PKP7P3C5X0A,0AX5A,0AfQRaP9P4P5P6P7P3P`G3POfPRbP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGCLP1AKE]GPIP]PHPBP\P?P`PKP7P3C5X0A,0AX5A,0AfRRcP9P4P5P6P7P3fORdG3POPaP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGP`P^P_P]P[D=P3AKE^GPIP`PHPBP_P?PaPKP7P3C5X0A,0AX5A,0AfUReP9P4P5P6P7P3PcG3POfTRfP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGP1AJIdHPBP^P?PAPcPKP7P3C5X0A,0AX5AfVRgP9P4P5P6P7P3fSRhG3POPeP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PcPaPbPdP`D=P3AJIaHPBPbP?PAPePKP7P3C5X0A,0AX5AfYRiP9P4P5P6P7P3PgG3POfXRjP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PAfZRkPiP4P5fWRlP6P7P3GAPEPjPGPIPjPHPBPgP?PAf[Rm%?=#?#B#B#D#?#D#D#N%?>#F#B#F#?,Z<'YR<P7P3C8X0A,0AX5Af_R>P9P4P5P6P7P3f\R=G7POf^RnP@PNC;Ro'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP^PAPiPjPaP5PgP6P7P3GAPEPlPGPIPlPHA:Be?RpPAPkP<P7P3C8X0A,0AX5APnP9P4P5P6P7P3PmG7POf]RqP@PNC;Rr'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIG9X8A,0AX9A,0AX:8#1X;AP\P8PjPlPbP_PeP6P7P3GAPEPgPGPIPgPHPBPfP?PAPiP<P7P3C8X0A,0AX5APqP9P4P5P6P7P3PkG7POP=P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RbG9X8A,0AX9A,0AX:8PWPAPlPgPdP]PfPXP7P3GAPEPePGPIPePHA:Bh?RdPAPjP<P7P3C8X0A,0AX5AP=P9P4P5P6P7P3PiG7POPmP@PNC;Rs'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIG9X8A,0AX9APRPAPgPeP`P[PhPYPTP3GAPEPfPGPIPfPHA:Bc?RtPAPlP<P7P3C8X0A,0AX5APmP9P4P5P6P7P3PjG7POPkP@PNC;Ru'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIRvG9X8APQPePfP^P\PcPWPRPQGAAKEhGRGAJIhHRhA:Ba?RaPAPgP<P7P3C8X0A,0AX5APkP9P4P5P6P7P3PlG7POPiP@PNC;RH'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIRI'2RE'2PePfP^P\PcPWPRPQPDM9iPGPEP9PhPIP7P2PgPKP7P3C5X0A,0AX5A9WaAPkP9P4P5P6P7P3PlG3/2HX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PvP3PlPKP7P3C5X0A,0AX5A9WtAP1PdPjPKP7P3C5X0A,0AX5A,0APbP3PmPKP7P3C5X0A,0AX5A,0AP0PAP=PKP7P3C5X0A,0AX5APBPjP?PAPqP<P7P3C8X0A,0AX5AfaRqP9P4P5P6P7P3PnG7POf`RdP@PNC;Rt'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RlP3PnPKP7P3C5X0A,0AP0PAP>PKP6P3C5X0APBP=P?PAPqP<P7P3C8X0A,0AX5AfeRvP9P4P5P6P7P3fbRHG7POfdRkP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RgP3PqPKP4P3C5A:B>?RKPkP<P7P3C8X0A,0AX5AR2,0ARI'2fhRhP9P4P5P6P7P3PvG7POfgREP@PNC;RG'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PKPIPDPAP2P9PAfcR2P<P;P3C8X0AP7P3F@CE3hW@X0AP7P3O2n2001000010121100000W7X5AP7P3O2n2001000010121100000W7X>pP7P3O2n2001000010121000000W7P3O1PmP9P4P5P6P7P3PjG3/2uX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1P0P8P=P9P4P5P6P7P3PiG3/2sX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68PbP3PnP9P4P5P6P7P3PmG3/2rX1A,0AX0A,0AX2A,0AX3A,0AX48#1P0P8P>P;P4P5P6P7P3P=G3/2oX1A,0AX0A,0AX2A,0AX3A,0AX48PlP3PqPFP4P5P6P7P3PnG3/2tX1A,0AX0A,0AX2A,0AX3A,0AP0PAPHPDP9P5P6P7P3P>G3POPqP@PND4X1A,0AX0A,0AX2A,0AX3APgP3PkPJP:P5P6P7P3PqG3POP2P@PND4X1A,0AX0A,0AX2A,0AP0PAPvPMPFP4P6P7P3PHG3/2aX1A,0AX0A,0AX2APBPdP?PAPvP<P7P3C8X0A,0AX5AfiRdP9P4P5P6P7P3ffRaG7POPhP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PEPPPCP;P6P7P3PkG3POPaP@PND4X1A,0AX0A,0AP0PAPhPLPJP:P5P7P3PvG3/2GX1A,0AX0APBPkP?PAPdP<P7P3C8X0A,0AX5AfmRkP9P4P5P6P7P3fjRGG7POflRvP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PGPRPQPDP9P7P3PEG3POPdP@PND4X1A,0AP0PAfkR0PTPPPCP;P6P3PhG3POPGP@PND4X1APBPhP?PAPkP<P7P3C8X0A,0AX5AfqRhP9P4P5P6P7P3fnR;G7POfpRdP@PNC;RE'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PkPUPSPMPFP4P3PGG3/2aP1P;PWPRPQPDP9P7P0G3POPkP@PNC;PBPvP?PAPhP<P7P3C8X0A,0AX5AfuRvP9P4P5P6P7P3frR0G7POftR;P@PNC;R1'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PdPXPVPLPJP:P5PkG3PBfoRBP?P;P<P7P3C8X0A,0AX5A,0ACLfxP9P4P5P6P7P3PvG7POfwR<P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68R?#1P8P?P\P8P<P`P4P5P6P7P3P;G7POfvR4P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48PWPAP4P^P\P5P6P7P3fsR5G7POPvP@PND4X1A,0AX0A,0AX2A,0AX3APRPAPvP_PZPUP6P7P3P0G7/21X1A,0AX0A,0AX2APQPAP;P]PXPVPLP7P3PhG7POP5P@PND4X1A,0AX0APDPAP5P[PYPTPPPCP3PdG7POP0P@PND4X1AP9P0P\PWPRPQPDP9PBG7POPhP@PNC;P0P\PWPRPQPDP9PBP7M9gP3CEF@F@F@3fXAEWDP7P3O2n2001000010121000000W7X1AP7P3O2n2001000010121100000W7X0AP7P3O2n2001000010121100000W7X2AP7P3O2n2001000010121100000W7X3AP7P3O2n2001000010121100000W7X48P7P3O2n2001000010121100000W7X68P7P3O2n2001000010121100000W7P3O1n200100001021100011000CECECECOF@F@W=WCP7P3O2n2011000000121000000W7WBP7P3O2n2011000000121000000W7W?P7P3O2n2011000000121000000W7X8AP7P3O2n2011000000121100000W7X9AP7P3O2n2011000000121100000W7X:8P7P3O2n2011000000121100000W7X;AP7P3O2n2011000000121100000W7X<AP7P3O2n2011000000121100000W7WHXEAWGWFWIo"). Qed.


(* [comment removed for export] *)
Definition FOE23 {fx : FPState} : @StdioDefs.funcs_on_exit_spec o2_reloc fx :=
  @FuncsOnExit.funcs_on_exit fx o2_reloc o2_code o2_sites o2_data o2_rw o2_r23code.
Definition CXF23 : @ExitBase.cxa_finalize_ret o2_reloc := @R23Code.F23_13198 o2_reloc o2_data o2_r23code.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x395f8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) ["VP1"] "h01Hh12b1h22b2h31nh42ECh52F1h62Hhh75Hlazyh83RLTh91bh:4codeh;3memh<5modelh=4regsh>3rp1h?3rp2h@2sphA3tidhB2tphC3wp1hD3wp2p;1p;2p;8p;4p;3p;9p;5p;6p;Gg0000j16Tg000Uj14Tg001:j19Tg001Xj13Tg002;j2UTg002gj1?Tg003Ij8KTg005Rj18Tg00@aj4DTg00Toj1WTg00S5j1VTg007Lj32Tg00SWj2TTg00<Ej1PTg00\Pj1OTg00<ej1NTg00a=j1MTg00Vfl9LTg00b1j1ITg00Ufj2HTg00c0j2GTg00cjj1=Tg00dfj5>Tg00e_j2<Tg009Ij2BTg00fTj3@Tg00g9j1;Tg00glj2ATg00hgj3CTg007fj27Tg00ifj3FTg0060j3ETg00jJj2QTg00jdj6RTg00k@lGSTf0R0#6#6p=0%40#6p=:%60#4p=5%40#4p=1P0g00GOR1g00lDg00m?g00n<g00o6f1R2g00oof2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAMGSp=Jg00FLRB#6RC#4RD#9%0CRC#6#0RE#9RF#3RG'U%9C#3#?\Gg00_Og00G1RCP;P:P8P7P6P5P4P3GKP;%4B#:#5#5#5#1#1#:#0#8P3P2CD%?G%W;%VG321TGGRH#P%O<%NH32p,2fxRH%MHP?P>P=P<P;P:P9P8P7P6P5P?P>P<P;P:P9P8P7P4M9LP3P2P0MAJ%I1R7PHP?%0E#1,H1%5D#:#0#0#0#0#0#8'GP>%=7D>/<=%4B#1#1#1#8,BFR79@F:%;='A3Cg010cR:%30R>%32RDg00;j%33?2201743174252CR1[1732173052C%34?232[RE%35?243\1AF320P0n2001000000120000000W2W1W3PE^2D^1>^3:P0PF%6B#1#1#5#0#1#5#5#0#8RB,BFR:g00HG9EFBR>1QCB17F:17F>52CdO4b0A2G:>PGP:g00DfR:PHfAP0PA%=:D>/<@A@F=7%;@'A3CX9GP2P>P0ERb0b8W7W6W5W4X>GXCGX?GXDGWAX:GXBGX@GW<W;W=o"). Qed.
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
  realizes RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) ["VP2"] "h01Hh12b1h22b2h31nh42ECh53Hfdh62Hhh75Hlazyh83RLTh92SPh:1bh;4bufph<5bufszh=3canh>4codeh?3memh@5modelhA7pendinghB4regshC3rp1hD3rp2hE2sphF3tidhG2tphH2wbhI2wphJ3wp2p;1p;2p;8p;3p;9p;5p;6p;Mg0000j12Tg000Uj14Tg001:j18Tg001Xj15Tg002;j2TTg002gj19Tg00<Ej1?Tg003Ij8LTg00Khj8GTg00Toj1FTg00S5j1ETg007Lj31Tg00SWj2\Tg00\Pj1VTg00<ej1UTg00ZJj1STg005Rj17Tg009Ij2:Tg00[>j2RTg00T7j1QTg00=ej2PTg00a=j1OTg00Vfl9NTg00XWl9MTg00b1j1JTg00Ufj2HTg00c0j2ITg00cjj1=Tg00dfj5<Tg00e_j2>Tg011Aj2CTg00fTj3ATg00g9j1BTg00glj2@Tg012=j2;Tg00hgj3DTg007fj26Tg00ifj3[Tg0060j3ZTg00jJj2YTg00jdj6WTg0138lMXTf0R0#2#2p=0P0g00GOR1g00lDg00m?g00n<g00o6f1R2g00oof2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAfARBfBRCfCRDfDREfERFfFRGMMXp=K%40#4p=3g00FLRH#2RI#4RJ#8%0IRI#2#0RK#8RL#5RM'T%8I#5RI#9\Mg00_Og00G1RN%?IP@P?P=P<P;P:P9P8GLP@P8P7P6P5P4P3P2GG%9M%F@%EM311\MMRI#?%VA%UI31g00`ERI#9%SB%7HRO,:LRP'R%QP,PI31p,2fxRI%OIPEPDPCPBPAP@P?P>P=P<P;P:P9P8P7P6PEPDPBPAP@P?P>P=P5M9NPDP<P;P:P9P8P7P6P4M9MP3P2P0MGK%J1R7PIPE%0K#3,H1%2J#3#2#0#0#0#0#0#7'IPD%=7D</>C1CO6%4H#3#3#3#7,:LR69AL@%BC'@';3Dg010cR@%50R7%52RDg00;j%53?1201643164251NRJ[1632163051N%54?132[R1%55?143\JA[320P0n2001000000120000000W2W1W3P1^2D^17^3@P0PL%2H#3#3#2#4#0#3#2#4#2#4#0#7RH,:LR@g00HG9ZLHR71YNH16L@16L751NdO4b0A1M@7PMP@g00DfR@PIfGP0PG%=@D</>F1CO9AALC6%BF'@';3DX:MP2P7P0EWb0b8W5W7W6W9W4WAX=MXCMX<MX;MXINXHNXDMXJMWFX>MXGMXEMW@W?WBo"). Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) ["VP3"] "g014<o"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) ["VP4"] "h01Hh12b1h22b2h31nh43PREh53RLTh61bh74codeh83memh95modelh:7pendingh;4regsp;1p;2p;5p;6p;3p;>g0000j10Tg000Uj13Tg001:j18Tg001Xj15Tg002;j2PTg002gj1LTg00<Ej1ITg00R9j5HTg00a=j1GTg015Aj6FTg00b1j1CTg00Ufj2QTg005Rj17Tg00c0j2OTg00cjj1BTg00dfj5ATg00e_j2@Tg011Aj2:Tg009Ij29Tg00fTj3?Tg00g9j1>Tg00glj2;Tg012=j2=Tg00hgj3<Tg007Lj34Tg007fj26Tg00ifj3JTg0060j3KTg00jJj2ETg00jdj6MTg016:l>NTf0R0#0#0p=1f7R1g00GOR2g00lDg00m?g00n<g00o6f6R3g00oof5R4f4R5f3R6f2R7f1R8P0M>Np=D%30#3p=2g00FLR9#0R:#3R;#8%1:R:#0#1R<#8R=#5R>'P%8:#5R:#L\>g00_O%I:P5P6P7P8P0DHp,2fxR:%G:P4P5P6P7P8P4P5P6P7P8P0EFGD%C2R?P:P4%1<#2,Q2%0;#2#0#1#1#1#1#1#7'OP5%B?DA/@6%79R?/:8%39#2#2#2#7,9=R;9?=7%>6';'=3<g010cR2%50R<%58R@g00;j%57?480g00G1RA1667166834RB[1678167054A%56?478[RC%55?467\BAJ780P0n2001000000120000000W2W1W3PC^2@^1<^32P0P=%09#2#2#0#3#1#2#0#3#0#3#1#7R9,9=R2g00HG9K=9R<1EA916=216=<54AdO4b0A4>2<P>P2g00DfR2P:f8P0P1%B2DA/@31:?5A?=4;%>3';'=3<X6>P8P<P0EMb0b5W4W:X7>W9W8W;o"). Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2f4d4) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Exit ()) ["VP5"] "h03PREh13RLTh24codeh33memh45modelh57pendingh64regsp;1p;2p;5p;6p;3p;>g0000j11Tg000Uj13Tg001:j14Tg001Xj16Tg002;j2JTg002gj1>Tg00<Ej1=Tg00R9j5;Tg00a=j1:Tg015Aj67Tg00b1j19Tg00Ufj2KTg005Rj15Tg00c0j2ITg00cjj1HTg00dfj5BTg00e_j2?Tg011Aj2@Tg009Ij2ATg00fTj3<Tg00g9j1CTg00glj2DTg012=j2ETg00hgj3FTg0178l>GTf0R0#1#1p=0f7g00GOR1g00lDg00m?g00n<g00o6f6g00oof5R2f4R3f3R4f2R5f1R6P0M>Gp=8%30#3p=2g00FLR7#1R8#3R9#4%08R8#1#0R:#4R;#6R<'J%48#6R8#>\<g00_O%=8P3P4P5P6P0D;p,2fxR8%:8P2P3P4P5P6P2P3P4P5P6P0E7G8%91R=P8P2%0:#2,K1%19#2#1#0#0#0#0#0#5'IP3%H=DB/?4%57/@6%37#2#2#2#5,A;9<;5%C4'D'E3FP0b1W0W5X2<W4W3W6o"). Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
