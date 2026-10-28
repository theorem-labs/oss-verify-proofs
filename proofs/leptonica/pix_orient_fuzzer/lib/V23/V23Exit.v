(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require ExitBase StdioDefs Exit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23StdioDefs V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocMusl.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require R23Code FuncsOnExit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23R23Code.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Exit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs;exit_common00I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;exit_common00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs<atexit_stateC5ARocqVerifyHarness?AgentSubmission3V23;V23ExitBase=stdio_globalsC5ARocqVerifyHarness?AgentSubmission3V23;V23ExitBase:file_cleanK6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;exit_common01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocK47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;foe_variant00I5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs>stdout_pending00I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs>stdout_pending00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs9ssp_cellsK6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs>stdout_pending01C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs8exit_preK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltac5ARocqVerifyHarness?AgentSubmission3V237V23Exit=exit_common_GK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission3V237V23Exit@stdout_pending_GK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs8exit_preC6ARocqVerifyHarness?AgentSubmission6Common4Musl8ExitBase:file_cleanI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c5ARocqVerifyHarness?AgentSubmission3V237V23Exit5FOE23C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_exitI5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_cleanC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocSites9v23_sitesC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_dataC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocMusl6v23_rwc5ARocqVerifyHarness?AgentSubmission3V237V23Exit5CXF23I47Corelib7Numbers7BinNums1N00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec1WC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_emitC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_flushC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit?t_emit_nil_exitc5ARocqVerifyHarness?AgentSubmission3V237V23Exit:exit_pre_GC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit8ref_exitC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit:ref_exit_Z".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exit_common_G : forall regs mem sp tp code tid wp2 rp2,
  exit_common regs mem sp tp code tid wp2 rp2 ->
  @StdioDefs.exit_common v23_reloc regs mem sp tp code tid wp2 rp2.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) [] "p'0h01Hh14codeh23dsoh32f1h43f10h53f11h63f12h73f13h83f14h93f15h:3f16h;3f17h<3f18h=3f19h>2f2h?3f20h@3f21hA2f3hB2f4hC2f5hD2f6hE2f7hF2f8hG2f9hH3memhI4regshJ3rp2hK2sphL3tidhM2tphN1vhO3wp2i005ec_a0i019ec_atexiti027ec_compi036ec_dsoi046ec_erri055ec_fai065ec_fei075ec_fsi085ec_g1i095ec_g2i0:7ec_globi0;7ec_locki0<7ec_mtidi0=6ec_soki0>5ec_spi0?7ec_sphii0@7ec_sploi0A6ec_tidi0B5ec_tpi0C7ec_tphii0D7ec_tplop;1p;2p;8p;9p;3p;4p;Ng0000j11Tg000Uj12Tg001:j1GTg001Xj1OTg002;j2ZTg002gj1KTg003IR0j8XTg004Ll9UTg005Tj1=Tg0062j3FTg006Uj2ETg007Nj3?Tg007hj2ATg008Rj2HTg008oj2CTg009Kj2@Tg00:1j10Tg00:Pj4TTg00;Pj2JTg00;lj2STg00<Gj1RTg00<gj1QTg00=Gj3PTg00=gj2NTg00>Ij2MTg00>cj2_Tg00?ej1^Tg00@gj4]Tg00AflN[Tg00Bnj4LTg00Cfj2\Tf0R1#1#1p=3%11#1#1#1p=4%21#1#1#1p=I%11#=p=D%01#0p=Y%01#0#0#0p=W%01#0#0#0#0#0#0#0p=V%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=;f6R2g00DnR3f5R4f4R5f3R6CLf2R7f1R8/\1'N3?p=:%11#2p=>%11#1#2#2p=9%21#1p=8%11#1#=,@8p=5%11#1#2#1p=7%11#2#2#1p=<%21#2p=6%21#1#1#2p=BP3P6P7P8CL=?51p=`g00FUR9#1R:#2R;#GR<%1:R=#1R>#1#3R?#GR@#ORA'Z%G>R>#ORB#K\Ag00G:f7RCP2P4P5P6P7P8P1GXP0f8R0PCP2P4P5P6P7P8g00GXRDf9REP0PCP2P4P5P6P7M9UP1fM%=:g00HSR:5F<'EfKRF5?AfNRG%===F<:'E=?AFfORH%1;R;#==F<:'E=?AF%1?#4#4#4#4#4#4R?#1RF#=R:1A@G%I=#DR='H'C1A@H%3F#4#4#4#D'Cg00HoP3fQR3fPRF,A@RH/H=,@@g00IO#0R=#0#YRG#WR<#V#;#;#;#;#;#;#;#;CTg00In3?%2;#3#DR;/CH1A@3/C:g00JNR:/JF%=?,JF'S%RBRF#KR?fUfS,A@/H;,@@PGPFPG1@@3F:P?fV%>9#>#I#>#3#9#8,5@PGPFPG1@@:RGF:P?fW%79#<#6#4#7,5@P<PFP<%79#9#<#8#I,5@F:P?fX%79#<#6#4#>#3,5@P<PFP<%79#9#<#8#<,5@R3F:P?fYP3P<PFP<%89#9#3#7#6#3,5@F:P?fZR3%39#B#6#6#6#3#7,5@P=1@>:%QB5PB,NFD`P?f[RB%79#<#8#B#4,5@P<PFP<%39#9#8#9#6#3#>,5@F:P?f\R:%79#<#8#B#7,5@P<PFP<PGF:P?f^R?%39#B#6#6#3#9#8,5@P<PFP<P1F:X2A,MAg00JlR<f_RF/_1XN<'M%^Ff`R<%19#>#9#6#8#<#4#DPBP3C]PDfbfaP<PFP?f]P:PBfDRBfCR:fBR?fARFf@R<f?RDf>R3f=R9f<R@f;RGf:R>PEP0PCP2P4P5P6P7P8P1MN[W@W?W=W<W;W:W9W8W7W6W5W4WGWFWEWDWCWBWAW>W3PBP:P?PFP<PDP3P9P@PGP>PEP0PCP2P4P5P6P7P8P1OEn80000000010000001E110>10B10010@10?10=10D10C10A10<10;10610710510210810910310110:104W0XJAXOAWLX1AXMAXKAWHWIo"). Qed.

Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v23_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) [] "p'0h01Hh14bufph25bufszh33canh42f1h53f10h63f11h73f12h83f13h93f14h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC7pendinghD3rp1hE2wbhF2wpi006sp_bszi016sp_bufi028sp_bytesi035sp_fdi046sp_leni057sp_locki066sp_maxi078sp_rangei087sp_rendi097sp_rposi0:6sp_sspi0;8sp_wbasei0<7sp_wposi0=8sp_writep;1p;8p;9p;2p;3p;Gp;4g0000j10Tg001:j1DTg001Xj1FTg002gj1GTg00<Gj1RTg00L4R0j8QTg00M:l9NTg000Uj11Tg00:1j19Tg005Tj17Tg009Kj2:Tg008oj2>Tg00;Pj2PTg00;lj2ETg008Rj2MTg00NEj2?Tg00Nej1CTg007Nj3=Tg00OEj2LTg00=gj2BTg00Obj2KTg00PalGITg00Cfj2HTg00Qlj2OTg00Bnj4ATf0R1#0#0p=2%01#1p=<%11#1#1#1p=8%11#0p=3%11#1p=;%01#0#0#7p=6%01#7p=@f2R2f1R3/H1'Bp=5f6R4g00DnR5f5R6f4R7f3R8/O2':P3CA;=1p=4P5P8P2P3CA==71p=Jg00FUR5#0R9#0R:#0R;#0R<#2#DR=#FR>%D;#FR?#G[g00G:R@%R?RAf7RBP4P6P7P8P2P3P1GQP0f8R0PBP4P6P7P8P2P3g00GXRCf9RDP0PBP4P6P7P8P2M9NP1%GAREfFP=%05#<#2#8#3#;#<#3#6RF%1;#3#@g00IO#9#9#9#9RG%15RH#1RI#1RJ#8#8#8#8#8#8#8#7,:=95AGF4PEfGRKP=PF%19RL#6%9G#9#9#9RMfE,:=95AMF4PEfHRNP=PF%6IPM1:=K95AMF4PEfIRIP=PF%1:#6PM%05#2#3#<#;#2#;#3#<#3#@,:=95AMF4PEfJR:P=PF%1L#6PMA5AMKRKF4PEfKRLP=PF%2H#6PMPKF4PEfLP=PF%0JRJ#0#@PG%75,:=95AGF4PEfMRGP=PF%7;PMA5AMNF4PEfNRNP=PF%7<PMA5AMIF4%05#3#;#2#2#3#2#3#<#6/>N1PNG'E%05#3#;#2#3#2#2#2#2#6,>G'EfOR5,MN1??I#C5=@1??:#C%79%7J'L'>PEfRREfQRJ,:=1??L1BALDJfSRL/KGPCfTPLPEPJfPP5PNPGf=RGf<RNf;R5f:RJPDP0PBP4P6P7P8P2P3P1MGIW9W8W7W6W5WAW@W?W>W=W<W;W:W4PGPNP5PJPDP0PBP4P6P7P8P2P3P1O>n80000000010000001>110510<10;10=10110010310910810710410610210:W0WCX3>XD>X2>X1>XF@WEWBo"). Qed.

Lemma exit_pre_G : forall regs mem model code pending,
  exit_pre regs mem model code pending -> @StdioDefs.exit_pre v23_reloc regs mem model code pending.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) [] "p'0h03rp1h13canh25bufszh34bufph42wph53wp1h62wbh71Hh83rp2h93wp2h:3tidh;2tph<2sph=5CASESh>1Eh?2ECh@2F1hA3HfdhB2HhhC5HlazyhD2SPhE4codehF3memhG5modelhH7pendinghI4regsi001xp;1p;2p;5p;8p;4p;3p;9p;6g0000j1=Tg000Uj1DTg001:j1MTg001Xj1XTg002;j2cTg002gj1PTg00<Gj1TTg00RIj5]Tg003Ij8<Tg00SGj1\Tg00Sij2[Tg00<gj1STg005Tj1NTg00@gj45Tg00>IR0j20Tg00L4j83Tg009Kj2`Tg00TIj1_Tg00=gj2^Tg00UAj1HTg00V8j2ZTg00Qlj2YTg00;lR1j22Tg007Nj3:Tg00W8l9iTg00X6j4CTg00XQj3hTg00Xkl9gTg00Ylj3fTg00ZFj4OTg00Z`j1VTg00[Tj2UTg00\LR2j2RTg00\fj1QTg00]^j6bTg004Ll9aTg00^aj5dTg00M:l9eTf0R3#=#=p=@%D3#=p=F%=3#Dp=E%D3#Dp=?f4R4f3R5f2R6#Vf1R7'U;:3'2p=4g00G:R8/03p=1f5R9?:451067'21083'Rp=6f7R:f6R;%H9;:4%Q6=:57/23'2'2p=9g00GXR<P4P5P6P7P3Ebp=>%Q;=::9A:456/27/R3'2p=GA:567/23p=L%H7=:63p=K%Q7=:63p=JP<P:P;P9P4P5P6P7P3M9ap=AP<P5P6P7P3Ddp=8P<P:P;P9P4P5P6P7P3M9ep=7%V6/U7=:53p=;1067,25/R3p=I1073,26p=WP;P9P4P5P6P7P3COCOp=Bg00FUR=#=R>#D#M%=>R>#=R?#=#@#MR@#XRA'c%M?#XR?#P\Ag00_e%T?RBP4P5P6P7P3D]P0PAf:RCf9RDP4P5P:P6P7P3G<%PAREf8RF%\ARG1[AARH#TRIPF%SHRHPBP;%S?R?PAf;RJ%@=#F#E#?#?#E#F#?#@#@#NRKP7P3C5X0A,0AX5Af?RLP9P4P5P6P7P3f<RMG3g00`[RN#PROf>RP%N=,`@R@%_@,^NRND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP;P9P4P5P6D>P3PMPJP4P5PDP6P7P3G<PEPCPGPIPCPHPBPFP?PAf=RQPKP7P3C5X0A,0AX5AfARRP9P4P5P6P7P3PPG3POf@RSP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AP0PAPQPMP9P5PCP6P7P3G<PEPJPGPIPJPHPBPDP?PAPPPKP7P3C5X0A,0AX5AfBRTP9P4P5P6P7P3PLG3POPRP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;APCPDPFP:P;D>P3PLPPP:P5PMP6P7P3G<PEPQPGPIPQPHPBPJP?PAPSPKP7P3C5X0A,0AX5AfDRUP9P4P5P6P7P3PRG3POfCRVP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1P0P8PSPLPFP4PQP6P7P3G<PEPPPGPIPPPHPBPMP?PAPRPKP7P3C5X0A,0AX5AfERWP9P4P5P6P7P3PTG3POPUP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8PPPQPMPJPCD>P3PTPRPCP;PLP6P7P3G<PEPSPGPIPSPHPBPPP?PAPVPKP7P3C5X0A,0AX5AfGRXP9P4P5P6P7P3PUG3POfFRYP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AP0PAPVPTPJP:PSP5P7P3G<PEPRPGPIPRPHPBPLP?PAPUPKP7P3C5X0A,0AX5AfHRZP9P4P5P6P7P3PWG3POPXP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9APTPRPSPLPPD>P3PWPUPQPDPTP9P7P3G<PEPVPGPIPVPHPBPRP?PAPYPKP7P3C5X0A,0AX5AfJR[P9P4P5P6P7P3PXG3POfIR\P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AP0PAPYPWPPPCPVP;P6P3G<PEPUPGPIPUPHPBPTP?PAPXPKP7P3C5X0A,0AX5AfKR]P9P4P5P6P7P3PZG3POP[P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8APYPWPUPVPTD>P3PZPXPSPMPWPFP4P3G<PEPYPGPIPYPHPBPUP?PAP\PKP7P3C5X0A,0AX5AfMR^P9P4P5P6P7P3P[G3POfLR_P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9P1P\PZPRPQPYPDP9P7G<PE%HXPGPIPXPHPBPWP?P[PKP7P3C5X0A,0AX5A,0AfNR`P9P4P5P6P7P3P]G3POP^P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGCLP[P\PZPXPYD>P3P]P[PVPLPZPJP:P5G<PE%H[PGPIP[PHPBPZP?P^PKP7P3C5X0A,0AX5A,0AfQRaP9P4P5P6P7P3P`G3POfPRbP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGCLP1AKE]GPIP]PHPBP\P?P`PKP7P3C5X0A,0AX5A,0AfRRcP9P4P5P6P7P3fORdG3POPaP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGP`P^P_P]P[D>P3AKE^GPIP`PHPBP_P?PaPKP7P3C5X0A,0AX5A,0AfUReP9P4P5P6P7P3PcG3POfTRfP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1GGP1AJIdHPBP^P?PAPcPKP7P3C5X0A,0AX5AfVRgP9P4P5P6P7P3fSRhG3POPeP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PcPaPbPdP`D>P3AJIaHPBPbP?PAPePKP7P3C5X0A,0AX5AfYRiP9P4P5P6P7P3PgG3POfXRjP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6PAfZRkPiP4P5fWRlP6P7P3GAPEPjPGPIPjPHPBPgP?PAf[Rm%?=#?#E#E#@#?#@#@#N%?>#F#E#F#?,Z<'YR<P7P3C8X0A,0AX5Af_R>P9P4P5P6P7P3f\R=G7POf^RnP@PNC;Ro'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6G9X8A,0AX9A,0AX:8#1X;A,0AX<AP^PAPiPjPaP5PgP6P7P3GAPEPlPGPIPlPHA:Be?RpPAPkP<P7P3C8X0A,0AX5APnP9P4P5P6P7P3PmG7POf]RqP@PNC;Rr'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIG9X8A,0AX9A,0AX:8#1X;AP\P8PjPlPbP_PeP6P7P3GAPEPgPGPIPgPHPBPfP?PAPiP<P7P3C8X0A,0AX5APqP9P4P5P6P7P3PkG7POP=P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RbG9X8A,0AX9A,0AX:8PWPAPlPgPdP]PfPXP7P3GAPEPePGPIPePHA:Bh?RdPAPjP<P7P3C8X0A,0AX5AP=P9P4P5P6P7P3PiG7POPmP@PNC;Rs'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIG9X8A,0AX9APRPAPgPeP`P[PhPYPTP3GAPEPfPGPIPfPHA:Bc?RtPAPlP<P7P3C8X0A,0AX5APmP9P4P5P6P7P3PjG7POPkP@PNC;Ru'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIRvG9X8APQPePfP^P\PcPWPRPQGAAKEhGRGAJIhHRhA:Ba?RaPAPgP<P7P3C8X0A,0AX5APkP9P4P5P6P7P3PlG7POPiP@PNC;RH'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1CIRI'2RE'2PePfP^P\PcPWPRPQPDM9iPGPEP9PhPIP7P2PgPKP7P3C5X0A,0AX5A9WaAPkP9P4P5P6P7P3PlG3/2HX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PvP3PlPKP7P3C5X0A,0AX5A9WtAP1PdPjPKP7P3C5X0A,0AX5A,0APbP3PmPKP7P3C5X0A,0AX5A,0AP0PAP=PKP7P3C5X0A,0AX5APBPjP?PAPqP<P7P3C8X0A,0AX5AfaRqP9P4P5P6P7P3PnG7POf`RdP@PNC;Rt'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RlP3PnPKP7P3C5X0A,0AP0PAP>PKP6P3C5X0APBP=P?PAPqP<P7P3C8X0A,0AX5AfeRvP9P4P5P6P7P3fbRHG7POfdRkP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6RgP3PqPKP4P3C5A:B>?RKPkP<P7P3C8X0A,0AX5AR2,0ARI'2fhRhP9P4P5P6P7P3PvG7POfgREP@PNC;RG'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1PKPIPDPAP2P9PAfcR2P<P;P3C8X0AP7P3FBCC3hW@X0AP7P3O2n2001000010121100000W7X5AP7P3O2n2001000010121100000W7X>pP7P3O2n2001000010121000000W7P3O1PmP9P4P5P6P7P3PjG3/2uX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68#1P0P8P=P9P4P5P6P7P3PiG3/2sX1A,0AX0A,0AX2A,0AX3A,0AX48#1X68PbP3PnP9P4P5P6P7P3PmG3/2rX1A,0AX0A,0AX2A,0AX3A,0AX48#1P0P8P>P;P4P5P6P7P3P=G3/2oX1A,0AX0A,0AX2A,0AX3A,0AX48PlP3PqPFP4P5P6P7P3PnG3/2tX1A,0AX0A,0AX2A,0AX3A,0AP0PAPHPDP9P5P6P7P3P>G3POPqP@PND4X1A,0AX0A,0AX2A,0AX3APgP3PkPJP:P5P6P7P3PqG3POP2P@PND4X1A,0AX0A,0AX2A,0AP0PAPvPMPFP4P6P7P3PHG3/2aX1A,0AX0A,0AX2APBPdP?PAPvP<P7P3C8X0A,0AX5AfiRdP9P4P5P6P7P3ffRaG7POPhP@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PEPPPCP;P6P7P3PkG3POPaP@PND4X1A,0AX0A,0AP0PAPhPLPJP:P5P7P3PvG3/2GX1A,0AX0APBPkP?PAPdP<P7P3C8X0A,0AX5AfmRkP9P4P5P6P7P3fjRGG7POflRvP@PNC;Ra'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PGPRPQPDP9P7P3PEG3POPdP@PND4X1A,0AP0PAfkR0PTPPPCP;P6P3PhG3POPGP@PND4X1APBPhP?PAPkP<P7P3C8X0A,0AX5AfqRhP9P4P5P6P7P3fnR;G7POfpRdP@PNC;RE'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PkPUPSPMPFP4P3PGG3/2aP1P;PWPRPQPDP9P7P0G3POPkP@PNC;PBPvP?PAPhP<P7P3C8X0A,0AX5AfuRvP9P4P5P6P7P3frR0G7POftR;P@PNC;R1'2X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68E6P3PdPXPVPLPJP:P5PkG3PBfoRBP?P;P<P7P3C8X0A,0AX5A,0ACLfxP9P4P5P6P7P3PvG7POfwR<P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48#1X68R?#1P8P?P\P8P<P`P4P5P6P7P3P;G7POfvR4P@PND4X1A,0AX0A,0AX2A,0AX3A,0AX48PWPAP4P^P\P5P6P7P3fsR5G7POPvP@PND4X1A,0AX0A,0AX2A,0AX3APRPAPvP_PZPUP6P7P3P0G7/21X1A,0AX0A,0AX2APQPAP;P]PXPVPLP7P3PhG7POP5P@PND4X1A,0AX0APDPAP5P[PYPTPPPCP3PdG7POP0P@PND4X1AP9P0P\PWPRPQPDP9PBG7POPhP@PNC;P0P\PWPRPQPDP9PBP7M9gP3CCFBFBFB3fXAEWDP7P3O2n2001000010121000000W7X1AP7P3O2n2001000010121100000W7X0AP7P3O2n2001000010121100000W7X2AP7P3O2n2001000010121100000W7X3AP7P3O2n2001000010121100000W7X48P7P3O2n2001000010121100000W7X68P7P3O2n2001000010121100000W7P3O1n200100001021100011000CCCCCCCOFBFBW=WCP7P3O2n2011000000121000000W7WBP7P3O2n2011000000121000000W7W?P7P3O2n2011000000121000000W7X8AP7P3O2n2011000000121100000W7X9AP7P3O2n2011000000121100000W7X:8P7P3O2n2011000000121100000W7X;AP7P3O2n2011000000121100000W7X<AP7P3O2n2011000000121100000W7WHXEAWGWFWIo"). Qed.


(* [comment removed for export] *)
Definition FOE23 {fx : FPState} : @StdioDefs.funcs_on_exit_spec v23_reloc fx :=
  @FuncsOnExit.funcs_on_exit fx v23_reloc v23_code v23_sites v23_data v23_rw v23_r23code.
Definition CXF23 : @ExitBase.cxa_finalize_ret v23_reloc := @R23Code.F23_13198 v23_reloc v23_data v23_r23code.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x127db0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x10e4e0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP1"] "h01Hh12b1h22b2h31nh42ECh52F1h62Hhh75Hlazyh83RLTh91bh:4codeh;3memh<5modelh=4regsh>3rp1h?3rp2h@2sphA3tidhB2tphC3wp1hD3wp2p;1p;2p;8p;4p;3p;9p;5p;6p;Gg0000j16Tg000Uj14Tg001:j1:Tg001Xj13Tg002;j2UTg002gj1?Tg003Ij8KTg005Tj19Tg00@gj4DTg00UAj1WTg00SGj1VTg007Nj31Tg00Sij2TTg00<Gj1PTg00\fj1OTg00<gj1NTg00aSj1MTg00W8l9LTg00bIj1ITg00V8j2HTg00cHj2GTg00dBj1=Tg00e>j5>Tg00f7j2<Tg009Kj2BTg00flj3@Tg00gQj1;Tg00hDj2ATg00i?j3CTg007hj25Tg00j>j3FTg0062j3ETg00jbj2QTg00k<j6RTg00kXlGSTf0R0#6#6p=0%40#6p=7%60#4p=8%40#4p=2P0g00GXR1g00l\g00mZg00nZg00oWf1R2g010Sf2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAMGSp=Jg00FURB#6RC#4RD#:%0CRC#6#0RE#:RF#3RG'U%:C#3#?\Gg00_eg00G:RCP;P:P8P7P6P5P4P3GKP;%0B#7#8#2#2#8#7#2#0#0#9P3P2CD%?G%W;%VG311TGGRH#P%O<%NH31p,2fxRH%MHP?P>P=P<P;P:P9P8P7P6P5P?P>P<P;P:P9P8P7P4M9LP3P2P0MAJ%I1R7PHP?%0E#2,H1%8D#7#0#0#0#0#0#9'GP>%=7D>/<=%4B#2#2#2#9,BFR79@F:%;='A3Cg011IR:%30R>%32RDg00;l%33?1201543154251CR1[1532153051C%34?132[RE%35?143\1AF320P0n2001000000120000000W2W1W3PE^2D^1>^3:P0PF%0B#0#2#7#8#0#2#7#0#0#9RB,BFR:g00HS9EFBR>1QCB15F:15F>51CdO4b0A1G:>PGP:g00DnR:PHfAP0PA%=:D>/<@A@F=7%;@'A3CX9GP2P>P0ERb0b8W7W6W5W4X>GXCGX?GXDGWAX:GXBGX@GW<W;W=o"). Qed.
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
  realizes RSEGS (mkCfg (mkst regs (0x10e4e0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP2"] "h01Hh12b1h22b2h31nh42ECh53Hfdh62Hhh75Hlazyh83RLTh92SPh:1bh;4bufph<5bufszh=3canh>4codeh?3memh@5modelhA7pendinghB4regshC3rp1hD3rp2hE2sphF3tidhG2tphH2wbhI2wphJ3wp2p;1p;2p;8p;3p;9p;5p;6p;Mg0000j13Tg000Uj15Tg001:j18Tg001Xj14Tg002;j2TTg002gj19Tg00<Gj1?Tg003Ij8LTg00L4j8GTg00UAj1FTg00SGj1ETg007Nj31Tg00Sij2\Tg00\fj1VTg00<gj1UTg00Z`j1STg005Tj17Tg009Kj2:Tg00[Tj2RTg00TIj1QTg00=gj2PTg00aSj1OTg00W8l9NTg00Xkl9MTg00bIj1JTg00V8j2HTg00cHj2ITg00dBj1=Tg00e>j5<Tg00f7j2>Tg011gj2CTg00flj3ATg00gQj1BTg00hDj2@Tg012cj2;Tg00i?j3DTg007hj26Tg00j>j3[Tg0062j3ZTg00jbj2YTg00k<j6WTg013^lMXTf0R0#3#3p=0P0g00GXR1g00l\g00mZg00nZg00oWf1R2g010Sf2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAfARBfBRCfCRDfDREfERFfFRGMMXp=K%50#5p=2g00FURH#3RI#5RJ#8%0IRI#3#0RK#8RL#4RM'T%8I#4RI#9\Mg00_eg00G:RN%?IP@P?P=P<P;P:P9P8GLP@P8P7P6P5P4P3P2GG%9M%F@%EM311\MMRI#?%VA%UI31g00`[RI#9%SB%7HRO,:LRP'R%QP,PI31p,2fxRI%OIPEPDPCPBPAP@P?P>P=P<P;P:P9P8P7P6PEPDPBPAP@P?P>P=P5M9NPDP<P;P:P9P8P7P6P4M9MP3P2P0MGK%J1R7PIPE%0K#2,H1%3J#2#3#0#0#0#0#0#7'IPD%=7D</>C1CO6%5H#2#2#2#7,:LR69AL@%BC'@';3Dg011IR@%40R7%42RDg00;l%43?1201643164251NRJ[1632163051N%44?132[R1%45?143\JA[320P0n2001000000120000000W2W1W3P1^2D^17^3@P0PL%0H#0#5#2#0#5#0#5#2#3#0#0#7RH,:LR@g00HS9ZLHR71YNH16L@16L751NdO4b0A1M@7PMP@g00DnR@PIfGP0PG%=@D</>F1CO9AALC6%BF'@';3DX:MP2P7P0EWb0b8W5W7W6W9W4WAX=MXCMX<MX;MXINXHNXDMXJMWFX>MXGMXEMW@W?WBo"). Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP3"] "g014bo"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x10e4e0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP4"] "h01Hh12b1h22b2h31nh43PREh53RLTh61bh74codeh83memh95modelh:7pendingh;4regsp;1p;2p;5p;6p;3p;>g0000j12Tg000Uj14Tg001:j18Tg001Xj11Tg002;j2PTg002gj1LTg00<Gj1ITg00RIj5HTg00aSj1GTg015gj6FTg00bIj1CTg00V8j2QTg005Tj17Tg00cHj2OTg00dBj1BTg00e>j5ATg00f7j2@Tg011gj2:Tg009Kj29Tg00flj3?Tg00gQj1>Tg00hDj2;Tg012cj2=Tg00i?j3<Tg007Nj33Tg007hj26Tg00j>j3JTg0062j3KTg00jbj2ETg00k<j6MTg016bl>NTf0R0#2#2p=0f7R1g00GXR2g00l\g00mZg00nZg00oWf6R3g010Sf5R4f4R5f3R6f2R7f1R8P0M>Np=D%40#4p=5g00FUR9#2R:#4R;#8%0:R:#2#0R<#8R=#1R>'P%8:#1R:#L\>g00_e%I:P5P6P7P8P0DHp,2fxR:%G:P4P5P6P7P8P4P5P6P7P8P0EFGD%C2R?P:P4%0<#5,Q2%2;#5#2#0#0#0#0#0#7'OP5%B?DA/@6%79R?/:8%49#5#5#5#7,9=R;9?=7%>6';'=3<g011IR2%10R<%18R@g00;l%17?380g00G:RA1667166833RB[1678167053A%16?378[RC%15?367\BAJ780P0n2001000000120000000W2W1W3PC^2@^1<^32P0P=%09#0#4#5#0#4#0#4#5#2#0#0#7R9,9=R2g00HS9K=9R<1EA916=216=<53AdO4b0A3>2<P>P2g00DnR2P:f8P0P1%B2DA/@31:?5A?=4;%>3';'=3<X6>P8P<P0EMb0b5W4W:X7>W9W8W;o"). Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x10e4e0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP5"] "h03PREh13RLTh24codeh33memh45modelh57pendingh64regsp;1p;2p;5p;6p;3p;>g0000j11Tg000Uj13Tg001:j14Tg001Xj16Tg002;j2JTg002gj1>Tg00<Gj1=Tg00RIj5;Tg00aSj1:Tg015gj67Tg00bIj19Tg00V8j2KTg005Tj15Tg00cHj2ITg00dBj1HTg00e>j5BTg00f7j2?Tg011gj2@Tg009Kj2ATg00flj3<Tg00gQj1CTg00hDj2DTg012cj2ETg00i?j3FTg017`l>GTf0R0#1#1p=0f7g00GXR1g00l\g00mZg00nZg00oWf6g010Sf5R2f4R3f3R4f2R5f1R6P0M>Gp=8%30#3p=2g00FUR7#1R8#3R9#4%08R8#1#0R:#4R;#6R<'J%48#6R8#>\<g00_e%=8P3P4P5P6P0D;p,2fxR8%:8P2P3P4P5P6P2P3P4P5P6P0E7G8%91R=P8P2%0:#2,K1%19#2#1#0#0#0#0#0#5'IP3%H=DB/?4%57/@6%37#2#2#2#5,A;9<;5%C4'D'E3FP0b1W0W5X2<W4W3W6o"). Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
