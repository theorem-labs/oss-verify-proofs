(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanAcctImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanNodesIface AsanNodesMmA AsanNodesMmB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import SumsAsanClose.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanNodesStartX.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanNodesStartXAsan AsanSmearA AsanHeapSortA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanStartup () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01I79OSSVerify5KrLib2K52AS=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6alwaysC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00c69OSSVerify5KrLib2K55ASB23;AsanStartup3XN0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K52AS9AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify5KrLib2K52AS8AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC79OSSVerify5KrLib2K52AS=AsanPlanSound3APS:node1_stmtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS8ext_stmtC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I79OSSVerify5KrLib2K52AS8AsanPlan2AP6atable00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib2K52AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib2K55ASB23;AsanStartup3XE0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS2WpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS9emit_stmtC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP6spiece00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c69OSSVerify5KrLib2K55ASB23;AsanStartup3XB0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS9ext2_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit:argH0_highC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5argH0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K52AS8AsanInit;argH0_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6x_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseJasan_node_x_sound_XIMemsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseJasan_node_x_sound_XIMemcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseIasan_node_x_sound_XMemsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseIasan_node_x_sound_XMemcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseLasan_node_x_sound_XMemIsZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23CAsanNodesStartXAsanNnode_x_sound_XEnvScan_asan_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23CAsanNodesStartXAsanMnode_x_sound_XPnScan_asan_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS?AsanNodesStartX>x_sound_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseKasan_node_x_sound_XIStrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=SumsAsanCloseJasan_node_x_sound_XPopFreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23:AsanSmearAHasan_node_x_sound_XSniffC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23=AsanHeapSortAKasan_node_x_sound_XHeapSortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages3APHC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP4CEILC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP5xnode00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5LIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages7asan_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages<asan_in_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages<asan_hull_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8AsanInit9img_facts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit2R0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP7a_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5FULL0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit6model0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit2E0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS2sdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit:init_cs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5SINV0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP;init_acs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmB?node_exit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23;AsanStartupEasan_node_x_sound_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>AsanPlanSound2?node_join_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23;AsanStartup9XN0_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23;AsanStartup9XE0_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23;AsanStartup9XB0_soundC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K52AS8AsanInit3inpC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC56Stdlib6ZArith6BinInt1Z4of_NC69OSSVerify5KrLib2K52AS8AsanInit;init_cfg_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmB>node_sys_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmB?node_brk2_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmB@node_brk2s_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmADnode_mmap2_sound_OBLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmAEnode_mmapin_sound_OBLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanNodesMmAHnode_mprotect2_sound_OBLC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS;check_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages<asan_res_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages>asan_shadow_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages=asan_res_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages?asan_hull_coverC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23;AsanTablesA;asan_a_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB23>AsanPlanImages>asan_img_factsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I79OSSVerify5KrLib2K52AS8AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_pix_orient_fuzzer_both1M7init_pcC1@~~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) [] "p'0h01Ah11Eh22E'h33FS0h44FULLh55FULL'h61Hh72H0h85LIMITh91Rh:2R'h;4SEGSh<4SINVh=1Th>2_Hh?3_H0h@4argHhA4argshB2cshC3cs'hD1ehE2idhF5modelhG6model'hH3nx0i001op;1p;2p;<p;3p;6p;5p;9p;8p10000p4p70p1000`p4p710R0p8g001>R1p4p70P0p8g001lR2p4p7210P0p8p1002Xp4p70P0p8g003Nj1=Tg003nj10Tg004Sj11Tg0051j19Tg005TR0j1:Tg0066j1ETP2j2DTg006[l<;Tg007_R2j1?Tg008bj32Tg009<R3j33j2BTg00:9j28Tg00:[j6>Tg00;7j3<Tg00<5j1GTg00<oj2FTg00=Jj17Tg00>=j15Tg00?6j54Tg00@9j36Tg00A7j2CTg00AVl9ATg00B]j8@Tg00Cb#=g00Dag00E`R4g00F?g00F]R5g00G\#0R6#0#0R7#0#0#0#1#9R8%17#9#:[R7p-0R9[[g00HAR:\8\5g00Ha#=g00IaR;%E6#1/D8R8g00J]R6g00KSf?f>R<f=f<R=f;R>f:R?f9R@f4RAf6RBf3RCf2RDf1REM<;f7RF#?g00LK52:%:;R:f8RG93?@18;F32P:A3>?@P0P;P9f0R9g00LkR0g00MHn10110000021000000XD:g00Md18;GP9E>P0fER0?<=C%G<?<=C'FfHfGfFP0fDR0fCfBPAP<PCPDPEM<;%7D%7>521fJR<P<f5R<f@#5PAPCD4;6>[[[^G6^57^:8^25P0PG%5>PFPBD4=60<[/C9b7W6W?W>W=WFX47W9X15XC;WBPGPFPBP<PAPCPDP21BE9M9AeWAXE4PBP<PAPCP3PDPEP9G@eX31W@W<W8WHW0W;o"). Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) [] "p'0h01Ah11Eh22E'h33FS0h44FULLh55FULL'h61Hh72H0h85LIMITh91Rh:2R'h;4SEGSh<4SINVh=1Th>2_Hh?3_H0h@4argHhA4argshB2cshC3cs'hD1ehE2fdhF2idhG5modelhH6model'hI3nx0hJ2pshK1xi001op;1p;2p;<p;3p;4p;6p;5p;8g003Nj12Tg003nj10Tg004Sj13Tg0051j14Tg005TR0j1?Tg0066j1GTg001lj2CTg006[l<<Tg00N@j2;Tg00N`R1j37Tg00O]j41Tg00:9j28Tg008bj39Tg00P=j1ITg00:[j6HTg00;7j3>Tg00<5j1FTg00<oj2ETg00=Jj16Tg00>=j1:Tg00?6j5=Tg00@9j35Tg00P]j3BTg00Q\j2ATg00A7j2DTg00RVj8@Tg00Cb#2g00Dag00E`R2g00F?R3g00F]R4g00G\#0R5#0#0R6#0#0#0#3#4R7%36#4#?[R6p-0R8[[g00HA\7\4g001>R9g00Ha#2g00IaR:g00S\#2R;%G5#3/C7R7g00J]R5g00T[R<#2P8]KfAf@R=f?f>R>f=R?f<R@f;RAf4RBf8RCf3RDf2REf1RFM<<1;3;RG/;:RH#?RIf:RJf9RK57APGP:P3P;PCf7RLC1f6RMC1,8H39PE%I<O1PIA7?@AP0PHP8f0R8g00LkR0g00MHn10110000021000000XDIg00MdPGP:P3P;PJPKC1PCC1,8HPFEHP0fGR0?>@D%F=?>@D'EfJfIfHP0fFR0fEfDPBP>PDPEPFM<<%6E%6A599fLR9P9f5R9%:=PBPDD=;5A[[[^H5^56^:7^24P0PC%:?PLPMD=ABK@A/A9550[/D8b7W?W6W>W=WGX46W9X14XC:WJXE3WBWAXF2PMP9PBPDP1PEPFP8G@eW3W@W<W8WIW0W;o"). Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) [] "p'0h02E'h15FULL'h22R'h36model'h41Ah51Eh63FS0h74FULLh81Hh92H0h:5LIMITh;1Rh<4SEGSh=4SINVh>2TAh?2TBh@2_HhA4argHhB4argshC2cshD3csahE3csbhF1ehG2idhH5modelhI3nx0i001op;1p;2p;<p;3p;4p;6p;5p;8g003Nj1>Tg003nj10Tg004Sj17Tg0051j1:Tg005TR0j1@Tg0066j1FTg001lj2ETg006[l<5Tg00N@j2ATg00UQR1j3<Tg00O]j49Tg00:9j28Tg008bj34Tg00:[j6GTg00;7j31Tg00<5j1?Tg00<oj2=Tg00=Jj16Tg00>=j1;Tg00?6j53Tg00@9j32Tg00VNj2DTg00A7j2CTg00WHj8BTg00Cb#>g00Dag00E`R2g00F?g00F]R3g00G\#0R4#0#0R5#0#0#0#7#:R6%75#:#@[R5p-0R7[[g00HA\6\3g001>R8g00Ha#>g00IaR9%F4#7/E6R6g00J]R4g00KSR:fAR;f@R<f?R=f>f=R>f<R?f;R@f5RAf8RBf4RCf3RDf2REM<51A99RF#@RGf:RHf9RI5<@P9P9PBf7RJC9,8F34PGA<?@HP0PFP7f0R7g00LkR0g00MHn10110000021000000XFGg00MdP9P9PIPBC9,8FP7EGP0fFR0?1?D%?=?1?D'=fIRFfHRGfGRHP0fERKfDRLfCPCP=PDPEf1RMM<5%6ERN%6@548fKROPOPA%;;R;PCPDD3;2@[[[^34^15^26^03A1H>D%?<?1>D'=fJPFPGPHP0PKPLPCP=PDPEPMM<5%6?948NfLRNPNPAP;PCPDD3;2@[[[^34^15^26^03P0PI%;>PBPJD3f6RJ/DA520[[/C7b9W8W@X?:W>WHX75W;X53XE9XD9WCWBXG2PJPAPCPDP1PEPMP7GBeW6WAW=W:WIW4W<o"). Qed.

(* [comment removed for export] *)
Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) ["XAll"] "p'0h01Eh11ah22AAh32AHh42E'h51xi001xp;9p;1p;3p;2p;7p;8p;?p;@p;:g00XNl9GTg003nj10Tg004Sj14Tg0051j13Tg00YLl91j78Tg008bj32Tg00ZEj2;Tg00Zoj25Tg00[Kj76Tg00;7j37Tg00\Jj89Tg00]Ml9:Tg00^cl9FTg00`9l9ETg00aNl9DTg00bcl9<Tg00d;l?=Tg00e[l@>Tg00g:j7?Tg00hCl9@Tg00iZl9ATg00k0l:BTg00lAl9CTg00mXR0p,2spR1p,5rdrawR2p,4argvR3p,4envpR4p,3uidR5p,2hwR6p,3HspR7p,3HvaR8M9Gg00F]R9g00G\#0#0#0#0#0#0#4R:#3R;g00HAR<P0P1P2P3P4P5P6f1R=f0R>M91g00LK32g00nX1;:='5[]1]0P0P1P2P3P4P5P6F6g00oSR:f2R?;7=P0P1P2P3P4P5P6f3P=M91P0P1P2P3P4P5P6P?P=M9152<[^1;^49^09g010MR9P9g011KR9g012MR;P:g013MR<p,4SINVR@P0P1P2P3P4P5P6F8R0p,3FS0RAP>G9P>P:P<P@P0P?P=p,:SINV_frameR>p,:SINV_agreeRBPAM9:P:P<P@P0P?P=P>PBPAM9FP:P<P@P0P?P=P>PBPAM9EP:P<P@P0P?P=P>PBPAM9DP:P<P@P0P?P=P>PBPAM9<P1P2p,4brk0RCP3P4PAP7P8p,3HveRDP5P6p,4HfitREP@p,:SINV_SINV0RFP>M?=P1P2PCP3P4PAP7P8PDP5P6PEP@PFP>PBM@>P9P;P:P<P@P0PAF?P:P<P@P0P?P=P>PBPAM9@P:P<P@P0P?P=P>PBPAM9AP:P<P@P0PAg014Fg015Jg016SP?P>M:BP:P<P@P0P?P=P>PBPAM9Cn01100000<000000000000000000000000W5b2b3o"). Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_A NX0 LIM XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_a_init startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN_A NX0 LIM HS_asan SINV argH HOLES fs.

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net))
              (sd HOLES t_nil E0a fs startup_shape).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) ["Startup"] "h01Eh11Hh22HCh33IMGh41Mh51cp;3p;1p;7p;=p;5p;8p;Hp;<p;:p;@p;2p;9p;Bp;6p;Ap;eg017\j3_Tg018[j1^Tg019Qj1;Tg01:Oj74Tg01;Hl=]Tg00?6j5BTg01<Bj8<Tg01=8j5:Tg00@9j35Tg01>7lH6Tg01?5j87l:ETg00YLj78Tg01?nj19Tg006[l<\Tg01A0j7@Tg003nj10Tg004Sj11Tg0051j12Tg005Tj1DTg01B7l@FTg01CFj7GTg01DOj7HTg01ERj7ITg01FUj7JTg01GXj1KTg003Nj1LTg00P=j1MTg01H:j23Tg01HTl9PTg01IKl9QTg01JCj1RTg01JalBSTg000`j6[Tg01K`l=TTg01Lfl=UTg01Mml=VTg01O5lAWTg01PAlAXTg01QNlAYTg01R^leZTg011KR0g012MR1g00oSR2g013MR3f5R4f4R5f3R6g01SfR7g016SR8g01ToR9f2R:f1R;f0R<M=Tp=NP0P1P2P3P5P6P:g015JR=g01V:R>P8P9P;P<M=Up=CP0P1P2P3P5P6P:P=P>P8P9P;P<M=Vp=AP0P1P2P3f6R?P4P5P=P7P>P8P9P6P:P;P<g01WDR@MAWp==P0P1P2P3P?P4P5P=P7P>P8P9P6P:P;P<P@MAXp=>P0P1P2P3P?P4P5P=P7P>P8P9P6P:P;P<P@MAYp=?P0P<P;P1P2P3P:g009<g00N`g00UQg014FP=P8P9P6P5P4P?f7f8f9f:f;f<f=f>f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNg01XPfOfPfQfRfSfTg01YUR?fUg00MdfVMeZp=Og01ZNg00mXR49_01g01[YR5P0p,2spR6#^R9%;1P4P6p,5rdrawR8p,4argvR=p,4envpR:p,3uidR@p,2hwR>F4R7P0P6p,4brk0RAp,5mbaseRBP=P:p,2fsRCp,5stdinRDP@p,3gidREP>p,6groupsRFp,3netRGM=]RHDBp,5HOLESRIP?P4P6P8PAP=P:P@P>G<R?PCp,=startup_shapeRJD:950<X55P0P1P4P6P8PAPBP=P:PCPDP@PEP>PFPGP<p,3HspR5p,4Hbrkp,3Hmbp,3HvaRKp,3HveRLp,4HfitRMp,4HuidMH6P0P1P2P3P4P6P8PAP=P:P@P>G7RNP4P6P8P=P:P@P>F8ROPCP?%91P9P7PHM<\p,3IT0p,6IT0_okp,7HS_asanPNPOp,2AHRPp,2AARQp,2SFRRp,2SARSPIp,;HOLES_agreep,9HOLES_nilPCp,3KC0PNPOPCPQPRPSENPNPOPCPPPRDCPNPOPCPPPRDAPNPOPCPPPQPRPSF=PNPOPCPPPQPRPSF>PNPOPCPPPQPRPSF?P0P1P2P3PNPOPCF@P6P8PAP=P:PCP5PKPLP@P>PMPNg00F]g00G\#0#0#0RM#0#0#0#1#2%1M#2#D[P4P6P8PAP=P:P@P>P;P<M:EP<W1W4W0PRPSM@FP0P1P2P3PNPOPCFGP0P1P2P3PNPOPCFHP0P1P2P3PNPOPCFIP0P1P2P3PNPOPCFJp,;HOLES_soundp,4FUELp,5BFUELg01\N#Kp,<startup_planPJp,<startup_certP?P9P7PHP<g00T[R<#L%M<'3MWOb2P0g01]NR<P4P6PAPBP8P3P=P:PCPDP@PEP>PFPGM9PM9QP0P1P4P6P8PAPBP=P:PCPDP@PEP>PFPGP<g00F?%R<'3MBSE[b3o"). Qed.
End Startup.
