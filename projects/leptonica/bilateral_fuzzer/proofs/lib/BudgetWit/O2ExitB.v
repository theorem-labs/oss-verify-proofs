(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from O2/O2Exit.v (whole file): ref_exit and its cases restated over the budget carrier rzb; the KReplay name table gains entries for the twinned globals and the proof scripts are repointed at them, otherwise byte for byte. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of ref_exit_flush; recorded (KReplay) proofs re-proved by tactics). *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.BudgetWit Require Import Rzb ExitB.
Ltac2 kr_t_O2ExitB () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib2O2;O2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib2O2;O2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2O2;O2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2O2;O2StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2O2;O2StdioDefs8exit_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit=exit_common_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib2O26O2Exit@stdout_pending_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common4Musl9StdioDefs8exit_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib2O26O2Exit5FOE23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_cleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2RelocSites8o2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocMusl5o2_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit5CXF23C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_flushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Exit:exit_pre_GC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit8ref_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib9BudgetWit7O2ExitB=exit_common_Gc59OSSVerify5KrLib9BudgetWit7O2ExitB@stdout_pending_Gc59OSSVerify5KrLib9BudgetWit7O2ExitB5FOE23I59OSSVerify5KrLib9BudgetWit3Rzb3rzb00C59OSSVerify5KrLib9BudgetWit5ExitB>ref_exit_cleanc59OSSVerify5KrLib9BudgetWit7O2ExitB5CXF23C59OSSVerify5KrLib9BudgetWit5ExitB>ref_exit_flushC59OSSVerify5KrLib9BudgetWit5ExitB?t_emit_nil_exitc59OSSVerify5KrLib9BudgetWit7O2ExitB:exit_pre_GC59OSSVerify5KrLib9BudgetWit5ExitB8ref_exitC59OSSVerify5KrLib9BudgetWit5ExitB:ref_exit_Z".
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
ltac2:(KReplay.run1 (kr_t_O2ExitB ()) [] "p'0h01Hh14codeh23dsoh32f1h43f10h53f11h63f12h73f13h83f14h93f15h:3f16h;3f17h<3f18h=3f19h>2f2h?3f20h@3f21hA2f3hB2f4hC2f5hD2f6hE2f7hF2f8hG2f9hH3memhI4regshJ3rp2hK2sphL3tidhM2tphN1vhO3wp2i005ec_a0i019ec_atexiti027ec_compi036ec_dsoi046ec_erri055ec_fai065ec_fei075ec_fsi085ec_g1i095ec_g2i0:7ec_globi0;7ec_locki0<7ec_mtidi0=6ec_soki0>5ec_spi0?7ec_sphii0@7ec_sploi0A6ec_tidi0B5ec_tpi0C7ec_tphii0D7ec_tplop;1p;2p;8p;9p;3p;4p;Ng0000j10Tg000Uj12Tg001:j1HTg001Xj1OTg002;j2[Tg002gj1LTg003IR0j8YTg004Jl9UTg005Rj1;Tg0060j3GTg006Sj2FTg007Lj3=Tg007fj2@Tg008Pj2ITg008mj2CTg009Ij2>Tg009oj11Tg00:Nj4TTg00;Nj2JTg00;jj2STg00<Ej1RTg00<ej1QTg00=Ej3aTg00=ej2PTg00>Gj2NTg00>aj2_Tg00?aj1^Tg00@aj4]Tg00A^lN\Tg00Bfj4MTg00C^j2ZTf0R1#0#0p=:%01#0#0#0#0#0#0#0p=?%21#0#0#0p=8%01#;p=D%01#0#0#0p=K%11#1p=X%11#1#1#1p=W%11#1#1#1#1#1#1#1p=V%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=7f6R2g00DfR3f5R4f4R5f3R6CMf2R7f1R8/Z1'P3=p=6%21#0#2#0p=A%01#2p=<%21#0p=3%01#0#;,>8p=4%01#2#0#0p=9%21#2p=5%21#2#0p=B%01#0#0#2p=EP3P6P7P8CM==51p=`g00FLR9#0R:#2R;#HR<%0:R=#0R>#0#:R?#HR@#ORA'[%H>R>#ORB#L\Ag00G1f7RCP2P4P5P6P7P8P1GYP0f8R0PCP2P4P5P6P7P8g00GORDf9REP0PCP2P4P5P6P7M9UP1fM%;:g00HGR:5G<'FfKRF5=AfNRG%;==G<:'F==AFfORH%0;R;#;=G<:'F==AF%0?#?#?#?R?#0RF#;R:1@@G%8=#DR='I'C1@@H%:F#K#?#D'Cg00HcP3fQR3fPRF,@@RH/I=,>@g00IC#1R=#1#XRG#WR<#V#7#7#7#7#7#7#7#7CTg00Ib3=%2;#:#DR;/CH1@@3/C:g00JBR:/JF%;?,JF'S%RBRF#LR?fUfS,@@/I;,>@PGPFPG1>@3F6P?fV%A9#<#3#A#8,4@PGPFPG1>@:RGF6P?fW%29#8#9#3#A,4@P<PFP<%29#8#9#K#3,4@F6P?fX%29#8#9#3#5#:,4@P<PFP<%B9#E#?,4@R3F6P?fYP3P<PFP<%<9#5#<#<#8#3,4@F6P?fZR3%B9#<#<#5#:#5#3,4@P=1>>:%QB5aB,PFD`P?f[RB%29#8#9#9#3,4@P<PFP<%09#5#5#:#5#3#5#3,4@F6P?f\R:%B9#E#E#9,4@P<PFP<PGF6P?f^R?%B9#<#9#3#5#3,4@P<PFP<P1F6X2A,NAg00J`R<f_RF/_1XN<'N%^Ff`R<%59#:#A#8#9#DPBP3C]PDfbfaP<PFP?f]P:PBfDRBfCR:fBR?fARFf@R<f?RDf>R3f=R9f<R@f;RGf:R>PEP0PCP2P4P5P6P7P8P1MN\W@W?W=W<W;W:W9W8W7W6W5W4WGWFWEWDWCWBWAW>W3PBP:P?PFP<PDP3P9P@PGP>PEP0PCP2P4P5P6P7P8P1OEn80000000010000001E110>10B10010@10?10=10D10C10A10<10;10610710510210810910310110:104W0XJAXOAWLX1AXMAXKAWHWIo"). Qed.

Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o2_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ExitB ()) [] "p'0h01Hh14bufph25bufszh33canh42f1h53f10h63f11h73f12h83f13h93f14h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC7pendinghD3rp1hE2wbhF2wpi006sp_bszi016sp_bufi028sp_bytesi035sp_fdi046sp_leni057sp_locki066sp_maxi078sp_rangei087sp_rendi097sp_rposi0:6sp_sspi0;8sp_wbasei0<7sp_wposi0=8sp_writep;1p;8p;9p;2p;3p;Gp;4g0000j11Tg001:j1CTg001Xj1ETg002gj1GTg00<Ej1RTg00KhR0j8QTg00Lll9NTg000Uj10Tg009oj17Tg005Rj16Tg009Ij2:Tg008mj2>Tg00;Nj2PTg00;jj2DTg008Pj2MTg00N7j2?Tg00NWj1BTg007Lj3=Tg00O7j2LTg00=ej2ATg00OTj2KTg00PQlGITg00C^j2HTg00Q\j2OTg00Bfj4@Tf0R1#1#1p=2%01#0p=<%01#1p=8%01#0#0#0p=9%11#1#1#6p=3%11#6p=Ff2R2f1R3/H1'Ap=5f6R4g00DfR5f5R6f4R7f3R8/O2':P3C@;=1p=4%11#0p=;P5P8P2P3C@==71p=Jg00FLR5#1R9#1R:#1R;#1R<#2#CR=#ER>%C;#ER?#G[g00G1R@%R?RAf7RBP4P6P7P8P2P3P1GQP0f8R0PBP4P6P7P8P2P3g00GORCf9RDP0PBP4P6P7P8P2M9NP1%GAREfFP=%<5#2#8#8#<#9#3RF%0;#8#Fg00IC#7#7#7#7RG%05RH#0RI#0RJ#9#9#9#9#9#9#9#6,:=95AGF4PEfGRKP=PF%09RL#3%7G#7#7#7RMfE,:=95AMF4PEfHRNP=PF%3IPM1:=K95AMF4PEfIRIP=PF%0:#3PM%85#2#<#2#8#8#<#3,:=95AMF4PEfJR:P=PF%0L#3PMA5AMKRKF4PEfKRLP=PF%2H#3PMPKF4PEfLP=PF%1JRJ#1#FPG%65,:=95AGF4PEfMRGP=PF%6;PMA5AMNF4PEfNRNP=PF%6<PMA5AMIF4%05#;#2#<#;#;#;#8#3/>N1PNG'D%05#;#;#8#2#2#2#2#3,>G'DfOR5,MN1??I#B5=@1??:#B%69%6J'L'>PEfRREfQRJ,:=1??L1AALDJfSRL/KGPCfTPLPEPJfPP5PNPGf=RGf<RNf;R5f:RJPDP0PBP4P6P7P8P2P3P1MGIW9W8W7W6W5WAW@W?W>W=W<W;W:W4PGPNP5PJPDP0PBP4P6P7P8P2P3P1O>n80000000010000001>110510<10;10=10110010310910810710410610210:W0WCX3>XD>X2>X1>XF@WEWBo"). Qed.

Lemma exit_pre_G : forall regs mem model code pending,
  exit_pre regs mem model code pending -> @StdioDefs.exit_pre o2_reloc regs mem model code pending.
Proof.
  (* LPS 727298f3: both [exit_pre]s gained writev's channel-reader conjunct, which the recorded
     replay of this proof did not build; the plain proof, conjunct by conjunct *)
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & HC & Hh & Hl & HP).
  exists sp, tp, tid, wp2, rp2. split; [exact (exit_common_G _ _ _ _ _ _ _ _ HC)|].
  split; [exact Hh|]. split; [exact Hl|].
  destruct HP as [(Hp & wp1 & rp1 & Hf) | (wb & wp & bufp & bufsz & rp1 & can & Hs & Hfd & Hcr)].
  - left. split; [exact Hp|]. exists wp1, rp1.
    first [ exact Hf
          | lazymatch goal with |- ExitBase.file_clean _ ?a _ _ =>
              lazymatch type of Hf with ExitBase.file_clean _ ?b _ _ =>
                replace a with b by (vm_compute; reflexivity); exact Hf end end ].
  - right. exists wb, wp, bufp, bufsz, rp1, can.
    split; [exact (stdout_pending_G _ _ _ _ _ _ _ _ Hs)|]. split; [exact Hfd | exact Hcr].
Qed.


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
  rzb RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ExitB ()) ["VP1"] "h01Hh12b1h22b2h31nh42ECh52F1h62Hhh75Hlazyh83RLTh91bh:4codeh;3memh<5modelh=4regsh>3rp1h?3rp2h@2sphA3tidhB2tphC3wp1hD3wp2p;1p;2p;8p;4p;3p;9p;5p;6p;Gg0000j16Tg000Uj14Tg001:j19Tg001Xj13Tg002;j2UTg002gj1?Tg003Ij8KTg005Rj18Tg00@aj4DTg00Toj1WTg00S5j1VTg007Lj32Tg00SWj2TTg00<Ej1PTg00\Pj1OTg00<ej1NTg019_j1MTg0188l9LTg00b1j1ITg00Ufj2HTg00c0j2GTg00cjj1=Tg00dfj5>Tg00e_j2<Tg009Ij2BTg00fTj3@Tg00g9j1;Tg00glj2ATg01:Ij3CTg007fj27Tg00ifj3FTg0060j3ETg00jJj2QTg00jdj6RTg01:olGSTf0R0#6#6p=0%40#6p=:%60#4p=5%40#4p=1P0g00GOR1g00lDg00m?g00n<g00o6f1R2g01;`f2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAMGSp=Jg00FLRB#6RC#4RD#9%0CRC#6#0RE#9RF#3RG'U%9C#3#?\Gg00_Og00G1RCP;P:P8P7P6P5P4P3GKP;%4B#:#5#5#5#1#1#:#0#8P3P2CD%?G%W;%VG321TGGRH#P%O<%NH32p,2fxRH%MHP?P>P=P<P;P:P9P8P7P6P5P?P>P<P;P:P9P8P7P4M9LP3P2P0MAJ%I1R7PHP?%0E#1,H1%5D#:#0#0#0#0#0#8'GP>%=7D>/<=%4B#1#1#1#8,BFR79@F:%;='A3Cg010cR:%30R>%32RDg00;j%33?2201743174252CR1[1732173052C%34?232[RE%35?243\1AF320P0n2001000000120000000W2W1W3PE^2D^1>^3:P0PF%6B#1#1#5#0#1#5#5#0#8RB,BFR:g00HG9EFBR>1QCB17F:17F>52CdO4b0A2G:>PGP:g00DfR:PHfAP0PA%=:D>/<@A@F=7%;@'A3CX9GP2P>P0ERb0b8W7W6W5W4X>GXCGX?GXDGWAX:GXBGX@GW<W;W=o"). Qed.
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
  m_channel_reader model = true ->
  rzb RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: [ExitB.ref_exit_flush] takes the channel-reader premise; the recorded replay
     did not pass it *)
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hcr.
  pose proof (@ExitB.ref_exit_flush fx o2_reloc o2_code o2_sites o2_data o2_rw (FOE23 (fx := fx)) CXF23
                regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending
                (exit_common_G regs mem sp tp code tid wp2 rp2 EC)
                (stdout_pending_G mem wb wp bufp bufsz rp1 can pending SP) Hh Hlazy Hfd Hcr) as R.
  assert (E : (0x2f4d4 : word) = Z_to_bv 64 0x2f4d4)
    by (apply (proj2 (stdpp.bitvector.definitions.bv_eq _ _ _)); reflexivity).
  rewrite E. exact R.
Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ExitB ()) ["VP3"] "g01=;o"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (0x2f4d4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: the plain proof of [ExitB.ref_exit], over this file's lemmas *)
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrd)].
  - subst pending. cbn [W map].
    eapply rzb_conseq; [| apply t_emit_nil_exit].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2f4d4) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  assert (E : Z_to_bv 64 0x2f4d4 = (0x2f4d4 : word))
    by (apply (proj2 (stdpp.bitvector.definitions.bv_eq _ _ _)); reflexivity).
  rewrite E. exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
