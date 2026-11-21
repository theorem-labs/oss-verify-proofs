(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader premise; the recorded proofs of exit_pre_G, ref_exit_flush, ref_exit replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require ExitBase StdioDefs Exit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23StdioDefs O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocMusl.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require R23Code FuncsOnExit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23R23Code.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Exit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib3O23<O23StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3O23<O23StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23ExitBase:file_cleanC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3O23<O23StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3O23<O23StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3O23<O23StdioDefs8exit_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23Exit=exit_common_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib3O237O23Exit@stdout_pending_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common4Musl9StdioDefs8exit_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib3O237O23Exit5FOE23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_cleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocCode8o23_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23=O23RelocSites9o23_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocMusl6o23_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23Exit5CXF23C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_flushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23Exit:exit_pre_GC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit8ref_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exit_common_G : forall regs mem sp tp code tid wp2 rp2,
  exit_common regs mem sp tp code tid wp2 rp2 ->
  @StdioDefs.exit_common o23_reloc regs mem sp tp code tid wp2 rp2.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Exit ()) [] "p'0h01Hh14codeh23dsoh32f1h43f10h53f11h63f12h73f13h83f14h93f15h:3f16h;3f17h<3f18h=3f19h>2f2h?3f20h@3f21hA2f3hB2f4hC2f5hD2f6hE2f7hF2f8hG2f9hH3memhI4regshJ3rp2hK2sphL3tidhM2tphN1vhO3wp2i005ec_a0i019ec_atexiti027ec_compi036ec_dsoi046ec_erri055ec_fai065ec_fei075ec_fsi085ec_g1i095ec_g2i0:7ec_globi0;7ec_locki0<7ec_mtidi0=6ec_soki0>5ec_spi0?7ec_sphii0@7ec_sploi0A6ec_tidi0B5ec_tpi0C7ec_tphii0D7ec_tplop;1p;2p;8p;9p;3p;4p;Ng0000j10Tg000Uj13Tg001:j1FTg001Xj1OTg002;j2ZTg002gj1KTg003IR0j8XTg004Ll9UTg005Tj1<Tg0062j3ETg006Uj2DTg007Nj3>Tg007hj2@Tg008Rj2GTg008oj2BTg009Kj2?Tg00:1j11Tg00:Pj4TTg00;Pj2JTg00;lj2STg00<Gj1RTg00<gj1QTg00=Gj3PTg00=gj2NTg00>Ij2MTg00>cj2_Tg00?ej1^Tg00@gj4]Tg00AflN[Tg00Bnj4LTg00Cfj2\Tf0R1#0#0p=5%01#0#0#0p=4%31#0#0#0p=A%01#<p=C%11#1p=Y%11#1#1#1p=W%11#1#1#1#1#1#1#1p=V%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=9f6R2g00DnR3f5R4f4R5f3R6CLf2R7f1R8/\1'N3>p=8%01#3p==%31#3p=2%31#0p=6%01#0#3#0p=H%01#0#<,?8p=7%01#3#0#0p=:%31#0#0#3p=;%01#0#0#3p=IP3P6P7P8CL=>51p=`g00FUR9#0R:#3R;#FR<%0:R=#0R>#0#5R?#FR@#ORA'Z%F>R>#ORB#K\Ag00G:f7RCP2P4P5P6P7P8P1GXP0f8R0PCP2P4P5P6P7P8g00GXRDf9REP0PCP2P4P5P6P7M9UP1fM%<:g00HSR:5E<'DfKRF5>AfNRG%<==E<:'D=>AFfORH%0;R;#<=E<:'D=>AF%0?#4#4#4#4#4#4R?#0RF#<R:1@@G%A=#CR='G'B1@@H%5F#4#4#4#C'Bg00HoP3fQR3fPRF,@@RH/G=,?@g00IO#1R=#1#YRG#WR<#V#9#9#9#9#9#9#9#9CTg00In3>%3;#5#CR;/BH1@@3/B:g00JNR:/JF%<?,JF'S%RBRF#KR?fUfS,@@/G;,?@PGPFPG1?@3F8P?fV%=9#4#2#2#2#6#H,7@PGPFPG1?@:RGF8P?fW%59#:#;#2#=#A,7@P<PFP<%49#2#2#I#2#2#6,7@F8P?fX%59#:#;#2#=#6#6,7@P<PFP<%49#2#2#I#2#2#5,7@R3F8P?fYP3P<PFP<%69#H#6#6#A#2,7@F8P?fZR3%59#:#2#6#;#=#6,7@P=1?>:%QB5PB,NFD`P?f[RB%59#:#;#=#;#6,7@P<PFP<%39#2#;#2#2#5#A,7@F8P?f\R:%59#:#;#=#6#A,7@P<PFP<PGF8P?f^R?%59#:#2#=#2#6#:,7@P<PFP<P1F8X2A,MAg00JlR<f_RF/_1XN<'M%^Ff`R<%09#5#;#2#5#4#:#CPBP3C]PDfbfaP<PFP?f]P:PBfDRBfCR:fBR?fARFf@R<f?RDf>R3f=R9f<R@f;RGf:R>PEP0PCP2P4P5P6P7P8P1MN[W@W?W=W<W;W:W9W8W7W6W5W4WGWFWEWDWCWBWAW>W3PBP:P?PFP<PDP3P9P@PGP>PEP0PCP2P4P5P6P7P8P1OEn80000000010000001E110>10B10010@10?10=10D10C10A10<10;10610710510210810910310110:104W0XJAXOAWLX1AXMAXKAWHWIo"). Qed.

Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o23_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Exit ()) [] "p'0h01Hh14bufph25bufszh33canh42f1h53f10h63f11h73f12h83f13h93f14h:2f2h;2f3h<2f4h=2f5h>2f6h?2f7h@2f8hA2f9hB3memhC7pendinghD3rp1hE2wbhF2wpi006sp_bszi016sp_bufi028sp_bytesi035sp_fdi046sp_leni057sp_locki066sp_maxi078sp_rangei087sp_rendi097sp_rposi0:6sp_sspi0;8sp_wbasei0<7sp_wposi0=8sp_writep;1p;8p;9p;2p;3p;Gp;4g0000j10Tg001:j1CTg001Xj1ETg002gj1GTg00<Gj1RTg00L4R0j8QTg00M:l9NTg000Uj11Tg00:1j19Tg005Tj18Tg009Kj2:Tg008oj2>Tg00;Pj2PTg00;lj2DTg008Rj2MTg00NEj2?Tg00Nej1BTg007Nj3=Tg00OEj2LTg00=gj2ATg00Obj2KTg00PalGITg00Cfj2HTg00Qlj2OTg00Bnj4@Tf0R1#0#0p=2%11#0p=4%01#1p=;%11#1p=<%11#1#1#1p=3%01#0#0#8p=6%01#8p=Ff2R2f1R3/H1'Ap=7f6R4g00DnR5f5R6f4R7f3R8/O2':P3C@;=1p=5P5P8P2P3C@==71p=Jg00FUR5#0R9#0R:#0R;#0R<#2#CR=#ER>%C;#ER?#G[g00G:R@%R?RAf7RBP4P6P7P8P2P3P1GQP0f8R0PBP4P6P7P8P2P3g00GXRCf9RDP0PBP4P6P7P8P2M9NP1%GAREfFP=%05#2#4#;#<#2#;#3#6RF%1;#4#Fg00IO#9#9#9#9RG%15RH#1RI#1RJ#3#3#3#3#3#3#3#8,:=97AGF5PEfGRKP=PF%19RL#6%9G#9#9#9RMfE,:=97AMF5PEfHRNP=PF%6IPM1:=K97AMF5PEfIRIP=PF%1:#6PM%<5#3#4#4#4#;#;#6,:=97AMF5PEfJR:P=PF%1L#6PMA7AMKRKF5PEfKRLP=PF%2H#6PMPKF5PEfLP=PF%0JRJ#0#FPG%85,:=97AGF5PEfMRGP=PF%8;PMA7AMNF5PEfNRNP=PF%8<PMA7AMIF5%05#4#2#;#<#3#2#<#6/>N1PNG'D%05#4#2#4#4#2#2#2#2#6,>G'DfOR5,MN1??I#B5=@1??:#B%89%8J'L'>PEfRREfQRJ,:=1??L1AALDJfSRL/KGPCfTPLPEPJfPP5PNPGf=RGf<RNf;R5f:RJPDP0PBP4P6P7P8P2P3P1MGIW9W8W7W6W5WAW@W?W>W=W<W;W:W4PGPNP5PJPDP0PBP4P6P7P8P2P3P1O>n80000000010000001>110510<10;10=10110010310910810710410610210:W0WCX3>XD>X2>X1>XF@WEWBo"). Qed.

Lemma exit_pre_G : forall regs mem model code pending,
  exit_pre regs mem model code pending -> @StdioDefs.exit_pre o23_reloc regs mem model code pending.
Proof.
  (* LPS 727298f3: [exit_pre]'s flush case carries the channel reader; a plain proof in
     place of the recorded term, which built the case without it *)
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  exists sp, tp, tid, wp2, rp2.
  split; [exact (exit_common_G _ _ _ _ _ _ _ _ EC)|]. split; [exact Hh|]. split; [exact Hlazy|].
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrd)].
  - left. split; [exact E|]. exists wp1, rp1. exact F1.
  - right. exists wb, wp, bufp, bufsz, rp1, can.
    split; [exact (stdout_pending_G _ _ _ _ _ _ _ _ SP)|]. split; [exact Hfd | exact Hrd].
Qed.


(* [comment removed for export] *)
Definition FOE23 {fx : FPState} : @StdioDefs.funcs_on_exit_spec o23_reloc fx :=
  @FuncsOnExit.funcs_on_exit fx o23_reloc o23_code o23_sites o23_data o23_rw o23_r23code.
Definition CXF23 : @ExitBase.cxa_finalize_ret o23_reloc := @R23Code.F23_13198 o23_reloc o23_data o23_r23code.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x1138f8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0xfa03c : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Exit ()) ["VP1"] "h01Hh12b1h22b2h31nh42ECh52F1h62Hhh75Hlazyh83RLTh91bh:4codeh;3memh<5modelh=4regsh>3rp1h?3rp2h@2sphA3tidhB2tphC3wp1hD3wp2p;1p;2p;8p;4p;3p;9p;5p;6p;Gg0000j12Tg000Uj14Tg001:j18Tg001Xj15Tg002;j2STg002gj1>Tg003Ij8HTg005Tj17Tg00@gj4ETg00UAj1CTg00SGj1BTg007Nj33Tg00Sij2UTg00<Gj1TTg00\fj1RTg00<gj1MTg00aSj1LTg00W8l9KTg00bIj1ITg00V8j2GTg00cHj2FTg00dBj1=Tg00e>j5<Tg00f7j2?Tg009Kj2:Tg00flj3;Tg00gQj19Tg00hDj2@Tg00i?j3ATg007hj26Tg00j>j3DTg0062j3NTg00jbj2OTg00k<j6PTg00kXlGQTf0R0#2#2p=0%40#4p=1P0g00GXR1g00l\g00mZg00nZg00oWf1R2g010Sf2R3f3R4f4R5f5R6f6R7f7R8f8R9f9R:f:R;f;R<f<R=f=R>f>R?f?R@f@RAMGQp=Jg00FURB#2RC#4RD#8%0CRC#2#0RE#8RF#5RG'S%8C#5#>\Gg00_eg00G:RCP;P:P8P7P6P5P4P3GHP;%2B#0#4#0#4#1#2#0#4#1#1#2#0#7P3P2CE%>G%C;%BG331UGGRH#T%R<%MH33p,2fxRH%LHP?P>P=P<P;P:P9P8P7P6P5P?P>P<P;P:P9P8P7P4M9KP3P2P0MAJ%I1R7PHP?%0E#1,G1%2D#1#2#0#0#0#0#0#7'FP>%=7D</?=%4B#1#1#1#7,:FR79;F:%9='@3Ag011IR:%50R>%52RDg00;l%53?3201643164253CR1[1632163053C%54?332[RE%55?343\1AD320P0n2001000000120000000W2W1W3PE^2D^1>^3:P0PF%1B#1#2#4#2#0#0#0#1#1#0#7RB,:FR:g00HS9NFBR>1OCB16F:16F>53CdO4b0A3G:>PGP:g00DnR:PHfAP0PA%=:D</?@A;F=7%9@'@3AX9GP2P>P0EPb0b8W7W6W5W4X>GXCGX?GXDGWAX:GXBGX@GW<W;W=o"). Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
  (* this image's relocation, for the instance arguments of [Exit.ref_exit_flush] *)
  #[local] Existing Instances o23_reloc o23_code o23_sites o23_data o23_rw.
Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes RSEGS (mkCfg (mkst regs (0xfa03c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: the flush's write needs the channel reader ([Exit.ref_exit_flush]); a plain
     proof in place of the recorded term, which called it without *)
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrd.
  epose proof (Exit.ref_exit_flush FOE23) as RLT.
  try specialize (RLT CXF23).
  specialize (RLT regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending
                (exit_common_G _ _ _ _ _ _ _ _ EC) (stdout_pending_G _ _ _ _ _ _ _ _ SP) Hh Hlazy Hfd Hrd).
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z. exact RLT.
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
ltac2:(KReplay.run1 (kr_t_O23Exit ()) ["VP3"] "g014bo"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0xfa03c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: [exit_pre]'s flush case carries the channel reader, which [ref_exit_flush]
     takes; a plain proof in place of the recorded term *)
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrd)].
  - subst pending. cbn [W map].
    eapply rz_conseq; [| apply t_emit_nil_exit].
    exact (ref_exit_clean regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy).
  - exact (ref_exit_flush regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrd).
Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xfa03c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Exit ()) ["VP5"] "h03PREh13RLTh24codeh33memh45modelh57pendingh64regsp;1p;2p;5p;6p;3p;>g0000j11Tg000Uj13Tg001:j14Tg001Xj16Tg002;j2JTg002gj1>Tg00<Gj1=Tg00RIj5;Tg00aSj1:Tg015gj67Tg00bIj19Tg00V8j2KTg005Tj15Tg00cHj2ITg00dBj1HTg00e>j5BTg00f7j2?Tg011gj2@Tg009Kj2ATg00flj3<Tg00gQj1CTg00hDj2DTg012cj2ETg00i?j3FTg017`l>GTf0R0#1#1p=0f7g00GXR1g00l\g00mZg00nZg00oWf6g010Sf5R2f4R3f3R4f2R5f1R6P0M>Gp=8%30#3p=2g00FUR7#1R8#3R9#4%08R8#1#0R:#4R;#6R<'J%48#6R8#>\<g00_e%=8P3P4P5P6P0D;p,2fxR8%:8P2P3P4P5P6P2P3P4P5P6P0E7G8%91R=P8P2%0:#2,K1%19#2#1#0#0#0#0#0#5'IP3%H=DB/?4%57/@6%37#2#2#2#5,A;9<;5%C4'D'E3FP0b1W0W5X2<W4W3W6o"). Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
