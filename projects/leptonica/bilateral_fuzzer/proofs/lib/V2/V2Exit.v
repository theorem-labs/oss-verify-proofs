(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev's channel-reader flag; recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require ExitBase StdioDefs Exit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2StdioDefs V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require R23Code FuncsOnExit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2R23Code.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Exit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib2V2;V2StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib2V2;V2StdioDefs<atexit_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2ExitBase:file_cleanC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs;exit_common01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib6Common4Musl9StdioDefs;foe_variant00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2V2;V2StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2V2;V2StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl9StdioDefs>stdout_pending01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2V2;V2StdioDefs8exit_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Exit=exit_common_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib2V26V2Exit@stdout_pending_GC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib6Common4Musl9StdioDefs8exit_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8ExitBase:file_cleanC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib2V26V2Exit5FOE23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_cleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2RelocCode7v2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2<V2RelocSites8v2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg7v2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2RelocMusl5v2_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Exit5CXF23C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib6Common9CliDriver4Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit>ref_exit_flushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit?t_emit_nil_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Exit:exit_pre_GC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit8ref_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl4Exit:ref_exit_ZC1?~~~~~~~~~~~~~~~".
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
  m_channel_reader model = true ->
  realizes RSEGS (mkCfg (mkst regs (0x3bef8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: [Exit.ref_exit_flush] takes the channel-reader premise; the recorded replay
     did not pass it *)
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hcr.
  pose proof (@Exit.ref_exit_flush fx v2_reloc v2_code v2_sites v2_data v2_rw (FOE23 (fx := fx)) CXF23
                regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending
                (exit_common_G regs mem sp tp code tid wp2 rp2 EC)
                (stdout_pending_G mem wb wp bufp bufsz rp1 can pending SP) Hh Hlazy Hfd Hcr) as R.
  assert (E : (0x3bef8 : word) = Z_to_bv 64 0x3bef8)
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
ltac2:(KReplay.run1 (kr_t_V2Exit ()) ["VP3"] "g013ho"). Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x3bef8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (* LPS 727298f3: the plain proof of the generic [Exit.ref_exit], over this file's lemmas *)
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrd)].
  - subst pending. cbn [W map].
    eapply rz_conseq; [| apply t_emit_nil_exit].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.   (* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x3bef8) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  assert (E : Z_to_bv 64 0x3bef8 = (0x3bef8 : word))
    by (apply (proj2 (stdpp.bitvector.definitions.bv_eq _ _ _)); reflexivity).
  rewrite E. exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
