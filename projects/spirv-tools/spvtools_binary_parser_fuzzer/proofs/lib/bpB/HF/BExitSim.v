(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's mmap base; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSimInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BExitSim () := "C47Corelib7Classes?RelationClasses;reflexivityC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoc69OSSVerify5KrLib3bpB2HF8BExitSim:is_exit_noC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Exit9exit_specC47Corelib4Init5Logic3iffC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tableC47Corelib7Classes?RelationClasses=iff_ReflexiveC45stdpp9bitvector;definitions7Z_to_bvI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedc69OSSVerify5KrLib3bpB2HF8BExitSimAsyscall_spec_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic5proj1C46Stdlib5Lists4List9app_nil_lK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02c69OSSVerify5KrLib3bpB2HF8BExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF8BExitSimDexit_dispatch_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedc69OSSVerify5KrLib3bpB2HF8BExitSimAin_arg0_sys_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedc69OSSVerify5KrLib3bpB2HF8BExitSimJexit_dispatch_no_unmodeledC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "p'0h01Eh11Hh21ih31mh41oh51zi001ai011xp;1p;2p;3p;4p;6p-1g0000R0p4p710p9p1000^p4p70R1p1001Np4p710R2p8P1p1001jp4p710R3p8P1p1002Hp4p7210R4p8P1g002eR1p4p710R5p8p1003Cp4p710R6P5p8p1003`p4p70R7P2p8P7P6p8P7P3p8P7P4p8P7P5p8P7p1004Np4p710p8p1004kp4p7210R7P2p8P7P3p8P7P4p8P7P5p8p1005Wp4p70R7P2p8P7P3p8P7P4p8P7P5p8g006Mj1ATg007Ej13Tg008<j1;Tg009;j10Tg009`j1@Tg00:>j27Tg00:hj11Tg00;Mj19Tg00;kj32Tg00<Ej38Tg00=@j24Tg00>5j46Tg00?7R5j25Tg00?Pj2?Tg00@Pj4>Tg00AMj4=TP0j4<TP1j6:Tg00BEg00CBg00D8R1#Af2R0#3#;g00E6g00EPR7g00En#0R4#0#0#0#0#0#@R3f3R2#3'7R6%14#1#1R4#0#1#9R832%14#0#9R49276f4R6?820g00FSR9,46P6P2P0C6'5f0R0%36,73R:=278P7P8g00G2g00GTp-0R8g00HS/?0P0f7f6R;f5R<C>P1P;P<P6C=n1011010002101000014;9P;P<P6C6'5X57R;P8P5g00IW14<9P<P6P2C6R9C<R5%3<,73R3P0E:A8<62/59R9eW0P0O1A27:4P7P4P;P5P3P0E:P9eW0P0O1n200100000021000010000W1W4W3W2o"). Qed.

Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "h04evs2h14evs1h22m1h33Hnoh41ih51mh61xp;1p;2p;6p;3p;4g007Ej1NTg008<j1MTg009;j16Tg009`j1@Tg00JGj2HTg00Jmj1ETg00KPj1DTg00L0j2=Tg00LPj19Tg00M0j6KTg00=@j27Tg00:hj14Tg00;Mj1ITg00Mnj3:Tg00NSj28Tg00<Ej3GTg00>5j4FTg00OMj4LTg006Mj1CTg00PSj4>Tg004Nj3?Tg00;kj35Tg00QKj23Tg00Qej2BTg00R@j2<Tg00RZj4ATg00S5j4;Tg00SOj4JTg00D8R0f2R1f1R2f0R3C>p=0g00SjR4g00TJR5P2P3C>p=2f3R6?512/B3p=1g00BEg00CBR7%N2#Mg00EnR8#6#6#6R9#6#6#6#@R:g00Tj'H%E:R;%@9#E#D'=#91=;;#9R9P9g00UH#9g00V@,=;#9EKR;g00FSR9,71R<%48#4#4#4#4#4#4#I,H:R85::/82R=g00V_R>#9R?30R@9G121769RAP6P1A::A8/81RA=0;?RBCF[P<P1P2P@CFR<AG61B[P1P2P@P3CLP4%D>RC%C4RDP4P6P1P2C>f6/79=::8f5RE'8RF/2?%C0R0A0;F3A0;1?RFA?>2395C?RGC1C1X0C,3CX1C'3X27,37X64RHP5P7PD121217E9=::8f4RE'8R1/2?P0A0;13PFPGC1C1X0C,3CX1C,3CX27P=PCPD17E9=::8/86R6/22126?P0A0;63A0;6?PGC1C1X0C,3CX1CP?PCPD12A?RGPGP0A0;A3PBA?>?395C?C1C1X0CP?12=?R==5D=A50@@R3A?>??R>95C?R?'B1<D=P3P?1<0@1<C>CACAC;C;C;C;134HeP<eCJW3W5W4o"). Qed.

Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "p'0h04evs2h12H3h21eh31Hh42H0h52H1h62H2h74evs1h82H4h91lh:1mi001mh;2m1h<2H5h=5Hspech>3evsi013evsh?1oi021oh@1xi031xhA2x2hB2H6hC3HnohD3effhE1ihF2m'hG1shH1uhI2x0hJ2x1p;1p;3p;4p;2p;6g00KPj1WTg007Ej1`Tg008<j1[Tg00<Ej3NTg00>5j4STg00OMj4ZTg00WUj4YTg006MR0j1RTg009;j1@Tg009`j1OTg00:hj1>Tg00;Mj1^Tg00JGj2VTg00LPj1BTg00Jmj1TTg00L0j2KTg00M0j6\Tg00;kR1j30Tg00QKR2j24Tg002Hj6ATg00QeR3j27Tg00R@j2CTg00RZj4XTg00X0j2_Tg002ej68Tg00PSj4=Tg00=@j2ETg00Mnj3ITg00NSj2MTg004Nj3]Tg00D8R4f2R5f1R6f0R7C=p=1g00FSR8,E7p=Ug00SjR9P5P6P7C=p=5P9g00TJR:f4R;f3R</E8;I5/M6P7C=p=9g00V_R=?]67p=3f6R>f5R?;0;A0<56/77'7p=;1E58=I<6/M7p=2A04>?g00CBR@?0;<A0567'7'7p=:P9P:P6P7C=p=?P9P<P5P6C==0;7p=HP4P;P<P5C==0?6/77p=QP4P<P5P6C==0;7p=GA0@67p=6A0467p=DA0567,7<,7;p=<1767,75p=PA097:p=F1E68=I57p=J1M6790@5p=Lg00BE%W=R8%`;#[A1<569N?;A1;<5RA9N>?f7RB#UPBP>A1?;<RCCS[%U>P>P?PACSRDANB>C[P>P?PAP6CZP7CYPDP2P9%R9RDA5<56RAg00EnRC#@#@#@RE#@#@#@#ORFf;RG%>C#>#>#>#>#>#>#^,VFRCf:RH%B=RID9%R4RJf9RKf8RL;17g00Tj,VF%TFRM%OE#T#W'K#B1KMM#BREPEg00UH#Bg00V@,KM#BE\RM?15IRE1367RN908BF;X08,48X78,48X;@,4@X@9P>PMP?PFPLPCPBC2P8P;PIF:P7PDPAPFf=RAPCf<ROPID9PJA1GH7PEA08KNF;X08,48X78,48X;@,4@P2P@PDA5;56PFf>RPPCPAPID9PJA1OG7PEA08HNF;X08,48X78,48X;@PHPMPKPFPOPCPGC2P8PLPIF:P7PDA5>56PFf@RQPCf?RRC2RS/?IPJA1PA7PEA08ONF;X08,48X78,48P2P8PDA5B<6PFfAREPCPQPID9PJA1RP7A1M<IA08ANF;X08,48X78PPPMPAPSP8POPIF:P7PDA5K?6PFfCRSPCfBRPPID9PJA1EQ7A1M?IA08RNF;X08,48P2P8PDA5H>5PFfDR2PCPSC2RN/?IPJA1PE7A1M>I1357908QF;X08PPPMPEPNP8PQPIF:P7PDA5OL;PFfFRNPCfER>PID9PJA12S7A1MLI13;7908PF;P3PDPAPKP?PFfGR<PCPNPID9DHPJP>P2P6A1MKI13?6908SEQPNPMP>PFfHRTPCP<C2P8P2PIF:P7PDPRPGPBPFfIRUPCPTPID9DHPJPTP<P;A1MOI13L;908NEQP3PJPUPTP?A1MAIDG13K?908<fJR<PMPUPFfLR?PCfKR3C2P8PTPIF:P7PJP3P<PBA1MRIDG13OL908<P1PJfMRL?1?KRKA1MSIRR90J6fPRBPMfORNPFfRR;PCfQRVC2P8fNRWPIF:[P6A1MEIRE90JKPJPWPLPHA1MPIRHDGPJP8P0P4P8P7P7POn10110200023010310010100X2JA1NWGPRP7EAA08GIPJP@P0P4P@P7P6PBn10110200023010310010100X2JA1BNOA1M2IP6EA16N2PJP4P0P4P4P7P5P;n10110200023010310010100X2JA1VBAA1M>IP5EA1DVM1D;MP7fSR>/DMP4PMfTRA/6UROA08PIRPP5PMfVRRPFfYRKPCfXC2P8fURXPIF:[[XG416>TP7POP@P<A08SIRS1DMMROPFfZRYPCPKC2RK,66P8PRPID<[X:@P7PSP8PIPOPFf[RSPCPYC2RY,6LRZP8fWR[PID<X98P813T2A087IR\9POZX>8P8PIPOPZP813U7PID<XA8P1PDA5B?TRTPFf\R1PCPSC2RS/?IRZ90D6POPFf]R]PCP1C2R1,6NR^P8133IPID<[PQ1?KIRK90DTPDPVPLPU1?YIRYDHPDP8P0P9P8P7P7P3n10110200023010310010100X2DA5;W<PZP7EAA08<IPDP@P0P9P@P7P6PBn10110200023010310010100X2DA5>N31?1IP6EAP^PDP9P0P9P9P7P5PXn10110200023010310010100X2DA5AB?PFf^PCP]PID9P5EA%FA%FXP7%FRP9P:fbR:=JFCfaR55LAR]A08VIR?POfdR0=JFCfcR^5LRP813;IPID<[[XH9AJF5Cf`5L>P7P]P@PFP^PCP:C2A08;IR;POPFfeR:PCP0C2R0,66P813>IPID<[X:@P7P;P8PIPOPFffPCP:C2R:/6:R:P8137IPID<X98P8PIAPO:\X98PO1600R:A08IIR\'71C4MP:P\1C@01C8ICXCX13II1_=IE8P>P7E8b8X1?PXP7E8b1W6P[P7E8b6W5P7O1b5P7O1b5P7O1b5W4P7O1W4n2002102000010101A0D7YPO16WSP813<IPID<[X?DPKO1P71CDYO1b4P2P6E8PRPGE8P2P7E8bBX<PPXP7E8b<W8PAP7E8b8W1P7O1b1P7O1b1P7O1b1W6P7O1W6n2002102000010101A0J7HPNPMPWPFPVPCPBC2P8PLPIF:[X?JPEO1P71CJHO1b6W5W4P6P7O2n2001000000121000000W4W3P6P7O2n2001000000121000000W3XA8P6P7O2n2001000000121103000W3XJ8P6P7O2n2001000000121103000W3XI@P6P7O2n2001000000121103000W3X@9P6P7O2n2001000000121103000b=W=WCW>XF@XD4X:@WEo"). Qed.

Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "p'0h01Hh14evs1h21eh32m1h42H0h52H2h61xi001xh72H1h82H3h92H4h:5Hspech;1mi011mh<2x0h=2H5h>3Hnoh?1ih@1lhA1oi021ohB1uhC2x1i033evsp;1p;3p;4p;2p;6p;7g007Ej1YTg008<j1XTg00XNj1GTg00<Ej3?Tg00>5j4JTg00OMj4UTg00WUj4STg006MR0j1FTg009;j17Tg009`j1DTg00:hj16Tg00;Mj1MTg00JGj2KTg00LPj1:Tg00KPj1ITg00Jmj1HTg00L0j2CTg00M0j6TTg00;kR1j30Tg00QKR2j21Tg001Nj6ETg00YFj2RTg002Hj6ATg002ej7Oj6BTg00R@j2NTg00Yej1QTg00=@j2>Tg00Mnj3<Tg00NSj2;Tg00PSj48Tg00QeR3j2WTf0R4g00FSR5'>p=Lf3R6f2R7f1R83</;4p=Vg00SjR9g00TJR:P8P4C89067p==P9P7P8P4C8p=2g00D8R;P7P8P4C8p=4f7R<f6R=P9P:f5R>f4R?/>5;<6/;7P8C830/W4p=51>75=<68/;4p=3P9P:1>65=<?7/;8P4C8p=9P9P:P8P4C8p=PA094:p=@g00BEg00CBR5%Y8#X%G;R@9?78RAA?67@%L?RBP?P6P@CJ[%L6P6P7P@CJRCA??6@[P6P7P@P8CUP4CSPCg00E6%F9RC%G9RDg00EnRE#7#7#7RF#7#7#7#DRGPB%6E#6#6#6#6#6#6#M,KGREP6CVg00V_RB#:RHC=%IBRBPCA2784RIPGP<PEP=PH%F;RJg00Tj,KG%HGRK%DF#H#I'C#:1CKK#:RFPFg00UH#:g00V@,CK#:ETRK?48H70@RFG5X1B'1X35,15X69,19g00Z>RLP4PCPDPGP>PEP?C3PHC=PCPDP0P9p-0RDP4PLg00Z[RMn10110200023010010110300X2Cg00[7RNPGP=PEP>PHD9P4EEPL1RL4ROb4W0P4O1PCPIPGf8RPPEP<PHPFG5X1B,1BX35,15X69,19P2P9PCPIPGf9RQPEPPPHPFG5X1B,1BX35,15X69PLP4PCPIPGf;RIPEf:RRPHPFG5X1B,1BX35,15P2P5PCA2684PGf<RSPEPIPHPFG5X1B,1BX35PLP4PCA2>84PGf>RTPEf=RUPHPFG5X1B,1BP2PBPCA2=74PGf?R2PEPTPHA4K7H90J@G5X1BPLP4PCA2P?4PGfARFPEf@RVPHA4K?H90J@G5P3PCA2Q>8PGfBR3PEPFC3PHC=A4K>H90J@PLP4PCA2I<6PGfDR?PEfCRWC3PHC=A4KPH90J@P1PCA2UQ>R>PGfHR1PEfGRXPHD9RY90C8PL[P8PGfFRZPEfEPHD9R[90C>A2TR=PGPXPEPZPHD9RZ50CPCPBP0P9PBP4P4PPn10110200023010010110300X2CA22I<PYP4EAA0B<HPCP5P0P9P5P4P8PUn10110200023010010110300X2CA2VSPPGfIRPPEP1C3R1/PHP8EAA05S1PCP9P0P9P9P4P7P3n10110200023010010110300X2CA2FUQPGfJPEPPPHD9P7EA%@F%@3P4%@WP9P:PGfNR:PEfMRWC3905FRFA0BTHRTPL[[XB9PGPWPEfLC3905VP4PFP5PGfOPEP:C3A0B2HR2PL[X;5P4P2PBPHPLX@BP5PGfQR2PEfPC3R:A4K4H90J@PL]4X<5A4K:H90J@PJP@P0P;PDP4PLPMn10110200023010010110300X2JPNPGfRPEP2C3=4KHP4EEPLPOb0W4P?P6PIFOPVP4EBb=X9TP3P4EBb9W8P?P4EBb8W5P4O1b5P4O1b5P4O1b5W7P4O1W7n2002102000000101A0C4ZPL[XACP[O1P41NCZO1b7W4W0P8P4O2n2001000000121000000W0XCBP8P4O2n2001000000121100000W0X<5P8P4O2n2001000000121100000W0X69P8P4O2n2001000000121100000W0P4O1n200100000021000011000b:W:%QAeW>W;W?o"). Qed.

Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "h02msh14segsh22x8p;1p;2g00KPj15Tg009;j10Tg009`j12Tg00Jmj11Tg00[Sj24Tg00R@j23Tg00\Q#5g00]Pg00En#0#0#0#0#0#0#2#1R0f1g00FS'4,30W2W0W1o"). Qed.

Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof.
ltac2:(KReplay.run1 (kr_t_BExitSim ()) [] "h02msh14segsh22x8p;1p;2g00KPj14Tg009;j10Tg009`j12Tg00Jmj11Tg00R@j23Tg00\Q#4g00]Pg00En#0#0#0#0#0#0#2#1R0f0,30W2W0W1o"). Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* sstep_instr *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* sstep_instr_fault *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_instr_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_syscall *) congruence.
  - (* sstep_syscall_materialization_fault *) congruence.
  - (* sstep_exit *) congruence.
  - (* sstep_killed *) congruence.
  - (* sstep_syscall_unmodeled *) congruence.
Qed.

Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall : model' halted, contradiction with m_halted model' = None *)
    (* the accessors do not reduce through a setter on their own,
       so normalise the hypotheses before matching on their shape *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_syscall_materialization_fault: same pre-materialization model *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_exit *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* sstep_killed: the exit arm's post-model is [State.with_halted]'s,
       whose [State.m_killed] is [None] by construction *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

End WithSegs.

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp mbase : word) (init_rnd : EntryDraw) (inp : ProcInput)
    (argc : nat) (base : word -> option byte) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fregs      := ms_fregs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fcsr       := ms_fcsr (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) |}.

