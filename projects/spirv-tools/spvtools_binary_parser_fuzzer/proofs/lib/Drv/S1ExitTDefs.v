(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec3 SymExec3Sound SymRun3 SymDrive3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA S1ExitKn S1ExitDefs S1KnCut3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1ExitTDefs () := "K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib3Drv;S1ExitTDefs8SW_ENTRYC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1ExitDefs:EXIT_ECALLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N02K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv8S1KnCut3:log_out3_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3c1aC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymRun3:kn_vars_ltC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3k1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymRun3:sr_vars_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs9kn_tp2_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib3Drv;S1ExitTDefs4kn2aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs9sr_tp2_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs4sr2aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3c1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3k1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs4kn2bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs4sr2bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3c1cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs3k1cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs4kn2cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv;S1ExitTDefs4sr2cC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope. Import SX2. Import SXA.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition SW_ENTRY : Z := 0xd537c.
Definition SW_RET : Z := 0xd500c.

Definition kn_tp_extra (w : Z) : list kentry :=
  [ KImg 0xee1b0 0xee390;
    KWord (SA (ELit 0) 0xee390) 4 (ELit 5); KWord (SA (ELit 0) 0xee398) 8 (ELit 0); KWord (SA (ELit 0) 0xee3a0) 8 (ELit 0);
    KWord (SA (ELit 0) 0xee3b0) 8 (ELit 0x1216a8); KWord (SA (ELit 0) 0xee3b8) 8 (ELit w);
    KWord (SA (ELit 0) 0xee3c8) 8 (ELit 0x1212a8); KWord (SA (ELit 0) 0xee3d8) 8 (ELit 0xd537c);
    KWord (SA (ELit 0) 0xee418) 4 (ELit 0xffffffff); KWord (SA (ELit 0) 0xee420) 4 (ELit 0xffffffff);
    KWord (SA (ELit 0) 0x120928) 8 (EVar 35);
    KImg 0xee394 0xee398; KImg 0xee3a8 0xee3b0; KImg 0xee3c0 0xee3c8; KImg 0xee3d0 0xee3d8;
    KImg 0xee3e0 0xee418; KImg 0xee41c 0xee420; KImg 0xee424 0xee480 ].
Definition kn_exit_tp (w : Z) : list kentry := kn_exit_common0 ++ kn_cxx_exit_t ++ kn_tp_extra w.

Definition exit_clear_tp : list (Z * Z) := exit_clear_t0.

Definition run_tp1 (w : Z) := sym_execA SEGS 3000 true [SW_ENTRY] (SCR [] [] []) (SS EXIT sr_exit [] (kn_exit_tp w) 40) [].
Definition carry_tp1 (w : Z) := carry (s_log (fst (fst (run_tp1 w)))) (kn_exit_tp w) [].

Definition ABS_TP : list (Z * Z) := [(0xee3b0, 0xee3c0); (0xee3c8, 0xee3d0)]%Z.
Definition KEPT_SW : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.
Definition kn_tp2_of (kn1 : list kentry) : list kentry :=
  kn_cut3 0 (-352) (-240) ABS_TP 0x122000 kn1
   ++ [KWord (SA (ELit 0) 0xee3b0) 8 (ELit 0x1216a8); KWord (SA (ELit 0) 0xee3b8) 8 (ELit 0x1212a8);
       KWord (SA (ELit 0) 0xee3c8) 8 (ELit 0x1212a8)].
Definition sr_tp2_of (sr1 : list expr) : list expr := sr_after_call_j sr1 KEPT_SW 40.
Definition run_tp2 (sr2 : list expr) (kn2 : list kentry) := sym_execA SEGS 3000 true [] (SCR [] [] []) (SS SW_RET sr2 [] kn2 72) [].

Definition c1a := Eval vm_compute in run_tp1 0x1212aa.
Definition c1b := Eval vm_compute in run_tp1 0x1212ac.
Definition c1c := Eval vm_compute in run_tp1 0x1212ae.
Definition k1a := Eval vm_compute in carry_tp1 0x1212aa.
Definition k1b := Eval vm_compute in carry_tp1 0x1212ac.
Definition k1c := Eval vm_compute in carry_tp1 0x1212ae.
Definition sr2a := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1a))).
Definition sr2b := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1b))).
Definition sr2c := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1c))).
Definition kn2a := Eval vm_compute in kn_tp2_of (fst (fst k1a)).
Definition kn2b := Eval vm_compute in kn_tp2_of (fst (fst k1b)).
Definition kn2c := Eval vm_compute in kn_tp2_of (fst (fst k1c)).
Definition c2a := Eval vm_compute in run_tp2 sr2a kn2a.
Definition c2b := Eval vm_compute in run_tp2 sr2b kn2b.
Definition c2c := Eval vm_compute in run_tp2 sr2c kn2c.

Lemma c1a_pc : s_pc (fst (fst c1a)) = SW_ENTRY.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg000h'0o"). Qed.
Lemma c1a_scs : snd (fst c1a) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma k1a_scs : snd (fst k1a) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2a_pc : s_pc (fst (fst c2a)) = EXIT_ECALL.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg003a'0o"). Qed.
Lemma c2a_scs : snd (fst c2a) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2a_a7 : nth 17 (s_regs (fst (fst c2a))) (ELit 0) = ELit 94.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j11Tg005Dj10Tg005ij13Tg006Gj12Tg0000j24Tg007?g0087#1#0#0#0#0#1#3#2'4o"). Qed.
Lemma c2a_a0 : nth 10 (s_regs (fst (fst c2a))) (ELit 0) = EVar 2.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j13Tg008\j12Tg009:j10Tg0000j21Tg007?g0087#3#2#0'1o"). Qed.
Lemma c1a_log : log_out3_b 0 0x1212a8 0x1216a8 (s_log (fst (fst c1a))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3p;4g0000j2<Tg005ij16Tg001ej1;Tg00:2j2:Tg00:Rj34Tg00:oj19Tg00;fj48Tg00<bj37Tg004_j12Tg005Dj15Tf0R0#2#2p=1%50#2p=0%20#5p=3g00=<R0g00=\R1'<g00><g0087R2#1#0#1#3#1#0#0#0#0#1#6%12#0#1#3#3#0#0#0#0#1#6g00>ZR2g002e#;R31:23g00?Wg00@R3434#9C8=701do"). Qed.
Lemma k1a_vars : kn_vars_lt 40 (fst (fst k1a)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j28Tg004_j10Tg005Dj14Tg008\j13Tg001ej11Tg00:2j27Tg00:Rj32Tg00AJj25Tg00<bj36Tg00=<R0g00=\R1'8g0087#0#4#0#0#0#3g00BA#1R2g002e#1R31723%10g00C;3232'5=601do"). Qed.
Lemma c1a_vars : sr_vars_lt 40 (s_regs (fst (fst c1a))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j29Tg004_j10Tg005Dj13Tg008\j12Tg001ej18Tg00:2j27Tg00:Rj31Tg00D3j14Tg00Dkj25Tg00<bj36Tg00=<R0g00=\R1'9g0087#0#3#0#0#0#2g00>ZR2g002e#8R31723g00?Wg00@R3131#4'5=601do"). Qed.
Lemma kn2a_eq : kn2a = kn_tp2_of (fst (fst k1a)).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1`Tg009:j1jTg005Dj11Tg004_j10Tg00Ebj1OTg006Gj1=Tg00FAj3dTg005ij1HTg00G9j3cTg00H3j2mTg00Hmj2bTg00Igj2NTg002Ej1uTg0000j2sTg00:2j2rTg00:Rj3fTg00J`j1qTg00<bj3pTg00K^j1_Tg008\j1oTg00L<j3XTg00M6j3ITg00MVj2[Tf0R0#0#0#0p=W%H0#=p=Z%00#0p=U%00#_p=e%10#1#1#1p=2%10#1#0#0p=F%00#0#1#1p=E%00#0#0#Hp=4%10#0#0#0p=>%00#0#1#0#0p=]%10#0#0#1p=3%10#0#1#1p=D%00#0#H#=p=5%o0#jp=J%00#1#0#0p=;%00#1#0#0#0#0#0#0p=P%10#1#1#0p=A%00#0#0#0p=B%10#1#0#1p=<%00#1#1#0p=L%00#0#0#1p=:%00#1#0#1p=^%00#0#1#0#0#0#0#0p=V%00#0#1#0p=@%10#0p=n%00#0#0#0#0#0#0#0p=Qf1R1%_0'Np=l%00#1p=k%10#1p=if3R2f2R3'N?X10p=h%10#1#0#1#1#1#0#0p=K%10#1#0#1#1#1p=T%00#1#1#1p=C%10#1#0p=a%00#0#1p=v%10#0#1#0p=6%10#1#1#1#1#1#0p=8%10#1#1p=S%10#1#1#0#1#0#0#0p=Rg00BAR4f4R5/N2?X31;I0p=?%12#0#0#0#H,N5?X31=I40p=9%03#H/[1=I40p=M%02#0#0#0#H,N5?X31=I40p=G1[31=I40p=t%H2,N5?X31=I40p=YAI4109I43p=\1[521[31=I405I4p=g%_2,N5?X31=I40p=7%`4R0g00><#jR3g0087R1#1R5#1R2#1R6#WR7#0g00NP#OR8#O#O#OR9#O#O#O#OR:%Z5P3%02R2#1R;#WP:g00NoR<%01R=#1R>#1R?#1R@#U#eRA#=7d3P3%U2R2#0RB#0P:%21#F#2#E#4RC#=RDP3%05R5#1RE#>P:%]1#3#F#D#5P3%05R5#>P:%05RF#0RG#0RH#e#=9d<3P3PAP:%JFP3%0?RA#UR<#0P:%J@P3%0>R@#1RI#WP:%]1#>#;#>#5RJP3%U@R@#0RK#0P:%01#P#A#B#4RL#=P3%0=RM#1RN#>P:%11#2#3#<#L#5ROP3%WNRN#0P:%21#<#E#<#4RP#=RQP3%0MRR#1RS#WP:%01#P#E#:#5P3P7P8%H1R7#=P3PBP:PQP3%WEP:POP3PHP:POP3P<P:%]1#>#;#2#5P3PKP:%U1#>#:#F#:#5P3PNP:%11#E#2#D#;#5g00O[#=RN%01#P#A#:#4RKP9PNP3P2P:%JAP3PGP:%JIP3P@P:%J5P3%0RR5#0R@P:%J=P3PFP:%11#P#^#>#5PN%V1#3#@P9%J1RFP3P5P:%J?P3PRP:%JM%0@#BR@#0#BRM#n#B#Q#4%0MRM#B#Q#Q#Q#45c3%H5R5,m31l3@%Z@'b%F;#Q#4R;,NN%11#k#B#Q#5'bPN%Q1#L#:P9PF%i6#2#2#2#2R6#H9cF7PN%01#Q#<#:#4P:%U1#>#@#L#B#5ChRF%HMP;%K1#:#<#4%K1#E#L#4R;%T1#@#C#;%a1#A#;#A#3#HPLPK%01#P#A#E#4RK%01#P#A#;#4RL%v1#B#C#;#;%]1#:#<#@#4PN%V1#3#;#DP8PNPNPCP:%11#6#6#F#6#5RCPN%81#C#<P:%K1#C#@#4RM#=R7PN%81#C#AP:%21#A#;#@#4R@#=R3PN%81#C#AP:%11#2#3#<#3#5PN%21#F#2#2#4RRP:PCPN%S1#R#EP:%=;RCPN%S1#R#;P:P3PN%S1#R#;P:%11#2#3#<#D#5PN%21#<#B#D#4R3P:%11#6#D#:#L#5R?PN%S1#R#3P:P7PN%S1#R#6P:%21#A#C#;#4R7#=R=PN%S1#R#6P:%11#2#3#<#2#5PN%21#<#:#C#4RIP:P?PN%S1#R#2P:PCPN%81#3#BP:P=PN%81#3#BP:%11#2#3#A#:#5PNPPP:%11#6#3#D#@#5RPPN%81#3#2#3P8%=5R5PN%81#6#:P9PNPN%81#6#:P:PDPN%81#6#CP:PNPN%81#6#>P:%11#6#3#2#6#5RDPN%81#6#3#3P8P5PN%81#6#DP9PNPN%81#6#DP:%=3PN%81#D#:P:PNPN%81#F#LP:PPPN%81#F#C#3P8P5PN%81#F#3P9PNPN%81#F#3P:%=RPN%81#F#2P:PNPN%81#<#BP:PDPN%81#<#:#3P8P5PN%81#<#EP9PNPN%81#<#EP:%=IPN%81#<#3P:PNPNP@P:%11#6#F#L#>#5PNP7P:%11#6#D#D#F#5PN%S1#2#E#DP:%@1#<#2#;#5PN%01#P#A#@#4P:%=KChPNPLP:PJPN%V1#>#@P:POPN%V1#C#@P:%11#P#@#6#5PN%V1#>#@P:%31#L#>#;#5PN%81#;#2#;P8PNPNPMP9%Z>PN%K1#C#E#4R>P:PNPN%a1#A#E#6P:PNPN%K1#C#D#4R8P:%11#^#;#<#2#5PN%K1#>#E#4ROP9%i6#2#2#ZR6PN%K1#>#;#4RJP9P6PN%V1#3#@P:%1S#J%T1#:#F#6%T1#:#<#;%K1#C#L#4RS%T1#:#A#B%K1#C#3#4R6%T1#:#R%T1#:#2#B%T1#V#A%T1#@#:#@%K1#3#B#4PNPSP:%U1#>#^#6#6#5PN%a1#A#E#DP:%U1#>#;#6#6#5R1PNP6P:P1%u4D?D9D?3M7MJ7MO7M83M3M7M>D9D?D?D?DGD?D?9t;MDYD9D9DGD?5\FDGD?D?D9D9DGDYD9D9D9DGDYD9D9D9DGDYD9D9D9DGDYD?D9DGD9D?D9DGD9D?D9DGD9D?D9DGD9D?DY3MDg3MDg3\DG3\3\D7D7DGD7D7D7D7D7D?D7D7D7D7D7D7D7D7D7D7D7D7D7D?D7D7D7D7D7'sg00P9g002e#`RF1r0Fg00=<#`g00C;3f5f0#q5p0do"). Qed.
Lemma sr2a_eq : sr2a = sr_tp2_of (s_regs (fst (fst c1a))).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1CTg004_j10Tg005Dj11Tg005ij1=Tg006Gj16Tg009:j18Tg00K^j1ATg00FAj3@Tg008\j13Tg002Ej1JTg0000j2FTg00:2j2ETg00:Rj3BTg00D3j1DTg00Q2j1GTg00<bj3HTg00M6j3:Tf0R0#0#0p=;%00#1p=4%00#0#0#0p=<%10#1p=9%10#0p=2%30#8p=L%00#3p=Kg007?R1f1R2#1#3#8;:0p=5%02#3#8=:10p=7f2R3#8%82=:105:1p=?A:1209:13p=>%82=:10p=I%C1R0g0087R2#0R3#1R4#;%12#4#4#4#<#<#9#;#=#6g00NoR5g00><#8R6%12R7#1R8#2R9#0#;#A#63@%07R7#3%<2#<#4#2#2#9#2#;#=#6%14R4#4#L%14R4%12#9#9#2#4#9#2#4#2#;#=#6%12#2#9#2#;#9#2#4#<#=#6%07R:#1R;%17R7#0R<%17R7%08R8#0R=%=2#6R2g00O[#6%<:#A#69@56%3;%3<%37%3=%39%03#4R3#0R9#K%13R3%J1,53'7,593?,583?3?7>23>,5='7,57'7,5<'7,5;'73>,54'73>'I3>'7'Fg00R0g00>ZR4g002e#CR;1E4;g00?Wg00@R3B3B#D#G5H0do"). Qed.
Lemma c1b_pc : s_pc (fst (fst c1b)) = SW_ENTRY.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg000h'0o"). Qed.
Lemma c1b_scs : snd (fst c1b) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma k1b_scs : snd (fst k1b) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2b_pc : s_pc (fst (fst c2b)) = EXIT_ECALL.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg003a'0o"). Qed.
Lemma c2b_scs : snd (fst c2b) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2b_a7 : nth 17 (s_regs (fst (fst c2b))) (ELit 0) = ELit 94.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j11Tg005Dj10Tg005ij13Tg006Gj12Tg0000j24Tg007?g0087#1#0#0#0#0#1#3#2'4o"). Qed.
Lemma c2b_a0 : nth 10 (s_regs (fst (fst c2b))) (ELit 0) = EVar 2.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j13Tg008\j12Tg009:j10Tg0000j21Tg007?g0087#3#2#0'1o"). Qed.
Lemma c1b_log : log_out3_b 0 0x1212a8 0x1216a8 (s_log (fst (fst c1b))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3p;4g0000j2<Tg005ij16Tg001ej1;Tg00:2j2:Tg00:Rj34Tg00:oj19Tg00;fj48Tg00<bj37Tg004_j12Tg005Dj15Tf0R0#2#2p=1%50#2p=0%20#5p=3g00=<R0g00=\R1'<g00><g0087R2#1#0#1#3#1#0#0#0#0#1#6%12#0#1#3#3#0#0#0#0#1#6g00>ZR2g002e#;R31:23g00?Wg00Ri3434#9C8=701do"). Qed.
Lemma k1b_vars : kn_vars_lt 40 (fst (fst k1b)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j28Tg004_j10Tg005Dj14Tg008\j13Tg001ej11Tg00:2j27Tg00:Rj32Tg00AJj25Tg00<bj36Tg00=<R0g00=\R1'8g0087#0#4#0#0#0#3g00BA#1R2g002e#1R31723%10g00Sa3232'5=601do"). Qed.
Lemma c1b_vars : sr_vars_lt 40 (s_regs (fst (fst c1b))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j29Tg004_j10Tg005Dj13Tg008\j12Tg001ej18Tg00:2j27Tg00:Rj31Tg00D3j14Tg00Dkj25Tg00<bj36Tg00=<R0g00=\R1'9g0087#0#3#0#0#0#2g00>ZR2g002e#8R31723g00?Wg00Ri3131#4'5=601do"). Qed.
Lemma kn2b_eq : kn2b = kn_tp2_of (fst (fst k1b)).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1`Tg009:j1jTg005Dj11Tg004_j10Tg00Ebj1OTg006Gj1=Tg00FAj3dTg005ij1HTg00G9j3cTg00H3j2mTg00Hmj2bTg00Igj2NTg002Ej1uTg0000j2sTg00:2j2rTg00:Rj3fTg00J`j1qTg00<bj3pTg00K^j1_Tg008\j1oTg00L<j3XTg00M6j3ITg00MVj2[Tf0R0#0#0#0p=W%H0#=p=Z%00#0p=U%00#_p=e%10#1#1#1p=2%10#1#0#0p=F%00#0#1#1p=E%00#0#0#Hp=4%10#0#0#0p=>%00#0#1#0#0p=]%10#0#0#1p=3%10#0#1#1p=D%00#0#H#=p=5%o0#jp=J%00#1#0#0p=;%00#1#0#0#0#0#0#0p=P%10#1#1#0p=A%00#0#0#0p=B%10#1#0#1p=<%00#1#1#0p=L%00#0#0#1p=:%00#1#0#1p=^%00#0#1#0#0#0#0#0p=V%00#0#1#0p=@%10#0p=n%00#0#0#0#0#0#0#0p=Qf1R1%_0'Np=l%00#1p=k%10#1p=if3R2f2R3'N?X10p=h%10#1#0#1#1#1#0#0p=K%10#1#0#1#1#1p=T%00#1#1#1p=C%10#1#0p=a%00#0#1p=v%10#0#1#0p=6%10#1#1#1#1#1#0p=8%10#1#1p=S%10#1#1#0#1#0#0#0p=Rg00BAR4f4R5/N2?X31;I0p=?%12#0#0#0#H,N5?X31=I40p=9%03#H/[1=I40p=M%02#0#0#0#H,N5?X31=I40p=G1[31=I40p=t%H2,N5?X31=I40p=YAI4109I43p=\1[521[31=I405I4p=g%_2,N5?X31=I40p=7%`4R0g00><#jR3g0087R1#1R5#1R2#1R6#WR7#0g00NP#OR8#O#O#OR9#O#O#O#OR:%Z5P3%02R2#1R;#WP:g00NoR<%01R=#1R>#1R?#1R@#U#eRA#=7d3P3%U2R2#0RB#0P:%21#F#2#E#4RC#=RDP3%05R5#1RE#>P:%]1#3#F#D#5P3%05R5#>P:%05RF#0RG#0RH#e#=9d<3P3PAP:%JFP3%0?RA#UR<#0P:%J@P3%0>R@#1RI#WP:%]1#>#;#>#5RJP3%U@R@#0RK#0P:%01#P#A#B#4RL#=P3%0=RM#1RN#>P:%11#2#3#<#L#5ROP3%WNRN#0P:%21#<#E#<#4RP#=RQP3%0MRR#1RS#WP:%01#P#E#:#5P3P7P8%H1R7#=P3PBP:PQP3%WEP:POP3PHP:POP3P<P:%]1#>#;#2#5P3PKP:%U1#>#:#F#:#5P3PNP:%11#E#2#D#;#5g00O[#=RN%01#P#A#:#4RKP9PNP3P2P:%JAP3PGP:%JIP3P@P:%J5P3%0RR5#0R@P:%J=P3PFP:%11#P#^#>#5PN%V1#3#@P9%J1RFP3P5P:%J?P3PRP:%JM%0@#BR@#0#BRM#n#B#Q#4%0MRM#B#Q#Q#Q#45c3%H5R5,m31l3@%Z@'b%F;#Q#4R;,NN%11#k#B#Q#5'bPN%Q1#L#:P9PF%i6#2#2#2#2R6#H9cF7PN%01#Q#<#:#4P:%U1#>#@#L#B#5ChRF%HMP;%K1#:#<#4%K1#E#L#4R;%T1#@#C#;%a1#A#;#A#3#HPLPK%01#P#A#E#4RK%01#P#A#;#4RL%v1#B#C#;#;%]1#:#<#@#4PN%V1#3#;#DP8PNPNPCP:%11#6#6#F#6#5RCPN%81#C#<P:%K1#C#@#4RM#=R7PN%81#C#AP:%21#A#;#@#4R@#=R3PN%81#C#AP:%11#2#3#<#3#5PN%21#F#2#2#4RRP:PCPN%S1#R#EP:%=;RCPN%S1#R#;P:P3PN%S1#R#;P:%11#2#3#<#D#5PN%21#<#B#D#4R3P:%11#6#D#:#L#5R?PN%S1#R#3P:P7PN%S1#R#6P:%21#A#C#;#4R7#=R=PN%S1#R#6P:%11#2#3#<#2#5PN%21#<#:#C#4RIP:P?PN%S1#R#2P:PCPN%81#3#BP:P=PN%81#3#BP:%11#2#3#A#:#5PNPPP:%11#6#3#D#@#5RPPN%81#3#2#3P8%=5R5PN%81#6#:P9PNPN%81#6#:P:PDPN%81#6#CP:PNPN%81#6#>P:%11#6#3#2#6#5RDPN%81#6#3#3P8P5PN%81#6#DP9PNPN%81#6#DP:%=3PN%81#D#:P:PNPN%81#F#LP:PPPN%81#F#C#3P8P5PN%81#F#3P9PNPN%81#F#3P:%=RPN%81#F#2P:PNPN%81#<#BP:PDPN%81#<#:#3P8P5PN%81#<#EP9PNPN%81#<#EP:%=IPN%81#<#3P:PNPNP@P:%11#6#F#L#>#5PNP7P:%11#6#D#D#F#5PN%S1#2#E#DP:%@1#<#2#;#5PN%01#P#A#@#4P:%=KChPNPLP:PJPN%V1#>#@P:POPN%V1#C#@P:%11#P#@#6#5PN%V1#>#@P:%31#L#>#;#5PN%81#;#2#;P8PNPNPMP9%Z>PN%K1#C#E#4R>P:PNPN%a1#A#E#6P:PNPN%K1#C#D#4R8P:%11#^#;#<#2#5PN%K1#>#E#4ROP9%i6#2#2#ZR6PN%K1#>#;#4RJP9P6PN%V1#3#@P:%1S#J%T1#:#F#6%T1#:#<#;%K1#C#L#4RS%T1#:#A#B%K1#C#3#4R6%T1#:#R%T1#:#2#B%T1#V#A%T1#@#:#@%K1#3#B#4PNPSP:%U1#>#^#6#6#5PN%a1#A#E#DP:%U1#>#;#6#6#5R1PNP6P:P1%u4D?D9D?3M7MJ7MO7M83M3M7M>D9D?D?D?DGD?D?9t;MDYD9D9DGD?5\FDGD?D?D9D9DGDYD9D9D9DGDYD9D9D9DGDYD9D9D9DGDYD?D9DGD9D?D9DGD9D?D9DGD9D?D9DGD9D?DY3MDg3MDg3\DG3\3\D7D7DGD7D7D7D7D7D?D7D7D7D7D7D7D7D7D7D7D7D7D7D?D7D7D7D7D7'sg00TYg002e#`RF1r0Fg00=<#`g00Sa3f5f0#q5p0do"). Qed.
Lemma sr2b_eq : sr2b = sr_tp2_of (s_regs (fst (fst c1b))).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1CTg004_j10Tg005Dj11Tg005ij1=Tg006Gj16Tg009:j18Tg00K^j1ATg00FAj3@Tg008\j13Tg002Ej1JTg0000j2FTg00:2j2ETg00:Rj3BTg00D3j1DTg00Q2j1GTg00<bj3HTg00M6j3:Tf0R0#0#0p=;%00#1p=4%00#0#0#0p=<%10#1p=9%10#0p=2%30#8p=L%00#3p=Kg007?R1f1R2#1#3#8;:0p=5%02#3#8=:10p=7f2R3#8%82=:105:1p=?A:1209:13p=>%82=:10p=I%C1R0g0087R2#0R3#1R4#;%12#4#4#4#<#<#9#;#=#6g00NoR5g00><#8R6%12R7#1R8#2R9#0#;#A#63@%07R7#3%<2#<#4#2#2#9#2#;#=#6%14R4#4#L%14R4%12#9#9#2#4#9#2#4#2#;#=#6%12#2#9#2#;#9#2#4#<#=#6%07R:#1R;%17R7#0R<%17R7%08R8#0R=%=2#6R2g00O[#6%<:#A#69@56%3;%3<%37%3=%39%03#4R3#0R9#K%13R3%J1,53'7,593?,583?3?7>23>,5='7,57'7,5<'7,5;'73>,54'73>'I3>'7'Fg00URg00>ZR4g002e#CR;1E4;g00?Wg00Ri3B3B#D#G5H0do"). Qed.
Lemma c1c_pc : s_pc (fst (fst c1c)) = SW_ENTRY.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg000h'0o"). Qed.
Lemma c1c_scs : snd (fst c1c) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma k1c_scs : snd (fst k1c) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2c_pc : s_pc (fst (fst c2c)) = EXIT_ECALL.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2g0000j20Tg000Jg003a'0o"). Qed.
Lemma c2c_scs : snd (fst c2c) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g001ej12Tg002Ej11Tg0000j20Tg002eR0#2%10'0o"). Qed.
Lemma c2c_a7 : nth 17 (s_regs (fst (fst c2c))) (ELit 0) = ELit 94.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j11Tg005Dj10Tg005ij13Tg006Gj12Tg0000j24Tg007?g0087#1#0#0#0#0#1#3#2'4o"). Qed.
Lemma c2c_a0 : nth 10 (s_regs (fst (fst c2c))) (ELit 0) = EVar 2.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;2g004_j13Tg008\j12Tg009:j10Tg0000j21Tg007?g0087#3#2#0'1o"). Qed.
Lemma c1c_log : log_out3_b 0 0x1212a8 0x1216a8 (s_log (fst (fst c1c))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3p;4g0000j2<Tg005ij16Tg001ej1;Tg00:2j2:Tg00:Rj34Tg00:oj19Tg00;fj48Tg00<bj37Tg004_j12Tg005Dj15Tf0R0#2#2p=1%50#2p=0%20#5p=3g00=<R0g00=\R1'<g00><g0087R2#1#0#1#3#1#0#0#0#0#1#6%12#0#1#3#3#0#0#0#0#1#6g00>ZR2g002e#;R31:23g00?Wg00VK3434#9C8=701do"). Qed.
Lemma k1c_vars : kn_vars_lt 40 (fst (fst k1c)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j28Tg004_j10Tg005Dj14Tg008\j13Tg001ej11Tg00:2j27Tg00:Rj32Tg00AJj25Tg00<bj36Tg00=<R0g00=\R1'8g0087#0#4#0#0#0#3g00BA#1R2g002e#1R31723%10g00WC3232'5=601do"). Qed.
Lemma c1c_vars : sr_vars_lt 40 (s_regs (fst (fst c1c))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;2p;1p;3g0000j29Tg004_j10Tg005Dj13Tg008\j12Tg001ej18Tg00:2j27Tg00:Rj31Tg00D3j14Tg00Dkj25Tg00<bj36Tg00=<R0g00=\R1'9g0087#0#3#0#0#0#2g00>ZR2g002e#8R31723g00?Wg00VK3131#4'5=601do"). Qed.
Lemma kn2c_eq : kn2c = kn_tp2_of (fst (fst k1c)).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1`Tg009:j1jTg005Dj11Tg004_j10Tg00Ebj1OTg006Gj1=Tg00FAj3dTg005ij1HTg00G9j3cTg00H3j2mTg00Hmj2bTg00Igj2NTg002Ej1uTg0000j2sTg00:2j2rTg00:Rj3fTg00J`j1qTg00<bj3pTg00K^j1_Tg008\j1oTg00L<j3XTg00M6j3ITg00MVj2[Tf0R0#0#0#0p=W%H0#=p=Z%00#0p=U%00#_p=e%10#1#1#1p=2%10#1#0#0p=F%00#0#1#1p=E%00#0#0#Hp=4%10#0#0#0p=>%00#0#1#0#0p=]%10#0#0#1p=3%10#0#1#1p=D%00#0#H#=p=5%o0#jp=J%00#1#0#0p=;%00#1#0#0#0#0#0#0p=P%10#1#1#0p=A%00#0#0#0p=B%10#1#0#1p=<%00#1#1#0p=L%00#0#0#1p=:%00#1#0#1p=^%00#0#1#0#0#0#0#0p=V%00#0#1#0p=@%10#0p=n%00#0#0#0#0#0#0#0p=Qf1R1%_0'Np=l%00#1p=k%10#1p=if3R2f2R3'N?X10p=h%10#1#0#1#1#1#0#0p=K%10#1#0#1#1#1p=T%00#1#1#1p=C%10#1#0p=a%00#0#1p=v%10#0#1#0p=6%10#1#1#1#1#1#0p=8%10#1#1p=S%10#1#1#0#1#0#0#0p=Rg00BAR4f4R5/N2?X31;I0p=?%12#0#0#0#H,N5?X31=I40p=9%03#H/[1=I40p=M%02#0#0#0#H,N5?X31=I40p=G1[31=I40p=t%H2,N5?X31=I40p=YAI4109I43p=\1[521[31=I405I4p=g%_2,N5?X31=I40p=7%`4R0g00><#jR3g0087R1#1R5#1R2#1R6#WR7#0g00NP#OR8#O#O#OR9#O#O#O#OR:%Z5P3%02R2#1R;#WP:g00NoR<%01R=#1R>#1R?#1R@#U#eRA#=7d3P3%U2R2#0RB#0P:%21#F#2#E#4RC#=RDP3%05R5#1RE#>P:%]1#3#F#D#5P3%05R5#>P:%05RF#0RG#0RH#e#=9d<3P3PAP:%JFP3%0?RA#UR<#0P:%J@P3%0>R@#1RI#WP:%]1#>#;#>#5RJP3%U@R@#0RK#0P:%01#P#A#B#4RL#=P3%0=RM#1RN#>P:%11#2#3#<#L#5ROP3%WNRN#0P:%21#<#E#<#4RP#=RQP3%0MRR#1RS#WP:%01#P#E#:#5P3P7P8%H1R7#=P3PBP:PQP3%WEP:POP3PHP:POP3P<P:%]1#>#;#2#5P3PKP:%U1#>#:#F#:#5P3PNP:%11#E#2#D#;#5g00O[#=RN%01#P#A#:#4RKP9PNP3P2P:%JAP3PGP:%JIP3P@P:%J5P3%0RR5#0R@P:%J=P3PFP:%11#P#^#>#5PN%V1#3#@P9%J1RFP3P5P:%J?P3PRP:%JM%0@#BR@#0#BRM#n#B#Q#4%0MRM#B#Q#Q#Q#45c3%H5R5,m31l3@%Z@'b%F;#Q#4R;,NN%11#k#B#Q#5'bPN%Q1#L#:P9PF%i6#2#2#2#2R6#H9cF7PN%01#Q#<#:#4P:%U1#>#@#L#B#5ChRF%HMP;%K1#:#<#4%K1#E#L#4R;%T1#@#C#;%a1#A#;#A#3#HPLPK%01#P#A#E#4RK%01#P#A#;#4RL%v1#B#C#;#;%]1#:#<#@#4PN%V1#3#;#DP8PNPNPCP:%11#6#6#F#6#5RCPN%81#C#<P:%K1#C#@#4RM#=R7PN%81#C#AP:%21#A#;#@#4R@#=R3PN%81#C#AP:%11#2#3#<#3#5PN%21#F#2#2#4RRP:PCPN%S1#R#EP:%=;RCPN%S1#R#;P:P3PN%S1#R#;P:%11#2#3#<#D#5PN%21#<#B#D#4R3P:%11#6#D#:#L#5R?PN%S1#R#3P:P7PN%S1#R#6P:%21#A#C#;#4R7#=R=PN%S1#R#6P:%11#2#3#<#2#5PN%21#<#:#C#4RIP:P?PN%S1#R#2P:PCPN%81#3#BP:P=PN%81#3#BP:%11#2#3#A#:#5PNPPP:%11#6#3#D#@#5RPPN%81#3#2#3P8%=5R5PN%81#6#:P9PNPN%81#6#:P:PDPN%81#6#CP:PNPN%81#6#>P:%11#6#3#2#6#5RDPN%81#6#3#3P8P5PN%81#6#DP9PNPN%81#6#DP:%=3PN%81#D#:P:PNPN%81#F#LP:PPPN%81#F#C#3P8P5PN%81#F#3P9PNPN%81#F#3P:%=RPN%81#F#2P:PNPN%81#<#BP:PDPN%81#<#:#3P8P5PN%81#<#EP9PNPN%81#<#EP:%=IPN%81#<#3P:PNPNP@P:%11#6#F#L#>#5PNP7P:%11#6#D#D#F#5PN%S1#2#E#DP:%@1#<#2#;#5PN%01#P#A#@#4P:%=KChPNPLP:PJPN%V1#>#@P:POPN%V1#C#@P:%11#P#@#6#5PN%V1#>#@P:%31#L#>#;#5PN%81#;#2#;P8PNPNPMP9%Z>PN%K1#C#E#4R>P:PNPN%a1#A#E#6P:PNPN%K1#C#D#4R8P:%11#^#;#<#2#5PN%K1#>#E#4ROP9%i6#2#2#ZR6PN%K1#>#;#4RJP9P6PN%V1#3#@P:%1S#J%T1#:#F#6%T1#:#<#;%K1#C#L#4RS%T1#:#A#B%K1#C#3#4R6%T1#:#R%T1#:#2#B%T1#V#A%T1#@#:#@%K1#3#B#4PNPSP:%U1#>#^#6#6#5PN%a1#A#E#DP:%U1#>#;#6#6#5R1PNP6P:P1%u4D?D9D?3M7MJ7MO7M83M3M7M>D9D?D?D?DGD?D?9t;MDYD9D9DGD?5\FDGD?D?D9D9DGDYD9D9D9DGDYD9D9D9DGDYD9D9D9DGDYD?D9DGD9D?D9DGD9D?D9DGD9D?D9DGD9D?DY3MDg3MDg3\DG3\3\D7D7DGD7D7D7D7D7D?D7D7D7D7D7D7D7D7D7D7D7D7D7D?D7D7D7D7D7'sg00X;g002e#`RF1r0Fg00=<#`g00WC3f5f0#q5p0do"). Qed.
Lemma sr2c_eq : sr2c = sr_tp2_of (s_regs (fst (fst c1c))).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitTDefs ()) [] "p;1p;3p;2g001ej1CTg004_j10Tg005Dj11Tg005ij1=Tg006Gj16Tg009:j18Tg00K^j1ATg00FAj3@Tg008\j13Tg002Ej1JTg0000j2FTg00:2j2ETg00:Rj3BTg00D3j1DTg00Q2j1GTg00<bj3HTg00M6j3:Tf0R0#0#0p=;%00#1p=4%00#0#0#0p=<%10#1p=9%10#0p=2%30#8p=L%00#3p=Kg007?R1f1R2#1#3#8;:0p=5%02#3#8=:10p=7f2R3#8%82=:105:1p=?A:1209:13p=>%82=:10p=I%C1R0g0087R2#0R3#1R4#;%12#4#4#4#<#<#9#;#=#6g00NoR5g00><#8R6%12R7#1R8#2R9#0#;#A#63@%07R7#3%<2#<#4#2#2#9#2#;#=#6%14R4#4#L%14R4%12#9#9#2#4#9#2#4#2#;#=#6%12#2#9#2#;#9#2#4#<#=#6%07R:#1R;%17R7#0R<%17R7%08R8#0R=%=2#6R2g00O[#6%<:#A#69@56%3;%3<%37%3=%39%03#4R3#0R9#K%13R3%J1,53'7,593?,583?3?7>23>,5='7,57'7,5<'7,5;'73>,54'73>'I3>'7'Fg00Y4g00>ZR4g002e#CR;1E4;g00?Wg00VK3B3B#D#G5H0do"). Qed.
