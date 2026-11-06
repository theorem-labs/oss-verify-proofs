(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1MainEntry U1LibStdioCall U1ReadErr_defs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1Refused_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs3srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs3knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs4scRFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1Refused_defs2rHC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Section FXALL1.
Context {fx : FPState}.

Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

Definition ssB0 : sym_state := SS 0x65a84 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.

Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

Definition ssC0 : sym_state := SS 0xd7b64 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

Definition ssD0 : sym_state := SS 0xd7b64 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

Definition ssE0 : sym_state := SS 0xd7b64 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.

Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0xd7b64 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd7b64 srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Lemma itinerary_rf :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0xd70d4%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd1e54%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_U1Refused_defs ()) ["FXALL1"] "p%0p&0p;1p;2p;3p;<p;4g0000k10oTg000Pk206Tg0010k10KTg001Pj3eTg001jk10nTg002Lj10Tg0031j14Tg003Oj1]Tg004Gj11Tg004lj1bTg005Jj1BTg006Bj12Tg006ak20aTg007[k30LTg008Uk20RTg009Om<0TTg00:Rk20NTg00;4j4lTg00;Tj2\Tg00;ok209Tg00<Ik40MTg00<dj3sTg00=Ak101Tg00>7k30lTg00?9k10kTg00@7k10jTg00A3k10iTg00B0k10hTg00Bmk10gTg00Cjk10fTg00Dfk30dTg00E^j3:Tg00F>j2XTg00G7j2KTg00H1j3`Tg00Hkk30cTf0R0#1#1#0#0p==%00#1#0#1p=;%00#1#1#1p=>%00#0#1#1p=<%10#0#0#4p>0Ag00IHR1f2R2f1R3P0Clp=a%10#0#1#0p=C%10#1#1#0p=H%00#0#0#1#1#0#1#0p>0O%10#1#0#1p=8%10#1#1#1#1#1#1#0p>07%00#0#0#1#0#0#0#4p=m%10#0#1#1p=G%00#0#0#0p=3%10#1#0#0#0#0#0#4p>05%00#0p=Ag00If@0d30p=|%10#0p>04%40#Bp=O%20#2p>0>%20#2#2#2p>0=%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0<%00#0#4#Bp=F%00#0#0#0#0p=N%00#1#0#0#1#0#0#0p=r%00#0#0#4p=I%00#0#1#0#0#0#1#0#0p=k%10#0#0#0p=6%20#2#2#2#2#2#2#2p>0mg00JRR4%]2%]3=:403:p=jA:4309:42p>08%]3=:40p>0S%00#bp>0G%10#1#0p>0B%10#1#1#1#1#1#1#1p=f%00#1#0#0p=J%00#1#1#0p=9%00#0#1#0p=E%10#1p=^%00#0#0#1p=P%10#0#0#1p=5%00#0#0#1#1#1#1#0p=y%10#1#1#1p=D%00#0#0p=7%00#0#0#0#0#0#1#1p=S%00#0#0#1#0#0#1#1p>02%00#1p>0b%00#0#0#0#0#0#0p=U%00#0#0#0#0#1#1#1p=V%00#0#0#0#0#0#0#0p=Q%00#0#0#0#0#0#0#4p=W%b0,X3p>0`%00#0#4,X3p>0_%43/K0p>0^%00#0#0#0#0#1#0#0p=[%00#0#1#4p>0]%00#0#0#1#0#0#1#0p=d%00#0#0#0#0#0#0#0#0p=c%10#1#1#1#0#0#0#4p=~%00#0#0#0#1#0#0#0p=}%00#0#0#0#0#0#0#0#1p=T%00#1#0#0#0#1#0#0p>0Q%00#0#0#1#0#0#0#1p>0E%00#0#0#0#0#1#0#1p=R%00#0#0#0#0#0#0#0#1#1#0p=@%00#0#0#0#0#0#0#0#1#1#0#0#1p=u%00#0#0#0#0#0#0#0#1#1#0#1#0p=v%00#0#0#0#0#0#0#0#1#1#0#1#1p=x%00#0#1p>0@%00#0#1#0#0p={%00#0#0#1#1#0#1#1p>0\%00#0#1#0#0#0#1#0#0#1#1p=t%10#4p>0[%00#0#1#0#0#0#1p>0Zf3R5/X2?`30p>0Y%00#0#0#0#0#1#1#0p>0?%00#0#0#0#0#0#0#1p>0Xg00KJR6f4R7/X5?`23;:0p=?%05#0#0#0#4,X7?`23=:60p=Z%15#0#0#0#4,X7?`23=:60p=M%45,X7?`23=:60p>0DA:6309:62p>0C%07#4/K5%02#4/K3=:605:6p=z%02#4%03#0#0#4'K=:60p=Y%03#4,K2=:60p>0P%02#4/K3=:60p>0J%02#1#1#0#0#4%03#0#0#4'K=:60p=w%12#4/K3=:60p=o1K751K23=:605:6p>0W%12#1#1#0#0#4%03#0#0#4'K=:60p=q%12#1#1#0#0#4/K3=:60p>0;%12#0#1#0#0#4%03#0#0#4'K=:60p=p%17#0#1#0#0#4/K5%02#0#1#0#0#4/K3=:605:6p>0I%02#0#1#0#0#4%03#0#0#4'K=:60p=n%02#0#1#0#0#4/K3=:60p>0:%12#0#1#0#0#4/K3=:60p>0V%02#1#1#0#0#4/K3=:60p>0U%15#0#0#0#b,X7?`23=:60p=_%b5,X7%]37`2=:60p=i%05#b,X7?`23=:60p=g%b5,X7?`23=:60p=L%b5,X7%43#B7`2=:60p=hf6R8f5R9P7P5P2P3P0H0MH0Mp>0Hg00LDR:?s30p>03B0c:30p>00Ae523/\0p>0eAe897Ae523/\0'\p>0Fg00MAR0$0oR5-061R3g00N=R2#=#;#>#<$0A&0K0R05a5R9;e9R8%C2#H$0O$0A=a50R7=e37S00g00NbR;$0nR<%82$07#mR=%02R>#4S01%G2#3#=$05R?g00OeR@#]RA%0>RB#0RC#1RD#1RE#0RF#AS02#0RG#bRH#B'|RI%0CRJ#0RK#1RL#0RM$04RN#b#B,|AS03PI%1>R>#0RO#0RP#AS04#OS05g00PD#BRQPQ%1BRB#0RR#0RS#0RT#0S06#0S07#0RU#bRV#B,|ARW%2@R@#2RX$0>RY#2RZ#2$0>R[$0>$0=S08#2S09$0=R\#2R]#2S0:#2S0;#2S0<#2S0=#2S0>#2S0?#2S0@#2R^#2R_#2R`#2Ra#2Rb#2Rc$0>$0=$0<$0<$0<$0<$0<Rd%B?%1JRe#0Rf#0Rg#0Rh#ARi#3#F%N2#r#<#IRj#B%2d$0=Rk%2kRk%2kRk%B=Rl%1BRB#0Rm#O&0=kRk#]%2kRk%2kRk%2kRk%2kRk%2kRk%2kRk%k2#8#mRn#BRo%42Rp#BS0A%A2#6#C$07#F%2k$0>$0mRk%2kRk%2kRk%2k&0K43j3j9jbc9j`a9j^_808Q4083j3j3j608Q408+0S3j408808W+0SPQ%82$07#;#IS0BP[%12R_#1R^#1Ra#3R`$0G#B,|ARcPQ&0B2#f#<P[PIPQ%82$07#6#IRbP[PIPA&04gP[&0BP#J#9#;#>#<#>#;#9#9#9#;#>#EPA%1eRe#0RP$04P[%0KRK#0Rg#1Rk#0#^#P#=#8#5#;#8#y#;#6#6#6#FPA%1SRSP[%E2#9#G#5#OPA%3SP[PlPAPTP[%1>RT#0RS#OPAPUP[%1aRa#1RU#1Rq#1#fRr#^#DRs#DRt#0#5#OPA%1EREP[%1t#DRt#OPA%7EREP[%1RRR#OPAPFP[%12#9#E#3#=#FPA%0DRD#0RF#0Ru$04P[%0_R_#1Rv#ARw#ARx#^#9#<#6#<#6#<#S$02#>#<#9PA%1DRDP[PQPA%0uRy#AP[%OCRCPA%7DRDP[PCPA%0^R^#1RC#1Rz#1R{#7P@%1vRv#0R|#OR}PAPGP[%1N#<#FPA%0zRz#1RN#1RG#1P@%1vPAPGP@%0_R_#0RG#1#OPA%0NRN#1P@%0GRGPAPNP@%A^R^#ORNPA%0zRz#1Rv#1P@PNPAPvP@P}PA&0bzP@PwPA%1F#ARFP[PQPA%3UP[%0gRg#ARU#ARw#3Rz#UR}#0Rv#ARN#OR~PAPVP[%1O#A$0GRO#B,|APAPFPX%1k#8PAPDPY%7aRa$04#V#J#>#;PAPHP[%A^R^$0B#H#9#5#E#S#C#9#5#9#=#9#<#OPAPeP[%1t#^Rt#A#=#=#=#=#=#=#8#OPA%7PP[%1t#D#fRt#0#f#fPA%7qP[%1_R_#1#<#<#<#<#<#FPA%7MP[%7RRR#6#5PAPUP[PoPAPKP[PQPAPLP[PWPAPfP[PcPAPiP[%1B#A$0GRB#B,|APQ&0B2#f#PP[PQPQ%82$07#E#IRiP[PQPQ%82#f#E#IRcPY%1t#f#f#OPQ&0B2#f#9P[Q05PQ%82$07$05RtP[PIPQP=PY%O>PAQ07P[PQPAPRP[PQPA%AmRmP[PQPAPBP[PQPAQ02P[PQPAPEP[%AS$0GRS#B,|AREPAPyP[%]YRyPAPhP[Q0@PAPgP[Q0?PAPaP[Q0>PAP`P[Q0=PA%7CP[Q09PAP^P[PoPA%A|P[%12#;#=#G#6#FPAPxP[PEPA%7_P[PyPAPmP[Q0:PAQ04P[%]]PAPOP[%]\PAPSP[P~PAPuP[Q0<PAQ06P[Q0;PA%AGP[Q08PAPTP[%52#9#C#6#F%4JRJ-0aA%Qr#Q#Q#WRr%AN#3#Q#W60LA20`A}%4}+0R%]X%6v#3#Q#W80Lr%1{#A#Q-0_Q&042#C#3#W+0R20^z=%^2#>#D#6%^2#>#D#5#3Q0B%^2#>#D#5#=Pb%^2#>#D#C#JPt%^2#>#D#G#6Pc%^2#>#D#=%H2#[#W%^2#6#P#Q%H2#[#5$0]%U2#d#J%c2#5#H#I%U2#E#>#5%c2#5#~Rc%U2#E#C#6%c2#C#G#IRt%U2#E#8#6%c2#G#>#IRb%72#S#}%c2#=#<#IRz%72#S#<#6%c2#=#~%72#S#9#8%c2#8#=%72#S#C#P%c2#H#5#IR{%72#S#C#H%c2#H$05%72#S#D%c2#D#8#IRr%72#S#D%T2#3#W%U2$0Q%N2$0E#m%U2$0Q%N2$0E#J%72#[#5%N2#d#;%72#[#5%N2#d#6%72#[#H%N2$02#5#IRv%72#[#H%N2$02$05%72#R#<%T2#J#8#IRX%72#R#<%T2#;#W%72#R#6%T2#9#m%72#R#5%T2#9#;%72#R#8%T2#>#9%72#R#H%T2#>#C%@2#E%T2#6#G%@2#<%T2#6#8%@2#<%T2#6#~%@2#J%u2#m%@2#J%u2#<%@2#;%u2#;%@2#;%u2#>%@2#9%u2#5%@2#9%u2#G%@2#>%u2#8%@2#>%u2#~%@2#6%v2#m%@2#6%v2#<%@2#5%v2#;%@2#5%v2#>%@2#C%v2#5%@2#C%v2#G%@2#G%v2#8%@2#G%v2#~%@2#=%x2#m%@2#=%x2#<%@2#=%x2#J%@2#8%x2#9%@2#8%x2#6%@2#H%x2#C%@2#H%x2$05%@2#D%x2#H%@2#D%T2#=#J%72#V#P#;%T2#=#9%72#V#P#8%T2#=#6%72#V#E#;%N2#y#3%72#V#6%N2#y#E%72#V#6%N2#y#J%72#V#5%N2#y#9%72#V#5%N2#y#6%72#}#;#3%N2#E#E#WR}%72#}#=#6%N2#E#<#~%U2#5#R%N2#E#J#E%U2#5#G#8%02#S#;#9$0A%U2#8#;#=%02#S#;#=%U2#8#>#J%02#S#;#D%U2#8#>%02#S#9#W%U2#8#6#J%02#[#9#5&0@2#d#P#3%{2#r#6%72#P$0\%02#[#>#5%72#P#y#6%02#[#>#8#IRA%72$0E#D#6%N2#r#m%72#d#P#J&0@2#d#E#=%{2#r#8#IRN&0@2#d#<#9%{2#r#H#IRT%{2#r#~RG%k2#5#WRu%k2#5#m%k2#G#WR~&0@2#d#=#JPn%t2#r%k2#8#<#I%t2#;#J%t2#;#;$0[RS%t2#;%k2#8#9%t2#;#=%k2#8#6%t2#9#6%k2#8#G#IR\%k2#8$05RO%t2#6#6%t2#6#=%{2#;#[&0Z2#;#H#J%{2#9#6#P$0A&0@2$0O#3#C%02#r#3#WPQ%02#[#9#C#IR]P[%B]PQ%32#E#<#>PY%]ZRZPQPnP[PyPQPSP@PQPQP\P[%Ow%4s:0LZpPQPcP[%12#G#E#E#3#FRZH0YPQ%32#R#<P[%12#=#S#C#FRpPQ%32#R#JP[%N2#y#H#IRs#BRwPQ%32#R#JP[%A2#3$02#P#FPQPtP[PZPQ%32#R#5P[PlPQ%32#R#CP[PwPQ%32#R#CP[%A2#3$02#<#FPQPbP[%12#G#E#9#=#FRwPQ%32#R#DP[PpPQ%32$0?#3P[%B}RpPQ%32$0?#3P[%A2#3$02#>#FPQPzP[PwPQ%32$0?#;P[PlPQ%32$0?#9P[PpPQ%32$0?#9P[%A2#3$02#5#FPQP{P[%12#G#P#}#FR{PQ%32#V#;#5P@%BJRJPQ%32#V#>PYPQPQ%32#V#>P[%BcPQ%32#V#8P[PQPQPrP[%12#G#P#;#3#FRrPQ%32#V#D#5P@PJPQ%32#}#PPYPQPQ%32#}#PP[%BbPQ%32#}#>P[PQPQPvP[P{PQ%Q2#5#8#5P@PJPQ%Q2#5#DPYPQPQ%Q2#5#DP[%BtPQ%Q2#C#;P[PQPQPXP[PrPQ%Q2#C#>#5P@PJPQ%Q2#C#5PYPQPQ%Q2#C#5P[%BzPQ%Q2#C#DP[PQPQPsP[%12#G#<#G#H#FPQP}P[%12#G#<#d#FPQ&0X2$0EP[%E2#8#H#9#FPQPNPYQ0APQPTP[%BGPQPuP[%{2#D#5#H#FPQP~P[%A2#3#d#H#FPQPAP[%BO&0K6D?D?D?D?D?DZD?D?DMDMDZI0DD?DMDMDZI0DD?DMDMDZI0DD?DMDMDZI0DD?DMDZDMD?DMDZDMD?DMDZDMD?DMDZDM40CD?D?D?DZD?Dz3Y40P40J3Y3w3oDzI0WDz60PjDz3q3Y3Y40;3Y3Y3o3Y3o40J3q3w3q3w3Y3Y3Y3q3w40;3w3q3w3q3pI0I3n3p3n3p3n3pI0I3n3p3n3p3n3pI0I3n3p3w3w3n40:40;40:40;40:3q3n3q40:40;40:Dz3Y3o3o3o3o40J3o3o40VDzDz80Ui40C40C40CD_DiDiDiD?D?DgDiDLDLDLDLDiDiDiDiDiDLDLDLD?DgDLDLD?D?DMD?D?DMDLD_D_D_DLDhDLDhD_D?DhDhD?DLDgDhDgDLDgDhDgDhDgDLDgDLD_DhD_DgD_DgD_DLD_DLDhD?DZD?N<0T-0N;Ri;eiRj20611R60061ROP6P1P1P1P?P=ClQ01ClR=;e=R?20644R[0064RAP[P4P4P4PIQ03ClPQClRQ;eQRI%C2#<#=#C$0A=a50R0=e30R2'\R~'\Ru'\RG'\RT,\8RY,\8RN,\8R},\820939RsP8P}PsP8PNPsP8PYPsP8PTPsQ00PG20937PjPu209<iP?P~209O=PIP2209AQ20930H0MK0HK0HK0HK0HP3206:5R:g00PbR2g00Q]3sRI-035$012005I5a5P9P3g00RW9s:2RI-035$012005I5a5P9P3g00SQ9s:2RI-035$012005I5a5P9P3g00TK9s:2RI-035$012005I5a5P9P3g00UE9s:2RI-035$012005I5a5P9P3g00V?9s:2R9-035$01200595a5P7P<g00W9g00X460ldg00XoRd-0N;POP6P1P1P1&0kd&0jdCl&0idClP=PAP[P4P4P4&0hd&0gdCl&0fdClPQg00Yk9s:2R2-035$01200525a5=e30H0eK0FK0FK0FK0Fdo"). Qed.

End FXALL1.
