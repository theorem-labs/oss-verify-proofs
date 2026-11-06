(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1MainEntry S1LibStdioCall S1ReadErr_defs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1Refused_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs3srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs3knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs4scRFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1Refused_defs2rHC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Section FXALL1.
Context {fx : FPState}.

Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

Definition ssB0 : sym_state := SS 0x65830 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.

Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

Definition ssC0 : sym_state := SS 0xd5e0c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

Definition ssD0 : sym_state := SS 0xd5e0c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

Definition ssE0 : sym_state := SS 0xd5e0c srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.

Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0xd5e0c srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd5e0c srG0 [] knG0 199.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0xd537c%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd00fc%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_S1Refused_defs ()) ["FXALL1"] "p%0p&0p;1p;2p;3p;<p;4g0000k10lTg000Pk20:Tg0010k10LTg001Pj3`Tg001jk10WTg002Lj10Tg0031j14Tg003Oj1\Tg004Gj11Tg004lj1_Tg005Jj1BTg006Bj12Tg006ak20`Tg007[k30KTg008Uk20RTg009Om<0VTg00:Rk20MTg00;4j4lTg00;Tj2^Tg00;ok207Tg00<Ik40FTg00<dj3vTg00=Aj1|Tg00>7k30kTg00?9k10jTg00@7k10iTg00A3k10hTg00B0k10gTg00Bmk10fTg00Cjk10eTg00Dfk30cTg00E^j3<Tg00F>j2[Tg00G7j2PTg00H1j3bTg00Hkk30bTf0R0#1#1#0#0p=7%00#0#0#1p=I%10#0#0#0p=9%10#0#0#4p>0@g00IHR1f2R2f1R3P0Clp=a%10#0#1#0p=5%00#1#1#0p=:%10#1#1#1p=6%10#1#0#1#1#1#0#0p=X%00#0#1#1p=3%00#0#0#4p=G%10#1#0#1p=8%00#0#1#0p=E%00#0#0#1#0#0#0#4p=j%00#0p=Jg00If@0c30p=~%10#0p>09%40#Bp=N%20#2p>0?%20#2#2#2p>0=%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0<%00#0#0#0p=>%00#0#4#Bp=H%00#0#0#0#0#0#0#0p=V%00#1#1#1#0#0#0#4p=n%00#0#1#0#0#0#0#0#1p=w%00#1#0#1#0#0#0#4p=x%20#2#2#2#2#2#2#2p>0Ug00JRR4%\2%\3=<403<p=hA<4309<42p>0;%\3=<40p>0T%00#_p>0E%10#1#0p>0A%10#1#1#0#0#0#0#1p=y%00#1#0#0p==%00#1#0#1p=@%00#1#1#1p=C%10#1p=W%10#0#0#1p=;%10#1#1#0p=S%10#0#1#1p=?%10#1#1#1#1#1#1#1p=Z%10#1#1#1#1#1p=D%10#1#1#1#1p>0S%00#0#0p=U%00#0#0#0#0#0#1#1p=m%00#1p>0a%10#1#1p=R%00#0#0#0#0#0#0#4p=k%_0,[3p>0_%00#0#4,[3p>0^%43/P0p>0]%00#0#0#0#1#1#1#0p>04%10#1#1#1#1#0#0#0p>0Q%00#1#0#0#0#0#0#4p>03%00#0#1#4p>0\%00#0#1#1#0#0#0#4p>02%10#1#1#1#1#1#0#1p=F%10#1#1#1#1#1#1#0p=T%10#1#1#1#1#1#0#1#1#1p=K%10#1#0#1#1#1#1#1p=u%10#1#1#1#1#1#0#1#1#1#1#0p=t%10#1#1#1#1#0#0#1p=s%10#1#1#1#1#1#1#0#0#0p=M%10#1#1#0#0#0#0#0p>01%10#1#1#0#1#0#1#0p>00%00#0#1p>0J%00#1#0#0#0#0#0#0p>0P%00#0#1#0#0p=r%00#0#1#0#0#0#0p>0I%00#1#0#0#0#0#0#1p>0[%00#0#1#0#0#0#0#0#1#0#0p=q%10#4p>0Zf3R5/[2?b30p>0H%10#1#1#1#1#1#0p=Q%10#1#1#0#1#0#0#0p=}g00KJR6?<30p>0Yf4R7/[5?b23=<60p=AA<6309<62p>0>%05#0#0#0#4,[7?b23=<60p=Y%15#0#0#0#4,[7?b23=<60p=O%45,[7?b23=<60p>0C%07#4/P5%02#4/P3=<605<6p={%02#4%03#0#0#4'P=<60p=]%03#4,P2=<60p>0O%02#4/P3=<60p>0G%02#1#1#0#0#4%03#0#0#4'P=<60p=p%12#4/P3=<60p=g1P751P23=<605<6p>0X%12#1#1#0#0#4%03#0#0#4'P=<60p=o%12#1#1#0#0#4/P3=<60p>08%12#0#1#0#0#4/P3=<60p>0N%17#0#1#0#0#4/P5%02#0#1#0#0#4/P3=<605<6p=c%02#0#1#0#0#4/P3=<60p=z%15#0#0#0#_,[7?b23=<60p=e%_5,[7%\37b2=<60p=f%05#_,[7?b23=<60p=d%_5,[7?b23=<60p=L%_5,[7%43#B7b2=<60p=if6R8f5R9P7P5P2P3P0H0FH0Fp>0Bg00LDR:?v30p>06B0b:30p>05A`523/^0p>0dA`897A`523/^0'^p>0Dg00MAR0$0lR5-0:1R3g00N=R2#7#I#7#9$0@&0L0R05a5R9;`9R8%52#5#:#6$0@=a50R7=`37S00g00NbR;$0WR<%X2#3#:#GR=%02R>#4S01%52#8#E#jR?g00OeR@#\RA%0>RB#0RC#1RD#1RE#0RF#JS02#0RG#_RH#B'~RI%0CRJ#0RK#1RL#0RM$09RN#_#B,~AS03PI%1>R>#0RO#0RP#JS04#NS05g00PD#BRQPQ%1BRB#0RR#0RS#0RT#0S06#0S07#0RU#_RV#B,~ARW%2@R@#2RX$0?RY#2RZ#2$0?R[$0?$0=S08#2S09$0=R\#2R]#2S0:#2S0;#2S0<#2S0=#2S0>#2S0?#2S0@#2R^#2R_#2R`#2Ra#2Rb#2Rc$0?$0=$0<$0<$0<$0<$0<Rd%B?%1JRe#0Rf#0Rg#0Rh#JRi#>#H%02#V#8#nRj#B%2d$0=Rk%2kRk%2kRk%B=Rl%1BRB#0Rm#N&0=kRk#\%2kRk%2kRk%2kRk%2kRk%2kRk%2kRk%w2#E#xRn#BRo%42Rp#BS0A%J2#9#3#5#:#H%2k$0?$0URk%2kRk%2kRk%2k&0L43h3h9hbc9h`a9h^_80;Q40;3h3h3h60;Q40;+0T3h40;80;W+0TPQ%X2#3#5#GS0BP[%12R_#1R^#1Ra#>R`$0E#B,~ARcPQ&0A2#y#8P[PIPQ%X2#3#8#GRbP[PIPA&09gP[&0AP#=#:#@#C#3#C#@#:#:#:#@#C#EPA%1eRe#0RP$09P[%0KRK#0Rg#1Rk#0#W#I#7#8#;#@#8#I#S#@#9#9#9#HPA%1SRSP[%E2#:#?#;#NPA%>SP[PlPAPTP[%1>RT#0RS#NPAPUP[%1aRa#1RU#1Rq#1#ZRr#DRs#6Rt#0#;#NPA%1EREP[&0StRt#NPA%UEREP[%1RRR#NPAPFP[%12#@#5#?#:#HPA%0DRD#0RF#0Ru$09P[%0_R_#1Rv#JRw#JRx#W#:#3#9#3#9#3#m#I#3#C#3#:PA%1DRDP[PQPA%0uRy#JP[%NCRCPA%UDRDP[PCPA%0^R^#1RC#1Rz#9R{P@%1vRv#0R|#NR}PAPGP[%1N#3#HPA%0zRz#1RN#1RG#1P@%1vPAPGP@%0_R_#0RG#1#NPA%0NRN#1P@%0GRGPAPNP@%J^R^#NRNPA%0zRz#1Rv#1P@PNPAPvP@P}PA&0azP@PwPA%1F#JRFP[PQPA%>UP[%0gRg#JRU#JRw#>Rz#U#>R}#0Rv#JRN#NR~PAPVP[%1O#J$0ERO#B,~APAPFPX%1k#8PAPDPY%UaRa$09#>#C#=#C#@PAPHP[%J^R^$0A#S#:#;#E#m#5#:#;#:#7#:#3#NPAPeP[%RtRt#J#7#7#7#7#7#7#8#NPA%UPP[&0St#ZRt#0#Z#ZPA%UqP[%1_R_#1#3#3#3#3#3#HPA%UMP[%URRR#9#;PAPUP[PoPAPKP[PQPAPLP[PWPAPfP[PcPAPiP[%1B#J$0ERB#B,~APQ&0A2#y#7P[PQPQ%X2#3#nRiP[PQPQ%X2#=#nRcPY%1t#Z#Z#NPQ&0A2#S#E#IP[Q05PQ%X2#=#jRtP[PIPQP=PY%N>PAQ07P[PQPAPRP[PQPA%JmRmP[PQPAPBP[PQPAQ02P[PQPAPEP[%JS$0ERS#B,~AREPAPyP[%\YRyPAPhP[Q0@PAPgP[Q0?PAPaP[Q0>PAP`P[Q0=PA%UCP[Q09PAP^P[PoPA%J|P[%12#@#@#:#E#HPAPxP[PEPA%U_P[PyPAPmP[Q0:PAQ04P[%\]PAPOP[%\\PAPSP[P~PAPuP[Q0<PAQ06P[Q0;PA%JGP[Q08PAPTP[%;2#:#I#3#H%4JRJ-0`A%Vr#V#V#kRr%JN#>#V#k60KA20_A}%4}+0R%\X%9v#>#V#k80Kr%V{-0^Q&092#9#>#k+0R20]z=%W2#C#>#8%W2#C$04#=Q0B%W2#C#>#6#>Pb%W2#C#>$0QPt%W2#C#I#>#7Pc%W2#C#I#I%X2#;$03%W2#C#E#@#>%X2#;#8$0\%D2#E#C#=%62#7#6#E#G%D2#3#7#;%62#7#6$02Rc%D2#3$0Q%62#7#Z#GRt%D2#=#E#9%F2#>#?#GRb%D2#=#@#9%F2#I#nRz%D2#=#9#9%F2#E$02%D2#=#?#8%F2#3#>%D2#=#6#I%F2#3#8#GR{%D2#=#T%F2#=#k%D2#@#=%F2#@#jRr%D2#@#=%F2#@$03%D2#@#;%F2#:#x%D2#@#;%F2#:#9%D2#@#S%F2#C#;#G%D2#@#S%F2#C#7%D2#:#3%F2#9#8#GRv%D2#:#3%F2#;#k%D2#:#9%F2#5#jRX%D2#:#9%F2#5$03%D2#:#8%F2#?#x%D2#:#S%F2#?#;#G%K2#E%62#X#5%K2#3%62#X#S%K2#C%F2#u#G%K2#9%t2#j%K2#9%t2$02%K2#;%t2#x%K2#;%t2#n%K2#5%t2#;#G%K2#5%t2#?#G%K2#?%t2#8#G%K2#?%t2#6#G%K2#7%62#u#j%K2#7%62#u$02%K2#8%62#u#x%K2#8%62#u#n%K2#S%F2#s#G%K2#S%62#u#?#G%K2#6%F2#F#G%K2#6%F2#Z#G%M2#>%62$01#j%M2#>%62$01$02%M2#I%62$01#x%M2#I%62$01#n%M2#I%62$01#9%M2#E%62$01#5%M2#E%62$01#7%M2#3%T2$04%M2#3%62#y#k%M2#=%62#y#E%M2#=%62#y#9%M2#:#@%62#y#5%M2#:#8%62#y#7%M2#C#@%T2#3#=%M2#8%T2#3#:%M2#8%T2#3#9%M2#S%T2#3#5%M2#S%T2#3#7%W2#s#5#>%T2#C$03R}%D2#5#I#9%T2#;$02%D2#5#@#@%T2#;#:%D2#?#>#8%Z2#5#5$0@%D2$00#7%Z2#?#>%W2#T#7#=%Z2#?#3%W2#T#7%Z2#?$03%W2#T#8#=%02#V#?#8&0J2#m#:#>%02$0P#X%U2#m#>%02#V#7#8%U2#m#3#9%02#V#8#jRA%U2#m#=#9%02#V#8#x%U2#m#:#=&0J2#m#C#7%r2$04#jRN&0J2#m#9#:%r2$04#E#GRT%r2$04$02RG%r2$04$03Ru%r2$04#x%w2#>$03R~&0I2$0[#=Pn%q2#;#9%w2#E#n%q2#5#=%q2#5#@$0ZRS%q2#5%w2#E#5%q2#5#7%w2#E#7%q2#?#9%w2#E#6#GR\%w2#3#kRO%q2#8#9%q2#X%w2#@#9&0I2#C#3#=%r2#E#8#@$0@&0I2#?#@#5%r2$0P#kPQ%02#V#?#S#GR]P[%B]PQ%V2#:#IPY%\ZRZPQPnP[PyPQPSP@PQPQP\P[%Nw%4s:0KZpPQPcP[%12#5#5#7#5#HRZH0HPQ%Q2#C#8P[%12#?#9#S#=#HRpPQ%Q2#C#SP[%T2#=#E#GRs#BRwPQ%Q2#C#SP[%12#s#8#;#HPQPtP[PZPQ%R2#}#3P[PlPQ%R2#}#=P[PwPQ%R2#}#=P[%12#s#8#?#HPQPbP[%12#5#?#I#:#HRwPQ%R2#}#;P[PpPQ%R2#}#5P[%B}RpPQ%R2#}#5P[%12#s#u#HPQPzP[PwPQ%R2#}#6P[PlPQ%Q2#;#>P[PpPQ%Q2#;#>P[%12#s#y#HPQP{P[%12#5#;#?#E#HR{PQ%Q2#;#sP@%BJRJPQ%R2$00#IPYPQPQ%R2$00#IP[%BcPQ%R2$00#CP[PQPQPrP[%12#5#;#6#5#HRrPQ%R2$00#;#;P@PJPQ%R2$00#?PYPQPQ%R2$00#?P[%BbPQ%Q2#?#IP[PQPQPvP[P{PQ%Q2#7#C#;P@PJPQ%Q2#7#;PYPQPQ%Q2#7#;P[%BtPQ%Q2#7#6P[PQPQPXP[PrPQ%Q2#8#I#;P@PJPQ%Q2#8#3PYPQPQ%Q2#8#3P[%BzPQ%Q2#8#;P[PQPQPsP[%12#5#7#:#9#HPQP}P[%12#5#?#?#7#HPQ%R2#6#3#?P[%E2#u#=#HPQPAP[%BOH0HROPQPNPYQ0AH0HPQPTP[%BGPQPuP[%r2#9#=#9#HPQP~P[%12#s#8#:#H&0L6-0YODADADA40>DYDADADODODYI0CDADODODYI0CDADODODYI0CDADODODYI0CDADODYDODADODYDODADODYDODADODYDO40>DADADADYDAD{3]40O40G3]3p3gD{I0XD{60OjD{3o3]3]4083]3]3g3]3g40G3o3p3o3p3]3]3]3o3p4083p3o3p3o40NDcDcDcDcDcDcDcDcDcDc3p3p3z3z4083z4083z3o3z3o3z4083zD{3]3g3g3g3g40G3g3g408D{D{80Ni40>40>40>DeDfDfDfDADADdDfDLDLDLDLDfDfDfDfDfDLDLDLDADdDLDLDADADYDADADYDLDeDeDeDLDiDLDiDeDADiDiDADLDdDiDdDLDdDiDdDiDdDLDdDLDeDiDeDdDeDdDeDLDeDLDiDADODAN<0V-0M;Ri;`iRj20:11RO00:1R6POP1P1P1P?P=ClQ01ClR=;`=R?20:44R[00:4R~P[P4P4P4PIQ03ClPQClRQ;`QRI%52#>#I#6$0@=a50R0=`30R2'^Ru'^RG'^RT'^RY,^8RN,^8RA,^8R},^820739RsP8P}PsP8PAPsP8PNPsP8PYPsQ00PT20737PjPG207<iP?Pu2076=PIP2207~Q20730H0FK0BK0BK0BK0BP320::5R:g00PbR2g00Q]3vRI-065#|2055I5a5P9P3g00RW9v:2RI-065#|2055I5a5P9P3g00SQ9v:2RI-065#|2055I5a5P9P3g00TK9v:2RI-065#|2055I5a5P9P3g00UE9v:2RI-065#|2055I5a5P9P3g00V?9v:2R9-065#|205595a5P7P<g00W9g00X460kdg00XoRd-0M;P6POP1P1P1&0jd&0idCl&0hdClP=P~P[P4P4P4&0gd&0fdCl&0edClPQg00Yk9v:2R2-065#|205525a5=`30H0dK0DK0DK0DK0Ddo"). Qed.

End FXALL1.
