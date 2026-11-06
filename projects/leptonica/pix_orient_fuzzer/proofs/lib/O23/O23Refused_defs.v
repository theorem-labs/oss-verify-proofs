(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23ReadErr_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Refused_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs3srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs3knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs4scRFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23Refused_defs2rHC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x62d64 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0xfff20 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xfff20 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xfff20 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xfff20 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xfff20 srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Section VP1.
Lemma itinerary_rf :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0xff528%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xfa03c%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Refused_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10ETg000Pj2hTg0010j10Tg001Uj1uTg0025j3OTg002Ok10DTg0031j1;Tg003Oj1QTg004Xj11Tg005=j1RTg005[j1>Tg006dj12Tg007Ck40BTg008Lk20ATg009Wj3wTg00:bj2~Tg00;mj2STg00=7k30?Tg00>Bj2TTg00?Mm<0=Tg00@Vj2yTg00A8j4VTg00AXj2JTg00B3j2eTg00BMj4tTg00Bhj3ZTg00CEj1_Tg00DLk50<Tg00ETk10;Tg00FXk10:Tg00GZk107Tg00H]k108Tg00I`k109Tg00Jck106Tg00Kek304Tg00Lnj3:Tg00MNj3gTg00NYk303Tf0R0#0#0#0#1p=9%00#0#1#1p==%10#0#0#1p=A%00#1#1#0p=@%00#0#0#;p=3g00O6R1f2R2f1R3P0CVp=L%10#1#1#1p=?%10#1#1#0p=F%10#0#1#0p=P%00#1#0#1p=]%00#0#0#1#0#0#1#1#1#0#0#0#0p=\%00#0#0p=I%00#0#0#0p=5%00#;p=|%00#0p=6g00OT@0430p=c%00#Rp=j%;0#>p=7%20#2p=k%20#2#2#2p=m%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=n%00#1#0#0#0#1#1#1p=X%00#1#0#0p=D%10#0#0#0p=4%00#1#1#1p=C%00#0#1#0p=B%00#0#0#0#0#0#0#0p=G%20#2#2#2#2#2#2#2p>02g00P@R4%Q2%Q3=:403:p=YA:4309:42p=i%Q3=:40p>01%10#0p=W%10#1#0#0p=8%10#0#1#1p=x%10#1#1#1#1#1#1#1p=d%10#1p=p%00#1p>0C%10#1#0#1p=M%10#1#0#0#1#1#0#0p=o%00#0#1#0#0#1#1#1p>00%R0,S3p>0@%;3/T0p=}%00#0#0#1#0#0#1p=[%10#;p=s%00#0#1p=f%00#1#0p=bg00QIR5A:5307:2p=l%02#;%03#0#0#;'T=:50p=^f4R6f3R7'S?g23=:50p=<%02#;/T3=:50p={%03#;,T2=:50p=z1T671T23=:505:5p>0>%06#;/T7%02#;/T3=:505:5p=v%17#0#0#0#R,S6?g23=:50p=K%R7,S6%Q37g2=:50p=U%07#R,S6?g23=:50p=N%R7,S6?g23=:50p=E%R7,S6%;3#>7g2=:50p=Hf6R8f5R9P6P7P2P3P0CtCtp=qg00RTR:?Z30p=`B03:30p=aAO723/J0p>05AO896AO723/J0'Jp=rg00SbR0$0ER7,h1R3g00ToR2#0#9#=#A#@#3%u0R05L7R9;O9R8%?2#F#P#]#3=L70R6=O36S00g00UTR;$0DR<%\2#9#3R=%02R>#;S01%I2#5#=#A#F#|R?g00V]R@#QRA%0>RB#0RC#1RD#1RE#0RF#6S02#0RG#RRH#>'cRI%0CRJ#0RK#1RL#0RM#1#j#>,cAS03PI%1>R>#0RN#0RO#6S04#7S05g00W<RP#>RQPQ%1BRB#0RR#0RS#0RT#0S06#0S07#0RU#RRV#>,cARW%2@R@#2RX#kRY#2RZ#2#kR[#k#mS08#2S09#mR\#2R]#2S0:#2S0;#2S0<#2S0=#2S0>#2S0?#2S0@#2R^#2R_#2R`#2Ra#2Rb#2Rc#k#m#n#n#n#n#nRd%>?%1JRe#0Rf#0Rg#0Rh#6Ri#0Rj#0#5#7%02#X#P#D#3Rk#>%2d#mRl%2lRl%2lRl%>=Rm%1BRB#0Rn#7%mlRl#Q%2lRl%2lRl%2lRl%2lRl%2lRl%2lRl%02#4#C#?#B#3Ro#>Rp%;2Rq#>%D2#D#D#G#7%2l#k$02Rl%2lRl%2lRl%2l%u43Y3Y9Ybc9Y`a9Y^_7iQ3i3Y3Y3Y5iQ3i+013Y3i7iW+01PQ%\2#]#3S0AP[%12R_#1R^#1Ra#5R`#j#>,cARcPQ%\2#@#3P[PIPQ%\2#4#3RbP[PIPA%WgP[%1O#W#D#@#]#C#=#C#]#@#@#@#]#C#BPA%1eRe#0RO#WP[%0KRK#0Rg#1Rl#0#8#C#=#@#]#C#X#A#@#B#B#5PA%1SRSP[%C2#8#x#]#7PA%5SP[PmPAPTP[%1>RT#0Rm#7PAPUP[%1aRa#1RU#1RS#1#dRr#p#?Rs#?Rt#0#A#7PA%1EREP[%1t#?Rt#7PA%IEREP[%1RRR#7PAPFP[%G2#A#5#8#7PA%0DRD#0RF#0Ru#WP[%0_R_#1Rv#6Rw#6Rx#p#@#=#4#=#4#=#5#=#9#=#C#=#@PA%1DRDP[PQPA%0uRy#6P[%7CRCPA%IDRDP[PCPA%0^R^#1Rz#1R{P@%1vRv#0R|#7R}PAPGP[%1j#P#7PA%0{R{#1Rj#1RG#1P@%1vPAPGP@%0_R_#0RG#1#7PA%0jRj#1P@%0GRGPAPjP@%6^R^#7RjPA%0{R{#1Rv#1P@PjPAPvP@P}PA&0C{P@PwPA%1FRF#6RwP[PQPA%5UP[%0gRg#6RU#6R@#5R{#I#5R}#0Rv#6Rj#7R~PAPVP[%1N#6#jRN#>,cAPAPwPX%1l#MPAPDPY%IaRa#W#5#C#X#]PAPHP[%6^R^#1#W#F#@#A#B#5#=#P#@#A#@#8#@#=#7PAPeP[%1t#pRt#6#o#o#o#M#7PA%IOP[%1t#?#dRt#0#d#dPA%ISP[%1_R_#1#6#8#o#oPA%IMP[%IRRR#4#APAPUP[PpPAPKP[PQPAPLP[PWPAPfP[PcPAPiP[%1B#6#jRB#>,cAPQ%\2#=#3P[PQPQ%\2#B#3RiP[PQPQ%02$00#9#B#3RcPY%1t#d#d#7PQ%\2#M#3P[Q05PQ%\2#8#3RtP[PIPQP=PY%7>PAQ07P[PQPAPRP[PQPA%6nRnP[PQPAPBP[PQPAQ02P[PQPAPEP[%6m#jRm#>,cAREPAPyP[g00WZPXPPP[H0BRyPAPhP[Q0@PAPgP[Q0?PAPaP[Q0>PAP`P[Q0=PA%IzP[Q09PAP^P[PpPA%6|P[%12#p#?#C#=#DPAPxP[PEPA%I_P[PyPAPnP[Q0:PAQ04P[%Q]PAPNP[%Q\PAPmP[P~PAPuP[Q0<PAQ06P[Q0;PA%6GP[Q08PAPTP[%W2#B#M#4#5#7%;J-0AA%5r#G#G#G#3Rr%6j#G#G#35wA20@A}%;}'~%QX%4v#G#G#37wr%WF#G#3,SQ%W2#D#G#3'~1}{=%[2#8#5#@Pi%[2#8#9#5Q0A%[2#8#9#8Pb%[2#8#B#DPt%[2#8#=#4Pc%[2#8#D#P%02$00#D#B#3%[2#M#5#4#s%[2#M#B#8#s%f2#9#M#B#8#s%02#X#4#P#3%f2#9#F#A#8%02#4#C#P#APQ%02#X#4#x#3RcP[%>cPQ%02#X#4#?#3PY%QZRZ%f2#9#F#D#B%02#X#A#P%f2#9#F#@#8%02#X#A#F%f2#9#F#C#8%02#X#P#B%f2#9#F#A#4%b2#9#F#x#51SQo@0?CX%D2#=#?#A#4%02#4#C#?#D#3'}%b2#9#?#M#4#s%b2#9#?#M#8%b2#9#?#F#5%02#4#C#?#A%b2#9#?#F#8%02#4#C#?#8#3RCPQPCP[%;@R@#>%b2#9#d#D%02#4#4#5#=%b2#B#9#?#5%02#4#P#G%;s9wZq1TP@%u53l3^3^D<3{3^3z3l7{o5zk3^3^3^D<D<3^I0>DvDvDv3l3l3lDKDUDUDUD<D<DNDUDEDEDHDEDUDUDUDUDUDEDEDED<DNDEDED<D<D<D<D<D<DEDKDKDKDEDHDHDHDKD<DHDHD<DEDNDHDNDEDNDHDNDHDNDKDNDEDKDHDKDNDKDNDKDEDKDHDHD<D<D<N<0=,y;Rk;OkRo1h11R5/h1R@P5P1P1P1P?P=CVQ01CVR=;O=R?1h44RP/h4RZPPP4P4P4PIQ03CVPQCVRQ;OQRI%p2#M#5#9#F#|=L70R0=O30R2'JRq'JRs'JR['JRC,J8RX,J8RY,J8Rc,J81e39RtP8PcPtP8PYPtP8PXPtP8PCPtQ00P[1e36PoPs1e<kP?Pq1e@=PIP21eZQ1e30CtFqFqFqFqP31h:7R:g00X:R2g00YF3ZRI,`7#_1a7I5L7P9P3g00ZA9Z:2RI,`7#_1a7I5L7P9P3g00[<9Z:2RI,`7#_1a7I5L7P9P3g00\79Z:2RI,`7#_1a7I5L7P9P3g00]29Z:2RI,`7#_1a7I5L7P9P3g00]m9Z:2R9,`7#_1a795L7P6P<g00^hg00_cPdg00``g00a\I0<g00bXRd,y;P@P5P1P1P1&0;d&0:dCV&07dCVP=PZPPP4P4P4&08d&09dCV&06dCVPQg00cU9Z:2R2,`7#_1a725L7=O30H05FrFrFrFrdo"). Qed.
End VP1.
