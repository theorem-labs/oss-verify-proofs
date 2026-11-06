(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2ReadErr_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Refused_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs3srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs3knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs4scRFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2Refused_defs2rHC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x17860 srRF0 [] knRE0 39.
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
Definition ssC0 : sym_state := SS 0x31d38 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x31d38 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x31d38 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x31d38 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x31d38 srG0 [] knG0 199.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x31958%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x2f4d4%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Refused_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10CTg000Pj2eTg0010j1uTg001Pj3JTg001jk101Tg002Lj10Tg0031j1;Tg003Oj1MTg004Xj11Tg005=j1TTg005[j1=Tg006dj12Tg007Ck40BTg008Lk20ATg009Wj3vTg00:bj2{Tg00;mj2YTg00=7k30?Tg00>Bj2VTg00?Mm<0=Tg00@Vj2wTg00A8j4UTg00AXj2HTg00B3j2fTg00BMj4sTg00Bhj3ZTg00CEj1aTg00DLk509Tg00ETk108Tg00FXk105Tg00GZk106Tg00H]k107Tg00I`k104Tg00Jck10:Tg00Kek303Tg00Lnj39Tg00MNj3dTg00NYk302Tf0R0#1#0p=F%10#1#0#1p=A%00#1#0#0p=6%10#0#1#1p=O%00#0#0#;p=5g00O6R1f2R2f1R3P0CUp=K%00#0#1#1p=4%00#0#1#0p=B%10#1#0#0#1#0#1#0#1#0p=\%00#0#0#1p=n%00#0#0#0p=:%00#1#0#1p=E%00#0p=7g00OT@0330p=`%00#Tp=l%;0#=p=@%20#2p=k%20#2#2#2p=j%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=i%00#0#;#=p=[%00#0#1p=c%10#0#0#0p=>%10#0#1p=]%10#0#1#0p=D%00#1#1#1p=C%10#1#0#0p=3%20#2#2#2#2#2#2#2p>00g00P@R4%M2%M3=94039p=RA94309942p=h%M3=940p=~%00#1#1#0p=8%10#1p=r%10#0#0#1p=G%10#1#1#0p=X%10#1#1#1#1#1#1#1p=g%10#1#1#1p=I%00#0#0p=P%00#1p=}%10#1#0#0#1#0p=|%00#0#0#0#0#0#0#0p=N%T0,Y3p>0@%;3/V0p=z%10#;p=qg00QIR5A9530792p=m%02#;%03#0#0#;'V=950p=bf4R6f3R7'Y?d23=950p=?%02#;/V3=950p=y%03#;,V2=950p=x1V671V23=950595p>0>%06#;/V7%02#;/V3=950595p=t%17#0#0#0#T,Y6?d23=950p=L%T7,Y6%M37d2=950p=S%07#T,Y6?d23=950p=Q%T7,Y6?d23=950p=<%T7,Y6%;3#=7d2=950p=W%00#;p>0<f6R8f5R9P6P7P2P3P0CsCsp=pg00RTR:?Z30p=_B02:30p=^AJ723/H0p>0;AJ896AJ723/H0'Hp=og00SbR0$0CR7,e1R3g00ToR2#F#A#6#O#5%u0R05K7R9;J9R8%F2#4#B#O#5=K70R6=J36S00g00UTR;$01R<%\2#n#5R=%02R>#;S01%F2#6#:#E#5R?g00V]R@#MRA%0>RB#0RC#1RD#1RE#0RF#7S02#0RG#TRH#='`RI%0CRJ#0RK#1RL#0RM#1#l#=,`AS03PI%1>R>#0RN#0RO#7S04#@S05g00W<RP#=RQPQ%1BRB#0RR#0RS#0RT#0S06#0S07#0RU#TRV#=,`ARW%2@R@#2RX#kRY#2RZ#2#kR[#k#jS08#2S09#jR\#2R]#2S0:#2S0;#2S0<#2S0=#2S0>#2S0?#2S0@#2R^#2R_#2R`#2Ra#2Rb#2Rc#k#j#i#i#i#i#iRd%=?%1JRe#0Rf#0Rg#0Rh#7Ri#:#[%c2#4#:#>#5Rj#=%2d#jRk%2kRk%2kRk%==Rl%1BRB#0Rm#@%jkRk#M%2kRk%2kRk%2kRk%2kRk%2kRk%2kRk%]2#4#E#E#5Rn#=Ro%;2Rp#=%D2#C#3#B#[%2k#k$00Rk%2kRk%2kRk%2k%u43R3R9Rbc9R`a9R^_7hQ3h3R3R3R5hQ3h'~3R3h7hW'~PQ%\2#E#5S0AP[%12R_#1R^#1Ra#:R`#l#=,`ARcPQ%\2#8#5P[PIPQ%\2#>#5RbP[PIPA%FgP[%1O#F#6#8#E#C#4#C#E#8#8#8#E#C#BPA%1eRe#0RO#FP[%0KRK#0Rg#1Rk#0#r#n#3#A#G#E#A#n#X#E#>#>#>#[PA%1SRSP[%0DRD#1Rq#7Rr#F#A#[PA%:SP[PlPAPTP[%1>RT#0Rl#@PAPUP[%1aRa#1RU#1RS#1#gRs#r#IRt#IRu#0#G#@PA%1EREP[%1u#IRu#@PA%PEREP[%1RRR#@PAPFP[%12#7#>#C#X#[PA%0DRD#0RF#FP[%0_R_#1Rv#7Rw#7Rx#r#8#4#>#4#>#4#:#4#n#4#C#4#8PAPqP[PQPA%0FRq#7P[%@CRCPA%0rRrP[PCPA%0^R^#1Ry#1RzP@%1vRv#0R{#@R|PAPGP[%1KRK#1#C#D#@PA%0zRz#1RG#1R}#1P@%1vPAP}P@%0_R_#0R}#1#@PA%0GRG#1P@%0}R}PAPGP@%0^R^#0RG#@RvPA%0zRz#1R~#1P@PvPAP~P@P|PA%}zP@PwPA%1D#7RDP[PQPA%:UP[%0gRg#7RU#7Rw#:R@#P#:Rz#0R|#7R~#@RvPAPVP[%1N#7#lRN#=,`APAPDPX%1k#APAPrPY%PaRa#F#:#C#6#C#EPAPHP[%7GRG#1#F#X#8#G#B#:#4#D#8#G#8#3#8#4#@PAPeP[%1u#rRu#7#3#3#3#3#3#3#A#@PA%POP[%1u#I#gRu#0#g#gPA%PSP[%1_R_#1#4#4#4#4#4#[PA%PMP[%PRRR#>#GPAPUP[PoPA%PKP[PQPAPLP[PWPAPfP[PcPAPiP[%1B#7#lRB#=,`APQ%\2#4#5P[PQPQ%\2#B#5RiP[PQPQ%|2#O#B#5RcPY%1u#g#g#@PQ%\2#A#5P[Q05PQ%\2#3#5RuP[PIPQP=PY%@>PAQ07P[PQPAPRP[PQPA%7mRmP[PQPAPBP[PQPAQ02P[PQPAPEP[%7l#lRl#=,`AREPAPqP[g00WZPXPPP[H0BRqPAPhP[Q0@PAPgP[Q0?PAPaP[Q0>PAP`P[Q0=PA%PyP[Q09PAPGP[PoPA%7{P[%12#7#8#A#G#[PAPxP[PEPA%P_P[PqPAPmP[Q0:PAQ04P[%M]PAPNP[%M\PAPlP[PvPAPFP[Q0<PAQ06P[Q0;PA%7}P[Q08PAPTP[%}2#X#n#I#[%;J-0AA%:s#N#N#N#5Rs%7~#N#N#55vA20@Az%;z'{%MX%>|#N#N#57vs%F^#N#5,YQ%F2#6#N#5'{1z@=%32#D#>#8Pi%32#D#G#:Q0A%32#D#G#3Pb%32#D#D#6Pu%32#D#O#>Pc%32#D#3#D%|2#A#X#5%32#O#C#>#q%32#O#G#3#q%02#6#O#G#3#q%c2#B#X#X#5%02#6#3#B#3%]2#4#:#APQ%c2#B#X#I#5RcP[%=cPQ%c2#B#I#4#5PY%MZRZ%02#6#O#A#B%c2#B#I#X%02#6#O#I#3%c2#4#:#B%02#6#3#:#3%c2#4#:#8%02#6#3#B#>%12#6#3#6#:1YQn@0?CX%F2#G#D#O#:%]2#4#E#C#5'z%12#6#A#8#6#q%12#6#A#8#>%12#6#A#8#3%]2#4#E#3%12#6#A#C#>%]2#4#E#I#5RCPQPCP[%;wRw#=%12#6#A#>#:%]2#4#8#8%12#6#I#C#6%]2#8#N%;t9vZp1VPw%u53m3b3bD?3y3b3x3m7yn5xj3b3b3bD?D?3bI0>DtDtDt3m3m3mDLDSDSDSD?D?DQDSD<D<D<D<DSDSDSDSDSD<D<D<D?DQD<D<D?D?D?D?D?D?D<DLDLD<D<DWD<DWDLD?DWDWD?D<DQDWDQD<DQDWDQDWDQDLDQD<DLDWDLDQDLDQDLD<DLD<DWD?D?D?N<0=,w;Rj;JjRn1e11R5/e1RwP5P1P1P1P?P=CUQ01CUR=;J=R?1e44RP/e4RZPPP4P4P4PIQ03CUPQCURQ;JQRI%C2#D#8#D$0<=K70R0=J30R2'HRp'HRt'HR['HRC,H8RX,H8RY,H8Rc,H81f39RuP8PcPuP8PYPuP8PXPuP8PCPuQ00P[1f36PnPt1f<jP?Pp1fw=PIP21fZQ1f30CsFpFpFpFpP31e:7R:g00X:R2g00YF3ZRI,_7#a1^7I5K7P9P3g00Z?9Z:2RI,_7#a1^7I5K7P9P3g00[89Z:2RI,_7#a1^7I5K7P9P3g00\19Z:2RI,_7#a1^7I5K7P9P3g00\j9Z:2RI,_7#a1^7I5K7P9P3g00]c9Z:2R9,_7#a1^795K7P6P<g00^\g00_TPdg00`Ng00aHI09g00bBRd,w;PwP5P1P1P1&08d&05dCU&06dCUP=PZPPP4P4P4&07d&04dCU&0:dCUPQg00c=9Z:2R2,_7#a1^725K7=J30H0;FoFoFoFodo"). Qed.
End VP1.
