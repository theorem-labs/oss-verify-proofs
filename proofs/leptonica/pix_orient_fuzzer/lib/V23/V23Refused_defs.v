(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23ReadErr_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Refused_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K47Corelib7Numbers7BinNums8positive03I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rBc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rCc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rDc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rEc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rFc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rGC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs3srGc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs3knGc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs4scRFc5ARocqVerifyHarness?AgentSubmission3V23?V23Refused_defs2rH".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x63388 srRF0 [] knRE0 39.
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
Definition ssC0 : sym_state := SS 0x1143c4 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x1143c4 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x1143c4 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x1143c4 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x1143c4 srG0 [] knG0 199.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x1139cc%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x10e4e0%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Refused_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10FTg000Pj2iTg0010j1vTg001Pj3JTg001jk10ETg002Lj10Tg0031j1=Tg003Oj1LTg004Xj11Tg005=j1QTg005[j1@Tg006dj12Tg007Ck40CTg008Lk20BTg009Wj3wTg00:bk200Tg00;mj2UTg00=7k30?Tg00>Bj2TTg00?Mm<0=Tg00@Vj2zTg00A8j4PTg00AXj2ITg00B3j2dTg00BMj4tTg00Bhj3XTg00CEj1\Tg00DLk50<Tg00ETk10;Tg00FXk108Tg00GZk109Tg00H]k10:Tg00I`k107Tg00Jck106Tg00Kek304Tg00Lnj3;Tg00MNj3hTg00NYk303Tf0R0#0#0#0p=E%10#1#1#1p=D%00#0#0#0p=3%10#0#1#0p=F%00#=p=}g00O6R1f2R2f1R3P0CPp=N%10#0#0#1p=9%10#1#0#0p=4%10#1#1#0p=O%00#1#1#0p=?%00#0#1#0#0#1#1#1#1p=M%10#0#0#0p=5%00#0#0#=p=>%00#0#1#0p=B%00#1#1#1p=<%00#0p=:g00OT@0430p=[%00#Qp=k%=0#@p=7%20#2p=l%20#2#2#2p=n%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=p%00#0#1#1p=6%10#0#1#1#0#0#0#0p=W%00#1#0#1p=V%20#2#2#2#2#2#2#2p>02g00P@R4%L2%L3=;403;p=SA;4309;42p=c%L3=;40p>01%10#1#0#1p=Z%10#0p=b%00#1#0#0p=8%00#0#0#1p=a%10#1#1#1#1#1#1#1p=j%10#1p=y%00#1p>0D%10#1#0#0#1#1#0#0p=o%10#0#1#1p=x%00#0#0#0#0#0#0#0p=g%00#0#0#0#0#0#0#=p=f%Q0,U3p>0A%00#0#1#0#0p>0@%=3/T0p=~%00#0#1#0#0#1#1p=Y%10#=p=r%00#0#1p=e%00#1#0p=`g00QIR5A;5307;2p=m%02#=%03#0#0#='T=;50p=_f4R6f3R7'U?h23=;50p=A%02#=/T3=;50p=|%03#=,T2=;50p={1T671T23=;505;5p>0>%06#=/T7%02#=/T3=;505;5p=u%17#0#0#0#Q,U6?h23=;50p=H%Q7,U6%L37h2=;50p=R%07#Q,U6?h23=;50p=K%Q7,U6?h23=;50p=C%Q7,U6%=3#@7h2=;50p=Gf6R8f5R9P6P7P2P3P0CtCtp=qg00RTR:?X30p=^B03:30p=]AJ723/I0p>05AJ896AJ723/I0'Ip=sg00SbR0$0FR7,i1R3g00ToR2#E#D#3#F#F#}%v0R05N7R9;J9R8%E2#9#4#O#?#}=N70R6=J36S00g00UTR;$0ER<%M2#9#5#>R=%02R>#=S01%02#B#9#<#4#>R?g00V]R@#LRA%0>RB#0RC#1RD#1RE#0RF#:S02#0RG#QRH#@'[RI%0CRJ#0RK#1RL#0RM#1#k#@,[AS03PI%1>R>#0RN#0RO#:S04#7S05g00W<RP#@RQPQ%1BRB#0RR#0RS#0RT#0S06#0S07#0RU#QRV#@,[ARW%2@R@#2RX#lRY#2RZ#2#lR[#l#nS08#2S09#nR\#2R]#2S0:#2S0;#2S0<#2S0=#2S0>#2S0?#2S0@#2R^#2R_#2R`#2Ra#2Rb#2Rc#l#n#p#p#p#p#pRd%@?%1JRe#0Rf#0Rg#0Rh#:Ri#0Rj#0#3#7%02#<#3#6#F#>Rk#@%2d#nRl%2lRl%2lRl%@=Rm%1BRB#0Rn#7%nlRl#L%2lRl%2lRl%2lRl%2lRl%2lRl%2lRl%02#W#5#5#>Ro#@Rp%=2Rq#@%V2#5#5#W#7%2l#l$02Rl%2lRl%2lRl%2l%v43S3S9Sbc9S`a9S^_7cQ3c3S3S3S5cQ3c+013S3c7cW+01PQ%M2#9#4#>R_P[%12R^#1Ra#1R`#3Rc#k#@,[ARbPQ%M2#9#Z#>P[PIPQ%M2#9#D#>RlP[PIPA%bgP[%1O#b#8#?#V#<#6#<#V#?#?#?#V#<#BPA%1eRe#0RO#bP[%0KRK#0Rg#1Rr#0#4#<#6#?#V#<#8#<#9#?#B#B#3PA%1SRSP[%<2#4#Z#a#7PA%3SP[PmPAPTP[%1>RT#0Rm#7PAPUP[%1`R`#1RU#1RS#1#jRs#y#DRt#DRu#0#9#7PA%1EREP[%1u#DRu#7PA%EEREP[%1RRR#7PAPFP[%a2#8#Z#W#7PA%0DRD#0RF#0Rv#bP[%0^R^#1Rw#:Rx#:Ry#y#?#6#5#6#5#6#3#6#a#6#<#6#?PA%1DRDP[PQPA%0vRz#:P[%7CRCPA%EDRDP[PCPA%0aRa#1R{#1R|P@%1wRw#0R}#7R~PAPGP[%1j#F#7PA%0|R|#1Rj#1RG#1P@%1wPAPGP@%0^R^#0RG#1#7PA%0jRj#1P@%0GRGPAPjP@%:aRa#7RjPA%0|R|#1Rw#1P@PjPAPwP@P~PA&0D|P@PxPA%1F#:RFP[PQPA%3UP[%0gRg#:RU#:Rx#3R@#E#3R|#0R~#:Rw#7RjPAPVP[%1N#:#kRN#@,[APAPFPX%1r#ZPAPDPY%E`R`#b#3#<#8#<#VPAPHP[%:aRa#1#b#O#?#9#B#3#6#F#?#9#?#4#?#6#7PAPeP[%1u#yRu#:#o#o#o#Z#7PA%EOP[%1u#D#jRu#0#j#jPA%ESP[%1^R^#1#:#4#o#oPA%EMP[%ERRR#5#9PAPUP[PpPAPKP[PQPAPLP[PWPAPfP[PbPAPiP[%1B#:#kRB#@,[APQ%M2#9#F#>P[PQPQ%M2#9#9#>RiP[PQPQ%M2#F#9#>RbPY%1u#j#j#7PQ%M2#F#8#>P[Q05PQ%M2#F#6#>RuP[PIPQP=PY%7>PAQ07P[PQPAPRP[PQPA%:nRnP[PQPAPBP[PQPAQ02P[PQPAPEP[%:m#kRm#@,[AREPAPzP[g00WZPXPPP[H0CRzPAPhP[Q0@PAPgP[Q0?PAP`P[Q0>PAPcP[Q0=PA%E{P[Q09PAPaP[PpPA%:}P[%a2#6#x#Z#5PAPyP[PEPA%E^R^P[PzPAPnP[Q0:PAQ04P[%L]PAPNP[%L\PAPmP[PjPAPvP[Q0<PAQ06P[Q0;PA%:GP[Q08PAPTP[%b2#6#6#F#8#7%=J-0BA%gs#g#g#fRs%:w#3#g#f5wA20AA|%=|+00%LX%5~#3#g#f7ws&0@2#O#3#f,UQ%E^#f+001~@=%Y2#O#?#BPi%Y2#O#?#4P_%Y2#O#<#5Pl%Y2#O#5#3Pu%Y2#O#9#8Pb%Y2#O#F#?%M2#Z#5#>%Y2#D#?#3#r%Y2#D#5#8#r%e2#x#D#5#8#r%02#<#3#B#f%e2#4#3#D#8%02#W#6#DPQ%02#<#3#B#a#>RbP[%@bPQ%02#<#3#B#V#>PY%LZRZ%e2#4#3#9#F%02#<#3#6#3%e2#4#3#4#8%02#<#3#6#8%e2#4#3#Z#8%02#<#3#6#5%e2#4#3#D#3%`2#4#a#3#51UQo@0?CX%V2#5#8#8#5%02#W#5#F#>'~%`2#4#B#6#3#r%`2#4#B#6#8%`2#4#B#6#5%02#W#5#D%`2#4#B#8#8%02#W#9#B#>RCPQPCP[%=xRx#@%`2#4#B#8#4%02#W#9#9%`2#4#8#8#5%02#x#B#g%=t9wZq1TPx%v53m3_3_DA3|3_3{3m7|o5{k3_3_3_DADA3_I0>DuDuDu3m3m3mDHDRDRDRDADADKDRDCDCDGDCDRDRDRDRDRDCDCDCDADKDCDCDADADADADADADCDHDHDHDCDGDGDGDHDADGDGDADCDKDGDKDCDKDGDKDGDKDHDKDCDHDGDHDKDHDKDHDCDHDGDGDADADAN<0=,z;Rk;JkRo1i11R5/i1RxP5P1P1P1P?P=CPQ01CPR=;J=R?1i44RP/i4RZPPP4P4P4PIQ03CPPQCPRQ;JQRI%02#a#4#9#4#>=N70R0=J30R2'IRq'IRt'IR['IRC,I8RX,I8RY,I8Rb,I81d39RuP8PbPuP8PYPuP8PXPuP8PCPuQ00P[1d36PoPt1d<kP?Pq1dx=PIP21dZQ1d30CtFqFqFqFqP31i:7R:g00X:R2g00YF3XRI,^7#\1]7I5N7P9P3g00ZA9X:2RI,^7#\1]7I5N7P9P3g00[<9X:2RI,^7#\1]7I5N7P9P3g00\79X:2RI,^7#\1]7I5N7P9P3g00]29X:2RI,^7#\1]7I5N7P9P3g00]m9X:2R9,^7#\1]795N7P6P<g00^hg00_cPdg00``g00a\I0<g00bXRd,z;PxP5P1P1P1&0;d&08dCP&09dCPP=PZPPP4P4P4&0:d&07dCP&06dCPPQg00cU9X:2R2,^7#\1]725N7=J30H05FsFsFsFsdo"). Qed.
End VP1.
