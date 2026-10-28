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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond06K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03C6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lK47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K4ELinuxProcessSemantics5Riscv5Instr5aluop02I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rBc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rCc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rDc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rEc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2PXc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rFc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rGc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rHC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs3srHc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs3knHc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs4scREc5ARocqVerifyHarness?AgentSubmission3V23?V23ReadErr_defs2rI".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS : list Z := [0x11e154; 0x11e6d4; 0x11ec28; 0x11e058; 0x12a64; 0x12bf0; 0x10fefc; 0x10e4e0; 0x1139cc]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x159000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x1381d0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=   (* [comment removed for export] *)
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0x127000) 0x32000;
   KImg 0x10000 0x127ec0; KImg 0x127ec1 0x127f09; (* [comment removed for export] *) KImg 0x137f09 0x138100; KImg 0x1381e8 0x1581f8;
   KWord (SA (ELit 0) 0x138108) 8 (ELit 0x138108);
   KWord (SA (ELit 0) 0x138128) 4 (EVar 5);
   KImg 0x138134 0x138180; KImg 0x138188 0x1381a0; KImg 0x1381a8 0x1381c0;
   KImg 0x1381d0 0x1381e0; KImg 0x158210 0x158440;
   KBlob (SA (ELit 0) 0x158440) (ELit 8) 2;
   KImg 0x158448 0x158450; KImg 0x158461 0x158468; KImg 0x158470 0x158478; KImg 0x158488 0x158490;
   KWord (SA (ELit 0) 0x158490) 8 (ELit 4096);
   KImg 0x158498 0x1584c8;
   KImg 0x158890 0x159000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x6336c srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
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
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x115280 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x1143c4 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x1143c4 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x1143c4 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Section VP1.
Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x11ec28%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x11e154%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x11e154%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x11e154%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x1139cc%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x10e4e0%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadErr_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10RTg000Pj2lTg0010j1{Tg001Pj3DTg001jj10Tg002Oj12Tg002nj1HTg0047j1=Tg005@j4dTg006Mj2ITg007Wk402Tg008dj11Tg009Ik400Tg00:Rj1OTg00;0k305Tg00<9j19Tg00<Wk10QTg00=9j3|Tg00>Bj3tTg00?Mk40LTg00@Vk20KTg00Aak207Tg00Blk30FTg00D7j2UTg00EBm<0CTg00FKk201Tg00Fmj4LTg00GMj2KTg00Ghj2wTg00HBj3MTg00H_j3zTg00Ihk50ATg00K0k10@Tg00L4k10?Tg00M6k10DTg00N9k10>Tg00O<k10=Tg00P?k10HTg00QAj37Tg00Qaj3hTg00Rlj4uTg00SGk30;Tg00Sdj1~Tf0R0#0#0#0p=<%10#1#1#1p=C%00#0#0#0p=3%10#0#1#0p=G%00#9p>09g00TkR1f2R2f1R3P0CLp=N%00#0#1#1p=;%10#1#0#1p=k%10#0#0#0p=6%00#1#0#1p=q%00#0#0#9p=:%20#2p=i%20#2#2#2p=o%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>08%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=ng00UIR4?|30p=fAz430p=Fg00V5R5?730p=Q%90#=p=Ag00WBR6g00WbS00P3P0Cdp=v%10#0#0#1p=5%10#1#0#0p=4%10#1#1#0p=J%00#1#1#0p=E%00#0#1#0#0#1#1#1#1p=T%00#0#1#0p=@%00#1#1#1p=S%00#0p=B%00#0#9#=p=[%10#0#1#1p=R%00#1p>0P%20#2#2#2#2#2#2#2p>0Og00XTR7%H2%H3=77037p=VA77309772p=j%H3=770p>0:%00#Op=p%10#0p=}%10#1#1#1#1#1#1#1p=bf3R8/I2?h30p>0N%00#1#0#0p=>%00#0#0#1p=s%10#1p>0M%00#0#0#0#0#0#0#0p=a%00#0#0#0#0#0#0#9p=g%O0,I3p>0J%00#0#1#0#0p>0G%93/U0p>06%00#0#1#0#0#1#1p=Z%10#9p=r%00#0#1p=e%00#1#0p=\g00Y]R9A7930772p=c%02#9%03#0#0#9'U=790p=`f4R:/I8?h23=790p=?%02#9/U3=790p>04%03#9,U2=790p>031U:81U23=790579p>0E%0:#9/U8%02#9/U3=790579p=y%18#0#0#0#O,I:?h23=790p=P%O8,I:%H37h2=790p=_%08#O,I:?h23=790p=Y%O8,I:?h23=790p=8P7P7P3P0CLp=xP:P81w23P0Cup=Wf6R;f5R<P:P8P2P3P0CuCup>0Bg00ZhR=?M30p=]B0;=30p=XP1P2%~3P0CLp=^AM=30#~p>0<P1P8P2P3CL=D:0p>0IAD;<:AD823/K0'Kp=m&0R5R0,l1R8g00\6R3#<#C#3#G#G$09R2%{5R55N0R<;D<R;%03#;#k#6#q#:=N05R:=D8:S01g00\[R>g00];S02g00]mR?#2R@#2RA#iRB#2RC#2#iRD#i#oS03#2RE#oRF#2RG#2S04#2S05#2S06#iS07#2S08#2S09#2RH#2RI#2RJ#2RK#2RL#2RM$08#n#nRN#HROg00^LRP#=RQ'fRRPOCd%HARS/FO/IPP@P>PQH02/Q5'Q9N02RT=D8TS0:%13RU#1RV#1RW#0RX#1#ARY/vOP6g00^jS0;P6P?PBPOH001fRQCd/Q5'Q9N02RZ=D8ZS0<g00_\R[%O3#=R\<05O/FY%93R]#=R^'v/Q59N02R_=D8_S0=%<3#5#4#J#E$09=N05R`=D8`S0>g00`HRa$0QRb%T3#5#6#:Rc%03Rd#9S0?%03#@#5#S#4#:Re%H?Rf%0dRg#0Rh#1Ri#1Rj#0Rk#BS0@#0S0A#OS0B#='FRl1FfO%0hRm#1Rn#1Ro#1Rp#BS0C#O#=Rq'FRrPl%1dRd#0Rs#<S0D#AS0EPQPQ%1gRg#0Rt#0Ru#0Rv#0S0F#0S0G#0Rw#OS0H#=,FfRx%iN#o$08#n#n#nRN%=e%0nS0I#BS0J#BS0K#0Rn#<#[%03#S#3#;#G#:Ry#=%2N#oRz%2zRz%2zRz%=cR{1fQRRR%1gRg#A'fR|,f^%ozRz#H%2zRz%2zRz%2zRz%2zRz%2zRz%2zRz%03#R#3#6#6#:R}#=R~&0P3#E#@#@#4#[%2z#i$0ORz%2zRz%2zRz%2z%{73V3V9VLM9VJK9VHI7jQ7j^3V3V3V5jQ3j+0:3V3j7jx+0:PQ%T3#5#4#:RIPD%<XRX#p#=,FfRHPQ%T3#5#k#:PDPlPQ%T3#5#C#:RKPDPlPf%1uRuPD%}3#J#;#R#[Pf%3uPDP{PfPvPDP|PfPwPDg00aQ%1WRW#1Rw#1Rv#1#bR{#1Ru#1#CRJ#1#bRM#ARL;||Pf%1jRjPDPLPf%<jRjPD%1tRt#APfPkPD%B3#q#;#E#4#[Pf%0iRi#1RkPDPQPf%0iRi#0RL#0R|#0RzPDPRPf%<kRkPDPOPfQ0APD%1n#G#APfPiPDPQ%9u9tOPPf%<w#pPDPSH0NPfQ0HPD%1s#B#pRs#=,FfPf%}pP@%0mRp#APfPzPA%0URU#1Rz#1Rw#}#E#C#APfPkPD%0pRk#1RO#4#5#R#k#4#5#4#5#5#>#6#s#5#[PfQ0BPD%0URU#BRu#1#E#q#S#@#@#3#;#G#E#5#E#4#E#;#APfQ0CPD%1M$0MRM#B#4#4#4#4#4#4#k#APf%3oPD%1M#C#bRM#0#b#b#APf%<vPD%1URU#1#;#;#;#;#;#[Pf%1pRp#3PD%<tRt#6#5#APf%BkRk#BRvPDP~Pf%<OPDPQPfPpPDPxPfQ0IPDPHPfQ0KPD%1g#B#pRH#=,FfPQ%T3#5#G#:PDPQPQ%T3#5#5#:RxPDPQPQ%T3#G#5#:RpPB%1M#b#b#APQ%T3#G#>#:PDQ0EPQ%T3#G#;#:RMPDPlPQPcPB%AdPfQ0GPDPQPfPtPDPQPf%<gRgPDPQPfPHPDPQPfQ0@PDPQPfPjPD%1dRd#<#pRj#=,FfRHPfP|PDP>PAPPPDH0LR|PfQ0JPDQ09PfPkPDQ08Pf%<WPDQ07PfPXPDPSPf%0VRVPD%HEPf%3VPDP~Pf%<wPD%B3#>#J#C#E#[Pf%3zPDPHPf%<URUPDP|PfPgPDQ04PfQ0DPD%HGPfPsPD%HFPfPjPDPSPfPLPDQ06PfQ0FPDQ05Pf%BuPDQ03PfPdPD%63#4#J#5#[%9m-0Kf%a{#a#a#gR{%BvRv#3Rm#<#3Rd#0Ru#a#a#g5tf20Jfd%9d+07%6u#3#a#g9tS{&0G3#J#3#g,IQ%<U#g+07206mc%Z3#J#E#@Px%Z3#J#E#4PI%Z3#J#S#6PK%Z3#J#6#3PM%Z3#J#5#>Pp%Z3#J#G#E%T3#k#6#:%Z3#C#E#3#r%Z3#C#6#>#r%e3#R#C#6#>#r%03#S#3#@#g%e3#4#3#C#>%03#R#3#;#CPQ%03#S#3#@#s#:RpPD%=pPQ%03#S#3#@#q#:PB%HCRC%e3#4#3#5#G%03#S#3#;#3%e3#4#3#4#>%03#S#3#;#>%e3#4#3#k#>%03#S#3#;#6%e3#4#3#C#3%\3#4#s#3#61IQ}%Ah<0FA%q3#6#>#>#6%03#R#3#6#G#:+06%\3#4#@#;#3#r%\3#4#@#;#>%\3#4#@#;#6%03#R#3#6#C%\3#4#@#>#>%03#R#3#5#@#:RAPQPAPD%9vRv#=%\3#4#@#>#4%03#R#3#5#5%\3#4#>#>#6%03#R#@#a%9J9tC]1UPv%{93c3`3`D?4043`4033c804}603y3`3`3`D?D?3`I0EDyDyDy3c3c3cDPD_D_D_D?D?DYD_D8D8D8D8DPD8D_D_D_D8D8D8D?DYD8D8D?D?D?D?D?D?D8DPDPD8D8D8D8D8DYD?D8D8D8D?3cDPDYDYDYDPDPDYDPDYDPD8DPD?D?D?N<0C-01aRy;DyR}1l11R9/l1RvP9P1P1P1PePcCLQ0?CLRc;DcRe1l77RC/l7R]PCP71xlrPQCLRr;DrRJ%03#s#4#5#4#:=N05R3=D83RD'KRA'KRh'KRp'KRM'KRK'KRI'KRx'KRm,K;1w8<RUP;PmPUQ01PxP8P:Q0:PIP8PTQ0<PKP8PZQ0=PMP8P_Q0>PpP8P`P}PhPbPyPePAPvPcPJPDP]Pr1w83DWDWDWDWDWDWDWDWK0BP81l=0R=g00b=Rrg00cI3MRD,]01X0D5^0P<P8g00dD9M=rRD,]01X0D5^0P<P8g00e?9M=rR<,]01X0<5^0P:P8g00f:9M=rR:,]01X0:5^0P>Q02g00g5R:=|4QR<P:CdAz4S:/IPP@P>PQH02/Q5'Q9N02P8g00h09M=rR>,]01X0>5^0P6Q00PYP:CdP6Q0;P6P?PBP:H001f<QCd/Q5'Q9N02P8g00hk9M=rR<,]01X0<5^0B05[\:/FY/v^/Q59N02P8g00if9M=rR2,]01X025^0P`Pbg00jag00k\PNg00lYg00mUI0Ag00nQRN-01aPvP9P1P1P1&0@N&0?NCL&0DNCLPcP]PCP7&0>N&0=N'x&0HNCLPCP7Az4f:/Fq,xlPQCLP8P0g00oN9M=rRr-0<01X0rP3I0IFmFmFmFmFmdo"). Qed.
End VP1.

