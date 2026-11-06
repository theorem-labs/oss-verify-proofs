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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs4scREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2>O2ReadErr_defs2rIC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS : list Z := [0x36a58; 0x36e5c; 0x36fe4; 0x3698c; 0x12ac0; 0x12c4c; 0x30ef0; 0x2f4d4; 0x31958]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x6b000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x49840; ELit 0; ELit 0; ELit 0;
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
   KWr (SA (ELit 0) 0x39000) 0x32000;
   KImg 0x10000 0x396f0; KImg 0x396f1 0x39739; (* [comment removed for export] *) KImg 0x49739 0x49770; KImg 0x49858 0x69868;
   KWord (SA (ELit 0) 0x49778) 8 (ELit 0x49778);
   KWord (SA (ELit 0) 0x49798) 4 (EVar 5);
   KImg 0x497a4 0x497f0; KImg 0x497f8 0x49810; KImg 0x49818 0x49830;
   KImg 0x49840 0x49850; KImg 0x69880 0x69aa8;
   KBlob (SA (ELit 0) 0x69aa8) (ELit 8) 2;
   KImg 0x69ab0 0x69ab8; KImg 0x69ac9 0x69ad0; KImg 0x69ad8 0x69ae0; KImg 0x69af0 0x69af8;
   KWord (SA (ELit 0) 0x69af8) 8 (ELit 4096);
   KImg 0x69b00 0x69b30;
   KImg 0x69ee8 0x6b000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x17844 srRE0 [] knRE0 39.
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
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x326c8 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x31d38 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x31d38 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x31d38 srH0 [] knH0 231.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x36fe4%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x36a58%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x36a58%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x36a58%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x31958%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x2f4d4%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadErr_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10PTg000Pj2lTg0010j1zTg001Pj3BTg001jj12Tg002Ij1JTg003Rj1;Tg004[j4gTg005hj2ITg0072k401Tg008?j11Tg008dj10Tg009Ij4}Tg00:Rj1LTg00;0k300Tg00<9j18Tg00<Wk10;Tg00=9j3|Tg00>Bj3sTg00?Mk40LTg00@Vk20JTg00Aak205Tg00Blk30GTg00D7j2UTg00EBm<0ETg00FKj2~Tg00Fmj4MTg00GMj2KTg00Ghj2wTg00HBj3OTg00H_j3uTg00Ihk50ATg00K0k10@Tg00L4k10?Tg00M6k10>Tg00N9k10CTg00O<k10DTg00P?k10=Tg00QAj37Tg00Qaj3bTg00Rlj4{Tg00SGk30KTg00Sdk107Tf0R0#1#0p=T%10#1#0#1p=N%00#1#0#0p=6%10#0#1#1p=H%00#0#0#8p=3g00TkR1f2R2f1R3P0CMp=S%00#1#1#1p=G%10#1#1#1p=E%00#0#1#0p=:%00#8p>0:%20#2p=k%20#2#2#2p=q%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>08%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=og00UIR4?|30p=hAu430p=Fg00V5R5?730p=P%80#;p==g00WBR6g00WbS00P3P0Cgp=v%00#0#1#1p=@%10#1#0#0#1#0#1#0#1#0p=X%00#0#0#1p=t%00#0#0#0p=5%00#1#0#1p=W%00#0p=>%00#0#0p=?%00#0#1p=e%10#0#0#0p=A%10#0#1p=d%10#0#0#1p=\%20#2#2#2#2#2#2#2p>0Og00XTR7%J2%J3=77037p=VA77309772p=j%J3=770p>09%00#Lp=p%00#1#1#0p=9%10#1#1#0p=i%10#1#1#1#1#1#1#1p=c%10#0#1#0p=Cf3R8/I2?b30p>0N%10#1#0#0p=4%10#1p>0M%10#1#0#0#1#1#0#0p=n%10#1#0#0#1#0p>06%00#0#0#0#0#0#0#0p=Q%L0,I3p>0I%83/U0p>04%10#8p=rg00Y]R9A7930772p=f%02#8%03#0#0#8'U=790p=af4R:/I8?b23=790p=<%02#8/U3=790p>03%03#8,U2=790p>021U:81U23=790579p>0F%0:#8/U8%02#8/U3=790579p=y%18#0#0#0#L,I:?b23=790p=R%L8,I:%J37b2=790p=`%08#L,I:?b23=790p=Z%L8,I:?b23=790p=D%L8,I:%83#;7b2=790p=_P7P7P3P0CMp=xP:P81w23P0C{p=[f6R;f5R<P:P8P2P3P0C{C{p>0Bg00ZhR=?O30p=]B0K=30p=YP1P2&073P0CMp=^AO=30$07p>0<P1P8P2P3CM=B:0p>0HAB;<:AB823/K0'Kp=m&0P5R0,l1R8g00\6R3#T#N#6#H#3R2%z5R55S0R<;B<R;%H3#G#E#:$0:=S05R:=B8:S01g00\[R>g00];S02g00]mR?#2R@#2RA#kRB#2RC#2#kRD#k#qS03#2RE#qRF#2RG#2S04#2S05#2S06#kS07#2S08#2S09#2RH#2RI#2RJ#2RK#2RL#2RM$08#o#oRN#JROg00^LRP#;RQ'hRRPOCg%JARS/FO/IPP@P>PQH01/P5'P9S02RT=B8TS0:%13RU#1RV#1RW#0RX#1#=RY/vOP6g00^jS0;P6P?PBPOC}1hRQCg/P5'P9S02RZ=B8ZS0<g00_\R[%L3#;R\<00O/FY%83R]#;R^'v/P59S02R_=B8_S0=%T3#@#:#H#3=S05R`=B8`S0>g00`HRa$0;Rb%X3#t#3Rc%03Rd#8S0?%T3#6#5#W#3Re%J?Rf%0dRg#0Rh#1Ri#1Rj#0Rk#>S0@#0S0A#LS0B#;'FRl1FfO%0hRm#1Rn#1Ro#1Rp#>S0C#L#;Rq'FRrPl%1dRd#0Rs#?S0D#=S0EPQPQ%1gRg#0Rt#0Ru#0Rv#0S0F#0S0G#0Rw#LRx#;,FfRy%kN#q$08#o#o#oRN%;e%0nS0H#>S0I#>S0J#>#5#=%e3#@#5#A#3Rn#;%2N#qRz%2zRz%2zRz%;cR{1hQRRR%1gRg#='hR|,h^%qzRz#J%2zRz%2zRz%2zRz%2zRz%2zRz%2zRz%d3#@#W#W#3R}#;R~%T3#\#E#5#A#=%2z#k$0ORz%2zRz%2zRz%2z%z73V3V9VLM9VJK9VHI7jQ7j^3V3V3V5jQ3j+093V3j7jy+09PQ%X3#W#3S0KPD%?XS0L#p#;,FfRXPQ%X3#9#3PDPlPQ%X3#A#3S0MPDPlPf%1uRuPD%1jRj#0RI#1#5#i#=Pf%5uPDP{PfPvPDP|PfPwPDg00aQ%1WRW#1Rw#1Rv#1#cR{#1Ru#1#ERH#1#cRK#=RJ;||PfPjPDPJPf%>IRIPD%1tRt#=PfPkPD%13#:#t#E#A#=Pf%0iRi#1RkPDPQPf%0iRi#0RJ#0Rj#0R|PDPRPf%?kRkPDPOPfQ0APD%0mRR#0RM#1RL#1Rz#G#C#=PfPiPDPQ%8u9sOPPf%?w#pPDPSH0NPfPxPD%1s#>#pRs#;,FfPf%TpP@PRPfP|PA%0URU#1R|#1Rp#T#9#EPfPkPD%1z#:#9#E#G#:#G#:#9#W#:#5#9#6PfQ0BPD%0URU#>Rz#1#9#W#G#:#:#5#@#C#9#\#9#4#9#@#=PfQ0CPD%1K$0MRK#>#n#n#n#N#=Pf%5oPD%1K#E#cRK#0#c#cPf%?vPD%1URU#1#>#4#n#nPf%1RRR#5PD%?tRt#A#\Pf%>MRM#>RvPDP~Pf%?LPDPQPfPRPDPyPfQ0HPDPXPfQ0JPD%1g#>#pRX#;,FfPQ%X3#@#3PDPQPQ%X3#:#3RyPDPQPQ&063#H#:#3RRPB%1K#c#c#=PQ%X3#N#3PDQ0EPQ%X3#4#3RKPDPlPQPcPB%=dPfQ0GPDPQPfPtPDPQPf%?gRgPDPQPfPXPDPQPfQ0@PDPQPfPIPD%1dRd#?#pRI#;,FfRXPfPjPDP>PAPPPDH0LRjPfQ0IPDQ09PfPMPDQ08Pf%?WPDQ07PfQ0LPDPSPf%0VRVPD%JEPf%0VRV#?PDP~Pf%?pPD%13#t#H#9#6Pf%5|PDPXPf%?UPDPjPfPgPDQ04PfQ0DPD%JGPfPsPD%JFPfPIPDPSPfPJPDQ06PfQ0FPDQ05Pf%>zPDQ03PfPdPD%G3#A#G#4#=%8m-0Jf%5{#Q#Q#Q#3R{%>vRv#5Rm#?#5Rd#0Rz#5#Q#Q#35sf20Ifd%8d+05%Az#Q#Q#39sS{%TV#Q#3,IQ%T3#6#Q#3+05204mc%43#C#A#9Py%43#C#\#5Q0K%43#C#\#4Q0M%43#C#C#6PK%43#C#H#APR%43#C#4#C&063#N#i#3%43#H#G#A#r%43#H#\#4#r%03#6#H#\#4#r%e3#:#i#i#3%03#6#4#:#4%d3#@#5#NPQ%e3#:#i#E#3RRPD%;RPQ%e3#:#E#@#3PB%JCRC%03#6#H#N#:%e3#:#E#i%03#6#H#E#4%e3#@#5#:%03#6#4#5#4%e3#@#5#9%03#6#4#:#A%13#6#4#6#51IQ}%=h<0GA%T3#\#C#H#5%d3#@#W#G#3+04%13#6#N#9#6#r%13#6#N#9#A%13#6#N#9#4%d3#@#W#4%13#6#N#G#A%d3#@#W#E#3RAPQPAPD%8vRv#;%13#6#N#A#5%d3#@#9#9%13#6#E#G#6%d3#9#Q%8H9sC]1UPv%z93f3a3aD<4033a4023f803}602n3a3a3aD<D<3aI0FDyDyDy3f3f3fDRD`D`D`D<D<DZD`DDDDD_DDDRDDD`D`D`DDDDDDD<DZDDDDD<D<D<D<D<D<DDDRDRDDDDD_D_D_DZD<D_D_D_D<3fDRDZDZDZDRDRDZDRDZDRDDDRD<D<D<N<0E,~aRn;BnR}1l11R9/l1RvP9P1P1P1PePcCMQ0?CMRc;BcRe1l77RC/l7R]PCP71xlrPQCMRr;BrRH%G3#C#9#C$0:=S05R3=B83RD'KRA'KRh'KRR'KRK'KRy'KRm'KRV'KR{,K;1w8<RzP;P{PzQ01PVP8P:Q0:PmP8PTQ0<PyP8PZQ0=PKP8P_Q0>PRP8P`P}PhPbPnPePAPvPcPHPDP]Pr1w83D[D[D[D[D[D[D[D[K0BP81l=0R=g00b=Rrg00cI3ORD,]01Y0D5^0P<P8g00dB9O=rRD,]01Y0D5^0P<P8g00e;9O=rR<,]01Y0<5^0P:P8g00f49O=rR:,]01Y0:5^0P>Q02g00fmR:=|4QR<P:CgAu4S:/IPP@P>PQH01/P5'P9S02P8g00gf9O=rR>,]01Y0>5^0P6Q00PYP:CgP6Q0;P6P?PBP:C}1h<QCg/P5'P9S02P8g00h_9O=rR<,]01Y0<5^0B00[\:/FY/v^/P59S02P8g00iX9O=rR2,]01Y025^0P`Pbg00jQg00kIPNg00lCg00m=I0Ag00n7RN,~aPvP9P1P1P1&0@N&0?NCM&0>NCMPcP]PCP7&0CN&0DN'x&0=NCMPCP7Au4f:/Fq,xlPQCMP8P0g00o29O=rRr-0<01Y0rP3I0HFmFmFmFmFmdo"). Qed.
End VP1.

