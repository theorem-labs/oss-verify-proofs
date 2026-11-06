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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs4scREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23ReadErr_defs2rIC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS : list Z := [0x109cb0; 0x10a230; 0x10a784; 0x109bb4; 0x12a64; 0x12bf0; 0xfba58; 0xfa03c; 0xff528]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x145000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x123d20; ELit 0; ELit 0; ELit 0;
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
   KWr (SA (ELit 0) 0x113000) 0x32000;
   KImg 0x10000 0x113a10; KImg 0x113a11 0x113a59; (* [comment removed for export] *) KImg 0x123a59 0x123c50; KImg 0x123d38 0x143d48;
   KWord (SA (ELit 0) 0x123c58) 8 (ELit 0x123c58);
   KWord (SA (ELit 0) 0x123c78) 4 (EVar 5);
   KImg 0x123c84 0x123cd0; KImg 0x123cd8 0x123cf0; KImg 0x123cf8 0x123d10;
   KImg 0x123d20 0x123d30; KImg 0x143d60 0x143f90;
   KBlob (SA (ELit 0) 0x143f90) (ELit 8) 2;
   KImg 0x143f98 0x143fa0; KImg 0x143fb1 0x143fb8; KImg 0x143fc0 0x143fc8; KImg 0x143fd8 0x143fe0;
   KWord (SA (ELit 0) 0x143fe0) 8 (ELit 4096);
   KImg 0x143fe8 0x144018;
   KImg 0x1443e0 0x145000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x62d48 srRE0 [] knRE0 39.
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
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x100ddc srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xfff20 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xfff20 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xfff20 srH0 [] knH0 231.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x10a784%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x109cb0%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x109cb0%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x109cb0%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xff528%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xfa03c%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadErr_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10QTg000Pj2kTg0010j10Tg001Uj1zTg0025j3CTg002Oj12Tg002nj1HTg0047j1;Tg005@j4eTg006Mj2GTg007Wk405Tg008dj11Tg009Ik403Tg00:Rj1NTg00;0k306Tg00<9j19Tg00<Wk10=Tg00=9j3~Tg00>Bj3uTg00?Mk40NTg00@Vk20MTg00Aak20:Tg00Blk30KTg00D7j2UTg00EBm<0ITg00FKk204Tg00Fmj4OTg00GMj2MTg00Ghj2|Tg00HBj3PTg00H_j3vTg00Ihk50FTg00K0k10ETg00L4k10DTg00M6k10CTg00N9k10BTg00O<k10ATg00P?k10@Tg00QAj37Tg00Qaj3dTg00Rlj4{Tg00SGk30>Tg00Sdk102Tf0R0#0#0#0#1p=:%00#0#1#1p=T%10#0#0#1p=F%00#1#1#0p=I%00#0#0#9p=3g00TkR1f2R2f1R3P0COp=S%00#0#0p==%00#1#0#1p=l%10#1#0#0p=8%00#0#1#0p=?%00#9p>01%20#2p=i%20#2#2#2p=q%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0;%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=ng00UIR4?~30p=fAv430p=Eg00V5R5?730p=Q%90#;p=@g00WBR6g00WbS00P3P0Cep=w%10#1#1#1p=>%10#1#1#0p=K%10#0#1#0p=L%00#0#0#1#0#0#1#1#1#0#0#0#0p=]%00#0#0#0p=4%00#0p=D%00#1#0#0p=5%00#1#1#1p=A%10#0#0#0p=6%00#0#0#0#0#0#0#0p=J%20#2#2#2#2#2#2#2p>0Pg00XTR7%H2%H3=77037p=WA77309772p=j%H3=770p>0<%00#Np=r%10#0#1#1p>00%10#1#0#1p=R%10#1#1#1#1#1#1#1p=[f3R8/G2?d30p>0O%10#0p=p%10#1p=t%00#0#1#0#0#1#1#1p=}%10#1#0#0#1#1#0#0p=o%N0,G3p>0L%93/U0p>09%00#0#0#1#0#0#1p=\%10#9p=s%00#0#1p=h%00#1#0p=cg00Y]R9A7930772p=g%02#9%03#0#0#9'U=790p=`f4R:/G8?d23=790p=<%02#9/U3=790p>08%03#9,U2=790p>071U:81U23=790579p>0J%0:#9/U8%02#9/U3=790579p=y%18#0#0#0#N,G:?d23=790p=V%N8,G:%H37d2=790p=b%08#N,G:?d23=790p=Y%N8,G:?d23=790p=B%N8,G:%93#;7d2=790p=aP7P7P3P0COp=xP:P81|23P0C{p=Zf6R;f5R<P:P8P2P3P0C{C{p>0Hg00ZhR=?P30p=^B0>=30p=XP1P2&023P0COp=_AP=30$02p>0GP1P8P2P3CO=C:0p>0?AC;<:AC823/M0'Mp=m&0Q5R0,k1R8g00\6R3#0#:#T#F#I#3R2%z5R55S0R<;C<R;%=3#l#T#8#?$01=S05R:=C8:S01g00\[R>g00];S02g00]mR?#2R@#2RA#iRB#2RC#2#iRD#i#qS03#2RE#qRF#2RG#2S04#2S05#2S06#iS07#2S08#2S09#2RH#2RI#2RJ#2RK#2RL#2RM$0;#n#nRN#HROg00^LRP#;RQ'fRRPOCe%HARS/EO/GPP@P>PQH05/Q5'Q9S02RT=C8TS0:%13RU#1RV#1RW#0RX#1#@RY/wOP6g00^jS0;P6P?PBPOH031fRQCe/Q5'Q9S02RZ=C8ZS0<g00_\R[%N3#;R\<06O/EY%93R]#;R^'w/Q59S02R_=C8_S0=%>3#K#L#l#3=S05R`=C8`S0>g00`HRa$0=Rb%]3#:#3Rc%03Rd#9S0?%=3#4#T#F#K$01Re%H?Rf%0dRg#0Rh#1Ri#1Rj#0Rk#DS0@#0S0A#NS0B#;'ERl1EfO%0hRm#1Rn#1Ro#1Rp#DS0C#N#;Rq'ERrPl%1dRd#0Rs#=S0D#@S0EPQPQ%1gRg#0Rt#0Ru#0Rv#0S0F#0S0G#0Rw#NS0H#;,EfRx%iN#q$0;#n#n#nRN%;e%0nS0I#DS0J#DS0K#0Rn#0#4#@%03#5#A#L#5#3Ry#;%2N#qRz%2zRz%2zRz%;cR{1fQRRR%1gRg#@'fR|,f^%qzRz#H%2zRz%2zRz%2zRz%2zRz%2zRz%2zRz%03#6#A#>#?#3R}#;R~%53#5#5#J#@%2z#i$0PRz%2zRz%2zRz%2z%z73W3W9WLM9WJK9WHI7jQ7j^3W3W3W5jQ3j+0<3W3j7jx+0<PQ%]3#l#3RIPD%=XRX#r#;,EfRHPQ%]3#I#3PDPlPQ%]3#6#3RKPDPlPf%1uRuPD&003#6#L#R#@Pf%4uPDP{PfPvPDP|PfPwPDg00aQ%1WRW#1Rw#1Rv#1#[R{#1Ru#1#>RJ#1#[RM#@RL;~|Pf%1jRjPDPLPf%=jRjPD%1tRt#@PfPkPD%J3#F#4#8#@Pf%0iRi#1RkPDPQPf%0iRi#0RL#0R|#0RzPDPRPf%=kRkPDPOPfQ0APD%1n#L#@Pf%1iRi#=PDPQ%9u9uOPPf%=w#rPDPSH0OPfQ0HPD%1s#D#rRs#;,EfPf%ppP@%0mRpPfPzPA%0URU#1Rz#1Rw#p#I#>PfPkPD%0pRk#1RO#t#?#I#>#A#}#?#I#l#?#4#I#5PfQ0BPD%0URU#DRu#1#I#l#A#?#?#4#T#L#I#F#I#8#I#T#@PfQ0CPD%1M#tRM#D#o#o#o#R#@Pf%4oPD%1M#>#[RM#0#[#[Pf%=vPD%1URU#1#D#8#o#oPf%1pRp#4PD%=tRt#6#FPf%DkRk#DRvPDP~Pf%=OPDPQPfPpPDPxPfQ0IPDPHPfQ0KPD%1g#D#rRH#;,EfPQ%]3#T#3PDPQPQ%]3#?#3RxPDPQPQ%03#}#:#?#3RpPB%1M#[#[#@PQ%]3#R#3PDQ0EPQ%]3#8#3RMPDPlPQPcPB%@dPfQ0GPDPQPfPtPDPQPf%=gRgPDPQPfPHPDPQPfQ0@PDPQPfPjPD%1dRd#=#rRj#;,EfRHPfP|PDP>PAPPPDH0NR|PfQ0JPDQ09PfPkPDQ08Pf%=WPDQ07PfPXPDPSPf%0VRVPD%HEPf%4VPDP~Pf%=wPD%13#t#>#A#T#5Pf%4zPDPHPf%=UPDP|PfPgPDQ04PfQ0DPD%HGPfPsPD%HFPfPjPDPSPfPLPDQ06PfQ0FPDQ05Pf%DuPDQ03PfPdPD%p3#?#R#6#4#@%9m-0Mf%4{#J#J#J#3R{%DvRv#4Rm#=#4Rd#0Ru#4#J#J#35uf20Lfd%9d+0:%6u#J#J#39uS{%pi#J#3,GQ%p3#5#J#3+0:209mc%\3#8#4#IPx%\3#8#:#4PI%\3#8#:#8PK%\3#8#?#5PM%\3#8#T#6Pp%\3#8#5#L%03#}#5#?#3%\3#R#4#6#s%\3#R#?#8#s%h3#:#R#?#8#s%03#5#A#6#L#3%h3#:#K#F#8%03#6#A#L#FPQ%03#5#A#6$00#3RpPD%;pPQ%03#5#A#6#>#3PB%HCRC%h3#:#K#5#?%03#5#A#F#L%h3#:#K#I#8%03#5#A#F#K%h3#:#K#A#8%03#5#A#L#?%h3#:#K#F#6%c3#:#K$00#41GQ}%@h<0KA%53#T#>#F#6%03#6#A#>#5#3+09%c3#:#>#R#6#s%c3#:#>#R#8%c3#:#>#K#4%03#6#A#>#F%c3#:#>#K#8%03#6#A#>#8#3RAPQPAPD%9vRv#;%c3#:#[#5%03#6#6#4#T%c3#?#:#>#4%03#6#L#J%9J9uC]1UPv%z93g3`3`D<4083`4073g808}607y3`3`3`D<D<3`I0JDyDyDy3g3g3gDVDbDbDbD<D<DYDbDBDBDaDBDVDBDbDbDbDBDBDBD<DYDBDBD<D<D<D<D<D<DBDVDVDBDBDaDaDaDYD<DaDaDaD<3gDBDYDYDYDVDVDYDVDYDVDBDVD<D<D<N<0I-04aRy;CyR}1k11R9/k1RvP9P1P1P1PePcCOQ0?CORc;CcRe1k77RC/k7R]PCP71xlrPQCORr;CrRJ%t3#R#4#:#K$01=S05R3=C83RD'MRA'MRh'MRp'MRM'MRK'MRI'MRx'MRm,M;1|8<RiP;PmPiQ01PxP8P:Q0:PIP8PTQ0<PKP8PZQ0=PMP8P_Q0>PpP8P`P}PhPbPyPePAPvPcPJPDP]Pr1|83DZDZDZDZDZDZDZDZK0HP81k=0R=g00b=Rrg00cI3PRD,^01X0D5_0P<P8g00dD9P=rRD,^01X0D5_0P<P8g00e?9P=rR<,^01X0<5_0P:P8g00f:9P=rR:,^01X0:5_0P>Q02g00g5R:=~4QR<P:CeAv4S:/GPP@P>PQH05/Q5'Q9S02P8g00h09P=rR>,^01X0>5_0P6Q00PYP:CeP6Q0;P6P?PBP:H031f<QCe/Q5'Q9S02P8g00hk9P=rR<,^01X0<5_0B06[\:/EY/w^/Q59S02P8g00if9P=rR2,^01X025_0P`Pbg00jag00k\PNg00lYg00mUI0Fg00nQRN-04aPvP9P1P1P1&0EN&0DNCO&0CNCOPcP]PCP7&0BN&0AN'x&0@NCOPCP7Av4f:/Eq,xlPQCOP8P0g00oN9P=rRr-0G01X0rP3I0?FmFmFmFmFmdo"). Qed.
End VP1.

