(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1RwWindow U1KnCells U1MainEntry U1LibStdioCall.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs4scREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>U1ReadErr_defs2rIC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FXALL1.
Context {fx : FPState}.

Definition STOPS : list Z := [0xe2b9c; 0xe311c; 0xe36f0; 0xe2aa0; 0x12a64; 0x12bf0; 0xd56bc; 0xd1e54; 0xd70d4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0x124000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x102418; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0xef000) 0x35000;
   KImg 0x10000 0xf0200;
   KImg 0xf0201 0xf0249;
   KImg 0x100249 0x1004f0;
   KImg 0x1004f2 0x1004f8;
   KImg 0x100551 0x100558;
   KImg 0x1005b1 0x1005b8;
   KImg 0x100611 0x100618;
   KImg 0x100671 0x100678;
   KImg 0x1006da 0x1006e0;
   KImg 0x100742 0x100748;
   KImg 0x10075c 0x100760;
   KImg 0x1007e4 0x1007e8;
   KImg 0x1007fc 0x100800;
   KImg 0x100884 0x100888;
   KImg 0x10089c 0x1008a0;
   KImg 0x100924 0x100928;
   KImg 0x10093c 0x100940;
   KImg 0x1009c4 0x1009c8;
   KImg 0x1009dc 0x1009e0;
   KImg 0x100a64 0x100a68;
   KImg 0x100a7c 0x100a80;
   KImg 0x100b04 0x100b08;
   KImg 0x100b24 0x100b28;
   KImg 0x100bac 0x100bb0;
   KImg 0x100bcc 0x100bd0;
   KImg 0x100c54 0x100c58;
   KImg 0x100c64 0x100c68;
   KImg 0x100c74 0x100c78;
   KImg 0x100c84 0x100c88;
   KImg 0x100c94 0x100c98;
   KImg 0x100ca4 0x100ca8;
   KImg 0x100cb4 0x100cb8;
   KImg 0x100cc4 0x100cc8;
   KImg 0x100cd4 0x100cd8;
   KImg 0x100ce4 0x100ce8;
   KImg 0x100cf4 0x100cf8;
   KImg 0x100d04 0x100d08;
   KImg 0x100d14 0x100d18;
   KImg 0x100d24 0x100d28;
   KImg 0x100d34 0x100d38;
   KImg 0x100d44 0x100d48;
   KImg 0x100d54 0x100d58;
   KImg 0x100d64 0x100d68;
   KImg 0x100d74 0x100d78;
   KImg 0x100d84 0x100d88;
   KImg 0x100d94 0x100d98;
   KImg 0x100d9c 0x100da0;
   KImg 0x100dac 0x100db0;
   KImg 0x100dbc 0x100dc0;
   KImg 0x100dcc 0x100dd0;
   KImg 0x100ddc 0x100de0;
   KImg 0x100dec 0x100df0;
   KImg 0x100dfc 0x100e20;
   KImg 0x100e2a 0x100e30;
   KImg 0x100e3a 0x100e40;
   KImg 0x100e4a 0x100f00;
   KImg 0x100f0c 0x100f10;
   KImg 0x100f1c 0x100f20;
   KImg 0x100f2c 0x100f30;
   KImg 0x100f3c 0x100f40;
   KImg 0x1010a0 0x101100;
   KImg 0x101191 0x1011f8;
   KImg 0x10120a 0x101210;
   KImg 0x10137b 0x101ab4;
   KImg 0x101ab8 0x101ae0;
   KImg 0x101ae8 0x101af8;
   KImg 0x101afc 0x101b00;
   KImg 0x101b08 0x102348;
   KImg 0x122420 0x122440;
   KImg 0x10237c 0x1023c8;
   KImg 0x1023d0 0x1023e8;
   KImg 0x1023f0 0x102408;
   KImg 0x102418 0x102428;
   KImg 0x122458 0x122468;
   KImg 0x12246c 0x122470;
   KImg 0x122478 0x122480;
   KImg 0x122488 0x122580;
   KImg 0x122588 0x122688;
   KImg 0x122690 0x122698;
   KImg 0x1226a9 0x1226ab;
   KImg 0x1226ac 0x1226b0;
   KImg 0x1226b8 0x1226c0;
   KImg 0x1226d0 0x1226d8;
   KImg 0x1226e0 0x122710;
   KImg 0x122718 0x122820;
   KImg 0x122bc8 0x12340c;
   KImg 0x123414 0x124000;
   KWord (SA (ELit 0) 0x102350) 8 (ELit 0x102350);
   KWord (SA (ELit 0) 0x102370) 4 (EVar 5);
   KWord (SA (ELit 0) 0x122688) 8 (EVar 4);
   KWord (SA (ELit 0) 0x1226ab) 1 (ELit 0);
   KWord (SA (ELit 0) 0x1226d8) 8 (ELit 4096);
   KRange (EVar 5) 1 4194303] ++ kn_drv_cells.

Definition ssB0 : sym_state := SS 0x65a68 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.

Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
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
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

Definition ssE0 : sym_state := SS 0xd8d00 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0xd7b64 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd7b64 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

Definition ssH0 : sym_state := SS 0xd7b64 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe36f0%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xe2b9c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xe2b9c%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xe2b9c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd70d4%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xd1e54%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_U1ReadErr_defs ()) ["FXALL1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10|Tg000Pk209Tg0010k10KTg001Pj3VTg001jj12Tg002Ij1ZTg003Aj1CTg0049k405Tg0055j2TTg005nk40XTg006jj11Tg007Oj10Tg0084k40VTg008lj1gTg009Jk30UTg00:Bj16Tg00:`k10`Tg00;Bk30MTg00<:k30GTg00=4k20iTg00=nk20YTg00>hm<0yTg00?kk20^Tg00@Mj4_Tg00@mj2^Tg00AHk20QTg00Abj3eTg00B?k30PTg00C7k30wTg00D9k10vTg00E7k10uTg00F3k10tTg00G0k10sTg00Gmk10rTg00Hjk10qTg00Ifj3:Tg00JFj3lTg00K@j2KTg00L:k40OTg00LUk30mTg00M2k10]Tf0R0#1#1#0#0p=8%00#1#0#1p=<%00#1#1#1p=B%00#0#1#1p=?%10#0#0#6p>0Ag00MhR1f2R2f1R3P0C_p=c%00#1#1#0p=;%10#1#0#1p=7%10#1#1#0p=>%00#0#0#6p=H%20#2p>08%20#2#2#2p>0D%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0\%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0Bg00NFR4@0M30p>06B0P430p=Yg00O2R5?:30p=b%60#Cp=Pg00OnR6g00PNS00P3P0H05p>0J%10#0#1#0p=A%00#0#0#1#1#0#1#0p>0T%10#1#1#1#1#1#1#0p>03%00#0#0#1#0#0#0#6p=i%10#0#1#1p=G%00#0#0#0p=3%10#1#0#0#0#0#0#6p>0:%00#0p=J%00#0#0p=4%00#0#6#Cp=D%00#0#0#0#0p=]%00#1#0#0#1#0#0#0p=m%00#0#1#0#0#0#1#0#0p=h%10#0#0#0p=9%20#2#2#2#2#2#2#2p>0ng00Q@R7%Z2%Z3=:703:p=kA:7309:72p>07%Z3=:70p>0[%00#gp>0C%10#1#0p>0N%10#1#1#1#1#1#1#1p=`%10#1#1#1p=F%00#0#1#0p=E%00#1p>0lf3R8/T2?l30p>0Z%10#0p>0L%10#0#0#1p=5%00#0#0#1#1#0#0#1p>0k%00#0#0#0#0#0#1#1p=S%10#1#1p>0j%00#0#0#1p=Q%00#0#0#0#0#0#0#0p=O%00#0#0#0#0#0#0#6p=X%00#0#0#0#0#0#0p=U%g0,T3p>0h%00#0#6,T3p>0g%63/K0p>0f%10#1p=}%00#1#0#0p=N%00#0#0#0#0#1#0#0p=\%00#0#1#6p>0e%00#0#0#1#0#0#1#0p=f%00#0#0#0#0#0#0#0#0p=d%10#1#1#1#0#0#0#6p=|%00#0#0#0#1#0#0#0p=~%00#0#0#0#0#0#0#0#1p=L%00#1#0#0#0#1#0#0p>0W%00#0#0#1#0#0#0#1p>0@%00#0#0#1#0#0#1#1p>04%00#0#0#0#0#1#0#1p=R%00#0#0#0#0#0#0#0#1#1#0p=@%00#0#0#0#0#0#0#0#1#1#0#0#1p=t%00#0#0#0#0#0#0#0#1#1#0#1#0p=q%00#0#0#0#0#0#0#0#1#1#0#1#1p=p%00#0#0#0#0#1#1#1p=W%00#0#1p>0?%00#0#1#0#0p={%00#0#0#1#1#0#1#1p>0d%00#0#1#0#0#0#1#0#0#1#1p=s%10#6p>0c%00#0#1#0#0#0#1p>0b%00#0#0#0#0#1#1#0p>0>%00#0#0#0#0#0#0#1p>0ag00R8R9f4R:/T8?l23;:0p==%08#0#0#0#6,T:?l23=:90p=[%18#0#0#0#6,T:?l23=:90p=M%68,T:?l23=:90p>0FA:9309:92p>0=%0:#6/K8%02#6/K3=:905:9p>01%02#6%03#0#0#6'K=:90p=a%03#6,K2=:90p>0S%02#6/K3=:90p>0I%02#1#1#0#0#6%03#0#0#6'K=:90p=r%12#6/K3=:90p=n1K:81K23=:905:9p>0_%12#1#1#0#0#6%03#0#0#6'K=:90p=u%12#1#1#0#0#6/K3=:90p>0<%12#0#1#0#0#6%03#0#0#6'K=:90p=x%1:#0#1#0#0#6/K8%02#0#1#0#0#6/K3=:905:9p>0H%02#0#1#0#0#6%03#0#0#6'K=:90p=j%02#0#1#0#0#6/K3=:90p>0;%12#0#1#0#0#6/K3=:90p>0{%02#1#1#0#0#6/K3=:90p>0z%18#0#0#0#g,T:?l23=:90p=o%g8,T:%Z37l2=:90p=z%08#g,T:?l23=:90p=w%g8,T:?l23=:90p=IP7P7P3P0C_p>0RP:P820Q23P0H0Op=yf6R;f5R<P:P8P2P3P0H0OH0Op>0xg00S2R=?e30p>02B0m=30p=vP1P2&0]3P0C_p>00Ae=30$0]p>0pP1P8P2P3C_=V:0p>0oAV;<:AV823/^0'^p>0E&0|5R0-091R8g00SoR3#8#<#B#?$0AR2&0K5R55c0R<;V<R;%83#;#7#>#H=c05R:=V8:S01g00TTR>g00U4S02g00UfR?#2R@#2RA$08RB#2RC#2$08RD$08$0DS03#2S04$0DRE#2RF#2S05#2S06#2S07$08S08#2S09#2S0:#2RG#2RH#2RI#2RJ#2RK#2RL$0\$0B$0BRM#ZRNg00VERO#CRP+06RQPNH05%ZARR/YN/TOP@P>PPH0X/b5'b9c02RS=V8SS0;%13RT#1RU#1RV#0RW#1#PRX00JNP6g00VcS0<P6P?PBPNH0V206QPH05/b5'b9c02RY=V8YS0=g00WURZ%g3#CR[<0UN/YX%63R\#CR]+0J/b59c02R^=V8^S0>%A3#>$0T$0A=c05R_=V8_S0?g00XAR`$0`Ra%73$03#iRb%03Rc#6S0@%G3#3#8$0:Rd%Z?Re%0cRf#0Rg#1Rh#1Ri#0Rj#JS0A#0Rk#gRl#C'YRm1YeN%0gRg#1Rn#1Ro#1Rp#JS0B#g#CRq'YRrPm%1cRc#0Rs#4S0C#PS0DPPPP%1fRf#0Rt#0Ru#0Rv#0S0E#0S0F#0Rw#gRx#C,YeRy&08M$0D$0\$0B$0B$0BRM%Cd%0nS0G#JS0H#JS0I#3#D%]3#m#?#HRn#C%2M$0DRz%2zRz%2zRz%CbR{206PQRQ%1fRf#P+06R|-06]&0DzRz#Z%2zRz%2zRz%2zRz%2zRz%2zRz%2zRz%h3#7#iR}#CR~%J3#9#A$03#D%2z$08$0nRz%2zRz%2zRz%2z&0K73k3k9kKL9kIJ9kGH807P807]3k3k3k607P407+0[3k407807y+0[PP%73$03#<#HS0JPD%4WRW$0C#C,YeRHPP&0N3#`#?PDPmPP%73$03#9#HS0KPDPmPe%1uRuPD%J3#7#>#A#DPe%3uPDP{PePvPDP|PePwPDg00YD%1VRV#1Rw#1Rv#1#`Ru#1RG#1#FRJ#1#`RI#PRL<0M|Pe%1iRiPDPLPe%4iRiPD%1tRt#PPePjPD%13#;#E#3#8#DPe%0hRh#1RjPDPPPe%0hRh#0RL#0R|#0RKPDPQPe%4jRjPDPNPePkPD%0gRk#1RQ#0Rz#1$0l#?#DPePhPDPP%6G:0GNOPe%4w$0CPDPRH0ZPePxPD%1s#J$0CRs#C,YePe&0LpP@%PkPePKPA%0TRT#1RA#1RK$0L#;#F#PPePjPD%0kRk#1Rj#8#5#G#7#8#5#8#5#5#m$0k#DPePlPD%0TRT#JRl#1#;#<#B#E#E#S#A#;#5#;#8#;#?#PPeQ0BPD&0jIRI#J#8#8#8#8#8#8#7#PPe%3oPD%1I#F#`RI#0#`#`#PPe%4vPD%1TRT#1#?#?#?#?#?#DPe%4zPD%4tRt#9#5#PPe%JkRk#JRzPDP~Pe%4jPDPPPePQPDPyPeQ0GPDPHPeQ0IPD%1f#J$0CRH#C,YePP&0N3#`#QPDPPPP%73$03#E#HRyPDPPPP%73#`#E#HRQPB%1I#`#`#PPP&0N3#`#;PDQ0DPP%73$03$0:RIPDPmPPPbPB%PcPeQ0FPDPPPePtPDPPPe%4fRfPDPPPePHPDPPPeQ0APDPPPePiPD%1cRc#4$0CRi#C,YeRHPeP|PD%ZBR|PeQ0HPDQ0:PePkPDQ09Pe%4VPDQ08PePWPDPRPe%0URU#1RW#4PDQ04Pe%3UPDP~Pe%4KPD%13#<#8#G#9#DPe%3APDPHPe%4TPDP|PePfPDQ05PeQ0CPD%ZFPePsPD%ZEPePiPDPRPePLPDQ07PeQ0EPDQ06Pe%JlPDQ03PePcPD%53#;#A#9#D%6gRg-0ie%Ou#O#O#XRu%JzRz#3Rc#URl#0RL#O#O#X60Ge20hel%6l+0Y%9L#3#O#X:0GRu%1W#8#O-0gP&0L3#A#3#X+0Y20fcb%}3#B#F#9%}3#B#F#5#3Q0J%}3#B#F#5#8Q0K%}3#B#F#A#NPI%}3#B#F#G#9PQ%}3#B#F#8%>3#\#X%}3#9#Q#O%>3#\#5$0e%U3#f#N%d3#5#>#H%U3#E#B#5%d3#5#|RQ%U3#E#A#9%d3#A#G#HRI%U3#E#7#9%d3#G#B#HRc%43#S#~%d3#8#?#HRW%43#S#?#9%d3#8#|%43#S#;#7%d3#7#8%43#S#A#Q%d3#>#5#HRu%43#S#A#>%d3#>$0:%43#S#F%d3#F#7#HRL%43#S#F%L3#3#X%U3$0W%]3$0@#i%U3$0W%]3$0@#N%43#\#5%]3#f#<%43#\#5%]3#f#9%43#\#>%]3$04#5#HRl%43#\#>%]3$04$0:%43#R#?%L3#N#7#HRi%43#R#?%L3#<#X%43#R#9%L3#;#i%43#R#5%L3#;#<%43#R#7%L3#B#;%43#R#>%L3#B#A%@3#E%L3#9#G%@3#?%L3#9#7%@3#?%L3#9#|%@3#N%t3#i%@3#N%t3#?%@3#<%t3#<%@3#<%t3#B%@3#;%t3#5%@3#;%t3#G%@3#B%t3#7%@3#B%t3#|%@3#9%q3#i%@3#9%q3#?%@3#5%q3#<%@3#5%q3#B%@3#A%q3#5%@3#A%q3#G%@3#G%q3#7%@3#G%q3#|%@3#8%p3#i%@3#8%p3#?%@3#8%p3#N%@3#7%p3#;%@3#7%p3#9%@3#>%p3#A%@3#>%p3$0:%@3#F%p3#>%@3#F%L3#8#N%43#W#Q#<%L3#8#;%43#W#Q#7%L3#8#9%43#W#E#<%L3#>#3%43#W#9%L3#>#E%43#W#9%L3#>#N%43#W#5%L3#>#;%43#W#5%L3#>#9%43#~#<#3%]3#E#E#XRE%43#~#8#9%]3#E#?#|%U3#5#R%]3#E#N#E%U3#5#G#7%03#S#<#;$0A%U3#7#<#8%03#S#<#8%U3#7#B#N%03#S#<#F%U3#7#B%03#S#;#X%U3#7#9#N%03#\#;#5&0?3#f#Q#3%{3#m#9%43#Q$0d%03#\#B#5%43$0@#>#9%03#\#B#7#HRs%43$0@#F#9%]3#m#i%43#f#Q#N&0?3#f#E#8%{3#m#7#HRF&0?3#f#?#;%{3#m#>#HRf%{3#m#|RT%h3#5#XRH%h3#5#i%h3#G#XRA&0?3#f#8#NP}%s3#m%h3#7#?#H%s3#<#N%s3#<#<$0cRK%s3#<%h3#7#;%s3#<#8%h3#7#9%s3#;#9%h3#7#G#HR~%h3#7$0:RU%s3#9#9%s3#9#8%{3#<#\&0b3#<#>#N%{3#;#9#Q$0A&0?3$0T#3#A%03#m#3#XPP%03#\#;#A#HRVPD%CVPP%33#E#?#BPB%ZCRCPPP}PDP|PPPKP@PPPPP~PD%Pz%6J:0GC\PPPQPD%13#G#E#E#3#DRCH0ZPP%33#R#?PD%13#8#S#A#DR\PP%33#R#NPD%L3#>#>#HRJ#CRzPP%33#R#NPD%J3#3$04#Q#DPPPIPDPCPP%33#R#5PDP{PP%33#R#APDPzPP%33#R#APD%J3#3$04#?#DPPPcPD%13#G#E#;#8#DRzPP%33#R#FPDP\PP%33$0>#3PD%CER\PP%33$0>#3PD%J3#3$04#B#DPPPWPDPzPP%33$0>#<PDP{PP%33$0>#;PDP\PP%33$0>#;PD%J3#3$04#5#DPPPuPD%13#G#Q#~#DRuPP%33#W#<#5P@%CgRgPP%33#W#BPBPPPP%33#W#BPD%CQPP%33#W#7PDPPPPPLPD%13#G#Q#<#3#DRLPP%33#W#F#5P@PgPP%33#~#QPBPPPP%33#~#QPD%CcPP%33#~#BPDPPPPPlPDPuPP%O3#5#7#5P@PgPP%O3#5#FPBPPPP%O3#5#FPD%CIPP%O3#A#<PDPPPPPiPDPLPP%O3#A#B#5P@PgPP%O3#A#5PBPPPP%O3#A#5PD%CWPP%O3#A#FPDPPPPPJPD%13#G#?#G#>#DPPPEPD%13#G#?#f#DPP&0a3$0@PD%E3#7#>#;#DPPPFPBP]PPPfPD%CTPPPHPD%{3#F#5#>#DPPPAPD%J3#3#f#>#DPPPsPD%CU&0K9D=D=D=D=D=D[D=D=DMDMD[I0FD=DMDMD[I0FD=DMDMD[I0FD=DMDMD[I0FD=DMD[DMD=DMD[DMD=DMD[DMD=DMD[DM40=D=D=D=D[D=I013a40S40I3a3r3nI01I0_I0160SnI013u3a3a40<3a3a3n3a3n40I3u3r3u3r3a3a3a3u3r40<3r3u3r3u3xI0H3j3x3j3x3j3xI0H3j3x3j3x3j3xI0H3j3x3r3r3j40;40<40;40<40;3u3j3u40;40<40;I013a3n3n3n3n40I3n3n40{I01I0180zy40=40=40=DoDzDzDzD=D=DwDzDIDIDIDIDzDIDzDzDzDIDIDID=DwDIDID=D=DMD=D=DMDIDoDoDIDIDIDIDIDwD=DIDIDID=40=DoDwDwDwDoDoDwDoDwDoDIDoD=D[D=N<0y-0^`Ry;VyRn20911R90091RUP9P1P1P1PdPbC_Q0@C_Rb;VbRd20977RD0097RsPDP720RmrPPC_Rr;VrRA%A3#?#8#A$0A=c05R3=V83RH'^RT'^Rf'^RF'^RE'^RJ'^RW'^Rg'^RL,^;20Q8<RiP;PLPiQ01PgP8P:Q0;PWP8PSQ0=PJP8PYQ0>PEP8P^Q0?PFP8P_PnPfPaPyPdPTPUPbPAPHPsPr20Q83DyDyDyDyDyDyDyDyK0xP8209=0R=g00Z0Rrg00Zk3eRH-0201v0H6000P<P8g00[e9e=rRH-0201v0H6000P<P8g00\_9e=rR<-0201v0<6000P:P8g00]Y9e=rR:-0201v0:6000P>Q02g00^SR:>0M4PR<P:H05B0P4R:/TOP@P>PPH0X/b5'b9c02P8g00_M9e=rR>-0201v0>6000P6Q00PXP:H05P6Q0<P6P?PBP:H0V206<PH05/b5'b9c02P8g00`G9e=rR<-0201v0<6000B0UZ[:/YX00J]/b59c02P8g00aA9e=rR2-0201v026000P_Pag00b;g00c660wMg00d1RM-0^`PUP9P1P1P1&0vM&0uMC_&0tMC_PbPsPDP7&0sM&0rM+0R&0qMC_PDP7B0P4e:/Yq-0RmPPC_P8P0g00dm9e=rRr-0p01v0rP3I0oK0EK0EK0EK0EK0Edo"). Qed.

End FXALL1.

