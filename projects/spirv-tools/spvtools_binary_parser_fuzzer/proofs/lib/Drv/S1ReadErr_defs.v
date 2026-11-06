(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1RwWindow S1KnCells S1MainEntry S1LibStdioCall.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs4scREC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv>S1ReadErr_defs2rIC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FXALL1.
Context {fx : FPState}.

Definition STOPS : list Z := [0xe0e44; 0xe13c4; 0xe1998; 0xe0d48; 0x12a64; 0x12bf0; 0xd3964; 0xd00fc; 0xd537c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0x122000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x1006b8; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0xee000) 0x34000;
   KImg 0x10000 0xee4a0;
   KImg 0xee4a1 0xee4e9;
   KImg 0xfe4e9 0xfe790;
   KImg 0xfe792 0xfe798;
   KImg 0xfe7f1 0xfe7f8;
   KImg 0xfe851 0xfe858;
   KImg 0xfe8b1 0xfe8b8;
   KImg 0xfe911 0xfe918;
   KImg 0xfe97a 0xfe980;
   KImg 0xfe9e2 0xfe9e8;
   KImg 0xfe9fc 0xfea00;
   KImg 0xfea84 0xfea88;
   KImg 0xfea9c 0xfeaa0;
   KImg 0xfeb24 0xfeb28;
   KImg 0xfeb3c 0xfeb40;
   KImg 0xfebc4 0xfebc8;
   KImg 0xfebdc 0xfebe0;
   KImg 0xfec64 0xfec68;
   KImg 0xfec7c 0xfec80;
   KImg 0xfed04 0xfed08;
   KImg 0xfed1c 0xfed20;
   KImg 0xfeda4 0xfeda8;
   KImg 0xfedc4 0xfedc8;
   KImg 0xfee4c 0xfee50;
   KImg 0xfee6c 0xfee70;
   KImg 0xfeef4 0xfeef8;
   KImg 0xfef04 0xfef08;
   KImg 0xfef14 0xfef18;
   KImg 0xfef24 0xfef28;
   KImg 0xfef34 0xfef38;
   KImg 0xfef44 0xfef48;
   KImg 0xfef54 0xfef58;
   KImg 0xfef64 0xfef68;
   KImg 0xfef74 0xfef78;
   KImg 0xfef84 0xfef88;
   KImg 0xfef94 0xfef98;
   KImg 0xfefa4 0xfefa8;
   KImg 0xfefb4 0xfefb8;
   KImg 0xfefc4 0xfefc8;
   KImg 0xfefd4 0xfefd8;
   KImg 0xfefe4 0xfefe8;
   KImg 0xfeff4 0xfeff8;
   KImg 0xff004 0xff008;
   KImg 0xff014 0xff018;
   KImg 0xff024 0xff028;
   KImg 0xff034 0xff038;
   KImg 0xff03c 0xff040;
   KImg 0xff04c 0xff050;
   KImg 0xff05c 0xff060;
   KImg 0xff06c 0xff070;
   KImg 0xff07c 0xff080;
   KImg 0xff08c 0xff090;
   KImg 0xff09c 0xff0c0;
   KImg 0xff0ca 0xff0d0;
   KImg 0xff0da 0xff0e0;
   KImg 0xff0ea 0xff1a0;
   KImg 0xff1ac 0xff1b0;
   KImg 0xff1bc 0xff1c0;
   KImg 0xff1cc 0xff1d0;
   KImg 0xff1dc 0xff1e0;
   KImg 0xff340 0xff3a0;
   KImg 0xff431 0xff498;
   KImg 0xff4aa 0xff4b0;
   KImg 0xff61b 0xffd54;
   KImg 0xffd58 0xffd80;
   KImg 0xffd88 0xffd98;
   KImg 0xffd9c 0xffda0;
   KImg 0xffda8 0x1005e8;
   KImg 0x1206c0 0x1206e0;
   KImg 0x10061c 0x100668;
   KImg 0x100670 0x100688;
   KImg 0x100690 0x1006a8;
   KImg 0x1006b8 0x1006c8;
   KImg 0x1206f8 0x120708;
   KImg 0x12070c 0x120710;
   KImg 0x120718 0x120720;
   KImg 0x120728 0x120820;
   KImg 0x120828 0x120928;
   KImg 0x120930 0x120938;
   KImg 0x120949 0x12094b;
   KImg 0x12094c 0x120950;
   KImg 0x120958 0x120960;
   KImg 0x120970 0x120978;
   KImg 0x120980 0x1209b0;
   KImg 0x1209b8 0x120ac0;
   KImg 0x120e68 0x1216ac;
   KImg 0x1216b4 0x122000;
   KWord (SA (ELit 0) 0x1005f0) 8 (ELit 0x1005f0);
   KWord (SA (ELit 0) 0x100610) 4 (EVar 5);
   KWord (SA (ELit 0) 0x120928) 8 (EVar 4);
   KWord (SA (ELit 0) 0x12094b) 1 (ELit 0);
   KWord (SA (ELit 0) 0x120978) 8 (ELit 4096);
   KRange (EVar 5) 1 4194303] ++ kn_drv_cells.

Definition ssB0 : sym_state := SS 0x65814 srRE0 [] knRE0 39.
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

Definition ssC0 : sym_state := SS 0xd5e0c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

Definition ssD0 : sym_state := SS 0xd5e0c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

Definition ssE0 : sym_state := SS 0xd6fa8 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0xd5e0c srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd5e0c srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

Definition ssH0 : sym_state := SS 0xd5e0c srH0 [] knH0 231.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe1998%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xe0e44%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xe0e44%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xe0e44%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd537c%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xd00fc%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_S1ReadErr_defs ()) ["FXALL1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10yTg000Pk20<Tg0010k10MTg001Pj3XTg001jj12Tg002Ij1\Tg003Aj1ATg0049k40=Tg0055j2WTg005nk40[Tg006jj11Tg007Oj10Tg0084k40XTg008lj1cTg009Jk30WTg00:Bj13Tg00:`k10bTg00;Bk30NTg00<:k30GTg00=4k20jTg00=nk20ZTg00>hm<0xTg00?kk20`Tg00@Mj4_Tg00@mj2`Tg00AHk20RTg00Abj3fTg00B?k30QTg00C7k30vTg00D9k10uTg00E7k10tTg00F3k10sTg00G0k10rTg00Gmk10qTg00Hjk10pTg00Ifj39Tg00JFj3kTg00K@j2OTg00L:k40PTg00LUk30lTg00M2k10^Tf0R0#1#1#0#0p=8%00#0#0#1p=I%10#0#0#0p=:%10#0#0#3p>0Cg00MhR1f2R2f1R3P0C_p=e%00#0#1#1p=7%00#0#1#1#0#0#0#3p={%20#2p>0:%20#2#2#2p>0D%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0_%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0Bg00NFR4@0N30p>0>B0Q430p=[g00O2R5?930p=b%30#Ap=Rg00OnR6g00PNS00P3P0H0=p>0K%10#0#1#0p=4%00#1#1#0p=;%10#1#1#1p=5%10#1#0#1#1#1#0#0p=a%00#0#0#3p=F%10#1#0#1p=6%00#0#1#0p=C%00#0#0#1#0#0#0#3p=l%00#0p=U%00#0#0p=K%00#0#0#0p=?%00#0#3#Ap=E%00#0#0#0#0#0#0#0p=T%00#1#1#1#0#0#0#3p=|%00#0#1#0#0#0#0#0#1p=y%00#1#0#1#0#0#0#3p=z%20#2#2#2#2#2#2#2p>0mg00Q@R7%\2%\3=97039p=gA97309972p>0?%\3=970p>0]%00#cp>0@%10#1#0p>0O%10#1#1#0#0#0#0#1p=x%10#1#1#0#1#0#1#0p=w%10#1#1#1#1#1#1#1p=Y%10#1#1#1#1p>0\%00#1#0#1p=G%10#0#1#1p=>%00#1p>0kf3R8/W2?k30p>0F%10#0p>0L%10#1#0#0#1#0#0#1p=v%10#0#0#1p==%00#1#0#0p=<%00#1#1#1p=H%00#0#0#0#0#0#1#1p=t%10#1#1p=Q%10#1#1#0p=V%00#0#0#0#0#0#0#3p=i%c0,W3p>0i%00#0#3,W3p>0h%33/O0p>0g%10#1p=]%00#0#0#0#1#1#1#0p>05%10#1#1#1#1#0#0#0p>0Y%00#1#0#0#0#0#0#3p>04%00#0#1#3p>0f%10#1#1#1#1#1p=B%10#1#1#1#1#1#0#1p=D%10#1#1#1#1#1#1#0p=S%10#1#1#1#1#1#0#1#1#1p=L%10#1#0#1#1#1#1#1p=r%10#1#1#1#1#1#0#1#1#1#1#0p=p%10#1#1#1#1#0#0#1p=m%10#1#1#1#1#1#1#0#0#0p=M%10#1#1#0#0#0#0#0p>03%00#0#1p>0J%00#1#0#0#0#0#0#0p>0V%00#0#1#0#0p=q%00#0#1#0#0#0#0p>0I%00#1#0#0#0#0#0#1p>0e%00#0#1#0#0#0#0#0#1#0#0p=o%10#3p>0d%10#1#1#1#1#1#0p=P%10#1#1#0#1#0#0#0p>02g00R8R9?930p>0cf4R:/W8?k23=990p=@A99309992p>0;%08#0#0#0#3,W:?k23=990p=Z%18#0#0#0#3,W:?k23=990p=N%38,W:?k23=990p>0E%0:#3/O8%02#3/O3=990599p>07%02#3%03#0#0#3'O=990p=^%03#3,O2=990p>0U%02#3/O3=990p>0H%02#1#1#0#0#3%03#0#0#3'O=990p=n%12#3/O3=990p=j1O:81O23=990599p>0a%12#1#1#0#0#3%03#0#0#3'O=990p=}%12#1#1#0#0#3/O3=990p>09%12#0#1#0#0#3/O3=990p>0T%1:#0#1#0#0#3/O8%02#0#1#0#0#3/O3=990599p=d%02#0#1#0#0#3/O3=990p>01%18#0#0#0#c,W:?k23=990p=h%c8,W:%\37k2=990p>00%08#c,W:?k23=990p=s%c8,W:?k23=990p=JP7P7P3P0C_p>0SP:P820R23P0H0Pp=~f6R;f5R<P:P8P2P3P0H0PH0Pp>0wg00S2R=?f30p>08B0l=30p=uP1P2&0^3P0C_p>06Af=30$0^p>0oP1P8P2P3C_=X:0p>0nAX;<:AX823/`0'`p>0A&0y5R0-0<1R8g00SoR3#8#I#8#:$0CR2&0M5R55e0R<;X<R;%83#7#7#{=e05R:=X8:S01g00TTR>g00U4S02g00UfR?#2R@#2RA$0:RB#2RC#2$0:RD$0:$0DS03#2S04$0DRE#2RF#2S05#2S06#2S07$0:S08#2S09#2S0:#2RG#2RH#2RI#2RJ#2RK#2RL$0_$0B$0BRM#\RNg00VERO#ARP+0>RQPNH0=%\ARR/[N/WOP@P>PPH0[/b5'b9e02RS=X8SS0;%13RT#1RU#1RV#0RW#1#RRX00KNP6g00VcS0<P6P?PBPNH0X20>QPH0=/b5'b9e02RY=X8YS0=g00WURZ%c3#AR[<0WN/[X%33R\#AR]+0K/b59e02R^=X8^S0>%43#4#;#5$0C=e05R_=X8_S0?g00XAR`$0bRa%a3#7#;#FRb%03Rc#3S0@%43#6#C#lRd%\?Re%0cRf#0Rg#1Rh#1Ri#0Rj#US0A#0Rk#cRl#A'[Rm1[eN%0gRg#1Rn#1Ro#1Rp#US0B#c#ARq'[RrPm%1cRc#0Rs#KS0C#RS0DPPPP%1fRf#0Rt#0Ru#0Rv#0S0E#0S0F#0Rw#cRx#A,[eRy&0:M$0D$0_$0B$0B$0BRM%Ad%0nS0G#US0H#US0I#?#E%03#T#6#|Rn#A%2M$0DRz%2zRz%2zRz%AbR{20>PQRQ%1fRf#R+0>R|-0>]&0DzRz#\%2zRz%2zRz%2zRz%2zRz%2zRz%2zRz%y3#C#zR}#AR~%U3#:#7#4#;#E%2z$0:$0mRz%2zRz%2zRz%2z&0M73g3g9gKL9gIJ9gGH80?P80?]3g3g3g60?P40?+0]3g40?80?y+0]PP%a3#7#4#FS0JPD%KWRW$0@#A,[eRHPP&0O3#x#6PDPmPP%a3#7#6#FS0KPDPmPe%1uRuPD%U3#6#w#EPe%?uPDP{PePvPDP|PePwPDg00YD%1VRV#1Rw#1Rv#1#YRu#1RG$0\RJ#1#YRI#RRL<0N|Pe%1iRiPDPLPe%KiRiPD%1tRt#RPePjPD%13#G#4#>#;#EPe%0hRh#1RjPDPPPe%0hRh#0RL#0R|#0RKPDPQPe%KjRjPDPNPePkPD%0gRk#1RQ#0Rz#1$0k#7#EPePhPDPP%3G:0GNOPe%Kw$0@PDPRH0FPePxPD%1s#U$0@Rs#A,[ePe&0LpP@%RkPePKPA%0TRT#1RA#1RK$0L#;#5#RPePjPD%0kRk#1Rj#v#>#6#v#v#=#<#:#I#=#EPePlPD%0TRT#URl#1#;#G#H#C#C#t#4#;#=#;#8#;#7#RPeQ0BPD%QIRI#U#8#8#8#8#8#8#6#RPe%?oPD&0\I#YRI#0#Y#Y#RPe%KvPD%1TRT#1#7#7#7#7#7#EPe%KzPD%KtRt#:#=#RPe%UkRk#URzPDP~Pe%KjPDPPPePQPDPyPeQ0GPDPHPeQ0IPD%1f#U$0@RH#A,[ePP&0O3#x#8PDPPPP%a3#7#|RyPDPPPP%a3#<#|RQPB%1I#Y#Y#RPP&0O3#V#C#IPDQ0DPP%a3#<#lRIPDPmPPPbPB%RcPeQ0FPDPPPePtPDPPPe%KfRfPDPPPePHPDPPPeQ0APDPPPePiPD%1cRc#K$0@Ri#A,[eRHPeP|PD%\BR|PeQ0HPDQ0:PePkPDQ09Pe%KVPDQ08PePWPDPRPe%0URU#1RW#KPDQ04Pe%?UPDP~Pe%KKPD%13#G#G#;#C#EPe%?APDPHPe%KTPDP|PePfPDQ05PeQ0CPD%\FPePsPD%\EPePiPDPRPePLPDQ07PeQ0EPDQ06Pe%UlPDQ03PePcPD%=3#;#I#7#E%3gRg-0je%Tu#T#T#iRu%UzRz#?Rc#K#?Rl#0RL#T#T#i60Ge20iel%3l+0Z%:L#?#T#i:0GRu%1W#:#T-0hP&0L3#:#?#i+0Z20gcb%]3#H#?#6%]3#H$05#<Q0J%]3#H#?#5#?Q0K%]3#H#?$0YPI%]3#H#I#?#8PQ%]3#H#I#I%63#v$04%]3#H#C#G#?%63#v#6$0f%B3#C#H#<%53#8#5#C#F%B3#7#v%53#8#5#{RQ%B3#7$0Y%53#8#Y#FRI%B3#<#C#:%D3#?#>#FRc%B3#<#G#:%D3#I#|RW%B3#<#:#:%D3#C#{%B3#<#>#6%D3#7#?%B3#<#5#I%D3#7#6#FRu%B3#<#S%D3#<#i%B3#G#<%D3#G#lRL%B3#G#<%D3#G$04%B3#G#=%D3#;#z%B3#G#=%D3#;#:%B3#G#V%D3#H#=#F%B3#G#V%D3#H#8%B3#;#7%D3#:#6#FRl%B3#;#7%D3#=#i%B3#;#:%D3#4#lRi%B3#;#:%D3#4$04%B3#;#6%D3#>#z%B3#;#V%D3#>#=#F%L3#C%53#a#4%L3#7%53#a#V%L3#H%D3#r#F%L3#:%p3#l%L3#:%p3#{%L3#=%p3#z%L3#=%p3#|%L3#4%p3#=#F%L3#4%p3#>#F%L3#>%p3#6#F%L3#>%p3#5#F%L3#8%53#r#l%L3#8%53#r#{%L3#6%53#r#z%L3#6%53#r#|%L3#V%D3#m#F%L3#V%53#r#>#F%L3#5%D3#D#F%L3#5%D3#Y#F%M3#?%53$03#l%M3#?%53$03#{%M3#I%53$03#z%M3#I%53$03#|%M3#I%53$03#:%M3#C%53$03#4%M3#C%53$03#8%M3#7%S3$05%M3#7%53#x#i%M3#<%53#x#C%M3#<%53#x#:%M3#;#G%53#x#4%M3#;#6%53#x#8%M3#H#G%S3#7#<%M3#6%S3#7#;%M3#6%S3#7#:%M3#V%S3#7#4%M3#V%S3#7#8%]3#m#4#?%S3#H$04RE%B3#4#I#:%S3#=#{%B3#4#G#G%S3#=#;%B3#>#?#6%Y3#4#4$0C%B3#w#8%Y3#>#?%]3#S#8#<%Y3#>#7%]3#S#8%Y3#>$04%]3#S#6#<%03#T#>#6&0J3#t#;#?%03$0V#a%K3#t#?%03#T#8#6%K3#t#7#:%03#T#6#lRs%K3#t#<#:%03#T#6#z%K3#t#;#<&0J3#t#H#8%q3$05#lRF&0J3#t#:#;%q3$05#C#FRf%q3$05#{RT%q3$05$04RH%q3$05#z%y3#?$04RA&0I3$0e#<P}%o3#=#:%y3#C#|%o3#4#<%o3#4#G$0dRK%o3#4%y3#C#4%o3#4#8%y3#C#8%o3#>#:%y3#C#5#FR~%y3#7#iRU%o3#6#:%o3#a%y3#G#:&0I3#H#7#<%q3#C#6#G$0C&0I3#>#G#4%q3$0V#iPP%03#T#>#V#FRVPD%AVPP%T3#;#IPB%\CRCPPP}PDP|PPPKP@PPPPP~PD%Rz%3J:0GC\PPPQPD%13#4#4#8#4#ERCH0FPP%P3#H#6PD%13#>#:#V#<#ER\PP%P3#H#VPD%S3#<#C#FRJ#ARzPP%P3#H#VPD%13#m#6#=#EPPPIPDPCPP%Q3$02#7PDP{PP%Q3$02#<PDPzPP%Q3$02#<PD%13#m#6#>#EPPPcPD%13#4#>#I#;#ERzPP%Q3$02#=PDP\PP%Q3$02#4PD%AER\PP%Q3$02#4PD%13#m#r#EPPPWPDPzPP%Q3$02#5PDP{PP%P3#=#?PDP\PP%P3#=#?PD%13#m#x#EPPPuPD%13#4#=#>#C#ERuPP%P3#=#mP@%AgRgPP%Q3#w#IPBPPPP%Q3#w#IPD%AQPP%Q3#w#HPDPPPPPLPD%13#4#=#5#4#ERLPP%Q3#w#=#=P@PgPP%Q3#w#>PBPPPP%Q3#w#>PD%AcPP%P3#>#IPDPPPPPlPDPuPP%P3#8#H#=P@PgPP%P3#vPBPPPP%P3#vPD%AIPP%P3#8#5PDPPPPPiPDPLPP%P3#6#I#=P@PgPP%P3#6#7PBPPPP%P3#6#7PD%AWPP%P3#6#=PDPPPPPJPD%13#4#8#;#:#EPPPEPD%13#4#>#>#8#EPP%Q3#5#7#>PD%C3#r#<#EPPPsPD%AUH0FRUPPPFPBP]H0FPPPfPD%ATPPPHPD%q3#:#<#:#EPPPAPD%13#m#6#;#E&0M9-0cUD@D@D@40;DZD@D@DNDNDZI0ED@DNDNDZI0ED@DNDNDZI0ED@DNDNDZI0ED@DNDZDND@DNDZDND@DNDZDND@DNDZDN40;D@D@D@DZD@I073^40U40H3^3n3jI07I0aI0760UnI073}3^3^4093^3^3j3^3j40H3}3n3}3n3^3^3^3}3n4093n3}3n3}40TDdDdDdDdDdDdDdDdDdDd3n3n4014014094014094013}4013}401409401I073^3j3j3j3j40H3j3j409I07I0780Ty40;40;40;DhI00I00I00D@D@DsI00DJDJDJDJI00DJI00I00I00DJDJDJD@DsDJDJD@D@DZD@D@DZDJDhDhDJDJDJDJDJDsD@DJDJDJD@40;DhDsDsDsDhDhDsDhDsDhDJDhD@DND@N<0x-0``Ry;XyRn20<11RU00<1R9PUP1P1P1PdPbC_Q0@C_Rb;XbRd20<77RD00<7RAPDP720SmrPPC_Rr;XrRH%43#?#I#5$0C=e05R3=X83RT'`Rf'`RF'`Rs'`RE'`RJ'`RW'`Rg'`RL,`;20R8<RiP;PLPiQ01PgP8P:Q0;PWP8PSQ0=PJP8PYQ0>PEP8P^Q0?PsP8P_PnPFPaPyPdPfP9PbPHPTPAPr20R83D~D~D~D~D~D~D~D~K0wP820<=0R=g00Z0Rrg00Zk3fRT-0801u0T6060P<P8g00[e9f=rRT-0801u0T6060P<P8g00\_9f=rR<-0801u0<6060P:P8g00]Y9f=rR:-0801u0:6060P>Q02g00^SR:>0N4PR<P:H0=B0Q4R:/WOP@P>PPH0[/b5'b9e02P8g00_M9f=rR>-0801u0>6060P6Q00PXP:H0=P6Q0<P6P?PBP:H0X20><PH0=/b5'b9e02P8g00`G9f=rR<-0801u0<6060B0WZ[:/[X00K]/b59e02P8g00aA9f=rR2-0801u026060P_Pag00b;g00c660vMg00d1RM-0``P9PUP1P1P1&0uM&0tMC_&0sMC_PbPAPDP7&0rM&0qM+0S&0pMC_PDP7B0Q4e:/[q-0SmPPC_P8P0g00dm9f=rRr-0o01u0rP3I0nK0AK0AK0AK0AK0Ado"). Qed.

End FXALL1.

