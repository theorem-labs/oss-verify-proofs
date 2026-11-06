(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1MainEntry S1LibStdioCall.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4srH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4knH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4scH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rI3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4srF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4knF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4scF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4srH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4knH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4scH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3rI4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs4scOFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?S1OpenFail_defs2rIC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FXALL.
Context {fx : FPState}.

Definition STOPS : list Z := [0xe0e44; 0xe13c4; 0xe1998; 0xe0d48; 0x65a88; 0xd3964; 0xd00fc; 0xd537c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.

Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.

Definition IHI : Z := 0x122000.

Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition ssA0 : sym_state := SS 0x655e8 sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xe1e50 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.

Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
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
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd5e0c srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

Definition ssH0 : sym_state := SS 0xd5e0c srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

Definition ssI0 : sym_state := SS 0xd6908 srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Definition scrG3 : scripts := SCR [false] [] [].
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.

Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.

Definition ssI30 : sym_state := SS 0xd6908 srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

Definition scrF4 : scripts := SCR [true; false] [] [].
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.

Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.

Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.

Definition ssH40 : sym_state := SS 0xd5e0c srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.

Definition ssI40 : sym_state := SS 0xd6908 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xd537c%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0xd6ad8%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x13790, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xd537c%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0xd00fc%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xd537c%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0xd74f8%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xd537c%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0xd00fc%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_S1OpenFail_defs ()) ["FXALL"] "p%0p&0p;1p;2p;3p;4p;<g0000k10~Tg000Pk20;Tg0010j1QTg001Nj1BTg002Fj12Tg002ej1UTg003]k30qTg004Uj11Tg005:j14Tg005Xk10^Tg0068j3OTg006Rk10{Tg0074j10Tg007Yk30YTg008Qk30ITg009Kj2_Tg00:Dk20kTg00;>k20jTg00<8k40yTg00=2j2TTg00=lm<0\Tg00>oj2|Tg00?Qk40rTg00@Ik40[Tg00AEj2KTg00A`j2lTg00B:j3tTg00BWk10CTg00CMk30XTg00DOk10UTg00EMk10WTg00FIk10ZTg00GFk10STg00HCk10VTg00I@k10pTg00J<k10TTg00K8k30bTg00L0k409Tg00LPj33Tg00M0j3fTg00Mjk40aTg00NEk30}Tf0R0#1#0#1#0p=7%00#1#1#0p=>%10#1#1#1p=6%10#0#0#4p>0O%20#2#2p>0N%20#2p>0h%20#2#2#2p=r%20#2#2#2#2#2#2#2p>0L%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p={%40#Bp=[g00NbR1f1R2<0b0p>0=g00ONS00g00OnS01P2P0H0[p>0_g00P`R3?320p>0Gg00Q\R4f2R5P2P0H09p=]%10#1#0#1#1#1#0#0p=^%00#0#1#1p=5%00#0#0#4p=9%10#1#0#1p=;%00#1#0#1p=N%10#0#1#1p=@%00#0p=J%B0:0b12p=m%10#1p=a%10#1#0#1#1#1#1#0p>0t%00#1#0#0p=<%00#0#4#Bp=E%00#Qp>0]%00#0#0#0p=A%00#0#0#0#0#0#0#0p=R%00#1#1#1#0#0#0#4p>0B%10#1#1#1#1#1#1#1p=d%10#1#1#1#1p>0dB0Y120p>05%00#1#1#1p=G%10#0#0#1p=:%00#0#0#1p=Fg00R:R6%U2;30p>0c%U5%U2=360536p=Yf3R7%U2=3609365536p>0Kf4R8A362093659367536p=n%U7A36209365536p>0`%00#0#0p=M1_75?f20p=b%05#Q,_7?f20p=`%00#1p>0o%10#0#0p>0J%10#1#0#0p=8%00#0#1#0p=I%10#1#1#0p=X%10#4p>0n%B09f52p>0m%10#1#1p=V%10#0#0#0p=?%00#1#0#0#0#0#0#1p=y%00#1#0#1#0#0#0#4p=x%10#1#0p>0l%10#1#1#0#0#0#0#1p>0:%00#0#0#1#0#0#0#4p=k%00#0#0#0#0#0#0#4p=w%00#0#1#4p>0|%10#1#1#0#1#0#1#0p=v%Q0,_2p>0z%00#0#4,_2p>0x%10#0p>0w%00#0#0#0#1#1#1#0p>08%10#1#1#1#1#0#0#0p>0i%00#1#0#0#0#0#0#4p>07%10#1#1#1#1#1p=D%00#0#1#1#0#0#0#4p>06%10#1#1#1#1#1#0#1p=H%10#1#1#1#1#1#1#0p=\%10#1#1#1#1#1#0#1#1#1p=L%10#1#0#1#1#1#1#1p=s%10#1#1#1#1#1#0#1#1#1#1#0p=}%10#1#1#1#1#0#0#1p=z%10#1#1#1#1#1#1#0#0#0p=P%10#1#1#0#0#0#0#0p>04%00#0#1p=j%00#0#0#0#0#0#1#1p>03%00#1#0#0#0#0#0#0p>0v%00#0#1#0#0p>02%00#0#1#0#0#0#0p>0u%00#0#0#0#0#1#0#0p>0F%10#1#1#1#1#1#0p=W%10#1#1#0#1#0#0#0p>01g00S2R9?320p>0g1_87?f52=390p=CA39209395p>00%07#0#0#0#4,_8?f52=390p=c%17#0#0#0#4,_8?f52=390p=S%47,_8?f52=390p>0E%05#4%02#0#0#4'T=390p=e%02#4,T5=390p>0f%05#4/T2=390p>0R%15#4/T2=390p=q1T871T52=390539p>0e%08#4/T7%05#4/T2=390539p>0M%15#1#1#0#0#4%02#0#0#4'T=390p=~%15#1#1#0#0#4/T2=390p>0H%05#1#1#0#0#4/T2=390p>0?%15#0#1#0#0#4/T2=390p>0s%18#0#1#0#0#4/T7%05#0#1#0#0#4/T2=390539p=h%05#0#1#0#0#4/T2=390p>0DA3920939593979398p=Z%Q7,_8?f52=390p==%17#0#0#0#Q,_8?f52=390p=g%07#Q,_8?f52=390p=pP4P4P2P0H09p>0@P5P4P2P0H09p>0>P7P6P6P6P5P2H09P0H09p=oP5P6P2P0H09p>0Qf6R:f5R;P8P7P5P2P0H0aH0ap>0PP8P71l52P0H0ap=ug00SlR<?t20p>0AB0}<20p>0<AO:;8AO752/K0'Kp=i&0~3R0-0;4R7g00TiR5#7#7#>#6$0OR2g00UNS02%Q5#BS03g00V:R;#2R:#2R8#2R=#2R>#2R?$0NR@$0h#r$0L#{RA$0N$0L#{#{#{#{RB#URC40q%15RD#1RE#1RF#1RG#1RH#[RI+0=%45RJ#BRK+0_&0^3R3+0G5]0RL;OLg00VYRM$0{RN%^5#5#>#9RO%05RP#4RQ%75#;#N#@#9RR%U;RS%0PRT#0RU#1RV#1RW#0S04#JS05#0RX#QRY'mRZ20=SC%0UR[#1R\#1R]#1R^#a#Q#BR_+0=S06PZ%1PRP#0R`#0Ra#0S07#0Rb#[Rc%J5$0t#<#ERdPK&0]XRX,mSRe&0hB#r#{#{#{RB#2#rS08#2S09#2S0:#rS0;#2S0<#2S0=#2S0>#2S0?#2S0@#2S0A$0N$0LS0B#2S0C#2S0D#2S0E#2Rf%BRS0FPe%0\R\#JS0G#JRg#A#ES0H%05#R#;$0BS0I#BS0J%2f#rRh%2hRh%2hRh%1TRT#0Ri#1Rj#[S0K%1HRk#1#dRl#1Rm$0dRn#1#dRo#[RpPK%rhRh#U%2hRh%2hRh%2hRh%2hRh%2hRh%2hRhg00W\Rqg00XHRr#BRs205CsRt+05S0L%[VS0M+05Ru80YpS0NPu%BORv%55#G#:#F#[S0OPKPdPs205tsS0PPKPt&0Nh$0LRh%2hRh%2hRh%2hS0Q&0^6Rh+0c3YH0KDnDn3Y3Y3YDn3YH0KH0`Ps%^5#5#7#9S0RP@%MFS0S#0S0T$0],mSS0UCbS0VPs%^5#5#@#9P@PZCbS0WPs%^5#5#;#9S0XP@PZCbS0YPS%0VRV#1RF#1S0Z#JP@PsC`S0[PS%0VRV#0S0\#0S0]#0RwP@Q0LC`S0^PS%MFRFP@PCC`S0_PSPXP@%0[RX#1Rx#0Ry#1$0o#5#ECbS0`PS&0JVP@PsC`S0a%4m:0ICrS0bPS%MHP@%U8R8C`S0cPS%0iRi#0S0d#0S0e#0S0f#0S0g#QRHP@%1`Rm#0RV#JRz#QS0h,mSCbS0iPS%QwP:%[XRwCbR{PS%QFP@%0DRD#1RF#1R|$0J#8R}#1$0o#G#A#>#6#I#A#G#<#>#6#>#X#[CbR~1_SYS0j%J}#@#F#:#A#F#;#5#<#@#>#5#F$0n80m@R}PS%J^P@%VoRo#J#8#8#8#8#8#8#;#[C`S0kPS%M]P@&0do#dRo#0#d#d#[C`S0lPS%JkP@%0DRD#1Rk#1#5#5#5#5#5#EC`S0mPS%JyP@%MjRy#?#:#[C`S0nPS%1m#AP@%U>RmPS%0XRX#JS0o#JR]#QP@%05#y#I#xR^#BRYCbS0pPS&0JXP@PsC`S0qPS&0JxP@1mSHRHC`S0rPS&0J\P@Q0UC`S0UPS%QgP@%1TRT#1Rg#MR\#QS0s,mSCbRxPS&0JVP@PsC`PS%JzP@PsPS%1aRaP@PsPS%AaP@PsPSQ07P@PsPS%0bRa#JP@PsPSPgP@%[PRgPSP\P@%J5#?#5#7#>#ES07PS%0TRTP@PKPS%JTRT#0R\P@PYPSPjP@%55#G#G#;#[PSPyP@PvPS%1iS0t#MS0uP@%15#N#7#5#7#EPs&0l5$0:#8P@PsPs%^5#5$0BRiP@PsPs%^5#<$0BS0vP>&0doRo#V#d$0nRj#BPs&0l5#X#I#FP@PcPs%^5#<#kRzP@PZPsPOP>PgPSQ0fP@PsPSPyP@PsPSP\P@PsPSQ0sP@PsPSQ05P@PsPS%1WS05#MS0sP@%1PRP#MRW$0]R\,mSRyPSQ0]P@PmPSQ0GP@PsPSQ0oP@PsPS%MGP@20=SwRwPSQ0TP@P8PS%0ERE#1RG#MP@%BQRgPS%JERE#0RVP@PYPS%M|P@%15#N#N#>#I#EPS%MFRFP@PyPS%MkP@PmPSPTP@PsPSPaP@PsPSQ0hP@%UARAPSP\P@P8PSQ0\P@%[EPSQ0eP@PsPS%0DRD#JR\P@PgPSPPP@%:5#>#F#5#EPs%R5#>#F#<P>205As:0Yqs%Rl#R#R#wRl%J]R]#ARq#M#ARP#0RT#?#A#R#wRk60I8%0o#R$0|>0IAjPSQ0SP@PsPSPVP@PsPSPFP@PsPSP\P@PsPSPWP@PwPSPbP@%:5#N#G#7#EPSQ0dP@PgPSPXP@%4URU,mSPSPEP@%15#5#v#8#E%4[R[-0kS%RT#R#w:0ISl20zSPRT%4PRP+0jPSPrP@PgCbPSPUP@%U:PSP[P@P8PSPDP@Ps%U=R=@0IlkPTPP1_=r%4aH0y20k=U%1G#?#R-0xs&0w5#?#A#w+0j%4qPO%^5#5#>$0OPi%a5#G$08#<Q0R%a5#G#A#6#AQ0X%a5#G#A$0iPz%a5#G#F#A#8Q0v%a5#G#F#F%^5#:$07%a5#G#I#N#A%65#8#6#I#9%D5#5#8#:%65#8#6$06Rz%D5#5$0i%65#8#d#9Ri%D5#<#I#?%H5#A#@#9Rq%D5#<#N#?%H5#F$0BRG%D5#<#?#?%H5#I$06%D5#<#@#;%H5#5#A%D5#<#6#F%H5#5#;#9RU%D5#<#\%H5#<#w%D5#N#<%H5#N#kRa%D5#N#<%H5#N$07%D5#N#:%H5#>#x%D5#N#:%H5#>#?%D5#N#X%H5#G#:#9%D5#N#X%H5#G#8%D5#>#5%H5#?#;#9RP%D5#>#5%H5#:#w%D5#>#?%H5#7#kRT%D5#>#?%H5#7$07%D5#>#;%H5#@#x%D5#>#X%H5#@#:#9%L5#I%65#^#7#9%L5#5%65#^#X#9%L5#G%H5#s#9%L5#?%}5#k%L5#?%}5$06%L5#:%}5#x%L5#:%}5$0B%L5#7%}5#:#9%L5#7%}5#@#9%L5#@%}5#;#9%L5#@%}5#6#9%L5#8%65#s#k%L5#8%65#s$06%L5#;%65#s#x%L5#;%65#s$0B%L5#X%H5#z#9%L5#X%65#s#@#9%L5#6%H5#H#9%L5#6%H5#d#9%P5#A%65$04#k%P5#A%65$04$06%P5#F%65$04#x%P5#F%65$04$0B%P5#F%65$04#?%P5#I%65$04#7#9%P5#I%65$04#8%P5#5%\5$08#9%P5#5%65$0:#w%P5#<%65$0:#I#9%P5#<%65$0:#?%P5#>#N%65$0:#7%P5#>#;%65$0:#8%P5#G#N%\5#5#<%P5#;%\5#5#>#9%P5#;%\5#5#?%P5#X%\5#5#7#9%P5#X%\5#5#8%a5#z#7#A%\5#G$07Rk%D5#7#F#?%\5#:$06%D5#7#N#N%\5#:#>%D5#@#A#;%d5#7#7$0O%D5#v#8%d5#@#A%a5#\#8#<%d5#@#5%a5#\#8%d5#@$07%a5#\#;#<%05#R#@#;%j5$03#>#A%05$0v#^Ps%05#R#@#X#9RlP@%BlPs%R5#>#FP>%U?R?%M5$03#A%05#R#8#;%M5$03#5#?%05#R#;#kRl%M5$03#<#?%05#R#;#xRDPsPDP@PmQ0I%M5$03#>#<%j5$03#G#8&025$08#kRD%j5$03#?#>&025$08#I#9Rg&025$08$06RE&025$08$07RX&025$08#x%05#y#A$07Rb&0u5#y#<PsP^P@Pm%j5$0F#:#?%05#y#I#G%j5$0F#7#<%05#y#I#7#9RmPsPmP@P=%j5$0F#7#8%05#y#I#8%j5$0F#@#?%05#y#I#6#9R=PsP=P@%4]R]#B%05#y#5#wR=%j5$0F#;#?%j5$0F#^&025#<#R%4n:0I?J1Tr]PsPzP@%15#7#7#8#7#ER]Ps%W5#G#;P@%15#@#?#X#<#ERrPs%W5#G#XP@%\5#<#I#9R?#BRJPs%W5#G#XP@%15#z#;#:#EPsPiP@P]Ps%V5$01#5P@PvPs%V5$01#<P@PJPs%V5$01#<P@%15#z#;#@#EPsPqP@%15#7#@#F#>#ERJPs%V5$01#:P@PrPs%V5$01#7P@%BkRrPs%V5$01#7P@%15#z#s#EPsPGP@PJPs%V5$01#6P@PvPs%W5#:#AP@PrPs%W5#:#AP@%15#z$0:#EPsPUP@%15#7#:#@#I#ERUPs%W5#:#zP:%B[R[Ps%V5#v#FP>PsPs%V5#v#FP@%BzPs%V5#v#GP@PsPsPaP@%15#7#:#6#7#ERaPs%V5#v#:#:P:P[Ps%V5#v#@P>PsPs%V5#v#@P@%BqPs%W5#@#FP@PsPsPPP@PUPs%W5#8#G#:P:P[Ps%W5#8#:P>PsPs%W5#8#:P@%BiPs%W5#8#6P@PsPsPTP@PaPs%W5#;#F#:P:P[Ps%W5#;#5P>PsPs%W5#;#5P@%BGPs%W5#;#:P@PsPsP?P@%15#7#8#>#?#EPsPkP@%15#7#@#@#8#EPs%V5#6#5#@P@%I5#s#<#EPsPlP@%B=CbR=PsPDP>PKCbPsPgP@%BEPsPXP@&025#?#<#?#EPsPbP@%15#z#;#>#E&0^9-0g=DCDCDC400DcDCDCDSDSDcI0EDCDSDSDcI0EDCDSDSDcI0EDCDSDSDcI0EDCDSDcDSDCDSDcDSDCDSDcDSDCDSDcDSDC4003e40fDC40R3eDC3q3eDC80R^I0eI0M40fDCI0M3~DcDC3e3e40H3e3e3q3e3q40R3~40?3~40?3e3e3e3~40?40H40?3~40?3~40sDhDhDhDhDhDhDhDhDhDh40?40?40D40D40H40D40H40D3~40D3~40D40H40DI0M3e3q3q3q3q40R3q40HI0MI0MI0eDZI0EDCDCDZD=D=D=D=D=D=D=D=D=400I0EDgDpD=D=DCDCD=D=D=DpD=DpD=D=D=D=D=D=D=D=DCD=D=D=DCDCDcDCDCDcR^D=DpDgDpDgDpDgD=DgD=DgD=400DZD=400DZDZDZDZR=N<0\,|MR9;O9Rb20;44RX00;4R420@RO>0>XQRR;ORRE20;66Rg00;6RD00;6RlPgPZQ06PdCo>0QDKRk;OkR?A]023RG=O7GR[POPQ%75#;#I#kRaPZPZPZPcPsPsPHQ0Q#2RT%BaPHQ0HQ0J%2T#rRi%2iRi%2iRiPv205KuPs%riRi#U%2iRi%2iRi%2iRi%2iRi%2iRi%2iRiPYPKQ07PsPsPsPsPsPsPs&0Ni$0LRi%2iRi%2iRi%2i00ch3YH0KDnDn3Y3Y3YDn3YH0KH0`RiQ0VQ0WQ0YQ0[Q0^Q0_Q0`Q0aQ0bQ0cQ0iP{Q0kQ0lQ0mQ0nQ0pQ0qQ0rQ0U20gx^DZDZR^:00~}DZDZDZN<0\,|MR}=ON}Rx20@aO>0>XQRY=O4YRUPgPZPZPsCoRP=ODPRq%75#A#F#6$0O=]03Rz=O7zRr20_ICg00XfRJg00YFR]PJP;P>PCH0rQ0PH0[00G3+0G9]02Rn=O7nRmPOPQ%75#X#:#6#9RwPZ20=S_RWPZPcP8PCPePB%BwPeQ0HQ0JQ08Q09Q0:Q0KPpPCQ0;#UQ0<Q0=Q0>Q0?Q0@Q0APsQ0MPvPdPsP8PsQ0PQ0LPtQ0BQ0CQ0DQ0E00ch3YH0KDnDn3Y3Y3YDn3YH0KH0`P=N<0\,|MR==ON=Rh20@wO>0>XQRw=O4wRtPgPZPWP8CoR8>0QDCRC=OlCRW%85#F#8#?$0O=]03R5=O75RePOPQPaPZQ0Z#a#Q,mSRaPZPcPsPsPHPiQ0VQ0WQ0YQ0j%4`80m:PSQ0tP@Q0OPSQ0uP@PvPSQ0dP@PuPSQ0gP@Q0NPSQ05P@PpPSQ0sP@Q0KPSQ04P@Q0FQ0[Q0^Q0_Q0`Q0aQ0bQ0cQ0iB00{~^DZDZDgDpDgDpDgDpDgDZN<0\,|MR^=ON^R~PgPZPaPsCoRa=ODaR{/KrR@,KURp'KRu,K[Rv'KR:'KR`'KRi'KRH'KRc'KRQ'KRO'KR\'KRF'KRV'KRA'KRj'KP7PLPbPjPNP9PEPAP4PRP?PVPlPkP[PF1l7GRFPxP\1lN}PUPO1l4YROPqPQ1lDPPrPc1l7zRcPmPH1l7nPhPiPNP=PtP`P4PwPWP:PlPCPePvP7P5P[PuPFP~Pp1lN^PUP@POP{Pr1lDaPcK0PK0PDuDuDuDuK0PK0PK0PDuDuDuDuP720;<0R<g00Z8Rcg00[33tRr-0A0$0C20<0r5]0Q02Q03g00[oRr40q00=I00_K00G39]02PNg00\jg00]g60Xfg00^dRf,|MP4&0Uf&0Wf+0@&0Zf60>XPRPlPg&0Sf&0Vf&0pfCo&0Tf60QDPgPZB0b1Sr00=_PdCo>0QDKP7g00_a9t<cRK-0A0$0C20<0K5]0PGPNg00`]g00aZ60XTg00bWRK,|MP4&0UK&0WK+0@&0ZK60>XPYPDPg&0SK&0VK&0TKCoPPP7g00cT9t<cRP-0A0$0C20<0P5]0PzP7g00dP9t<cRP-0A0$0C20<0P5]0Q00Q01PIPrH0[PJP]PJP;P>PrH0rB0Y1rs005sH0[00G3+0G9]02PNg00eLg00fI60XBg00gFRB,|MP4&0UB&0WB+0@&0ZB60>XPwPlPg&0SB&0VB&0pBCo&0TB60QDPDP6P8PrH09P7g00hC9t<cRr-0A0$0C20<0r5]0P5P7g00i?9t<cR5-0A0$0C20<055]0PGPNg00j;g00k860XTg00l5RT,|MP4&0UT&0WT+0@&0ZT60>XPYPDPg&0ST&0VT&0TTCoPag00m29t<cRc-0A0$0C20<0c5]0=O7zFiFiFiFiFiFiFiFiFido"). Qed.

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xe1e4c%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0xe0e44%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe1998%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xe0e44%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xe0e44%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xe0e44%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd537c%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xd00fc%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_S1OpenFail_defs ()) ["FXALL"] "p%0p&0p;1p;2p;3p;4p;<g0000k10uTg000Pk20>Tg005Xk10JTg0068j3PTg002Fj12Tg002ej1[Tg001Nj1=Tg004Uj11Tg0074j10Tg00@Ik403Tg009Kj2YTg00mnk40QTg00?Qk40PTg0010j1rTg003]k30MTg005:j14Tg006Rk10sTg007Yk30DTg008Qk30:Tg00:Dk20TTg00;>k20STg00<8k40bTg00=2j2QTg00=lm<0tTg00>ok20[Tg00L0j4aTg00AEj2TTg00A`k20ZTg00B:j3cTg00K8k30KTg00CMk30rTg00DOk10qTg00EMk10pTg00FIk10oTg00GFk10nTg00HCk10mTg00J<k10lTg00LPj3>Tg00M0j3{Tg00Mjk40fTg00BWk10YTg00NEk30WTf0R0#1#1#0#0p=5%00#0#1#1p=3%10#0#0#1p=:%10#0#0#4p>0=g00Q\R1f2R2f1R3P0Cap=\%00#0#0#1p=I%10#0#0#0p=@%20#2p>0?%20#2#2#2p>0E%20#2#2#2#2#2#2#2p>0G%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0Xg00NbR4@0D30p>05%10#1#1#1#1#1#1#1p=]%10#1#1#1#1p>0H%10#1#1p=R%00#0#0#0#0#0#0#0p=O%00#0#1#4p>0dg00P`R5?>30p=b%00#0#1#1#0#0#0#4p=p%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0AB0K430p=W%40#=p=Vg00XfR6g00OnS00P3P0H03p>0F%10#0#1#0p=7%00#1#1#0p=8%10#1#1#1p=6%10#1#0#1#1#1#0#0p=^%00#0#0#4p=;%10#1#0#1p=A%00#0#1#0p=H%00#0#0#1#0#0#0#4p=j%00#0p=Z%00#rp>0<%00#0#0p=J%00#0#0#0p=B%00#0#4#=p=E%00#1#1#1#0#0#0#4p>06%00#1#0#0#0#0#0#1p=y%00#1#0#1#0#0#0#4p=xg00R:R7%[2%[3=>703>p>0;A>7309>72p=i%[3=>70p>0V%10#1#0p>0I%10#1#1#0#0#0#0#1p=u%00#1#1#1p=G%00#1#0#1p=L%10#0#1#1p=C%00#1p>0Uf3R8/Y2?{30p>0C%00#1#0#0p=?%10#1#1#0p=X%00#0#1p=f%00#0#0#0#0#0#1#1p=s%10#4p>0e%00#0#0#0#0#0#0#4p=q%10#1#1#0#1#0#1#0p=v%r0,Y3p>0c%00#0#4,Y3p>0a%10#0p>0`%10#1p=e%00#0#0#0#1#1#1#0p>02%10#1#1#1#1#0#0#0p>0R%00#1#0#0#0#0#0#4p>01%10#1#1#1#1#1p=D%10#1#1#1#1#1#0#1p=F%10#1#1#1#1#1#1#0p=U%10#1#1#1#1#1#0#1#1#1p=K%10#1#0#1#1#1#1#1p=o%10#1#1#1#1#1#0#1#1#1#1#0p=w%10#1#1#1#1#0#0#1p=n%10#1#1#1#1#1#1#0#0#0p=M%10#1#1#0#0#0#0#0p>00%00#1#0#0#0#0#0#0p>0_%00#0#1#0#0p=~%00#0#1#0#0#0#0p>0^%00#0#0#0#0#1#0#0p>08%10#1#1#1#1#1#0p=S%10#1#1#0#1#0#0#0p=}g00S2R9?>30p>0]f4R:/Y8?{23=>90p=<A>9309>92p=m%08#0#0#0#4,Y:?{23=>90p=`%18#0#0#0#4,Y:?{23=>90p=N%48,Y:?{23=>90p>07%02#4%03#0#0#4'Q=>90p=_%03#4,Q2=>90p>0O%02#4/Q3=>90p>0B%12#4/Q3=>90p=l1Q:81Q23=>905>9p>0N%0:#4/Q8%02#4/Q3=>905>9p>0@%12#1#1#0#0#4%03#0#0#4'Q=>90p=t%12#1#1#0#0#4/Q3=>90p>09%02#1#1#0#0#4/Q3=>90p>04%12#0#1#0#0#4/Q3=>90p>0\%1:#0#1#0#0#4/Q8%02#0#1#0#0#4/Q3=>905>9p=h%02#0#1#0#0#4/Q3=>90p=|%r8,Y:?{23=>90p=9%18#0#0#0#r,Y:?{23=>90p=g%08#r,Y:?{23=>90p=kP7P7P3P0Cap>0LP:P820Z23P0H0fp=dg00SlR;?c30$0Yp>0kB0W;30p>0iP1P8P2P3Ca=P:0p>0hAP823/T0p>0jf6R<f5R=;P:AP823/T0'Tp>0gf7P1P<Ac;=:$0YB0W;82Ca;P3/T0p=z&0u5R0-0>1R3g00TiR8#5#3#5#:$0=&0J5R55\0R2;P2%58#I#5#@$0=R=g00ONR:g00njg00V:R<#2R>#2R?#2R@#2RA#2RB#2$0?RC$0?$0E$0G$0XRD#[REg00XHRF#=RG+05RH%18RI#1RJ#1RK#1RL#1RM#1RN#1#]RO#1RP$0HRQ#1#]RR#RRS$0H#]RT$0HRU#0#O$0dRV#=H03/b55\0RW=P3WS01A\0=5RX=P3XS02%58#3#3#p=\05RY=P3YS03P:g00o\S04%2D$0?$0G$0A$0ARD#[RZ005GR[PZH03%[?R?/WZ/YFP>P:PGH0Q/b5'b9\0=R\=P3\S05%VMR]00FZP6g00YFS06P6P<PAPZH0P205[GH03/b5'b9\0=R^=P3^S07g00UNS08%r8#=S09<0MZ/W]%48R_#=R`+0F/b59\0=Ra=P3aS0:%78#7#8#6$0==\05Rb=P3bS0;g00VYRc$0sRd%^8#3#8#;Re%08Rf#4Rg%78#A#H#jRh%[<Ri%0fRj#0Rk#1Rl#1Rm#0S0<#ZS0=#0S0>#rS0?#='WRn1WiZ%0kRo#1Rp#1Rq#1Rr#1$0<#=Rs'WRtPn%1fRf#0Ru#JRv#VS0@PGPG%1jRj#0Rw#0Rx#0Ry#0S0A#0S0B#0S0C#rS0D#=,WiRz&0?D$0E$0X$0A$0A$0ARD%=h%0pS0E#ZS0F#ZS0G#B#E%08#O#A$06Rp#=%2D$0ER{%2{R{%2{R{%=eR|205G[S0H%Vl+05R[-05`&0E{R{#[%2{R{%2{R{%2{R{%2{R{%2{R{%2{R{%08#y#H#xR}#=R~%Z8#@#3#7#8#E%2{$0?$0GR{%2{R{%2{R{%2{&0J740;40;9iGG9iGG9iGG7iG7i`40;40;40;5iG3i+0V40;3i7iz+0VPG%^8#3#7#;S0IPC%JKS0J#0S0K$0<#=,WiS0LPG&0I8#u#APCPnPG%^8#3#A#;S0MPCPnPi%1xRxPC%38#G#:#I#VPi%BxPCP|PiPyPCP[PiQ0CPCg00W\Rx%VRRR<0D[Pi%1mRmPCPRPi%JmS0CPC%1wRw#VPiQ0<PC%18#L#7#C#8#EPi%0lRl#1RmPCPGPi%0lRl#0S0<#0S0N#0RRPCQ0HPi%JmRmPCPZPiQ0>PC%0oR[#1RK#0R{#1$0U#3#EPiPlPCPG%4P:0:ZFPi%JM$0<PCP?H0CPiQ0DPC%1u#Z$0<Ru#=,WiPiPRP>%V[RRPiPmPC%0IRI#1Rm#1RM#1#Z#5RZ#1$0U#G#B#8#6#H#B#G#?#8#6#8#X#VPiQ0?PC%fZ#8#3#H#s#7#8#:#8#5#8#3#VPi%JrPC%ZS#5#5#5#5#5#5#A#VPi%BqPC%0T#]#]#VPi%JNPC%0IRI#1RN#1#3#3#3#3#3#EPi%J{PC%JwRw#@#:#VPi%0[R[#ZR{#ZRTPCP~PiP[PCPGPiPKPCPzPiQ0EPCQ0LPiQ0GPC%1jRj#1#Z$0<Rz#=,WiPG&0I8#u#5PCPGPG%^8#3$06RKPCPGPG%^8#?$06RqPA%RU#]$0eRU#=PG&0I8#X#H#IPCQ0@PG%^8#?#jRSPCPnPGPePA%VfPiQ0BPCPGPiPwPCPGPi%JjRjPCPGPiPzPCPGPiQ0=PCPGPiQ0CPC%1fRf#JRz$0<Rw#=,WiRrPiQ0NPC%[ARZPiQ0FPCPGPiP{PCPGPi%JLPC1WiRRRPiQ0KPCP?Pi%0JRJ#1RL#JPC%=gR{Pi%ZJRJ#0RPPCP~Pi%JMPC%18#L#L#8#H#EPi%JmRmPCPrPi%JNPCPZPiPjPCPGPi%0vRjPCPGPiPuPCPEPiPwPCP?PiQ0<PC%VJPiQ0APCPGPi%0IRI#ZRwPCP{PiPfPC%:8#8#I#3#EPG%O8#8#I#?PAB0DxGH%OO#O#O#qRO%ZTRT#BRx#J#BRH#0Rf#@#B#O#qRu60:?B0:EVUPiQ0JPCPGPiPPPCPGPiPmPCPGPiPwPCPGPiPzPCPRPiPvPC%:8#L#G#7#EPiPyPCP{PiP[PC%4kRk#=,WiPiPJPC%18#3#v#5#E%4oRo-0Ti%Of#O#q:0:iO20ciHRf%4HRH+0SPiPFPCP{H0CPiPkPC%[>PiPoPCP?PiPIPCPG%[@R@@0:OuPfPH1Y@F%4jH0b20T@k%1L#@#O-0aG&0`8#@#B#q+0S%4xPe%^8#3#8$0=PK%e8#G$02#?Q0I%e8#G#B#6#BQ0M%e8#G#B$0RPS%e8#G#I#B#5Pq%e8#G#I#I%^8#:$01%e8#G#H#L#B%68#5#6#H#;%D8#3#5#:%68#5#6#pRq%D8#3$0R%68#5#]#;RS%D8#?#H#@%F8#B#C#;RK%D8#?#L#@%F8#I$06Rx%D8#?#@#@%F8#H#p%D8#?#C#A%F8#3#B%D8#?#6#I%F8#3#A#;RL%D8#?#U%F8#?#q%D8#L#?%F8#L#jRk%D8#L#?%F8#L$01%D8#L#:%F8#8#x%D8#L#:%F8#8#@%D8#L#X%F8#G#:#;%D8#L#X%F8#G#5%D8#8#3%F8#@#A#;Rj%D8#8#3%F8#:#q%D8#8#@%F8#7#jRH%D8#8#@%F8#7$01%D8#8#A%F8#C#x%D8#8#X%F8#C#:#;%K8#H%68#^#7#;%K8#3%68#^#X#;%K8#G%F8#o#;%K8#@%w8#j%K8#@%w8#p%K8#:%w8#x%K8#:%w8$06%K8#7%w8#:#;%K8#7%w8#C#;%K8#C%w8#A#;%K8#C%w8#6#;%K8#5%68#o#j%K8#5%68#o#p%K8#A%68#o#x%K8#A%68#o$06%K8#X%F8#n#;%K8#X%68#o#C#;%K8#6%F8#F#;%K8#6%F8#]#;%M8#B%68$00#j%M8#B%68$00#p%M8#I%68$00#x%M8#I%68$00$06%M8#I%68$00#@%M8#H%68$00#7#;%M8#H%68$00#5%M8#3%U8$02#;%M8#3%68#u#q%M8#?%68#u#H#;%M8#?%68#u#@%M8#8#L%68#u#7%M8#8#A%68#u#5%M8#G#L%U8#3#?%M8#A%U8#3#8#;%M8#A%U8#3#@%M8#X%U8#3#7#;%M8#X%U8#3#5%e8#n#7#B%U8#G$01Rf%D8#7#I#@%U8#:#p%D8#7#L#L%U8#:#8%D8#C#B#A%]8#7#7$0=%D8#v#5%]8#C#B%e8#U#5#?%]8#C#3%e8#U#5%]8#C$01%e8#U#A#?%08#O#C#A%f8#s#8#B%08$0_#^PG%08#O#C#X#;RuPC%=uPG%O8#8#IPA%[BRB%J8#s#B%08#O#5#A%J8#s#3#@%08#O#A#jRu%J8#s#?#@%08#O#A#xROPGPOPCPZ%J8#s#8#?%f8#s#G#5%~8$02#jRO%f8#s#@#8%~8$02#H#;RI%~8$02#pR{%~8$02$01RJ%~8$02#x%08#y#B$01R[&0^8#y#?PGP}PCPZ%f8$08#:#@%08#y#H#G%f8$08#7#?%08#y#H#7#;RZPGPZPCP@%f8$08#7#5%08#y#H#5%f8$08#C#@%08#y#H#6#;R@PGP@PC%4TRT#=%08#y#3#qR@%f8$08#A#@%f8$08#^%~8#?#O%4Q:0:B_1QFTPGPqPC%18#7#7#5#7#ERTPG%S8#G#APC%18#C#@#X#?#ERBPG%S8#G#XPC%U8#?#H#;R_#=RQPG%S8#G#XPC%18#n#A#:#EPGPSPCPTPG%R8#}#3PCP|PG%R8#}#?PCPQPG%R8#}#?PC%18#n#A#C#EPGPKPC%18#7#C#I#8#ERQPG%R8#}#:PCPBPG%R8#}#7PC%=fRBPG%R8#}#7PC%18#n#o#EPGPxPCPQPG%R8#}#6PCP|PG%S8#:#BPCPBPG%S8#:#BPC%18#n#u#EPGPLPC%18#7#:#C#H#ERLPG%S8#:#nP>%=oRoPG%R8#v#IPAPGPG%R8#v#IPC%=qPG%R8#v#GPCPGPGPkPC%18#7#:#6#7#ERkPG%R8#v#:#:P>PoPG%R8#v#CPAPGPG%R8#v#CPC%=KPG%S8#C#IPCPGPGPjPCPLPG%S8#5#G#:P>PoPG%S8#5#:PAPGPG%S8#5#:PC%=SPG%S8#5#6PCPGPGPHPCPkPG%S8#A#I#:P>PoPG%S8#A#3PAPGPG%S8#A#3PC%=xPG%S8#A#:PCPGPGP_PC%18#7#5#8#@#EPGPfPC%18#7#C#C#5#EPG%R8#6#3#CPC%H8#o#?#EPGPuPC%=@H0CR@PGPOPAP`H0CPGPIPC%={PGPJPC%~8#@#?#@#EPGP[PC%18#n#A#8#E&0J9-0]@D<D<D<3mD`D<D<DNDND`I07D<DNDND`I07D<DNDND`I07D<DNDND`I07D<DND`DND<DND`DND<DND`DND<DND`DND<3m3_40OD<40B3_D<3l3_D<80B}I0NI0@60OpD<I0@3tD`D<3_3_4093_3_3l3_3l40B3t4043t4043_3_3_3t4044094043t4043t40\DhDhDhDhDhDhDhDhDhDh4044043|3|4093|4093|3t3|3t3|4093|I0@3_3l3l3l3l40B3l409I0@I0@I0N3m3mI07D<D<3m3mD9D9D9D9D9D9D9D9D93mI07DgDkD9D9D<D<D9D9D9DkD9DkD9D9D9D9D9D9D9D9D<DkD9D9D<D<D`D<D<D`D9DgDgDgD9D9D9D9D9D<D9D9D<3mDgDkDkDkDgDgDkDgDkDgD9DgD<DND<N<0t-0[cRp;PpR}20>11R@00>1R9P@P1P1P1PhPeCaPgCaRg;PgRe20>77Rh00>7RCPhP720LntPGCaRt;PtR[%78#B#I#6$0==\05R8=P38RJ'TR{'TRI'TRO'TRu'TRf'TR_'TRx'TRo'TRk'TP3P2Q01PkP3PWQ02PoP3PXQ03PxP3PYQ05P_P3P\Q07PfP3P^Q0:PuP3PaQ0;POP3PbP}PIPdPpPeP{P9PgP[PJPCPt20Z38DdDdDdDdDdDdDdDdDdDdDdP3P0P020>;0R;g00Z8Rtg010N3cRJP0PJP2P3P0P0g011I9c;tR2P0P2PWP3P0P0g012D9c;tRWP0PWPXP3P0P0g013?9c;tRXP0PXPYP3P0P0g014:9c;tRYP0PYP:Q04g00[oRY>0D4GRXPYH03B0K4?Y/YFP>P:PGH0Q/b5'b9\0=P3P0P0g01559c;tR:P0P:P6Q00P]PYH03P6Q06P6P<PAPYH0P205XGH03/b5'b9\0=P3P0P0g01609c;tRXP0PXQ08Q09<0MY/W]00F`/b59\0=P3P0P0g016k9c;tR=P0P=PbPdg017fg018b60rDg019^RD-0[cP9P@P1P1P1&0qD&0pDCa&0oDCaPgPCPhP7&0nD&0mD+0L&0lDCaPhP7B0K4iY/Ws-0LnPGCaP3P0g01:[9c;tRt-0k020i0tP8I0hH0jK0gGzGzGzGzGzGzGzGzdo"). Qed.

End FXALL.
