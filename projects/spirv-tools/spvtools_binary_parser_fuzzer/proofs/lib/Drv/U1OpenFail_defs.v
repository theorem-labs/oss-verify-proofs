(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1MainEntry U1LibStdioCall.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2PXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4srH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4knH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4scH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rI3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4srF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4knF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4scF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4srH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4knH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4scH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3rI4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs4scOFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv?U1OpenFail_defs2rIC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FXALL.
Context {fx : FPState}.

Definition STOPS : list Z := [0xe2b9c; 0xe311c; 0xe36f0; 0xe2aa0; 0x65cdc; 0xd56bc; 0xd1e54; 0xd70d4]%Z.
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

Definition IHI : Z := 0x124000.

Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition ssA0 : sym_state := SS 0x6583c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xe3ba8 srB0 [] knB0 39.
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
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0xd7b64 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

Definition ssH0 : sym_state := SS 0xd7b64 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

Definition ssI0 : sym_state := SS 0xd8660 srI0 [] knI0 263.
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

Definition ssI30 : sym_state := SS 0xd8660 srI30 [] knI30 263.
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

Definition ssH40 : sym_state := SS 0xd7b64 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.

Definition ssI40 : sym_state := SS 0xd8660 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xd70d4%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0xd8830%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x13790, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xd70d4%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0xd1e54%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xd70d4%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0xd9250%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xd70d4%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0xd1e54%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_U1OpenFail_defs ()) ["FXALL"] "p%0p&0p&1p;1p;2p;3p;4p;<g0000k112Tg000Pk20ATg0010j1QTg001Nj1BTg002Fj12Tg002ej1STg003]k30tTg004Uj11Tg005:j15Tg005Xk10_Tg0068j3KTg006Rk10|Tg0074j10Tg007Yk30ZTg008Qk30FTg009Kj2ZTg00:Dk20kTg00;>k20jTg00<8k40yTg00=2j2OTg00=lm<0]Tg00>ok201Tg00?Qk40uTg00@Ik40[Tg00AEj2LTg00A`j2rTg00B:j3}Tg00BWk10:Tg00CMk30YTg00DOk10VTg00EMk10XTg00FIk10\Tg00GFk10TTg00HCk10WTg00I@k10sTg00J<k10UTg00K8k30cTg00L0k409Tg00LPj34Tg00M0j3cTg00Mjk40bTg00NEk30}Tf0R0#1#0#1#0p=D%10#1#1#0p=C%00#0#0#1#1#0#1#0p>11%10#0#0#5p>0O%20#2#2p>0N%20#2p>0h%20#2#2#2p=w%20#2#2#2#2#2#2#2p>0K%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>04%50#Bp=Vg00NbR1f1R2<0c0p>0=g00ONS00g00OnS01P2P0H0[p>0`g00P`R3?420p>0Eg00Q\R4f2R5P2P0H09p=X%10#1#0#1p=7%10#1#1#1#1#1#1#0p={%00#0#0#1#0#0#0#5p=j%10#0#1#1p=G%00#0#0#1p=R%00#0#0#0#0#1#1#0p>05%00#0#0#5p==%00#0p=E%B0:0c12p=g%10#1p=v%00#1#0#0p=J%00#0#5#Bp=F%00#Qp>0^%00#0#0#0p=6%00#0#0#0#0p>02%00#1#0#0#1#0#0#0p>03%00#0#1#1p=;%10#1#1#1#1#1#1#1p=s%10#1#1#1p=HB0Z120p>08%00#1#1#1p=?%10#0#0#1p=8g00R:R6%S2;40p>0d%S5%S2=460546p=Tf3R7%S2=4609465546p>0Hf4R8A462094659467546p=p%S7A46209465546p>0a%00#1#0#1p=I%00#0#0p=31Z75?c20p=d%00#1#1#0p=>%10#0#0#0p=9%05#Q,Z7?c20p=\%00#1p>0r%10#0#0p>0G%10#1#0#0p=:%00#0#1#0p=Y%00#0#0#0#0#1#1#1p=[%00#0#0#1#1#0#0#1p>0q%00#0#0#0#0#0#0#1p>0p%10#5p>0o%B09c52p>0n%10#1#1p>0m%00#0#1#0#0#0#1#0#0p=n%10#1#0p>0l%10#1#0#0#0#0#0#5p>0D%00#0#0#0#0#0#1#0p=m%00#0#0#0#0#0#0#0p=P%00#0#0#0#0#0#0#5p=`%00#0#0#0#0#0#0p=l%00#0#0#0#0#0#0#0#0p=a%00#0#1#5p>0{%Q0,Z2p>0z%00#0#5,Z2p>0x%10#0p>0w%00#0#0#0#0#1#0#0p=i%10#1#1#1#0#0#0#5p>07%00#0#0#0#0#0#1#1p=^%00#0#0#0#1#0#0#0p>06%00#0#0#0#0#0#0#0#1p=M%00#1#0#0#0#1#0#0p>0i%00#0#0#1#0#0#0#1p>0M%00#0#0#1#0#0#1#0p=h%00#0#0#1#0#0#1#1p=]%00#0#0#0#0#1#0#1p=W%00#0#0#0#0#0#0#0#1#1#0p=A%00#0#0#0#0#0#0#0#1#1#0#0#1p=y%00#0#0#0#0#0#0#0#1#1#0#1#0p=x%00#0#0#0#0#0#0#0#1#1#0#1#1p=|%00#0#1p=f%00#0#1#0#0p>0L%00#0#0#1#1#0#1#1p>0vg00S2R91Z87?c52;40p=@%07#0#0#0#5,Z8?c52=490p=b%17#0#0#0#5,Z8?c52=490p=N%57,Z8?c52=490p>0BA49209495p>0C%05#5%02#0#0#5'O=490p=_%02#5,O5=490p>0g%05#5/O2=490p>0S%15#5/O2=490p=u1O871O52=490549p>0f%08#5/O7%05#5/O2=490549p>0J%15#1#1#0#0#5%02#0#0#5'O=490p=z%15#1#1#0#0#5/O2=490p>0I%05#1#1#0#0#5/O2=490p>0<%15#0#1#0#0#5%02#0#0#5'O=490p>00%18#0#1#0#0#5/O7%05#0#1#0#0#5/O2=490549p>0e%05#0#1#0#0#5%02#0#0#5'O=490p=t%05#0#1#0#0#5/O2=490p>0R%15#0#1#0#0#5/O2=490p>10A4920949594979498p=U%Q7,Z8?c52=490p=<%17#0#0#0#Q,Z8?c52=490p=e%07#Q,Z8?c52=490p=oP4P4P2P0H09p>0@P5P4P2P0H09p>0>P7P6P6P6P5P2H09P0H09p=qP5P6P2P0H09p>0QA4920p>0~f6R:f5R;P8P7P5P2P0H0bH0bp>0PP8P71r52P0H0bp=~g00SlR<?}20p>0?B0}<20p>0;AK:;8AK752/L0'Lp=k&123R0-0A4R7g00TiR5#D#C$11$0OR2g00UNS02%Q5#BS03g00V:R;#2R:#2R8#2R=#2R>#2R?$0NR@$0h#w$0K$04RA$0N$0K$04$04$04$04RB#SRC40t%15RD#1RE#1RF#1RG#1RH#VRI+0=%55RJ#BRK+0`&0_3R3+0E5X0RL;KLg00VYRM$0|RN%75#{#jRO%05RP#5RQ%G5#R$05#=RR%S;RS%0PRT#0RU#1RV#1RW#0S04#ES05#0RX#QRY'gRZ20=SC%0UR[#1R\#1R]#1R^#v#Q#BR_+0=S06PZ%1PRP#0R`#0Ra#0S07#0Rb#VRc%E5#7#C#J#FRdPK&0^XRX,gSRe&0hB#w$04$04$04RB#2#wS08#2S09#2S0:#wS0;#2S0<#2S0=#2S0>#2S0?#2S0@#2S0A$0N$0KS0B#2S0C#2S0D#2S0E#2Rf%BRS0FPe%0\R\#ES0G#ERg#6#FS0H&025$03#;#=S0I#BS0J%2f#wRh%2hRh%2hRh%1TRT#0Ri#1Rj#VS0K%1HRk#1#sRl#1Rm#1#HRn#1#sRo#VRpPK%whRh#S%2hRh%2hRh%2hRh%2hRh%2hRh%2hRhg00W\Rqg00XHRr#BRs208CsRt+08S0L%VVS0M+08Ru80ZpS0NPu%BORv%;5#?#8#R#VS0OPKPdPs208tsS0PPKPt&0Nh$0KRh%2hRh%2hRh%2hS0Q&0_6Rh+0d3TH0HDpDp3T3T3TDp3TH0HH0aPs%75#{#I#=S0RP@%3FS0S#0S0T$0^,gSS0UCdS0VPs%75#{#>#=P@PZCdS0WPs%75#{#9#=S0XP@PZCdS0YPS%0VRV#1RF#1S0Z#EP@PsC\S0[PS%0VRV#0S0\#0S0]#0RwP@Q0LC\S0^PS%3FRFP@PCC\S0_PSPXP@%0[RX#1Rx#0Ry#1$0r#;#FCdS0`PS&0GVP@PsC\S0a%5m:0FCrS0bPS%3HP@%S8R8C\S0cPS%0iRi#0S0d#0S0e#0S0f#0S0g#QRHP@%1`Rm#0RV#ERz#QS0h,gSCdS0iPS%QwP:%VXRwCdR{PS%QFP@%0DRD#1RF#1R|$0G#:R}#1$0r#?$05#H#Y#[#J#>#H#>#C#VCdR~1ZSYS0j%E}#G$0q$0p#7#;#J#G#>#;#R$0o80n@R}PS%E^P@&0moRo#E#:#:#:#:#:#:#7#VC\S0kPS%3]P@%1o#H#sRo#0#s#s#VC\S0lPS%EkP@%0DRD#1Rk#1#;#;#;#;#;#FC\S0mPS%EyP@%3jRy#9#8#VC\S0nPS%1m#6P@%S>RmPS%0XRX#ES0o#ER]#QP@%n5#7#jR^#BRYCdS0pPS&0GXP@PsC\S0qPS&0GxP@1gSHRHC\S0rPS&0G\P@Q0UC\S0UPS%QgP@%1TRT#1Rg#3R\#QS0s,gSCdRxPS&0GVP@PsC\PS%EzP@PsPS%1aRaP@PsPS%6aP@PsPSQ07P@PsPS%0bRa#EP@PsPSPgP@%VPRgPSP\P@%E5#9#D#{#FS07PS%0TRTP@PKPS%ETRT#0R\P@PYPSPjP@%;5#?#?#7#VPSPyP@PvPS%1iS0t#3S0uP@%15#>$0q#6#FPs&0l5#s#RP@PsPs%75#{#Y#=RiP@PsPs%75#s#Y#=S0vP>%1o#HRo$0m#s$0oRj#BPs&0l5#s#>P@PcPs%75#{$0DRzP@PZPsPOP>PgPSQ0fP@PsPSPyP@PsPSP\P@PsPSQ0sP@PsPSQ05P@PsPS%1WS05#3S0sP@%1PRP#3RW$0^R\,gSRyPSQ0]P@PmPSQ0GP@PsPSQ0oP@PsPS%3GP@20=SwRwPSQ0TP@P8PS%0ERE#1RG#3P@%BQRgPS%EERE#0RVP@PYPS%3|P@%15#I#:#G#9#FPS%3FRFP@PyPS%3kP@PmPSPTP@PsPSPaP@PsPSQ0hP@%SARAPSP\P@P8PSQ0\P@%VEPSQ0eP@PsPS%0DRD#ER\P@PgPSPPP@%85#>#D#9#FPs%m5#;#?#JP>208As:0Zqs%Pl#P#P#`Rl%E]R]#6Rq#lRP#0RT#9#6#P#`Rk60F8%ao$0{>0FAjPSQ0SP@PsPSPVP@PsPSPFP@PsPSP\P@PsPSPWP@PwPSPbP@%85#>#6#H#FPSQ0dP@PgPSPXP@%5URU,gSPSPEP@%15#J#>#m#F%5[R[-0kS%PT#P#`:0FSl20zSPRT%5PRP+0jPSPrP@PgCdPSPUP@%S:PSP[P@P8PSPDP@Ps%S=R=@0FlkPTPP1Z=r%5aH0y20k=U%1G#:#P-0xs&0w5#D#6#`+0j%5qPO%75#{#R$0OPi%v5#?#H#8#6Q0R%v5#?#H#8#:Q0X%v5#?#H#D#JPz%v5#?#H#G#9Q0v%v5#?#H#:%C5#i#`%v5#9#R#P%a5#8#C#=%35#m#?#8%a5#8$07Rz%35#m#D#9%a5#D#G#=Ri%35#m#7#9%a5#G#?#=Rq%35#^$06%a5#:#;#=RG%35#^#;#9%a5#:$07%35#^#>#7%a5#7#:%35#^#D#R%a5#C#8#=RU%35#^#D#C%a5#C$0D%35#^#H%a5#H#7#=Ra%35#^#H%M5#6#`%l5$0i&025$0M#j%l5$0i&025$0M#J%35#i#8&025#h#I%35#i#8&025#h#9%35#i#C&025#]#8#=RP%35#i#C&025#]$0D%35#W#;%M5#J#7#=RT%35#W#;%M5#I#`%35#W#9%M5#>#j%35#W#8%M5#>#I%35#W#7%M5#?#>#=%35#W#C%M5#?#D#=%A5#Y%M5#9#G%A5#;%M5#9#7%A5#;%M5#9$07%A5#J%y5#j%A5#J%y5#;%A5#I%y5#I%A5#I%y5#?%A5#>%y5#8%A5#>%y5#G%A5#?%y5#7%A5#?%y5$07%A5#9%x5#j%A5#9%x5#;%A5#8%x5#I%A5#8%x5#?%A5#D%x5#8%A5#D%x5#G%A5#G%x5#7%A5#G%x5$07%A5#:%|5#j%A5#:%|5#;%A5#:%|5#J%A5#7%|5#>#=%A5#7%|5#9%A5#C%|5#D#=%A5#C%|5$0D%A5#H%|5#C#=%A5#H%M5#:#J%35#[#R#I%M5#:#>%35#[#R#7%M5#:#9%35#[#Y#I%M5#C#6%35#[#9%M5#C#Y#=%35#[#9%M5#C#J%35#[#8%M5#C#>#=%35#[#8%M5#C#9%35$06#I#6%05#m#Y#`Rk%35$06#:#9%05#m#;$07%l5#8#W%05#m#J#Y%l5#8#G#7%05#^#I#>$0O%l5#7#I#:%05#^#I#:%l5#7#?#J%05#^#I#H%l5#7#?%05#^#>#`%l5#7#9#J%05#i#>#8%f5#h#R#6&0L5$03#9Ps%05#i#>#D#=RlP@%BlPs%m5#;#?P>%S?R?%35#R$0v%05#i#?#8%35$0M#C#9%05#i#?#7#=Rl%35$0M#H#9&025$03#jRDPsPDP@PmQ0I%35#h#R#J%f5#h#Y#:&0L5$03#7#=RD%f5#h#;#>&0L5$03#C#=Rg&0L5$03$07RE%n5#8#`RX%n5#8#j%n5#G#`Rb%f5#h#:#JPsP^P@Pm%f5#]$03%n5#7#;%f5#]#I#J%n5#7#>#=RmPsPmP@P=%f5#]#I#:%n5#7#9%f5#]#>#9%n5#7#G#=R=PsP=P@%5]R]#B%n5#7$0DR=%f5#]#9#9%f5#]#9#:%05$03#P%5n:0F?J1Or]PsPzP@%15#G#Y#Y#6#FR]Ps%65#W#;P@%15#:#^#D#FRrPs%65#W#JP@%M5#C#C#=R?#BRJPs%65#W#JP@%E5#6#]#R#FPsPiP@P]Ps%65#W#8P@PvPs%65#W#DP@PJPs%65#W#DP@%E5#6#]#;#FPsPqP@%15#G#Y#>#:#FRJPs%65#W#HP@PrPs%65$05#6P@%BkRrPs%65$05#6P@%E5#6#]#?#FPsPGP@PJPs%65$05#IP@PvPs%65$05#>P@PrPs%65$05#>P@%E5#6#]#8#FPsPUP@%15#G#R$06#FRUPs%65#[#I#8P:%B[R[Ps%65#[#?P>PsPs%65#[#?P@%BzPs%65#[#7P@PsPsPaP@%15#G#R#I#6#FRaPs%65#[#H#8P:P[Ps%65$06#RP>PsPs%65$06#RP@%BqPs%65$06#?P@PsPsPPP@PUPs%P5#8#7#8P:P[Ps%P5#8#HP>PsPs%P5#8#HP@%BiPs%P5#D#IP@PsPsPTP@PaPs%P5#D#?#8P:P[Ps%P5#D#8P>PsPs%P5#D#8P@%BGPs%P5#D#HP@PsPsP?P@%15#G#;#G#C#FPsPkP@%15#G#;#h#FPs&0p5$0MP@%Y5#7#C#>#FPsPDP>PKPsPgP@%BEPsPXP@&0L5#H#8#C#FPsPbP@%E5#6#h#C#FPsPlP@%B=&0_9D@D@D@D@D@DbD@D@DNDNDbI0BD@DNDNDbI0BD@DNDNDbI0BD@DNDNDbI0BD@DNDbDND@DNDbDND@DNDbDND@DNDbDND@40C3_40gD@40S3_D@3u3_D@80S^I0fI0J40gD@I0J3zDbD@3_3_40I3_3_3u3_3u40S3z40<3z40<3_3_3_3z40<40I40<3z40<3z400I0e3t4003t4003t400I0e3t4003t4003t400I0e3t40040<40<3t40R40I40R40I40R3z3t3z40R40I40RI0J3_3u3u3u3u40S3u410I0JI0JI0fDUI0BD@D@DUD<D<D<D<D<D<D<D<D<40CI0BDeDoD<D<D@D@D<D<D<DoD<DoD<D<D<D<D<D<D<D<D@D<D<D<D@D@DND@D@DNR^D<DoDeDoDeDoDeD<DeD<DeD<40CDUD<40CDUDUDUDUR9N<0]-01MR=;K=Rl20A44Rb00A4R420@RO>0>bQRR;KRRX20A66RE00A6Rg00A6RDPEPZQ06PdCq>0QgKRk;KkR?AX023RG=K7GR[POPQ%G5#6#:$0DRaPZPZPZPcPsPsPHQ0Q#2RT%BaPHQ0HQ0J%2T#wRi%2iRi%2iRiPv208KuPs%wiRi#S%2iRi%2iRi%2iRi%2iRi%2iRi%2iRiPYPKQ07PsPsPsPsPsPsPs&0Ni$0KRi%2iRi%2iRi%2i00dh3TH0HDpDp3T3T3TDp3TH0HH0aRiQ0VQ0WQ0YQ0[Q0^Q0_Q0`Q0aQ0bQ0cQ0iP{Q0kQ0lQ0mQ0nQ0pQ0qQ0rQ0U20~x^DUDUR^:0C~}DUDUDUN<0]-01MR}=KN}Rx20@aO>0>bQRY=K4YRUPEPZPZPsCqRP=KgPRq%D5#;#:#D$0O=X03Rz=K7zRr20`ICg00XfRJg00YFR]PJP;P>PCH0uQ0PH0[00E3+0E9X02Rn=K7nRmPOPQ%G5#Y#J#D#=RwPZ20=S_RWPZPcP8PCPePB%BwPeQ0HQ0JQ08Q09Q0:Q0KPpPCQ0;#SQ0<Q0=Q0>Q0?Q0@Q0APsQ0MPvPdPsP8PsQ0PQ0LPtQ0BQ0CQ0DQ0E00dh3TH0HDpDp3T3T3TDp3TH0HH0aP9N<0]-01MR9=KN9Rh20@wO>0>bQRw=K4wRtPEPZPWP8CqR8>0QgCRC=KDCRW%:5#I#?#;$0O=X03R5=K75RePOPQPaPZQ0Z#v#Q,gSRaPZPcPsPsPHPiQ0VQ0WQ0YQ0j%5`80n:PSQ0tP@Q0OPSQ0uP@PvPSQ0dP@PuPSQ0gP@Q0NPSQ05P@PpPSQ0sP@Q0KPSQ04P@Q0FQ0[Q0^Q0_Q0`Q0aQ0bQ0cQ0iB0C{~^DUDUDeDoDeDoDeDoDeDUN<0]-01MR^=KN^R~PEPZPaPsCqRa=KgaR{/LrR@,LURp'LRu,L[Rv'LR:'LR`'LRi'LRH'LRc'LRQ'LRO'LR\'LRF'LRV'LRA'LRj'LP7PLPlPjPNP=PXPAP4PRP?PVPDPkP[PF1r7GRFPxP\1rN}PUPO1r4YROPqPQ1rgPPrPc1r7zRcPmPH1r7nPhPiPNP9PtP`P4PwPWP:PDPCPePvP7P5P[PuPFP~Pp1rN^PUP@POP{Pr1rgaPcK0PK0PD~D~D~D~K0PK0PK0PD~D~D~D~P720A<0R<g00Z8Rcg00[33}Rr-0?0$0:20;0r5X0Q02Q03g00[oRr40t00=I00`K00E39X02PNg00\jg00]g60Yfg00^dRf-01MP4&0Vf&0Xf+0@&0\f60>bPRPDPE&0Tf&0Wf&0sfCq&0Uf60QgPEPZB0c1Sr00=_PdCq>0QgKP7g00_a9}<cRK-0?0$0:20;0K5X0PGPNg00`]g00aZ60YTg00bWRK-01MP4&0VK&0XK+0@&0\K60>bPYPgPE&0TK&0WK&0UKCqPPP7g00cT9}<cRP-0?0$0:20;0P5X0PzP7g00dP9}<cRP-0?0$0:20;0P5X0Q00Q01PIPrH0[PJP]PJP;P>PrH0uB0Z1rs008sH0[00E3+0E9X02PNg00eLg00fI60YBg00gFRB-01MP4&0VB&0XB+0@&0\B60>bPwPDPE&0TB&0WB&0sBCq&0UB60QgPgP6P8PrH09P7g00hC9}<cRr-0?0$0:20;0r5X0P5P7g00i?9}<cR5-0?0$0:20;055X0PGPNg00j;g00k860YTg00l5RT-01MP4&0VT&0XT+0@&0\T60>bPYPgPE&0TT&0WT&0UTCqPag00m29}<cRc-0?0$0:20;0c5X0=K7zFkFkFkFkFkFkFkFkFkdo"). Qed.

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xe3ba4%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0xe2b9c%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xe36f0%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xe2b9c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xe2b9c%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xe2b9c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xd70d4%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xd1e54%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_U1OpenFail_defs ()) ["FXALL"] "p%0p&0p;1p;2p;3p;4p;<g0000k10wTg000Pk20:Tg005Xk10ITg0068j3NTg002Fj12Tg002ej1[Tg001Nj1?Tg004Uj11Tg00@Ik401Tg009Kj2VTg00mnk40QTg00?Qk40NTg0010j1uTg003]k30MTg005:j15Tg006Rk10tTg0074j10Tg007Yk30DTg008Qk307Tg00:Dk20TTg00;>k20STg00<8k40cTg00=2j2LTg00=lm<0vTg00>ok20]Tg00L0j4dTg00AEj2STg00A`k20\Tg00B:j3`Tg00K8k30JTg00CMk30sTg00DOk10rTg00EMk10qTg00FIk10pTg00GFk10oTg00HCk10nTg00J<k10kTg00LPj3=Tg00M0j3zTg00Mjk40gTg00BWk10ZTg00NEk30YTf0R0#1#1#0#0p=8%00#1#1#1p=@%00#1#0#0p=H%10#0#0#5p>0;g00Q\R1f2R2f1R3P0Cdp=Z%00#1#0#1p=G%00#0#1#1p=>%20#2p>0A%20#2#2#2p>0E%20#2#2#2#2#2#2#2p>0K%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0[g00NbR4@0D30p>02%10#1#1#1#1#1#1#1p=e%10#1#1#1p=E%10#1#1p>0V%00#0#0#0#0#0#0#0#0p=c%00#0#1#5p>0fg00P`R5?=30p=b%00#1#1#0p=<%10#1#0#1p=7%10#1#1#0p=C%00#0#0#5p=B%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0>B0J430p=T%50#?p=Ug00XfR6g00OnS00P3P0H01p>0G%10#0#1#0p=D%00#0#0#1#1#0#1#0p>0u%10#1#1#1#1#1#1#0p>00%00#0#0#1#0#0#0#5p=n%10#0#1#1p=I%00#0#0#0p=4%10#1#0#0#0#0#0#5p>06%00#0p=K%00#up>09%00#0#0p=3%00#0#5#?p=F%00#0#0#0#0p=x%00#1#0#0#1#0#0#0p=w%00#0#1#0#0#0#1#0#0p=m%10#0#0#0p=:g00R:R7%[2%[3==703=p>08A=7309=72p=l%[3==70p>0X%10#1#0p>0H%10#0#0#1p=6%00#0#0#1p=Q%00#0#1#0p=P%00#1p>0Wf3R8/V2?z30p>0U%00#0#0#0#0#1#1#0p>05%00#0#0#0#0#1#1#1p=W%00#0#1p=a%00#0#0#0#0#0#1#1p=X%10#5p>0e%00#0#0#0#0#0#1#0p=i%00#0#0#0#0#0#0#0p=O%00#0#0#0#0#0#0#5p=^%00#0#0#0#0#0#0p=h%u0,V3p>0d%00#0#5,V3p>0b%10#0p>0a%10#1p>04%00#0#0#0#0#1#0#0p=j%10#1#1#1#0#0#0#5p=~%00#0#0#0#1#0#0#0p=}%00#0#0#0#0#0#0#0#1p=J%00#1#0#0#0#1#0#0p>0R%00#0#0#1#0#0#0#1p>0@%00#0#0#1#0#0#1#0p=g%00#0#0#1#0#0#1#1p=Y%00#0#0#0#0#1#0#1p=R%00#0#0#0#0#0#0#0#1#1#0p=A%00#0#0#0#0#0#0#0#1#1#0#0#1p=s%00#0#0#0#0#0#0#0#1#1#0#1#0p=v%00#0#0#0#0#0#0#0#1#1#0#1#1p=r%00#0#1#0#0p>0=%00#0#0#1#1#0#1#1p>0`%00#0#0#0#0#0#0#1p>0_g00S2R9f4R:/V8?z23;=0p=;%08#0#0#0#5,V:?z23==90p=]%18#0#0#0#5,V:?z23==90p=M%58,V:?z23==90p>03A=9309=92p={%02#5%03#0#0#5'L==90p=\%03#5,L2==90p>0P%02#5/L3==90p>0C%12#5/L3==90p=q1L:81L23==905=9p>0O%0:#5/L8%02#5/L3==905=9p>0<%12#1#1#0#0#5%03#0#0#5'L==90p=p%12#1#1#0#0#5/L3==90p>0?%02#1#1#0#0#5/L3==90p=|%12#0#1#0#0#5%03#0#0#5'L==90p=t%1:#0#1#0#0#5/L8%02#0#1#0#0#5/L3==905=9p>0F%02#0#1#0#0#5%03#0#0#5'L==90p=k%02#0#1#0#0#5/L3==90p>0B%12#0#1#0#0#5/L3==90p>0^%u8,V:?z23==90p=9%18#0#0#0#u,V:?z23==90p=f%08#u,V:?z23==90p=oP7P7P3P0Cdp>0LP:P820\23P0H0gp=_g00SlR;?`30$0Zp>0jB0Y;30p>0iP1P8P2P3Cd=N:0p>0hAN823/S0p>0lf6R<f5R=;N:AN823/S0'Sp>0mf7P1P<A`;=:$0ZB0Y;82Cd;N3/S0p=y&0w5R0-0:1R3g00TiR8#8#@#@#H$0;&0I5R55Z0R2;N2%88#G#@#>$0;R=g00ONR:g00njg00V:R<#2R>#2R?#2R@#2RA#2RB#2$0ARC$0A$0E$0K$0[RD#[REg00XHRF#?RG+02RH%18RI#1RJ#1RK#1RL#1RM#1RN#1#eRO#1RP#1#ERQ#1#eRR$0VRS#1#E#eRT#1#ERU#c$0fRV#?H01/b55Z0RW=N3WS01AZ0=5RX=N3XS02%88#<#7#C#B=Z05RY=N3YS03P:g00o\S04%2D$0A$0K$0>$0>RD#[RZ002GR[PZH01%[?R?/TZ/VFP>P:PGH0Q/b5'b9Z0=R\=N3\S05%UMR]00GZP6g00YFS06P6P<PAPZH0N202[GH01/b5'b9Z0=R^=N3^S07g00UNS08%u8#?S09<0MZ/T]%58R_#?R`+0G/b59Z0=Ra=N3aS0:%D8#C$0u$0;=Z05Rb=N3bS0;g00VYRc$0tRd%78$00#nRe%08Rf#5Rg%I8#4#8$06Rh%[<Ri%0fRj#0Rk#1Rl#1Rm#0S0<#KS0=#0S0>#uS0?#?'TRn1TiZ%0kRo#1Rp#1Rq#1Rr#1$09#?Rs'TRtPn%1fRf#0Ru#3Rv#US0@PGPG%1jRj#0Rw#0Rx#0Ry#0S0A#0S0B#0S0C#uS0D#?,TiRz&0AD$0E$0[$0>$0>$0>RD%?h%0pS0E#KS0F#KS0G#4#F%x8#w#>#BRp#?%2D$0ER{%2{R{%2{R{%?eR|202G[S0H%Ul+02R[-02`&0E{R{#[%2{R{%2{R{%2{R{%2{R{%2{R{%2{R{%m8#7#nR}#?R~%K8#:#D$00#F%2{$0A$0KR{%2{R{%2{R{%2{&0I74084089lGG9lGG9lGG7lG7l`4084084085lG3l+0X4083l7lz+0XPG%78$00#G#BS0IPC%3KS0J#0S0K$09#?,TiS0LPG&0H8#e#>PCPnPG%78$00#:#BS0MPCPnPi%1xRxPC%>8#@#6#Q#UPi%4xPCP|PiPyPCP[PiQ0CPCg00W\Rx%URRR<0D[Pi%1mRmPCPRPi%3mS0CPC%1wRw#UPiQ0<PC%18#<#P#4#8#FPi%0lRl#1RmPCPGPi%0lRl#0S0<#0S0N#0RRPCQ0HPi%3mRmPCPZPiQ0>PC%0oR[#1RK#0R{#1$0W#>#FPiPlPCPG%5P:07ZFPi%3M$09PCP?H0UPiQ0DPC%1u#K$09Ru#?,TiPiPRP>%U[RRPiPmPC%0IRI#1Rm#1RM#1#K#8RZ#1$0W#@$05#E#P#W#H#<#E#<#C#UPiQ0?PC%aZ#<#>#P#X#D#<#6#<#8#<#>#UPi%3rPC%KS#8#8#8#8#8#8#7#UPi%4qPC%0T#e#e#UPi%3NPC%0IRI#1RN#1#>#>#>#>#>#FPi%3{PC%3wRw#:#6#UPi%0[R[#KR{#KRTPCP~PiP[PCPGPiPKPCPzPiQ0EPCQ0LPiQ0GPC%1jRj#1#K$09Rz#?,TiPG&0H8#e#QPCPGPG%78$00#P#BRKPCPGPG%78#e#P#BRqPA&0VU#e$0eRU#?PG&0H8#e#<PCQ0@PG%78$00$06RSPCPnPGPePA%UfPiQ0BPCPGPiPwPCPGPi%3jRjPCPGPiPzPCPGPiQ0=PCPGPiQ0CPC%1fRf#3Rz$09Rw#?,TiRrPiQ0NPC%[ARZPiQ0FPCPGPiP{PCPGPi%3LPC1TiRRRPiQ0KPCP?Pi%0JRJ#1RL#3PC%?gR{Pi%KJRJ#0RPPCP~Pi%3MPC%18#G#8#I#:#FPi%3mRmPCPrPi%3NPCPZPiPjPCPGPi%0vRjPCPGPiPuPCPEPiPwPCP?PiQ0<PC%UJPiQ0APCPGPi%0IRI#KRwPCP{PiPfPC%68#<#D#:#FPG%i8#>#@#HPAB0DxGH%OO#O#O#^RO%KTRT#4Rx#hRH#0Rf#:#4#O#^Ru607?B07EVUPiQ0JPCPGPiPPPCPGPiPmPCPGPiPwPCPGPiPzPCPRPiPvPC%68#<#4#E#FPiPyPCP{PiP[PC%5kRk#?,TiPiPJPC%18#H#<#i#F%5oRo-0Ti%Of#O#^:07iO20diHRf%5HRH+0SPiPFPCP{H0UPiPkPC%[>PiPoPCP?PiPIPCPG%[@R@@07OuPfPH1V@F%5jH0c20T@k%1L#8#O-0bG&0a8#D#4#^+0S%5xPe%78$00#Q$0;PK&048#@#E#6#4Q0I&048#@#E#6#8Q0M&048#@#E#D#HPS&048#@#E#I#:Pq&048#@#E#8%C8#j#^&048#:#Q#O%c8#6#C#B%38#i#@#6%c8#6#~Rq%38#i#D#:%c8#D#I#BRS%38#i#7#:%c8#I#@#BRK%38#X#}%c8#8#>#BRx%38#X#>#:%c8#8#~%38#X#<#7%c8#7#8%38#X#D#Q%c8#C#6#BRL%38#X#D#C%c8#C$06%38#X#E%c8#E#7#BRk%38#X#E%J8#4#^%h8$0R%x8$0@#n%h8$0R%x8$0@#H%38#j#6%x8#g#G%38#j#6%x8#g#:%38#j#C%x8#Y#6#BRj%38#j#C%x8#Y$06%38#R#>%J8#H#7#BRH%38#R#>%J8#G#^%38#R#:%J8#<#n%38#R#6%J8#<#G%38#R#7%J8#@#<#B%38#R#C%J8#@#D#B%A8#P%J8#:#I%A8#>%J8#:#7%A8#>%J8#:#~%A8#H%s8#n%A8#H%s8#>%A8#G%s8#G%A8#G%s8#@%A8#<%s8#6%A8#<%s8#I%A8#@%s8#7%A8#@%s8#~%A8#:%v8#n%A8#:%v8#>%A8#6%v8#G%A8#6%v8#@%A8#D%v8#6%A8#D%v8#I%A8#I%v8#7%A8#I%v8#~%A8#8%r8#n%A8#8%r8#>%A8#8%r8#H%A8#7%r8#<#B%A8#7%r8#:%A8#C%r8#D#B%A8#C%r8$06%A8#E%r8#C#B%A8#E%J8#8#H%38#W#Q#G%J8#8#<%38#W#Q#7%J8#8#:%38#W#P#G%J8#C#4%38#W#:%J8#C#P#B%38#W#:%J8#C#H%38#W#6%J8#C#<#B%38#W#6%J8#C#:%38#}#G#4%08#i#P#^Rf%38#}#8#:%08#i#>#~%h8#6#R%08#i#H#P%h8#6#I#7%08#X#G#<$0;%h8#7#G#8%08#X#G#8%h8#7#@#H%08#X#G#E%h8#7#@%08#X#<#^%h8#7#:#H%08#j#<#6%a8#g#Q#4&0=8#w#:PG%08#j#<#D#BRuPC%?uPG%i8#>#@PA%[BRB%38#Q$0`%08#j#@#6%38$0@#C#:%08#j#@#7#BRu%38$0@#E#:%x8#w#nROPGPOPCPZ%38#g#Q#H%a8#g#P#8&0=8#w#7#BRO%a8#g#>#<&0=8#w#C#BRI&0=8#w#~R{%m8#6#^RJ%m8#6#n%m8#I#^R[%a8#g#8#HPGP}PCPZ%a8#Y#w%m8#7#>%a8#Y#G#H%m8#7#<#BRZPGPZPCP@%a8#Y#G#8%m8#7#:%a8#Y#<#:%m8#7#I#BR@PGP@PC%5TRT#?%m8#7$06R@%a8#Y#:#:%a8#Y#:#8%08#w#O%5Q:07B_1LFTPGPqPC%18#I#P#P#4#FRTPG%48#R#>PC%18#8#X#D#FRBPG%48#R#HPC%J8#C#C#BR_#?RQPG%48#R#HPC%K8#4#Y#Q#FPGPSPCPTPG%48#R#6PCP|PG%48#R#DPCPQPG%48#R#DPC%K8#4#Y#>#FPGPKPC%18#I#P#<#8#FRQPG%48#R#EPCPBPG%48$05#4PC%?fRBPG%48$05#4PC%K8#4#Y#@#FPGPxPCPQPG%48$05#GPCP|PG%48$05#<PCPBPG%48$05#<PC%K8#4#Y#6#FPGPLPC%18#I#Q#}#FRLPG%48#W#G#6P>%?oRoPG%48#W#@PAPGPG%48#W#@PC%?qPG%48#W#7PCPGPGPkPC%18#I#Q#G#4#FRkPG%48#W#E#6P>PoPG%48#}#QPAPGPG%48#}#QPC%?KPG%48#}#@PCPGPGPjPCPLPG%O8#6#7#6P>PoPG%O8#6#EPAPGPG%O8#6#EPC%?SPG%O8#D#GPCPGPGPHPCPkPG%O8#D#@#6P>PoPG%O8#D#6PAPGPG%O8#D#6PC%?xPG%O8#D#EPCPGPGP_PC%18#I#>#I#C#FPGPfPC%18#I#>#g#FPG&0_8$0@PC%P8#7#C#<#FPGPOPAP`PGPIPC%?{PGPJPC&0=8#E#6#C#FPGP[PC%K8#4#g#C#FPGPuPC%?@&0I9D;D;D;D;D;D]D;D;DMDMD]I03D;DMDMD]I03D;DMDMD]I03D;DMDMD]I03D;DMD]DMD;DMD]DMD;DMD]DMD;DMD]DMD;3{3\40PD;40C3\D;3q3\D;80C}I0OI0<60PpD;I0<3pD]D;3\3\40?3\3\3q3\3q40C3p3|3p3|3\3\3\3p3|40?3|3p3|3p3tI0F3k3t3k3t3k3tI0F3k3t3k3t3k3tI0F3k3t3|3|3k40B40?40B40?40B3p3k3p40B40?40BI0<3\3q3q3q3q40C3q40^I0<I0<I0O3{3{I03D;D;3{3{D9D9D9D9D9D9D9D9D93{I03DfDoD9D9D;D;D9D9D9DoD9DoD9D9D9D9D9D9D9D9D;DoD9D9D;D;DMD;D;DMD9DfDfDfD9D9D9D9D9D;D9D9D;3{DfDoDoDoDfDfDoDfDoDfD9DfD;D]D;N<0v-0]cRp;NpR}20:11R900:1R@P9P1P1P1PhPeCdPgCdRg;NgRe20:77Rh00:7RCPhP720LntPGCdRt;NtRu%D8#>#8#D$0;=Z05R8=N38R['SRJ'SR{'SRI'SRO'SRf'SR_'SRx'SRo'SRk'SP3P2Q01PkP3PWQ02PoP3PXQ03PxP3PYQ05P_P3P\Q07PfP3P^Q0:POP3PaQ0;PIP3PbP}P{PdPpPePJP@PgPuP[PCPt20\38D_D_D_D_D_D_D_D_D_D_D_P3P0P020:;0R;g00Z8Rtg010N3`R[P0P[P2P3P0P0g011I9`;tR2P0P2PWP3P0P0g012D9`;tRWP0PWPXP3P0P0g013?9`;tRXP0PXPYP3P0P0g014:9`;tRYP0PYP:Q04g00[oRY>0D4GRXPYH01B0J4?Y/VFP>P:PGH0Q/b5'b9Z0=P3P0P0g01559`;tR:P0P:P6Q00P]PYH01P6Q06P6P<PAPYH0N202XGH01/b5'b9Z0=P3P0P0g01609`;tRXP0PXQ08Q09<0MY/T]00G`/b59Z0=P3P0P0g016k9`;tR=P0P=PbPdg017fg018b60sDg019^RD-0]cP@P9P1P1P1&0rD&0qDCd&0pDCdPgPCPhP7&0oD&0nD+0L&0kDCdPhP7B0J4iY/Ts-0LnPGCdP3P0g01:[9`;tRt-0j020i0tP8I0hH0lK0mGyGyGyGyGyGyGyGydo"). Qed.

End FXALL.
