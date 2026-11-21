(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-knowledge checks proved by computation for the moved stack window). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1MainEntry S1LibStdioCall S1OpenFail_defs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1MainEntryN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>S1LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib3Drv>S1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs2LXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_scGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs4u_rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<S1Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FXALL.
Context {fx : FPState}.

Definition u_ssA0 : sym_state := SS 0x655e8 sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.

Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

Definition u_ssB0 : sym_state := SS 0xd5e0c u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

Definition u_ssC0 : sym_state := SS 0xd5e0c u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

Definition u_ssD0 : sym_state := SS 0xd6fa8 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

Definition u_ssE0 : sym_state := SS 0xd5e0c u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

Definition u_ssF0 : sym_state := SS 0xd5e0c u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.

Definition u_ssG0 : sym_state := SS 0xd5e0c u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.

Definition u_ssH0 : sym_state := SS 0xd6908 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

Definition u_scrF3 : scripts := SCR [false] [] [].
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.

Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.

Definition u_ssH30 : sym_state := SS 0xd6908 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

Definition u_scrE4 : scripts := SCR [true; false] [] [].
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.

Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.

Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.

Definition u_ssG40 : sym_state := SS 0xd5e0c u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.

Definition u_ssH40 : sym_state := SS 0xd6908 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xe0e44%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xe1998%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xe0e44%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xe0e44%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xe0e44%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xd537c%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0xd00fc%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xd537c%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xd6ad8%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x1152f, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xd537c%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0xd00fc%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xd537c%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xd74f8%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xe0e44%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xd537c%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xd6908%Z, 0xee1b0%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0xd00fc%Z, []).
Proof.
  (* LPS 727298f3: the recorded replay fixed the itinerary's full intermediate states,
     and the entry knowledge moved (the #38 stack window), so the conjuncts are
     recomputed here instead. *)
  vm_compute; repeat split; reflexivity. Qed.

End FXALL.
