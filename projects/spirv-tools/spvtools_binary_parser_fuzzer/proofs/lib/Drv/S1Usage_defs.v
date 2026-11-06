(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
ltac2:(KReplay.run1 (kr_t_S1Usage_defs ()) ["FXALL"] "p%0p%1p&0p&1p;1p;2p;4p;3p;<g0000k114Tg000Pk209Tg0010j12Tg001Oj1JTg002Gj10Tg002lj16Tg003Jj1CTg004Bj4rTg005>k10fTg005^j3BTg0068j2^Tg0071k40pTg007mj11Tg008Rk40lTg009Jj1\Tg009hk30jTg00:`k10wTg00;Bk30aTg00<:k30[Tg00=4k20{Tg00=nk20oTg00>hj2RTg00?bm<0VTg00@ej2kTg00AGj2>Tg00Abk20GTg00B<j3QTg00BYk30ZTg00CQk30UTg00DSk10LTg00EQk10MTg00FMk10TTg00GJk10NTg00HGk10KTg00IDk10STg00J@k10uTg00K<j4aTg00K\j35Tg00L<j3pTg00M6k40RTg00MQk30tTg00Mnk10dTf0R0#1#1#0#0p=9%00#0#0#1p=K%10#0#0#0p=7%10#0#0#6p>0Q%20#2p>0\%20#2#2p>0D%20#2#2#2p=lg00NdR1f3R2f2R3g00OBR4f1R5;50Cap=cP1P3P5P0Cap>0]%10#1#0#0#0#0#1#1p>0O%00#0#1#1p==%00#0#1#1#0#0#0#6p=n%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=}g00P>R6@0a50p>0EB0Z650p=mA5450p>0Y%60#Cp=]g00PjR7g00QJR8P5P0Crp>0`%10#0#1#0p=4%00#1#1#0p=L%10#1#1#1p=8%10#1#0#1#1#1#0#0p=s%00#0#1#1#0#1#1#0p>0A%00#0#0#6p=;%10#1#0#1p=:%00#0#1#0p=F%00#0#0#1#0#0#0#6p=t%00#0p=Z%C0:0Z65p>01%00#\p>0_%20#2#2#2#2#2#2#2p>0e%00#0#0#0p=A%00#0#6#Cp=I%00#0#0#0#0#0#0#0p=S%00#1#1#1#0#0#0#6p>0<%00#1#0#0#0#0#0#1p=~%00#1#0#1#0#0#0#6p=zg00R<R9%J5;50p>0c%J3%J5=590559p=Y%J5=59095939592p>0Ff4R:A595095939592559p=q%J2A59509593559p>0b%00#0#0p=N1^23?p50p=i%10#0#1#1p=?%00#1#0#1p=H%13#0#0#0#\,^2?p50p=d%03#\,^2?p50p=o%10#1#1#1#1#1#1#1p=_%10#1#1#1#1p>0s%00#1p>0}%10#0#0#1p=<%10#6p>0|%C09p35p>0r%10#1#1p=X%10#1#0p>0q%10#1#1#0#0#0#0#1p>0=%00#1#0#0p=@%10#1#1#0p=W%00#1#1#1p=M%10#1#1#0#1#0#1#0p=|%00#0#0#0#0#0#0#6p={%\0,^5p>0z%00#0#6,^5p>0y%10#0p>0n%10#1p=f%00#0#0#0#1#1#1#0p>0;%10#1#1#1#1#0#0#0p>0m%00#1#0#0#0#0#0#6p=y%10#1#1#1#1#1p=E%10#1#1#1#1#1#0#1p=G%10#1#1#1#1#1#1#0p=[%10#1#1#1#1#1#0#1#1#1p=O%10#1#0#1#1#1#1#1p=x%10#1#1#1#1#1#0#1#1#1#1#0p>04%10#1#1#1#1#0#0#1p>02%10#1#1#1#1#1#1#0#0#0p=P%10#1#1#0#0#0#0#0p>0:%00#0#1#0#0#0#0p>0k%00#1#0#0#0#0#0#0p>0x%00#0#0#0#0#0#1#1p>0C%00#0#1p>05%00#0#1#0#0p>08%00#0#0#0#0#1#0#0p>0B%10#1#1#1#1#1#0p=V%10#1#1#0#1#0#0#0p>07g00S4R;?550p>0J1^:2?p35=5;0p=DA5;5095;3p>06%02#0#0#0#6,^:?p35=5;0p=b%12#0#0#0#6,^:?p35=5;0p=T%62,^:?p35=5;0p>0X%03#6%05#0#0#6'R=5;0p=`%05#6,R3=5;0p>0i%03#6/R5=5;0p>0W%13#6/R5=5;0p=v1R:21R35=5;055;p>0h%0:#6/R2%03#6/R5=5;055;p>0I%13#1#1#0#0#6%05#0#0#6'R=5;0p>00%13#0#1#0#0#6/R5=5;0p>0v%13#1#1#0#0#6/R5=5;0p>0H%03#1#1#0#0#6/R5=5;0p>0@%1:#0#1#0#0#6/R2%03#0#1#0#0#6/R5=5;055;p=h%03#0#1#0#0#6/R5=5;0p>0?A5;5095;395;295;:p=U%\2,^:?p35=5;0p=3P2P1P1P1P3P5CaP0Cap>03P2P9P9P9P3P5CaP0Cap=jg00SnR<P8P5P0Crp>0gP3P9P5P0Cap>0>P9P9P5P0Cap>13f7R=f6R>f5R?P:P220G35P0H0RH0Rp=wP:P220G35P0H0Rp=eP>P?P:P2P3P5P0H0RH0Rp>12g00TNR@@0t50p>0PP1P2AQ@35$0dP0Cap>0^AQ@50$0dp>11P1P2P3P5Ca=B:0p>10AB235/>0p>0~AB>?:AB235/>0'>p=uP1P>AQ@?:$0dB0t@23Ca=B=5/>0p=g&144R0-091R=P0g00UKR5#9#K#9#7$0QR3P7g00V0g00VbR2#2R?$0\S00#2R:#2S01$0\R>#2RA$0D#lS02#2RB#J%05RC#6RD#CS03Cr&0f4R4CcRE;BEB0]034RF=B=FRG&0O5#=#n>0]04RH=B=HS04P0P3P<g00WAS05&0DBS06#2S07#2S08#2S09#2S0:$0\S0;$0D#l#}#}#}#}#}RB#JRIg00X3RJ#CRK+0ERLPICr%J?RM/mI/^JP?P<PKH0p00Y4CcRN=B=NS0<P0P3%0CRO#1RP#0RQ#0RR#1RS#]RT00`IP7g00XQS0=P7P2P:PIH0l20ELKS0>Cr00Y4S0?CcRU=B=US0@P0P3g00YCS0A%\5#CS0B<0jI/mTS0C%15RV#1RW#]RX+0`P4CcRY=B=YS0D%45#4#L#8$0QRZ>0]04R[=B=[R\g00YoR]$0wR^%s5$0A#;R_PD%45#:#F#tR`%J2Ra%0ORO#1Rb#1Rc#0S0E#ZS0F#0Rd#\Re+01Rf1maIS0G%0bRb#0S0H#0Rg#1$0_#CS0I'mS0JPf%1CRC#0Rh#0S0K#0S0L#0Ri#]RjPKPK%0RRR#0S0M#0S0N#0Rk#\S0O-01aRl&0\B#l#}#}#}RB#2#lS0P#2S0Q#2S0R#lS0S#2S0T#2S0U#2S0V#2S0W#2S0X#2S0Y$0D$0eS0Z#2S0[#2S0\#2S0]#2Rm#2#lS0^#2S0_#2S0`#lS0a#2S0b#2S0c#2S0d#2S0e#2S0f#2S0g$0D$0eS0h#2S0i#2S0j#2S0k#2Rn%C`Pl%0ORo#1Rp#0S0l#ZS0m#ZRq#A#IS0n%05#S#:$0<S0o#CS0p%2n#lRr%2rRr%2rRr%C_Rs20EKLS0q00EXRt-0EXPK%lrRr#J%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%05#~#F#zRu#CRv%65S0r#CS0s%Z5#7#=#4#L#IS0tPKPKPKPKPKPKPK&0Dr$0eRr%2rRr%2rRr%2r&0f9Rr+0c3YH0FDqDq3Y3Y3YDq3YH0FH0bS0uPK%:5$0O#4#;S0vPA%1WRw#NS0w#0S0x$0_-01aS0yCiRxPK%:5$0O#?#;PAPfCiRyPK%:5$0O#:#;S0zPAPfCiRzPaPSPA%K5#H$0A#]S0{CdS0|Pa%NSS0}PAPsCoS0~PaPRPAPtCdS10PaPkPAg00[2%1wRw#1Rk#1RS#1#_R{#1R|$0sS11#1#_R}#]R~<0atS12CoS13Pa%1cRcPAP~CdS14Pa%NcS15PA%1QRQ#]S16CoS17PaQ0EPA%45#:#H#?#;S0E#CS18CdS19Pa%1bRbPAPKCdS1:Pa%0gS1;#0PAQ0qCoS1<Pa%ZbS1=#0PAPICoS1>Pa&0_dS1?PA%0oRd#1Rb#0Rc#1$0}#=#ICiS1@PaQ0HPAPKCdS0H%6|:0[IJR|Pa%NkPAPMCoRkPaQ0OPA%1hS0O#0S1A#ZS1B#\S1C-01aCiRh1^aeS1D%0dRd#0Re#1#:#=#F#?#=#?#A#?#<#?#4$0|80r>S1EPa%1pRpPA%X}R}#Z#9#9#9#9#9#9#:#]CdS1FPa%NpPA&0s}#_R}#0#_#_#]CoS1GPa%ZSPA%0VRV#0RS#1Rp#1#=#=#=#=#=#ICoS1HPa%ZcPA%NQRc#7#<#]CoS1IPa%0eS1J#ZRe#\PAPvCiS1KPaPdPAPKCdS1LPaPbPAPlCdS1MPaQ0lPAQ0yCdS0yPa%\qPA%1PRP#1Rq#NS0l#\Rb-01aCiS1NPK&0q5$0=#9PAPKPK%:5$0O$0<S1OPAPKPK%s5#@$0<S1PP:%1}#_#_#]PK&0q5#W#F#KPAPjPK%s5#@#tS1QPAPfPKP_P:%]CS1RPaQ0NPAPKPaPcPAPKPa%0PRP#ZS0N#0R}PAPKPaPbPAPKPaQ0FPAPKPaQ15PA%1CRC#NS15$0_S0F-01aS1SPaQ1;PA%J:RbPaQ0mPAPKPaQ1JPAPKPa%NwPAQ0;#JS0;PaQ0xPA%<5#H#M#4#IS0xPa%0WRW#1Rw#NPAQ02#JS02Pa%ZWS1J#0RW#0PAPvPa%1VRV#7PA%15#H#H#L#F#IPa%NVRV#0PAQ1SPa%NpPAPbPaQ0NPAQ08#JPa%0iRpPAQ07#JPaQ1CPAQ06#JPaQ0FPAPMPaPgPAQ0:#JPaQ0MPAQ09#JPa%NSRS#0PAQ03Pa%7CPA%<5#H#W#M#IPaQ0wPAPKPaPWPAPKPaPVPAPKPaPSPAPKPaQ15PAQ0;PaPiPAQ0xPaPRPAQ02PaPdPA%6ORO-01aPaQ1JPA%15#=#|#9#I%6oRo-0{a%S{#S#S#{R{%ZeRe#ARd#N#ARR#0Ri#S#S#{60[a20zaR%6R+0oPaPOPAPMCi%7i#A#S#{:0[M{%1w#7#S-0yK&0n5#7#A#{+0o%6dP_%s5$0A$0QQ1O%f5#M$0;#@Q0v%f5#M#A#8#AQ0z%f5#M#A$0mQ1Q%f5#M#K#A#9Q1P%f5#M#K#K%s5#<#y%f5#M#F#H#A%85#9#8#F#;%E5#=#9#<%85#9#8#nRd%E5#=$0m%85#9#_#;Rw%E5#@#F#7%G5#A#?#;R{%E5#@#H#7%G5#K$0<Ri%E5#@#7#7%G5#F#n%E5#@#?#:%G5#=#A%E5#@#8#K%G5#=#:#;S1P%E5#@#[%G5#@#{%E5#H#@%G5#H#tS1Q%E5#H#@%G5#H#y%E5#H#<%G5#L#z%E5#H#<%G5#L#7%E5#H#W%G5#M#<#;%E5#H#W%G5#M#9%E5#L#=%G5#7#:#;S0z%E5#L#=%G5#<#{%E5#L#7%G5#4#tS0v%E5#L#7%G5#4#y%E5#L#:%G5#?#z%E5#L#W%G5#?#<#;%O5#F%85#s#4#;%O5#=%85#s#W#;%O5#M%G5#x#;%O5#7&045#t%O5#7&045#n%O5#<&045#z%O5#<&045$0<%O5#4&045#<#;%O5#4&045#?#;%O5#?&045#:#;%O5#?&045#8#;%O5#9%85#x#t%O5#9%85#x#n%O5#:%85#x#z%O5#:%85#x$0<%O5#W%G5$02#;%O5#W%85#x#?#;%O5#8%G5#G#;%O5#8%G5#_#;%P5#A%85$0:#t%P5#A%85$0:#n%P5#K%85$0:#z%P5#K%85$0:$0<%P5#K%85$0:#7%P5#F%85$0:#4#;%P5#F%85$0:#9%P5#=%[5$0;#;%P5#=%85$0=#{%P5#@%85$0=#F#;%P5#@%85$0=#7%P5#L#H%85$0=#4%P5#L#:%85$0=#9%P5#M#H%[5#=#@%P5#:%[5$0A#;%P5#:%[5#=#7%P5#W%[5#=#4#;%P5#W%[5#=#9%f5$02#4#A%[5#M#yRO%E5#4#K#7%[5#<#n%E5#4#H#H%[5#<#L%E5#?#A#:%_5#4#4$0Q%E5#|#9%_5#?#A%f5#[#9#@%_5#?#=%f5#[#9%_5#?#y%f5#[#:#@%05#S#?#:&0k5$0A#A%05$0x#sPK%05#S#?#W#;RRPA%CRPK%S5#L#KP:Q01#JRR%N5$0C#A%05#S#9#n%N5$0C#A%05#S#9#:%N5$0C#=#7%05#S#:#tS01%N5$0C#@#7%05#S#:#zRSPKPSPAPbQ0o%N5#A$0A#@&055$0C#M#9&085$0;#tS1O&055$0C#7#L&085$0;#F#;S1J&085$0;#nRS&085$0;#yS02&085$0;#z%05#~#A#yRV&0k5#~#@PKPuPAPb&055$0B#<#7%05#~#F#M&055$0B#4#@%05#~#F#4#;RWPKPWPAQ00#J&055$0B#4#9%05#~#F#9&055$0B#?#7%05#~#F#8#;RWPKPWPA%6eRe#C%05#~#=#{RW&055$0B#:#7&055$0B#s&085#@#SQ0rQ11#660[R1RJePKPdPA%15#4#4#9#4#IRePK%V5#M#:PA%15#?#7#W#@#IRRPK%V5#M#WPA%[5#@#F#;RC#CRgPK%V5#M#WPA%15$02#:#<#IPKPwPAPePK%X5$07#=PAPsPK%X5$07#@PAPgPK%X5$07#@PA%15$02#:#?#IPKP{PA%15#4#?#K#L#IRgPK%X5$07#<PAPRPK%X5$07#4PA%CORRPK%X5$07#4PA%15$02#x#IPKPiPAPgPK%X5$07#8PAPsPK%V5#<#APAPRPK%V5#<#APA%15$02$0=#IPKQ1PPA%15#4#<#?#F#IRRPK%V5#<$02P?%CoRoPK%X5#|#KP:PKPK%X5#|#KPA%CdPK%X5#|#MPAPKPKQ1QPA%15#4#<#8#4#IRdPK%X5#|#<#<P?PoPK%X5#|#?P:PKPK%X5#|#?PA%C{PK%V5#?#KPAPKPKQ0zPAPRPK%V5#9#M#<P?PoPK%V5#9#<P:PKPK%V5#9#<PA%CwPK%V5#9#8PAPKPKQ0vPAPdPK%V5#:#K#<P?PoPK%V5#:#=P:PKPK%V5#:#=PA%CiPK%V5#:#<PAPKPKPCPA%15#4#9#L#7#IPKPOPA%15#4#?#?#9#IPK%X5#8#=#?PA%F5#x#@#IPKQ01PA%CWCiRWPKQ1OP:Q0sCiPKQ1JPA%CSPKQ02PA&085#7#@#7#IPKPVPA%15$02#:#L#I&0f;-0JWDDDDDD406DbDDDDDTDTDbI0XDDDTDTDbI0XDDDTDTDbI0XDDDTDTDbI0XDDDTDbDTDDDTDbDTDDDTDbDTDDDTDbDTDD4063`40iDD40W3`DD3v3`DD80WuI0hI0I40iDDI0I40040vDbDD3`3`40H3`3`3v3`3v40W40040@40040@3`3`3`40040@40H40@40040@40040vDhDhDhDhDhDhDhDhDhDh40@40@40?40?40H40?40H40?40040?40040?40H40?I0I3`3v3v3v3v40W3v40HI0II0II0h406DUD3D3D3D3D3D3D3D3D3D3D3D3D3DDDDD3D3D3D3D3D3D3D3D3D3D3D3D3D3DDD3D3D3DDDDDbDDDDDbS0o+0JDUDURu+0JDUDURW406DUDUN<0V,k]R;;B;S0220911RV0091R1PVP`P_PDH03RS;BSRO20999RC0099RiPCPfQ0JPKCjRo;BoS0J%45#A#K#8$0Q>0]04Rd=B=dRwP0PZQ0C00gXP4CcRR=B=RS0CP_PDQ0EPfQ0GQ1=#1#\#CR{'mS0GPfPj%K5#H#F#8#]RgPXQ1?-01aRePmQ18PeQ0nQ0pQ0^Q0_Q0`Q16P~PXQ0a#JQ0bQ0cQ0dQ0eQ0fQ0gQ12PtPsQ0{PXPgPKQ0>PXPLQ0hQ0iQ0jQ0k00cr3YH0FDqDq3Y3Y3YDq3YH0FH0bPxPyPzQ1:Q1<Q1>Q1@Q0HP|PkPhQ1EQ1FQ1GQ1HQ1IPaQ0O#1#APAPbQ1KQ1LQ1MQ0yQ1NPaQ1APAPKCdPaQ1B#ZPAPKPaQ0K#1Rb#7PAPKPa%0bRb#NPAPKPaQ0L#7PAPKPa%ZpPAPKPa%7qPAQ1RPaQ0l#0PAQ0tPa%7PPAQ0sPa%0}PAPvPa%7QPA%K5#H#F#L#]Pa%0cPAPsPaQ0}PA%15#H#4#=#4#IQ0oD3D3D3D3D3D3D3D3D3D3D3D3406DUD3DUDUDUDURAN<0V,k]Rc=B^cS1NPVQ0EP_PDH03RQ=B1QS0E209i9RvPCPfQ0GPgCj>0>iXR};B}S0GP_PDP`PfPfPfPjPKPKPlQ0u20JzW:06xyN<0V,k]RW=B^WS0oPCPfPfPKCjRP=BiPS0}P0PZ20gTIQ0?CcRq=B=qS0?P_PD%45#W#<#8#;R5Pf1ma{RpPfPjPMPIPePB%C5PeQ0nQ0pQ0PQ0QQ0RQ16P~PIQ0S#JQ0TQ0UQ0VQ0WQ0XQ0YPKPXPsPgPKPMPKQ0>Q0qPLQ0ZQ0[Q0\Q0]00cr3YH0FDqDq3Y3Y3YDq3YH0FH0bPAN<0V,k]RA=B^AS0RPVP5P_PDH03R5=B15S0Q213fpRr>0>CMS0U>0>iIRI=BvIS0TP_PDP`PfPpPfPjPKPKPlQ0uPxPyPzQ1D&0nb#7#4#4#4#A#<#9#<#F#y80r>Q0|Q0~Q10Q13Q14Q17Q19Q1:Q1<Q1>Q1@Q0H20Jhu:06|kDUDUDUDUN<0V,k]Rk=B^kS0HB0>CrKRr=BirS1@/>wS1>,>OS1<'>S1:,>\S19,>GS17'>S14'>S13'>S10'>R|,>wRu'>Rh,>OR>'>Rb,>\Rz'>Ry'>Rx'>Rl'>Rj'>Rp'>R`'>RD'>R_'>RL'>Rs'>R~'>Re'>Rt'>P=PEPGPt20G=FRtQ04PeP=PHQ0<P~P=PNQ0@PsP=PUQ0DPLP=PYP\P_20G=[R_Q02PDP^P;POP`20G1SR`Q0JPpPiPoPwPj20G=dRjQ0CPlP=PRQ1NPxP^PcQ0EPyP1PQQ0GPzPvP}P\PbP_Q0oP>P^PWPOPhP`Q0}PuPiPPPwP|PjQ0?Q10P=PqQ0RQ13P^PAQ0QQ14P1P5Q0TQ17PvPIPGQ19PtP\Q1:P_Q0HQ1<P^PkPOQ1>P`Q1@PwPiPrPjGwDeK12DeDeDeGwGwGwDeDeDeGwGwGwDeDeDeGwDeP=P0P0209@0R@g00[^Rjg00\Y3QRwP0PwPEP=P0P0g00]S9Q@jREP0PEPFP=P0P0g00^M9Q@jREP0PEPHP=P0P0g00_G9Q@jRHP0PHP0P3P<Q05g00`ARH>0a6KREPHCrB0Z6MH/^JP?P<PKH0p00Y4CcP=P0P0g00a99Q@jR?P0P?P0P3P7P8PTPHCrP7Q0=P7P2P:PHH0l20EEKCr00Y4RECcP=P0P0g00b39Q@jR:P0P:P0P3Q0AQ0B<0jH/mTR300`XP4CcP=P0P0g00bm9Q@jR:P0P:P[P^g00cgg00db60Ung00e]R:,k]P1PV&0L:&0M:&0T:H03PSPiPC&0N:&0K:&0S:CjPCPfB0Z6aHRaQ0I'mPKCjP=P0P0g00fX9Q@jRK20P0KH0^PdP=P0P0g00gR9Q@jRKP0PKP0PZ20g3XP4CcP^g00hMg00iI60Umg00jERm,k]P1PV&0Lm&0Mm&0TmH03PQPvPC&0Nm&0Km&0umCj&0Sm60>iPCPf1ma{PgCj>0>iXP=P0P0g00kA9Q@jRX20P0XH0^P[P^g00l<g00m860Ung00n4RX,k]P1PV&0LX&0MX&0TXH03PSPiPC&0NX&0KX&0SXCjPPP=P0P0g00o09Q@jRP20P0PH0^PdP=P0P0g00ok9Q@jRPP0PPP0PZP<P8PTPHCrPECcP^g010fg011b60UBg012^RB,k]P1PV&0LB&0MB&0TBH03P5PvPC&0NB&0KB&0uBCj&0SB60>iPiP9Q0UPHCaP=P0P0g013Z9Q@jRH20P0HH0^PFP=P0P0g014U9Q@jRFP0PFP[P^g015Pg016L60Ung017HRn,k]P1PV&0Ln&0Mn&0TnH03PSPiPC&0Nn&0Kn&0SnCjPrP=P0g018D9Q@jRj-11020P0jPdI10H0~FuGgFuFuGgFuFuFuFuGgFuFuGgGgGgGgGgGgGgdo"). Qed.

End FXALL.
