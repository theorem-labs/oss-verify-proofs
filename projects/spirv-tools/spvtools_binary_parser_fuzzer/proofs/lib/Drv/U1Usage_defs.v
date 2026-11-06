(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1MainEntry U1LibStdioCall U1OpenFail_defs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1MainEntryN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K59OSSVerify5KrLib8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K59OSSVerify5KrLib8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv>U1LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib3Drv>U1LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs2LXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_scGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs4u_rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv<U1Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FXALL.
Context {fx : FPState}.

Definition u_ssA0 : sym_state := SS 0x6583c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.

Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

Definition u_ssB0 : sym_state := SS 0xd7b64 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

Definition u_ssC0 : sym_state := SS 0xd7b64 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

Definition u_ssD0 : sym_state := SS 0xd8d00 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

Definition u_ssE0 : sym_state := SS 0xd7b64 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

Definition u_ssF0 : sym_state := SS 0xd7b64 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.

Definition u_ssG0 : sym_state := SS 0xd7b64 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.

Definition u_ssH0 : sym_state := SS 0xd8660 u_srH0 [] u_knH0 262.
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

Definition u_ssH30 : sym_state := SS 0xd8660 u_srH30 [] u_knH30 262.
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

Definition u_ssG40 : sym_state := SS 0xd7b64 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.

Definition u_ssH40 : sym_state := SS 0xd8660 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xe2b9c%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xe36f0%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xe2b9c%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xe2b9c%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xe2b9c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xd70d4%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0xd1e54%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xd70d4%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xd8830%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x1152f, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xd70d4%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0xd1e54%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xd70d4%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xd9250%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xe2b9c%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xd70d4%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xd8660%Z, 0xeff08%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0xd1e54%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_U1Usage_defs ()) ["FXALL"] "p%0p%1p&0p&1p;1p;2p;4p;3p;<g0000k117Tg000Pk20<Tg0010j12Tg001Oj1JTg002Gj10Tg002lj17Tg003Jj1CTg004Bj4lTg005>k10dTg005^j3ATg0068j2ZTg0071k40pTg007mj11Tg008Rk40nTg009Jj1XTg009hk30lTg00:`k10wTg00;Bk30aTg00<:k30[Tg00=4k20|Tg00=nk20rTg00>hj2RTg00?bm<0STg00@ej2kTg00AGj2<Tg00Abk20?Tg00B<j3PTg00BYk30XTg00CQk30QTg00DSk10LTg00EQk10KTg00FMk10PTg00GJk10RTg00HGk10OTg00IDk10ITg00J@k10vTg00K<j4]Tg00K\j35Tg00L<j3tTg00M6k40NTg00MQk30uTg00Mnk10eTf0R0#1#1#0#0p=:%00#1#0#1p=E%00#1#1#1p=H%00#0#1#1p=?%10#0#0#7p>0M%20#2p>0Z%20#2#2p>0A%20#2#2#2p=rg00NdR1f3R2f2R3g00OBR4f1R5;50C]p=aP1P3P5P0C]p>0\%00#1#1#0p=>%10#1#0#1p=9%10#1#1#0p=G%00#0#0#7p==%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>01g00P>R6@0a50p>0BB0X650p=oA5450p>0Y%70#Cp=Yg00PjR7g00QJR8P5P0Clp>0`%10#0#1#0p=@%00#0#0#1#1#0#1#0p>0x%10#1#1#1#1#1#1#0p=}%00#0#0#1#0#0#0#7p=n%10#0#1#1p=F%00#0#0#0p=4%10#1#0#0#0#0#0#7p>0D%00#0p=L%C0:0X65p=z%00#Xp>0^%20#2#2#2#2#2#2#2p>0f%00#0#7#Cp=I%00#0#0#0#0p=f%00#1#0#0#1#0#0#0p>07%00#0#1#0#0#0#1#0#0p=u%10#0#0#0p=8g00R<R9%J5;50p>0c%J3%J5=590559p=U%J5=59095939592p>0Ef4R:A595095939592559p=s%J2A59509593559p>0b%00#0#0p=31Z23?t50p>03%00#0#0#1p=M%13#0#0#0#X,Z2?t50p=b%03#X,Z2?t50p=q%10#1#1#1#1#1#1#1p=g%10#1#1#1p=K%00#0#0#0#0#1#1#0p>0C%00#1p>10%00#0#1#0p=S%10#0#0#1p=;%10#7p>0~%C09t35p>0t%10#1#1p>0}%10#1#0p>0s%00#1#0#0p=N%00#0#0#0#0#0#1#0p=~%00#0#0#0#0#0#0#0p=W%00#0#0#0#0#0#0#7p=`%00#0#0#0#0#0#0p>0:%X0,Z5p>0{%00#0#7,Z5p>0z%10#0p>0q%10#1p>0@%00#0#0#0#0#1#0#0p=h%00#0#0#0#1#0#0#1p=|%10#1#1#1#0#0#0#7p={%00#0#0#0#0#0#0#0#0p>00%00#0#0#0#0#0#1#1p=_%00#0#0#0#1#0#0#0p>09%00#0#0#0#0#0#0#0#1p=O%00#1#0#0#0#1#0#0p>0o%00#0#0#1#0#0#0#1p>0J%00#0#0#1#0#0#1#0p=m%00#0#0#1#0#0#1#1p=\%00#0#0#0#0#1#0#1p=V%00#0#0#0#0#0#0#0#1#1#0p=B%00#0#0#0#0#0#0#0#1#1#0#0#1p=y%00#0#0#0#0#0#0#0#1#1#0#1#0p=x%00#0#0#0#0#0#0#0#1#1#0#1#1p>02%00#0#0#0#0#1#1#1p=[%00#0#1p=e%00#0#1#0#0p>0H%00#0#0#1#1#0#1#1p>0m%00#0#0#0#0#0#0#1p>0yg00S4R;1Z:2?t35;50p=D%02#0#0#0#7,Z:?t35=5;0p=d%12#0#0#0#7,Z:?t35=5;0p=Q%72,Z:?t35=5;0p>0WA5;5095;3p>0>%03#7%05#0#0#7'R=5;0p=^%05#7,R3=5;0p>0k%03#7/R5=5;0p>0V%13#7/R5=5;0p>061R:21R35=5;055;p>0j%0:#7/R2%03#7/R5=5;055;p>0F%13#1#1#0#0#7%05#0#0#7'R=5;0p>05%13#0#1#0#0#7/R5=5;0p>0i%13#1#1#0#0#7/R5=5;0p>0U%03#1#1#0#0#7/R5=5;0p>0=%13#0#1#0#0#7%05#0#0#7'R=5;0p>08%1:#0#1#0#0#7/R2%03#0#1#0#0#7/R5=5;055;p>0h%03#0#1#0#0#7%05#0#0#7'R=5;0p=v%03#0#1#0#0#7/R5=5;0p>0TA5;5095;395;295;:p=T%X2,Z:?t35=5;0p=6A5;50p>0_P2P1P1P1P3P5C]P0C]p>04P2P9P9P9P3P5C]P0C]p=jg00SnR<P8P5P0Clp>0g%00#0#0#1#1#0#0#1p>16P3P9P5P0C]p>0;P9P9P5P0C]p>15f7R=f6R>f5R?P:P220?35P0H0NH0Np=wP:P220?35P0H0Np=cP>P?P:P2P3P5P0H0NH0Np>14g00TNR@@0u50p>0GP1P2AP@35$0eP0C]p>0]AP@50$0ep>13P1P2P3P5C]=A:0p>12AA235/<0p>11AA>?:AA235/<0'<p=pP1P>AP@?:$0eB0u@23C]=A=5/<0p=i&174R0-0<1R=P0g00UKR5#:#E#H#?$0MR3P7g00V0g00VbR2#2R?$0ZS00#2R:#2S01$0ZR>#2RA$0A#rS02#2RB#J%05RC#7RD#CS03Cl&0d4R4CaRE;AEB0\034RF=A=FRG%:5#>#9#G#=>0\04RH=A=HS04P0P3P<g00WAS05&0ABS06#2S07#2S08#2S09#2S0:$0ZS0;$0A#r$01$01$01$01$01RB#JRIg00X3RJ#CRK+0BRLPICl%J?RM/oI/ZJP?P<PKH0p00Y4CaRN=A=NS0<P0P3%0CRO#1RP#0RQ#0RR#1RS#YRT00`IP7g00XQS0=P7P2P:PIH0n20BLKS0>Cl00Y4S0?CaRU=A=US0@P0P3g00YCS0A%X5#CS0B<0lI/oTS0C%15RV#1RW#YRX+0`P4CaRY=A=YS0D%@5#G$0x$0MRZ>0\04R[=A=[R\g00YoR]$0wR^%95#}#nR_PD%F5#4#:$0DR`%J2Ra%0ORO#1Rb#1Rc#0S0E#LS0F#0Rd#XRe'zRf1oaIS0G%0bRb#0S0H#0Rg#1$0^#CS0I'oS0JPf%1CRC#0Rh#0S0K#0S0L#0Ri#YRjPKPK%0RRR#0S0M#0S0N#0Rk#XS0O,zaRl&0ZB#r$01$01$01RB#2#rS0P#2S0Q#2S0R#rS0S#2S0T#2S0U#2S0V#2S0W#2S0X#2S0Y$0A$0fS0Z#2S0[#2S0\#2S0]#2Rm#2#rS0^#2S0_#2S0`#rS0a#2S0b#2S0c#2S0d#2S0e#2S0f#2S0g$0A$0fS0h#2S0i#2S0j#2S0k#2Rn%C`Pl%0ORo#1Rp#0S0l#LS0m#LRq#4#IS0n%f5$07#?#=S0o#CS0p%2n#rRr%2rRr%2rRr%C_Rs20BKLS0q00BXRt-0BXPK%rrRr#J%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%u5#9#nRu#CRv%75S0r#CS0s%L5#8#@#}#IS0tPKPKPKPKPKPKPK&0Ar$0fRr%2rRr%2rRr%2r&0d9Rr+0c3UH0EDsDs3U3U3UDs3UH0EH0bS0uPK%95#}#E#=S0vPA%1WRw#3S0w#0S0x$0^,zaS0yH03RxPK%95#}#>#=PAPfH03RyPK%95#}#8#=S0zPAPfH03RzPaPSPA%M5#E#?#>#YS0{CbS0|Pa%3SS0}PAPsCqS0~PaPRPAPtCbS10PaPkPAg00[2%1wRw#1Rk#1RS#1#gR{#1R|#1#KS11#1#gR}#YR~<0atS12CqS13Pa%1cRcPAP~CbS14Pa%3cS15PA%1QRQ#YS16CqS17PaQ0EPA%F5#M$0C#=S0E#CS18CbS19Pa%1bRbPAPKCbS1:Pa%0gS1;#0PAQ0qCqS1<Pa%LbS1=#0PAPICqS1>Pa&0^dS1?PA%0oRd#1Rb#0Rc#1$10#?#IH03S1@PaQ0HPAPKCbS0H%7|:0[IJR|Pa%3kPAPMCqRkPaQ0OPA%1hS0O#0S1A#LS1B#XS1C,zaH03Rh1ZaeS1D%0dRd#0Re#1#9#?#S#F#?#F#4#F#;#F#@$0~80t>S1EPa%1pRpPA&0}}R}#L#:#:#:#:#:#:#9#YCbS1FPa%3pPA%1}#K#gR}#0#g#g#YCqS1GPa%LSPA%0VRV#0RS#1Rp#1#?#?#?#?#?#ICqS1HPa%LcPA%3QRc#8#;#YCqS1IPa%0eS1J#LRe#XPAPvH03S1KPaPdPAPKCbS1LPaPbPAPlCbS1MPaQ0lPAQ0yCbS0yPa%XqPA%1PRP#1Rq#3S0l#XRb,zaH03S1NPK&0s5#g#MPAPKPK%95#}#S#=S1OPAPKPK%95#g#S#=S1PP:%1}#g#g#YPK&0s5#g#>PAPjPK%95#}$0DS1QPAPfPKP_P:%YCS1RPaQ0NPAPKPaPcPAPKPa%0PRP#LS0N#0R}PAPKPaPbPAPKPaQ0FPAPKPaQ15PA%1CRC#3S15$0^S0F,zaS1SPaQ1;PA%J:RbPaQ0mPAPKPaQ1JPAPKPa%3wPAQ0;#JS0;PaQ0xPA%;5#>#4#K#IS0xPa%0WRW#1Rw#3PAQ02#JS02Pa%LWS1J#0RW#0PAPvPa%1VRV#8PA%15#E#:#F#8#IPa%3VRV#0PAQ1SPa%3pPAPbPaQ0NPAQ08#JPa%0iRpPAQ07#JPaQ1CPAQ06#JPaQ0FPAPMPaPgPAQ0:#JPaQ0MPAQ09#JPa%3SRS#0PAQ03Pa%8CPA%;5#>#H#:#IPaQ0wPAPKPaPWPAPKPaPVPAPKPaPSPAPKPaQ15PAQ0;PaPiPAQ0xPaPRPAQ02PaPdPA%7ORO,zaPaQ1JPA%15#N#>#~#I%7oRo-0|a%W{#W#W#`R{%LeRe#4Rd$0:RR#0Ri#W#W#`60[a20{aR%7R+0rPaPOPAPMH03%8i#4#W#`:0[M{%1w#:#W-0zK&0q5#@#4#`+0r%7dP_%95#}#M$0MQ1O&0@5#H#K#;#4Q0v&0@5#H#K#;#:Q0z&0@5#H#K#@#NQ1Q&0@5#H#K#F#8Q1P&0@5#H#K#:%G5#h#`&0@5#8#M#W%f5#|#G#=%35#~#H#;%f5#|#{Rd%35#~#@#8&005#@#F#=Rw%35#~#9#8&005#F#H#=R{%35#_$09&005#:#?#=Ri%35#_#?#8&005#:#{%35#_#>#9&005#9#:%35#_#@#M&005#G#;#=S1P%35#_#@#G&005#G$0D%35#_#K&005#K#9#=S1Q%35#_#K%O5#4#`&0:5$0o%f5$0J#n&0:5$0o%f5$0J#N%35#h#;%f5#m#E%35#h#;%f5#m#8%35#h#G%f5#\#;#=S0z%35#h#G%f5#\$0D%35#V#?%O5#N#9#=S0v%35#V#?%O5#E#`%35#V#8%O5#>#n%35#V#;%O5#>#E%35#V#9%O5#H#>#=%35#V#G%O5#H#@#=%B5#S%O5#8#F%B5#?%O5#8#9%B5#?%O5#8#{%B5#N%y5#n%B5#N%y5#?%B5#E%y5#E%B5#E%y5#H%B5#>%y5#;%B5#>%y5#F%B5#H%y5#9%B5#H%y5#{%B5#8%x5#n%B5#8%x5#?%B5#;%x5#E%B5#;%x5#H%B5#@%x5#;%B5#@%x5#F%B5#F%x5#9%B5#F%x5#{%B5#:&025#n%B5#:&025#?%B5#:&025#N%B5#9&025#>#=%B5#9&025#8%B5#G&025#@#=%B5#G&025$0D%B5#K&025#G#=%B5#K%O5#:#N%35#[#M#E%O5#:#>%35#[#M#9%O5#:#8%35#[#S#E%O5#G#4%35#[#8%O5#G#S#=%35#[#8%O5#G#N%35#[#;%O5#G#>#=%35#[#;%O5#G#8%35$09#E#4%05#~#S#`RO%35$09#:#8%05#~#?#{%35#|#V%05#~#N#S%35#|#F#9%05#_#E#>$0M&0:5#9#E#:%05#_#E#:&0:5#9#H#N%05#_#E#K&0:5#9#H%05#_#>#`&0:5#9#8#N%05#h#>#;%e5#m#M#4&0H5$07#8PK%05#h#>#@#=RRPA%CRPK%~5#?#HP:Q01#JRR%35#M$0m%05#h#>#{%35#M$0m%05#h#H#;%35$0J#G#8%05#h#H#9#=S01%35$0J#K#8%f5$07#nRSPKPSPAPbQ0o%35#m#M#N%e5#m#S#:&0H5$07#9#=S1O%e5#m#?#>&0H5$07#G#=S1J&0H5$07#{RS%u5#;#`S02%u5#;#n%u5#F#`RV%e5#m#:#NPKPuPAPb%e5#\$07%u5#9#?%e5#\#E#N%u5#9#>#=RWPKPWPAQ00#J%e5#\#E#:%u5#9#8%e5#\#>#8%u5#9#F#=RWPKPWPA%7eRe#C%u5#9$0DRW%e5#\#8#8%e5#\#8#:%05$07#WQ0rQ11#760[R1RJePKPdPA%15#F#S#S#4#IRePK%45#V#?PA%15#:#_#@#IRRPK%45#V#NPA%O5#G#G#=RC#CRgPK%45#V#NPA%L5#4#\#M#IPKPwPAPePK%45#V#;PAPsPK%45#V#@PAPgPK%45#V#@PA%L5#4#\#?#IPKP{PA%15#F#S#>#:#IRgPK%45#V#KPAPRPK%45$0C#4PA%CORRPK%45$0C#4PA%L5#4#\#H#IPKPiPAPgPK%45$0C#EPAPsPK%45$0C#>PAPRPK%45$0C#>PA%L5#4#\#;#IPKQ1PPA%15#F#M$09#IRRPK%45#[#E#;P?%CoRoPK%45#[#HP:PKPK%45#[#HPA%CdPK%45#[#9PAPKPKQ1QPA%15#F#M#E#4#IRdPK%45#[#K#;P?PoPK%45$09#MP:PKPK%45$09#MPA%C{PK%45$09#HPAPKPKQ0zPAPRPK%45#|#9#;P?PoPK%45#|#KP:PKPK%45#|#KPA%CwPK%W5#@#EPAPKPKQ0vPAPdPK%W5#@#H#;P?PoPK%W5#@#;P:PKPK%W5#@#;PA%CiPK%W5#@#KPAPKPKPCPA%15#F#?#F#G#IPKPOPA%15#F#?#m#IPK&0y5$0JPA%S5#9#G#>#IPKQ1OP:Q0sPKQ1JPA%CSPKQ02PA&0H5#K#;#G#IPKPVPA%L5#4#m#G#IPKQ01PA%CW&0d;DDDDDDDDDDDdDDDDDQDQDdI0WDDDQDQDdI0WDDDQDQDdI0WDDDQDQDdI0WDDDQDdDQDDDQDdDQDDDQDdDQDDDQDdDQDD40>3^40kDD40V3^DD4063^DD80VuI0jI0F40kDDI0F40540iDdDD3^3^40U3^3^4063^40640V40540=40540=3^3^3^40540=40U40=40540=405408I0h3v4083v4083v408I0h3v4083v4083v408I0h3v40840=40=3v40T40U40T40U40T4053v40540T40U40TI0F3^40640640640640V40640iI0FI0FI0j40>DTD6D6D6D6D6D6D6D6D6D6D6D6D6DDDDD6D6D6D6D6D6D6D6D6D6D6D6D6D6DDD6D6D6DDDDDQDDDDDQS0o+0_DTDTRu+0_DTDTR;40>DTDTN<0S,k]RW;AWS0120<11RV00<1R1PVP`P_PDH04RS;ASRO20<99RC00<9RiPCPfQ0JPKCjRo;AoS0J%@5#?#:#@$0M>0\04Rd=A=dRwP0PZQ0C00gXP4CaRR=A=RS0CP_PDQ0EPfQ0GQ1=#1#X#CR{'oS0GPfPj%M5#E#S#K#YRgPXQ1?,zaRePmQ18PeQ0nQ0pQ0^Q0_Q0`Q16P~PXQ0a#JQ0bQ0cQ0dQ0eQ0fQ0gQ12PtPsQ0{PXPgPKQ0>PXPLQ0hQ0iQ0jQ0k00cr3UH0EDsDs3U3U3UDs3UH0EH0bPxPyPzQ1:Q1<Q1>Q1@Q0HP|PkPhQ1EQ1FQ1GQ1HQ1IPaQ0O#1#4PAPbQ1KQ1LQ1MQ0yQ1NPaQ1APAPKCbPaQ1B#LPAPKPaQ0K#1Rb#8PAPKPa%0bRb#3PAPKPaQ0L#8PAPKPa%LpPAPKPa%8qPAQ1RPaQ0l#0PAQ0tPa%8PPAQ0sPa%0}PAPvPa%8QPA%M5#E#S#>#YPa%0cPAPsPaQ0}PA%15#>$16#4#IQ0oD6D6D6D6D6D6D6D6D6D6D6D640>DTD6DTDTDTDTRAN<0S,k]Rc=A^cS1NPVQ0EP_PDH04RQ=A1QS0E20<i9RvPCPfQ0GPgCj>0;iXR};A}S0GP_PDP`PfPfPfPjPKPKPlQ0u20_z;:0>xyN<0S,k]R;=A^;S0oPCPfPfPKCjRP=AiPS0}P0PZ20gTIQ0?CaRq=A=qS0?P_PD%F5#S#N#@#=R5Pf1oa{RpPfPjPMPIPePB%C5PeQ0nQ0pQ0PQ0QQ0RQ16P~PIQ0S#JQ0TQ0UQ0VQ0WQ0XQ0YPKPXPsPgPKPMPKQ0>Q0qPLQ0ZQ0[Q0\Q0]00cr3UH0EDsDs3U3U3UDs3UH0EH0bPAN<0S,k]RA=A^AS0RPVP5P_PDH04R5=A15S0Q215fpRr>0;CMS0U>0;iIRI=AvIS0TP_PDP`PfPpPfPjPKPKPlQ0uPxPyPzQ1D&0qb#8#@#@#@#|#:#;#S#N#=80t>Q0|Q0~Q10Q13Q14Q17Q19Q1:Q1<Q1>Q1@Q0H20_hu:0>|kDTDTDTDTN<0S,k]Rk=A^kS0HB0;CrKRr=AirS1@/<wS1>,<OS1<'<S1:,<\S19,<GS17'<S14'<S13'<S10'<R|,<wRu'<Rh,<OR>'<Rb,<\Rz'<Ry'<Rx'<Rl'<Rj'<Rp'<R`'<RD'<R_'<RL'<Rs'<R~'<Re'<Rt'<P=PEPGPt20?=FRtQ04PeP=PHQ0<P~P=PNQ0@PsP=PUQ0DPLP=PYP\P_20?=[R_Q01PDP^PWPOP`20?1SR`Q0JPpPiPoPwPj20?=dRjQ0CPlP=PRQ1NPxP^PcQ0EPyP1PQQ0GPzPvP}P\PbP_Q0oP>P^P;POPhP`Q0}PuPiPPPwP|PjQ0?Q10P=PqQ0RQ13P^PAQ0QQ14P1P5Q0TQ17PvPIPGQ19PtP\Q1:P_Q0HQ1<P^PkPOQ1>P`Q1@PwPiPrPjGwDcK14DcDcDcGwGwGwDcDcDcGwGwGwDcDcDcGwDcP=P0P020<@0R@g00[^Rjg00\Y3PRwP0PwPEP=P0P0g00]S9P@jREP0PEPFP=P0P0g00^M9P@jREP0PEPHP=P0P0g00_G9P@jRHP0PHP0P3P<Q05g00`ARH>0a6KREPHClB0X6MH/ZJP?P<PKH0p00Y4CaP=P0P0g00a99P@jR?P0P?P0P3P7P8PTPHClP7Q0=P7P2P:PHH0n20BEKCl00Y4RECaP=P0P0g00b39P@jR:P0P:P0P3Q0AQ0B<0lH/oTR300`XP4CaP=P0P0g00bm9P@jR:P0P:P[P^g00cgg00db60Qng00e]R:,k]P1PV&0L:&0K:&0P:H04PSPiPC&0R:&0O:&0I:CjPCPfB0X6aHRaQ0I'oPKCjP=P0P0g00fX9P@jRK20G0KH0]PdP=P0P0g00gR9P@jRKP0PKP0PZ20g3XP4CaP^g00hMg00iI60Qmg00jERm,k]P1PV&0Lm&0Km&0PmH04PQPvPC&0Rm&0Om&0vmCj&0Im60;iPCPf1oa{PgCj>0;iXP=P0P0g00kA9P@jRX20G0XH0]P[P^g00l<g00m860Qng00n4RX,k]P1PV&0LX&0KX&0PXH04PSPiPC&0RX&0OX&0IXCjPPP=P0P0g00o09P@jRP20G0PH0]PdP=P0P0g00ok9P@jRPP0PPP0PZP<P8PTPHClPECaP^g010fg011b60QBg012^RB,k]P1PV&0LB&0KB&0PBH04P5PvPC&0RB&0OB&0vBCj&0IB60;iPiP9Q0UPHC]P=P0P0g013Z9P@jRH20G0HH0]PFP=P0P0g014U9P@jRFP0PFP[P^g015Pg016L60Qng017HRn,k]P1PV&0Ln&0Kn&0PnH04PSPiPC&0Rn&0On&0InCjPrP=P0g018D9P@jRj-13020G0jPdI12H11FpGiFpFpGiFpFpFpFpGiFpFpGiGiGiGiGiGiGido"). Qed.

End FXALL.
