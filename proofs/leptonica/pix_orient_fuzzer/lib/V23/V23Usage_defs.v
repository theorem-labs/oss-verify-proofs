(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntryN.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond06K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03C6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00K47Corelib4Init9Datatypes4bool02I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K4ELinuxProcessSemantics5Riscv5Instr5aluop02I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rAc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rBc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rCc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rDc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs2LXc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rEc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rFc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rGC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_srGc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_knGc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_scGc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs4u_rHc5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rF3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_srF3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_knF3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_scF3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rG3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_srG3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_knG3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_scG3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rH3c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rE4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_srE4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_knE4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_scE4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rF4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rG4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_srG4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_knG4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs6u_scG4c5ARocqVerifyHarness?AgentSubmission3V23=V23Usage_defs5u_rH4".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x63140 sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0x1143c4 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0x1143c4 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0x115280 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0x1143c4 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0x1143c4 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0x1143c4 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0x114be0 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : sym_state := SS 0x114be0 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : sym_state := SS 0x1143c4 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0x114be0 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Section VP1.
Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x11e154%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x11ec28%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0x11e154%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0x11e154%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0x11e154%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x1139cc%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x10e4e0%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0x1139cc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x114db0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x14381, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x1139cc%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x10e4e0%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0x1139cc%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x1157d0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x1139cc%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x10e4e0%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Usage_defs ()) ["VP1"] "p%0p%1p&0p;1p;2p;4p;3p;<p;5g0000k10bTg000Pj2pTg0010j12Tg001Oj1>Tg002Xj10Tg003=j1<Tg003[j1:Tg004dj4_Tg0061k10DTg006Qj38Tg006kj2NTg0085k40LTg009Bj11Tg009gk40ITg00;0j1ITg00;Nk30HTg00<Wk10_Tg00=9k30@Tg00>Bk308Tg00?Mk40]Tg00@Vk20\Tg00Aak20PTg00Blk30YTg00D7j2UTg00EBl<zTg00FKj2XTg00Fmj26Tg00GHj2qTg00Gbj3BTg00H?k30;Tg00IHj5yTg00JPj1{Tg00KTj1|Tg00LVj1xTg00MYk103Tg00N\k102Tg00O_k101Tg00Pak10GTg00Qcj4MTg00RCj34Tg00Rcj3oTg00Snk404Tg00TIk30RTg00Tfk10FTf0R0#0#0#0p=?%10#1#1#1p=J%00#0#0#0p=7%10#0#1#0p=E%00#<p>0?%20#2p>0>%20#2#2p=r%20#2#2#2p=Yg00UmR1f3R2f2R3g00VKR4f1R5;40CMp=RP1P3P5P0CMp>09%00#0#1#1p=C%10#1#0#1p=\%10#0#0#0p=9%00#1#0#1p=}%00#0#0#<p=;%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=eg00WXR6@0@50p=sB0;650p=DA4450p>07%<0#:p=Lg00XDR7g00XdR8P5P0C_p>0<%10#0#0#1p==%10#1#0#0p=5%10#1#1#0p=P%00#1#1#0p=a%00#0#1#0#0#1#1#1#1p=S%00#0#1#0p=@%00#1#1#1p=`%00#0p=G%00#Ip>0:%20#2#2#2#2#2#2#2p>0E%00#0#<#:p=V%10#0#1#1#0#0#0#0p=h%00#1p>0Cg00YVR9%>5;40p>0B%>3%>5=490549p=H%>5=49094939492p=vf4R:A495094939492549p=^%>2A49509493549p>0A1N23?o50p=g%13#0#0#0#I,N2?o50p=Q%03#I,N2?o50p=]%10#1#1#1#1#1#1#1p=n%10#0#1#1p=u%10#<p>00%:09o35p>0Q%10#1p>0^%00#1#0#0p=A%00#0#0#0#0#0#0#0p=m%00#0#0#0#0#0#0#<p=~%I0,N5p>0[%00#0#1#0#0p>0Z%00#0#1#0#0#1#1p=b%00#0#1p=l%00#0#0#1p=t%00#1#0p=k%<5/U0p>0X%00#1#0#1#1p>0Og00Z_R;A4;50743p=j%03#<%05#0#0#<'U=4;0p=Z1N:2?o35=4;0p=K%03#</U5=4;0p>0N1U35=4;0p>0W%05#<,U3=4;0p>0M1U:21U35=4;054;p>0K%0:#</U2%03#</U5=4;054;p>0JA4;5094;394;294;:p=F%I2,N:?o35=4;0p=3%12#0#0#0#I,N:?o35=4;0p=dA4;50p>06P2P1P1P1P3P5CMP0CMp=fP2P9P9P9P3P5CMP0CMp=Wg00[jR<P8P5P0C_p>0=P3P9P5P0CMp=iP9P9P5P0CMp>0V%10#0p>0Uf7R=f6R>f5R?P:P21q35P0H04H04p=cP:P21q35P0H04p=OP>P?P:P2P3P5P0H04H04p>0Tg00\JR@@0R50p=wP1P2AB@35$0FP0CMp>05AB@50$0Fp>0SP1P2P3P5CM=8:0p>0aA8235/60p>0`A8>?:A8235/60'6p=[P1P>AB@?:$0FB0R@23CM=8=5/60p=T&0b4R0,p1R=P0g00]XR5#?#J#7#E#E$0?R3P7g00^=g00^oR2#2R?#2R:#2S00#2R>#2S01$0>RA#2RB#r#YS02#2RC#>%05RD#<RE#:S03C_&0D4R4CRRF;8FB09034RG=8=GRH%05#C#\#9#}#;>0904RI=8=IS04P0P3P<g00_NS05%rCS06#2S07#2S08#2S09#2S0:$0>S0;#r#Y#e#e#e#e#eRC#>RJg00`@RK#:RL'sRMPJC_%>?RN/DJ/NKP?P<PLH0L0074CRRO=8=OS0<P0P3%0DRP#1RQ#0RR#0RS#1RT#LRU00<JP7g00`^S0=P7P2P>PJH0I1sMLS0>C_0074S0?CRRV=8=VS0@P0P3g00aPS0A%I5#:S0B<0HJ/DUS0C%15RW#1RX#LRY+0<P4CRRZ=8=ZS0D%?5#=#5#P#a$0?R[>0904R\=8=\R]g00b<R^$0_R_%S5#=#9#;R`PE%05#@#=#`#5#;Ra%>2Rb%0PRP#1Rc#1Rd#0S0E#GS0F#0Re#IRf#:'DRg1DbJS0G%0cRc#0S0H#0Rh#1$0:#:S0I'DS0JPg%1DRD#0Ri#0S0K#0S0L#0Rj#LRkPLPL%0SRS#0S0M#0S0N#0Rl#IS0O#:,DbRm&0>C#Y#e#e#eS0P#2#YS0Q#2S0R#2S0S#YS0T#2S0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#r$0ES0[#2S0\#2S0]#2S0^#2S0_#2#YS0`#2S0a#2S0b#YS0c#2S0d#2S0e#2S0f#2S0g#2S0h#2S0i#r$0ES0j#2S0k#2S0l#2S0m#2RC%:aPm%0PRn#1Ro#0S0n#GS0o#GRp#0Rq#?#VS0p%05#`#7#C#E#;S0q#:S0r%2C#YRr%2rRr%2rRr%:`Rs1sLMS0s/sYRt,sYPL%YrRr#>%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%05#h#9#9#;Ru#:Rv%<5S0t#:S0u&0C5#a#@#@#5#VS0vPLPLPLPLPLPLPL%rr$0ERr%2rRr%2rRr%2r&0D9Rr+0B3HCvD^D^3H3H3HD^3HCvH0AS0wPL%S5#=#5#;S0xPB%1XRw#?S0y#0S0z$0:#:,DbS0{CgRxPL%S5#=#\#;PBPgCgRyPL%S5#=#J#;S0|PBPgCgRzPbPTPB&0C5#7#P#@#VS0}CQS0~Pb%?TS10PBPsC]S11PbPSPBPtCQS12PbPlPBg00cE%1wRw#1Rl#1RT#1#nR{#1R|#1#JS13#1#nR}#LR~<0@tS14C]S15Pb%1dRdPBP~CQS16Pb%?dS17PB%1RRR#LS18C]S19PbQ0EPB%05#@#=#u#a#;S0E#:S1:CQS1;Pb%1cRcPBPLCQS1<Pb%0hS1=#0PBQ0sC]S1>Pb%GcRc#0PBPJC]S1?Pb&0:eS1@PB%1q#E#LCgS1APbQ0HPBPLCQS0H%<|:08JKR|Pb%?lPBPNC]RlPbQ0OPB%1iS0O#0S1B#GS1C#IS1D#:,DbCgRi1NbfS1E%0nRf#0Rq#0Re#1#\#C#@#u#C#h#u#=#u#E$0080QAS1FPb%1oRoPB%1}$0^R}#G#5#5#5#5#5#5#\#LCQS1GPb%?oPB%1}#J#nR}#0#n#n#LC]S1HPb%GTPB%0WRW#0RT#1Ro#1#C#C#C#C#C#VC]S1IPb%1fRf#?PB%?RRd#9#=#LC]S1JPb%0eS1K#GRe#IPBPvCgS1LPbPqPBPLCQS1MPbPfPBPmCQS1NPbQ0nPBQ0{CQS0{Pb%IpPB%1QRQ#1S0n#?Rp#IS1O#:,DbCgRfPL%S5#=#E#;PBPLPL%S5#=#=#;S1PPBPLPL%S5#E#=#;S1QP>%1}#n#n#LPL%S5#E#A#;PBPkPL%S5#E#C#;S1RPBPgPLP`P>%LDS1SPbQ0NPBPLPbPdPBPLPb%0QS0N#GS1T#0RQPBPLPbQ1OPBPLPbQ0FPBPLPbQ17PB%1DS17#?S0F$0:S1O#:,DbRDPbQ1=PBP<P:PKPBH0]R}PbQ0oPBPLPbQ1KPBPLPb%?wPBQ0;#>S0;PbQ0zPB%95#5#}#7#VS0zPb%0XRXPBQ02#>RwPb%GXS02#0RX#0PBPvPb%1WRWPB%G5#A#P#J#a#VPb%?WRW#0PBPDPb%?oRoPBP}PbQ1TPBQ08#>Pb%0jRDPBQ07#>PbQ1DPBQ06#>PbQ1OPBPNPbPhPBQ0:#>PbQ0MPBQ09#>Pb%?TRT#0PBQ03PbQ17PB%95#5#u#\#VPbQ0yPBPLPbPXPBPLPbPWPBPLPbPTPBPLPbQ0FPBQ0;PbPjPBQ0zPbPSPBPwPbPqPB%<PRP#:Rq,DbPbQ02PB%G5#C#`#5#9#V%<n-0\b%m{#m#m#~R{%GeRe#7Rn#?#7Rw#0RS#m#m#~608b20[bw%<w+0PPbPPPBPNCg%9S#7#m#~:08N{&0Z5#P#7#~,NL%?o#~+0P%<nP`%b5#P#a#@$0?Q1P%b5#P#a#5Q0x%b5#P#`#9Q0|%b5#P#9#7Q1R%b5#P#=#AQ1Q%b5#P#E#a%S5#\#9%b5#J#a#7$00%b5#J#9#A$00RnPn%l5#u#J#9#A$00Rn%l5#5#7#9#7%l5#5#7#J#A%05#h#C#JPL%05#`#7#@#t#;RoPB%:oPL%05#`#7#@#}#;P>Q01#>Ro%l5#5#7#=#E%05#`#7#C#7%l5#5#7#5#A%05#`#7#C#A%l5#5#7#\#A%05#`#7#C#9Q0q%l5#5#7#J#7%k5#5#t#7#91NLu@0Yq:%}5#9#A#A#9%05#h#9#E#;+0X%k5#5#@#C#7$00%05#h#9#\#;RqPLPqPBQ00#>%k5#5#@#C#9%05#h#9#J%k5#5#@#A#A%05#h#=#@#;RqPLPqPB%<eRe#:%k5#5#@#A#5%05#h#=#=%k5#5#@#a#9&0O5#t#t#7%k5#5#A#A#9&0O5#@#mQ0tQ13#<608o1UKe&0D;3j3Z3Z3ZDK40N3ZDK40W3j80Nu40M3Z3Z3ZDKDK3Z60MnI0K3ZI0JI0JI0K3jDFD3D3D3D3D3D3D3D3D3DdD3D3D3DKDKD3D3D3D3DdD3DdD3D3D3D3D3D3D3DKD3D3D3DKDKDKDKDKDKRn+06DFDFRu+06DFDFR;3jDFDFM<z,X^Re;8eS0q1p11Ro/p1R1PoPaP`PECfRq;8qR:1p99R{/p9RSP{PgQ0JPLCWRP;8PS0J%05#t#5#=#5#;>0904Rw=8=wRjP0P[Q0C00=YP4CRRT=8=TS0CP`PEQ0EPgQ0G%1c#I#:Rc'DRWPgPk%A5#C#9#t#LRXPYQ1@#:,DbRhQ0_Q1:PhQ0pQ0rQ0`Q0aQ0bQ18P~PYQ0c#>Q0dQ0eQ0fQ0gQ0hQ0iQ14PtPsQ0}PYPXPLQ0>PYPMQ0jQ0kQ0lQ0m00Br3HCvD^D^3H3H3HD^3HCvH0APxPyPzQ1<Q1>Q1?Q1AQ0HP|PlPiQ1FQ1GQ1HQ1IQ1JPbQ0O#1#7PBP}Q1LQ1MQ1NQ0{PbQ1BPBPLCQPbQ1C#GPBPLPbQ0K#1R}PBPLPb%0}R}#?PBPLPbQ0LPBPLPb%GDPBPLPbQ0nPBQ1SPb%0pPBQ0vPbQ0NPBQ0uPb%0QPBPvPbPRPB&0C5#7#\#P#VPb%0dPBPsPbQ10PB%G5#}#@#J#7#VPnD3D3DdD3DdD3DdD3DdD3DdD35jfDFD3DFDFDFDFRfM<z,X^Rn=8_nS10PoQ0EP`PECfRB=81BS0E1pS9RdP{PgPWPXCW=iSYRW;8WS0uP`PEPaPgPgPgPkPLPLPmQ0w206z;9jxyM<z,X^R;=8_;S0NP{PgPgPLCWRR=8SRS0vP0P[20=UJQ0?CRRv=8=vS0?P`PE%05#@#E#J#E#;R5Pg1DbcRQPgPkPNPJPhQ0P%:5PhQ0pQ0rQ0QQ0RQ0SQ18P~PJQ0T#>Q0UQ0VQ0WQ0XQ0YQ0ZPLPYPsPXPLPNPLQ0>Q0sPMQ0[Q0\Q0]Q0^00Br3HCvD^D^3H3H3HD^3HCvH0APfM<z,X^Rf=8_fS0SPoP5P`PECfR5=815S0R20VgQRr=i{NS0V=iSJRJ=8dJS0UP`PEPaPgPQPgPkPLPLPmQ0wPxPyPzQ1E&0U}#9#E#E#E#7#=#5#=#@#A#;80QAQ0~Q11Q12Q15Q16Q19Q1;Q1<Q1>Q1?Q1AQ0H206iu9j|lDFDFDFDFM<z,X^Rl=8_lS0HAi{rLRr=8SrS1A/6jS1?,6:S1>'6S1<,6]S1;,6HS19'6S16'6R|'6Ru'6Ri,6jRA'6R},6:Rz'6Ry,6]Rx'6Rm'6Rk'6RQ'6Ra'6RE'6R`'6RM'6Rs'6R~'6Rh'6Rp'6RD'6Rt'6P=PFPHPt1q=GRtQ04PDP=PIQ0<PpP=POQ0@PhP=PVQ0DP~P=PZP]Ps1q=\RsQ0qPMP_PeP:P`1q1qR`Q0JPEPSPPPjPa1q=wRaQ0CPQP=PTQ10PkP_PnQ0EPmP1PBQ0uPxPdPWP]PyPsQ0NPzP_P;P:P}P`Q0vPAPSPRPjPiPaQ0?PuP=PvQ0SP|P_PfQ0RQ16P1P5Q0UQ19PdPJPHQ1;PtP]Q1<PsQ0HQ1>P_PlP:Q1?P`Q1APjPSPrPaGcDOK0TDODODOGcGcGcDODODOGcGcGcDODODOGcDOP=P0P01p@0R@g00d1Rag00e=3BRjP0PjPFP=P0P0g00f89B@aRFP0PFPGP=P0P0g00g39B@aRFP0PFPIP=P0P0g00gn9B@aRIP0PIP0P3P<Q05g00hiRI>0@6LRFPIC_B0;6NI/NKP?P<PLH0L0074CRP=P0P0g00ib9B@aR?P0P?P0P3P7P8PUPIC_P7Q0=P7P2P>PIH0I1sFLC_0074RFCRP=P0P0g00j]9B@aR>P0P>P0P3Q0AQ0B<0HI/DUR300<YP4CRP=P0P0g00kX9B@aR>P0P>P\P_g00lSR>g00mNR2PCg00nKg00oGDyg010CR7,X^P1Po%{7%|7%x7CfPqPSP{&037&027&017CWP{PgB0;6bIRbQ0I'DPLCWP=P0P0g011?9B@aRL1w0LH05PwP=P0P0g012:9B@aRLP0PLP0P[20=3YP4CRP_P>P2Q0_g0136g0143Dyg0150R4,X^P1Po%{4%|4%x4CfPBPdP{&034&024&0G4CW&0145iSP{Pg1DbcPXCW=iSYP=P0P0g015m9B@aRY1w0YH05P\P_P>P2PCg016ig017fDyg018cRY,X^P1Po%{Y%|Y%xYCfPqPSP{&03Y&02Y&01YCWPRP=P0P0g019`9B@aRR1w0RH05PwP=P0P0g01:\9B@aRRP0PRP0P[P<P8PUPIC_PFCRP_P>P2Q0Pg01;Xg01<UDyg01=RRF,X^P1Po%{F%|F%xFCfP5PdP{&03F&02F&0GFCW&01F5iSPSP9Q0VPICMP=P0P0g01>O9B@aRI1w0IH05PGP=P0P0g01?K9B@aRGP0PGP\P_P>P2PCg01@Gg01ADDyg01BARC,X^P1Po%{C%|C%xCCfPqPSP{&03C&02C&01CCWPrP=P0g01C>9B@aRa-0S01w0aPwI0aH0`F[GTF[F[GTF[F[F[F[GTF[F[GTGTGTGTGTGTGTdo"). Qed.
End VP1.
