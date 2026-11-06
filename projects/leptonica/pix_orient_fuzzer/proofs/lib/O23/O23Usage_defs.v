(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntryN.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs2LXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_scGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs4u_rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x62b1c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0xfff20 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0xfff20 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0x100ddc u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0xfff20 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0xfff20 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0xfff20 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0x10073c u_srH0 [] u_knH0 262.
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
Definition u_ssH30 : sym_state := SS 0x10073c u_srH30 [] u_knH30 262.
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
Definition u_ssG40 : sym_state := SS 0xfff20 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0x10073c u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Section VP1.
Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x109cb0%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x10a784%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0x109cb0%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0x109cb0%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0x109cb0%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xff528%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0xfa03c%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xff528%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x10090c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x14365, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xff528%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0xfa03c%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xff528%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x10132c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xff528%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0xfa03c%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Usage_defs ()) ["VP1"] "p%0p%1p&0p;1p;2p;4p;3p;<p;5g0000k10aTg000Pj2pTg0010j10Tg001Uj12Tg0024j1;Tg003=j1<Tg003[j18Tg004dj4bTg0061k10CTg006Qj36Tg006kj2RTg0085k40MTg009Bj11Tg009gk40ITg00;0j1ITg00;Nk30HTg00<Wk10UTg00=9k30@Tg00>Bk307Tg00?Mk40^Tg00@Vk20]Tg00Aak20PTg00Blk30[Tg00D7j2XTg00EBl<yTg00FKj2UTg00Fmj25Tg00GHj2vTg00Gbj3ATg00H?k30<Tg00IHj5zTg00JPk100Tg00KTj1{Tg00LVk101Tg00MYj1xTg00N\j1}Tg00O_j1|Tg00Pak10FTg00Qcj4PTg00RCj34Tg00Rcj3qTg00Snk403Tg00TIk30STg00Tfk10ETf0R0#0#0#0#1p=7%00#0#1#1p=M%10#0#0#1p=K%00#1#1#0p>08%00#0#0#<p=9%20#2p>0?%20#2#2p=r%20#2#2#2p=]g00UmR1f3R2f2R3g00VKR4f1R5;40CPp=TP1P3P5P0CPp>0:%00#1#0#0p=?%10#1#1#1p=@%00#0#0#0p==%10#0#0#<p=u%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=eg00WXR6@0@50p=tB0<650p=CA4450p>06%<0#8p=Og00XDR7g00XdR8P5P0Cbp>0>%10#1p>0G%10#0#1#0p=J%00#1p=s%00#0#0#1#0#0#1#1#1#0#0#0#0p=j%00#0#0#0#0#0#0#0p=Q%10#1#1#0p=N%00#1#1#1p=>%00#0p=H%00#Ip>0;%20#2#2#2#2#2#2#2p>0D%00#0#0p=:%00#0#<#8p=\%00#1#0#0#0p=`%00#0#1#0p=Gg00YVR9%;5;40p>0B%;3%;5=490549p=F%;5=49094939492p=wf4R:A495094939492549p=_%;2A49509493549p>0A%10#0#0#1#1#1#0#0p=h1R23?q50p=g%10#0#0#0p=E%10#1#0#1p=[%10#0p>09%13#0#0#0#I,R2?q50p=Z%03#I,R2?q50p=W%10#1#1#1#1#1#1#1p=f%10#0#1#1p=n%10#<p=~%809q35p>0R%10#1#1p>0_%10#1#0#0p=B%00#0#1#0#0#1#1#1p>0Q%I0,R5p>0\%00#0#0#1#0#0#1p>0O%00#0#1p=l%00#1#0p=m%<5/X0p>0Zg00Z_R;A4;50743p=k%03#<%05#0#0#<'X=4;0p=a1R:2?q35=4;0p=L%03#</X5=4;0p>0N1X35=4;0p>0Y%05#<,X3=4;0p>0L1X:21X35=4;054;p>0K%0:#</X2%03#</X5=4;054;p>0JA4;5094;394;294;:p=D%I2,R:?q35=4;0p=3%12#0#0#0#I,R:?q35=4;0p=dA4;50p>05P2P1P1P1P3P5CPP0CPp=iP2P9P9P9P3P5CPP0CPp=Yg00[jR<P8P5P0Cbp>0=P3P9P5P0CPp=oP9P9P5P0CPp>0Xf7R=f6R>f5R?P:P21v35P0H03H03p=cP:P21v35P0H03p=SP>P?P:P2P3P5P0H03H03p>0Wg00\JR@@0S50p>02P1P2AA@35$0EP0CPp>04AA@50$0Ep>0TP1P2P3P5CP=6:0p>0VA6235/50p>0`A6>?:A6235/50'5p=^P1P>AA@?:$0EB0S@23CP=6=5/50p=V&0a4R0,p1R=P0g00]XR5#0#7#M#K$08#9R3P7g00^=g00^oR2#2R?#2R:#2S00#2R>#2S01$0?RA#2RB#r#]S02#2RC#;%05RD#<RE#8S03Cb&0C4R4CTRF;6FB0:034RG=6=GRH%05#7#?#@#=#u>0:04RI=6=IS04P0P3P<g00_NS05%rCS06#2S07#2S08#2S09#2S0:$0?S0;#r#]#e#e#e#e#eRC#;RJg00`@RK#8RL'tRMPJCb%;?RN/CJ/RKP?P<PLH0M0064CTRO=6=OS0<P0P3%0DRP#1RQ#0RR#0RS#1RT#ORU00>JP7g00`^S0=P7P2P>PJH0I1tMLS0>Cb0064S0?CTRV=6=VS0@P0P3g00aPS0A%I5#8S0B<0HJ/CUS0C%15RW#1RX#ORY+0>P4CTRZ=6=ZS0D&0G5#@#J#K#s#9R[>0:04R\=6=\R]g00b<R^$0UR_%j5#7#9R`PE%05#Q#N#>#uRa%;2Rb%0PRP#1Rc#1Rd#0S0E#HS0F#0Re#IRf#8'CRg1CbJS0G%0cRc#0Rh#0Ri#1$0;#8S0H'CS0IPg%1DRD#0Rj#0S0J#0S0K#0Rk#ORlPLPL%0SS0L#0S0M#0S0N#0RS#IS0O#8,CbRm&0?C#]#e#e#eS0P#2#]S0Q#2S0R#2S0S#]S0T#2S0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#r$0DS0[#2S0\#2S0]#2S0^#2S0_#2#]S0`#2S0a#2S0b#]S0c#2S0d#2S0e#2S0f#2S0g#2S0h#2S0i#r$0DS0j#2S0k#2S0l#2S0m#2RC%8aPm%0PRn#1Ro#0S0n#HS0o#HRp#0Rq#:#\S0p%05#?#>#J#?#9S0q#8S0r%2C#]Rr%2rRr%2rRr%8`Rs1tLMS0s/tYRt,tYPL%]rRr#;%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%`5#>#@#G#9Ru#8Rv%<5S0t#8S0u%s5#7#7#Q#\S0vPLPLPLPLPLPLPL%rr$0DRr%2rRr%2rRr%2r&0C9Rr+0B3FCwD_D_3F3F3FD_3FCwH0AS0wPL%:5#h#7#s#9S0xPB%1XRw#:S0y#0S0z$0;#8,CbS0{CgRxPL%j5$08#9PBPgCgRyPL%j5#E#9S0|PBPgCgRzPbPTPB%[kS0}$09S0~$0G#\S10CZS11Pb%:TS12PBPsCWS13PbQ0LPBPtCZS14PbPSPBg00cE%1wRw#1RS#1RT#1#fR{#1R|#1#@S15#1#fR}#OR~<0@tS16CWS17Pb%1dRdPBP~CZS18Pb%:dS19PB%1RRR#OS1:CWS1;PbQ0EPB%05#=#7#G#7#uS0E#8S1<CZS1=Pb%1cRcPBPLCZS1>Pb%0iS1?#0PBQ0sCWS1@Pb%HcRc#0PBPJCWS1APb&0;eS1BPB%1q#J#OCgS1CPb%1hRh#HPBPLCWS1D%<|:07JKR|Pb%:SPBPNCWRSPbQ0OPB%1jS0O#0S1E#HS1F#IS1G#8,CbCgRj1RbfS1H%0nRf#0Rq#0Re#1#[#M#G#n#M#n#=#n#K#n#J#~80RAS1IPb%1oRoPB&0_}R}#H#B#B#B#B#B#B#[#OCZS1JPb%:oPB%1}#@#fR}#0#f#f#OCWS1KPb%HTPB%0WRW#0RT#1Ro#1#M#M#M#M#M#\CWS1LPb%1fRf#:PB%:RRd#E#K#OCWS1MPb%0eS1N#HRe#IPBPvCgS1OPbPqPBPLCZS1PPbPfPBPmCZS1QPbQ0nPBQ0{CZS0{Pb%IpPB%1QRQ#1S0n#:Rp#IS1R#8,CbCgRfPL%j5#M#9PBPLPL%j5#G#9S1SPBPLPL%05$0Q#7#G#9S1TP>%1}#f#f#OPL%j5#[#9PBPlPL%j5#B#9S1UPBPgPLP`P>%ODS1VPbQ0NPBPLPbPdPBPLPb%0QS0N#HS1W#0RQPBPLPbQ1RPBPLPbQ0FPBPLPbQ19PB%1DS19#:S0F$0;S1R#8,CbRDPbQ1?PBP<P:PKPBH0^R}PbQ0oPBPLPbQ1NPBPLPb%:wPBQ0;#;S0;PbQ0zPB%E5#J#B#>#\S0zPb%0XRXPBQ02#;RwPb%HXS02#0RX#0PBPvPb%1WRWPB%15#@#[#B#[#\Pb%:WRW#0PBPDPb%:oPBP}PbQ1WPBQ08#;Pb%0kRoPBQ07#;PbQ1GPBQ06#;PbQ1RPBPNPbPiPBQ0:#;PbQ0MPBQ09#;Pb%:TRT#0PBQ03PbQ19PB%E5#n#M#?#\PbQ0yPBPLPbPXPBPLPbPWPBPLPbPTPBPLPbQ0FPBQ0;PbPkPBQ0zPbQ0LPBPwPbPqPB%<PRP#8Rq,CbPbQ02PB%15#N$08#K#@#\%<n-0]b%={#Q#Q#Q#9R{%HeRe#=Rn#:#=Rw#0Rk#=#Q#Q#9607b20\bw%<w+0PPbPPPBPNCg%Ek#Q#Q#9:07N{&09h#Q#9,RL&095#?#Q#9+0P%<nP`%j5#7#uQ1S%:5#h#7#=Q0x%:5#h#7#BQ0|%:5#h#G#?Q1U%:5#h#M#EQ1T%:5#h#?#J%05$0Q#?#G&0O5#[#=#E#~&0O5#[#G#B#~RnPn%l5#7#[#G#B#~Rn%l5#7#N#G#E%l5#7#N#h%`5#>#J#KPL%05#?#>#E#n#9RhPB%8hPL%05#?#>#E#@#9P>Q01#;Rh%l5#7#N#?#G%05#?#>#K#J%l5#7#N$08#B%05#?#>#K#N%l5#7#N#>#B%05#?#>#J#GQ0q%l5#7#N#K#E%m5#7#N#n#=1RLu@0[q:%?5#M#@#K#E%`5#>#@#?#9+0Z%m5#7#@#[#E#~%`5#>#@#>#9RqPLPqPBQ00#;%m5#7#@#N#=%`5#>#@#K%m5#7#@#N#B%`5#>#@#B#9RqPLPqPB%<eRe#8%m5#7#f#?%`5#E#=#M%m5#G#=#7#=%`5#E#>#J%m5#G#7#@#=%`5#J#QQ0tQ15#<607h1XKe&0C;3k3a3a3aDL40N3aDL40Y3k80Nu40L3a3a3aDLDL3a60LnI0K3aI0JI0JI0K3kDDD3D3D3D3D3D3D3D3D3DdD3D3D3DLDLD3D3D3D3DdD3DdD3D3D3D3D3D3D3DLD3D3D3DLDLDLDLDLDLRn+05DDDDRu+05DDDDR;3kDDDDM<y,U^Re;6eS0q1p11Rh/p1R1PhPaP`PECiRq;6qR:1p99R{/p9RkP{PgQ0IPLCYRP;6PS0I%@5#?#=#>#u>0:04Rw=6=wRTP0P[Q0C00=YP4CTRW=6=WS0CP`PEQ0EPgQ0G%1c#I#8Rc'CRXPgPlQ0~#s#s#ORiPYQ1B#8,CbRDQ0_Q1<PDQ0pQ0rQ0`Q0aQ0bQ1:P~PYQ0c#;Q0dQ0eQ0fQ0gQ0hQ0iQ16PtPsQ10PYPiPLQ0>PYPMQ0jQ0kQ0lQ0m00Br3FCwD_D_3F3F3FD_3FCwH0APxPyPzQ1>Q1@Q1AQ1CQ1DP|PSPjQ1IQ1JQ1KQ1LQ1MPbQ0O#1#=PBP}Q1OQ1PQ1QQ0{PbQ1EPBPLCZPbQ1F#HPBPLPbQ0J#1R}PBPLPb%0}R}#:PBPLPbQ0KPBPLPb%HoPBPLPbQ0nPBQ1VPb%0pPBQ0vPbQ0NPBQ0uPb%0QPBPvPbPRPBQ0}#>#\Pb%0dPBPsPbQ12PB%H5#=#7#B#>#\PnD3D3DdD3DdD3DdD3DdD3DdD35kfDDD3DDDDDDDDRfM<y,U^Rn=6_nS12PhQ0EP`PECiRB=61BS0E1pk9RdP{PgPXPiCY=okYRX;6XS0}P`PEPaPgPgPgPlPLPLPmQ0w205z;9kxyM<y,U^R;=6_;S0uP{PgPgPLCYRR=6kRS0NP0P[20=UJQ0?CTRv=6=vS0?P`PE%:5#=#K#K#s#uR5Pg1CbcRQPgPlPNPJPDQ0P%85PDQ0pQ0rQ0QQ0RQ0SQ1:P~PJQ0T#;Q0UQ0VQ0WQ0XQ0YQ0ZPLPYPsPiPLPNPLQ0>Q0sPMQ0[Q0\Q0]Q0^00Br3FCwD_D_3F3F3FD_3FCwH0APfM<y,U^Rf=6_fS0SPhP5P`PECiR5=615S0R20XgQRr=o{NS0V=okJRJ=6dJS0UP`PEPaPgPQPgPlPLPLPmQ0wPxPyPzQ1H&09}#E#J#J#J#=#h#K#G#?#980RAQ11Q13Q14Q17Q18Q1;Q1=Q1>Q1@Q1AQ1CQ1D205ju9k|SDDDDDDDDM<y,U^RS=6_SS1DAo{rLRr=6krS1C/5TS1A,5:S1@'5S1>,5]S1=,5HS1;'5S18'5R|'5Ru'5Rj,5TRA'5R},5:Rz'5Ry,5]Rx'5Rm'5Rl'5RQ'5Ra'5RE'5R`'5RM'5Rs'5R~'5RD'5Rp'5Ro'5Rt'5P=PFPHPt1v=GRtQ04PoP=PIQ0<PpP=POQ0@PDP=PVQ0DP~P=PZP]Ps1v=\RsQ0qPMP_PeP:P`1v1qR`Q0IPEPkPPPTPa1v=wRaQ0CPQP=PWQ12PlP_PnQ0EPmP1PBQ0}PxPdPXP]PyPsQ0uPzP_P;P:P}P`Q0NPAPkPRPTPjPaQ0?PuP=PvQ0SP|P_PfQ0RQ18P1P5Q0UQ1;PdPJPHQ1=PtP]Q1>PsQ1DQ1@P_PSP:Q1AP`Q1CPTPkPrPaGcDSK0WDSDSDSGcGcGcDSDSDSGcGcGcDSDSDSGcDSP=P0P01p@0R@g00d1Rag00e=3ARTP0PTPFP=P0P0g00f89A@aRFP0PFPGP=P0P0g00g39A@aRFP0PFPIP=P0P0g00gn9A@aRIP0PIP0P3P<Q05g00hiRI>0@6LRFPICbB0<6NI/RKP?P<PLH0M0064CTP=P0P0g00ib9A@aR?P0P?P0P3P7P8PUPICbP7Q0=P7P2P>PIH0I1tFLCb0064RFCTP=P0P0g00j]9A@aR>P0P>P0P3Q0AQ0B<0HI/CUR300>YP4CTP=P0P0g00kX9A@aR>P0P>P\P_g00lSR>g00mNR2PCg00nKg00oGDzg010CR7,U^P1Ph&007%{7&017CiPqPkP{%x7%}7%|7CYP{PgB0<6bIRbQ0H'CPLCYP=P0P0g011?9A@aRL2020LH04PwP=P0P0g012:9A@aRLP0PLP0P[20=3YP4CTP_P>P2Q0_g0136g0143Dzg0150R4,U^P1Ph&004%{4&014CiPBPdP{%x4%}4&0F4CY%|45okP{Pg1CbcPiCY=okYP=P0P0g015m9A@aRY2020YH04P\P_P>P2PCg016ig017fDzg018cRY,U^P1Ph&00Y%{Y&01YCiPqPkP{%xY%}Y%|YCYPRP=P0P0g019`9A@aRR2020RH04PwP=P0P0g01:\9A@aRRP0PRP0P[P<P8PUPICbPFCTP_P>P2Q0Pg01;Xg01<UDzg01=RRF,U^P1Ph&00F%{F&01FCiP5PdP{%xF%}F&0FFCY%|F5okPkP9Q0VPICPP=P0P0g01>O9A@aRI2020IH04PGP=P0P0g01?K9A@aRGP0PGP\P_P>P2PCg01@Gg01ADDzg01BARC,U^P1Ph&00C%{C&01CCiPqPkP{%xC%}C%|CCYPrP=P0g01C>9A@aRa-0T02020aPwI0VH0`F^GVF^F^GVF^F^F^F^GVF^F^GVGVGVGVGVGVGVdo"). Qed.
End VP1.
