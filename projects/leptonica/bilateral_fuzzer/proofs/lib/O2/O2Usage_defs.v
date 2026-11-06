(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2OpenFail_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntryN.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs2LXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_scGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs4u_rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x17618 sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0x31d38 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0x31d38 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0x326c8 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0x31d38 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0x31d38 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0x31d38 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0x32028 u_srH0 [] u_knH0 262.
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
Definition u_ssH30 : sym_state := SS 0x32028 u_srH30 [] u_knH30 262.
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
Definition u_ssG40 : sym_state := SS 0x31d38 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0x32028 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Section VP1.
Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x36a58%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x36fe4%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0x36a58%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0x36a58%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0x36a58%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x31958%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x2f4d4%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0x31958%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x321f8%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x10bd6, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x31958%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x2f4d4%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0x31958%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x32c18%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x31958%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x2f4d4%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Usage_defs ()) ["VP1"] "p%0p%1p&0p;1p;2p;4p;3p;<p;5g0000k10]Tg000Pj2oTg0010j12Tg001Oj1:Tg002Xj10Tg003=j1>Tg003[j18Tg004dj4aTg0061k10CTg006Qj37Tg006kj2MTg0085k40KTg009Bj11Tg009gk40ITg00;0j1KTg00;Nk30HTg00<Wk10TTg00=9k30@Tg00>Bk306Tg00?Mk40\Tg00@Vk20[Tg00Aak20LTg00Blk30YTg00D7j2\Tg00EBl<uTg00FKj2WTg00Fmj26Tg00GHj2pTg00Gbj3?Tg00H?k30:Tg00IHj5yTg00JPj1vTg00KTj1xTg00LVk100Tg00MYj1zTg00N\j1wTg00O_j1|Tg00Pak10GTg00Qcj4OTg00RCj35Tg00Rcj3kTg00Snk401Tg00TIk30PTg00Tfk10ETf0R0#1#0p=]%10#1#0#1p=<%00#1#0#0p=;%10#0#1#1p=A%00#0#0#>p=4%20#2p>0>%20#2#2p=q%20#2#2#2p=[g00UmR1f3R2f2R3g00VKR4f1R5;50COp=SP1P3P5P0COp>08%00#1#1#1p=n%10#1#1#1p=Q%00#0#1#0p=H%00#>p>0?%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=dg00WXR6@0@50p=rB0:650p=CA5450p>04%>0#8p=Ig00XDR7g00XdR8P5P0Cap>0;%00#0#1#1p=D%10#1#0#0#1#0#1#0p=b%10#0#0#0p=B%00#1p>0F%00#0#0#0p==%00#1#0#1p=Y%00#0p=J%00#Kp>09%20#2#2#2#2#2#2#2p>0D%00#0#>#8p=i%00#0#1p=t%10#0#1#0#0#1#1p=h%10#0#1#0p=@%10#1#0#0p=9g00YVR9%:5;50p>0B%:3%:5=590559p=G%:5=59095939592p=sf4R:A595095939592559p=`%:2A59509593559p>0A%10#1#0#0#1#0p=_%00#0#0p=F1M23?k50p=f%00#1#1#0p=N%10#1#1#0p>07%13#0#0#0#K,M2?k50p=^%03#K,M2?k50p=T%10#1#1#1#1#1#1#1p=m%10#0#0#1p=R%10#>p=~%809k35p>0O%10#1p>0N%10#0#0p>0M%00#0#0#0#0#0#0#0p=V%K0,M5p>0Z%>5/\0p>0Xg00Z_R;A5;50753p=l%05#>,\3=5;0p>0=%0:#>/\2%03#>/\5=5;055;p={1M:2?k35=5;0p=L1\35=5;0p>0W%03#>/\5=5;0p>051\:21\35=5;055;p>0JA5;5095;395;295;:p=E%K2,M:?k35=5;0p=3%12#0#0#0#K,M:?k35=5;0p=eA5;50p>03P2P1P1P1P3P5COP0COp=cP2P9P9P9P3P5COP0COp=Ug00[jR<P8P5P0Cap>0<P3P9P5P0COp=jP9P9P5P0COp>0Vf7R=f6R>f5R?P:P21p35P0H01H01p=gP:P21p35P0H01p=PP>P?P:P2P3P5P0H01H01p>0Ug00\JR@@0P50p=}P1P2A?@35$0EP0COp>02A?@50$0Ep>0SP1P2P3P5CO=7:0p>0RA7235/60p>0QA7>?:A7235/60'6p=ZP1P>A?@?:$0EB0P@23CO=7=5/60p=X&0]4R0,o1R=P0g00]XR5#]#<#;#A#4R3P7g00^=g00^oR2#2R?#2R:#2S00#2R>#2S01$0>RA#2RB#q#[S02#2RC#:%05RD#>RE#8S03Ca&0C4R4CSRF;7FB08034RG=7=GRH%A5#n#Q#H$0?>0804RI=7=IS04P0P3P<g00_NS05%qCS06#2S07#2S08#2S09#2S0:$0>S0;#q#[#d#d#d#d#dRC#:RJg00`@RK#8RL'rRMPJCa%:?RN/CJ/MKP?P<PLH0K0044CSRO=7=OS0<P0P3%0DRP#1RQ#0RR#0RS#1RT#IRU00;JP7g00`^S0=P7P2P>PJH0I1rMLS0>Ca0044S0?CSRV=7=VS0@P0P3g00aPS0A%K5#8S0B<0HJ/CUS0C%15RW#1RX#IRY+0;P4CSRZ=7=ZS0D%]5#D#H#A#4R[>0804R\=7=\R]g00b<R^$0TR_%b5#B$0F#4R`PE%]5#;#=#Y#4Ra%:2Rb%0PRP#1Rc#1Rd#0S0E#JS0F#0Re#KRf#8'CRg1CbJS0G%0cRc#0S0H#0Rh#1$09#8S0I'CS0JPg%1DRD#0Ri#0S0K#0S0L#0Rj#IRkPLPL%0SRS#0S0M#0S0N#0Rl#KS0O#8,CbRm&0>C#[#d#d#dS0P#2#[S0Q#2S0R#2S0S#[S0T#2S0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#q$0DS0[#2S0\#2S0]#2S0^#2S0_#2#[S0`#2S0a#2S0b#[S0c#2S0d#2S0e#2S0f#2S0g#2S0h#2S0i#q$0DS0j#2S0k#2S0l#2S0m#2RC%8aPm%0PRn#1Ro#0Rp#JS0n#JRq#=#iS0o%t5#D#=#B#4S0p#8S0q%2C#[Rr%2rRr%2rRr%8`Rs1rLMS0r/rYRt,rYPL%[rRr#:%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%h5#Y#Y#4Ru#8Rv%>5S0s#8S0t%@5#n#9#H#iS0uPLPLPLPLPLPLPL%qr$0DRr%2rRr%2rRr%2r&0C9Rr+0B3GCsD`D`3G3G3GD`3GCsH0AS0vPL%_5#@#Y#4S0wPB%1XRw#FS0x#0S0y$09#8,CbS0zCfRxPL%_5#@#N#4PBPgCfRyPL%_5#@#B#4S0{PBPgCfRzPbPTPB%1pRp$07S0|#1S0}#<#IS0~C^S10Pb%FTS11PBPsCTS12PbPSPBPtC^S13PbPlPBg00cE%1wRw#1Rl#1RT#1#mR{#1R|#1#QS14#1#mR}#IR~<0@tS15CTS16Pb%1dRdPBP~C^S17Pb%FdS18PB%1RRR#IS19CTS1:PbQ0EPB%]5#;#D#Q#4S0E#8S1;C^S1<Pb%1cRcPBPLC^S1=Pb%0hS1>#0PBQ0rCTS1?Pb%JcS1@#0PBPJCTS1APb&09eS1BPB%0nRe#0Rc#1Rd#1#n#@#ICfS1CPbQ0HPBPLC^S0H%>|:06JKR|Pb%FlPBPNCTRlPbQ0OPB%1iS0O#0S1D#JS1E#KS1F#8,CbCfRi1MbfS1G%0cRf#1#<#D#H#A#D#A#=#A#R#A#@#~80OAS1HPb%1oRoPB%1}$0NR}#J#9#9#9#9#9#9#<#IC^S1IPb%FoPB%1}#Q#mR}#0#m#m#ICTS1JPb%JTPB%0WRW#0RT#1Ro#1#D#D#D#D#D#iCTS1KPb%1eS1L#FPB%FRRe#B#R#ICTS1MPb%0fS1N#JRf#KPBPvCfS1OPb%JdPBPLCTS1PPbQ1LPBPmC^S1LPb%JpPBQ0zCTS0zPb%KqPB%1QRQ#1S1Q#FRq#KRp#8,CbCfRdPL%_5#@#D#4PBPLPL%_5#@#H#4S1RPBPLPL%_5#A#H#4S1SP>%1}#m#m#IPL%_5#@#<#4PBPkPL%_5#@#9#4S1TPBPgPLP`P>%IDS1UPbQ0NPBPLPbPePBPLPb%0QS0N#JS1V#0RQPBPLPbPpPBPLPbQ0FPBPLPbQ18PB%1DS18#FS0F$09RD#8,CbRpPbQ1>PBP<P:PKPBH0\R}PbQ0nPBPLPbQ1NPBPLPb%FwPBQ0;#:S0;PbQ0yPB&0F5#<#B#N#iS0yPb%0XRXPBQ02#:S02Pb%0XRX#0S1N#0Rw#0PBPvPb%1WRWPB&0M5#N#<#R#iPb%FWRW#0PBPpPb%FoPBP}PbQ1VPBQ08#:Pb%0jRoPBQ07#:PbQ1FPBQ06#:PbPDPBPNPbPhPBQ0:#:PbQ0MPBQ09#:Pb%FTRT#0PBQ03PbQ18PB&0F5#<#Q#D#iPbQ0xPBPLPbPwPBPLPbPWPBPLPbPTPBPLPbQ0FPBQ0;PbPjPBQ0yPbPSPBQ02PbPcPB%>PRP#8Rc,CbPbQ1NPB%05$0N#A#Q#N#i%>n-0[b%={#V#V#V#4R{%JfRf#=Rn#F#=RS#0Rj#=#V#V#4606b20ZbS%>S+0LPbPPPBPNCf%Bj#V#V#4:06N{%]X#V#4,ML%]5#;#V#4+0L%>nP`%b5#B#N$0?Q1R%b5#R#=Q0w%b5#R#9Q0{%b5#@#;Q1T%b5#A#BQ1S%b5#b%_5#<$07#4%95#A#n#B#~%95#A#R#9#~RnPn%05#;#A#R#9#~Rn%05#;#A#A#B%05#;#9#H#9%h5#=#<#4PL%t5#H$07#Q#4RXPB%8XPL%t5#H#Q#D#4P>Q01#:RX%05#;#A#<#H%t5#H#Q$07#4%05#;#A#Q#9%t5#D#=#H#4%05#;#9#=#9%t5#D#=#N#4Q0p%05#;#9#H#B%15#;#9#;#=1MLu@0Yc:%]5#R#@#A#=%h5#Y#n#4+0X%15#;#<#N#;#~%h5#Y#@#4RcPLPcPBQ00#:%15#;#<#N#9%h5#Y#9#4%15#;#<#n#B%h5#Y#Q#4RcPLPcPB%>fRf#8%15#;#<#B#=%h5#N#N#4%15#;#<#R#9%h5#<#<#4Rc%15#Y#B#VQ0sQ14#>606X1\Kf&0C;3l60=cD{DLD{DL40W3l805u40=405D{DLDL40560=nI0J405D{D{I0J3lDED3D3D3D3D3D3D3D3D3DeD3D3D3DLDLD3D3D3D3DeD3DeD3D3D3D3D3D3D3DLD3D3D3DLDLDLDLDLDLRn+03DEDERu+03DEDERc3lDEDEM<u,W^R;;7;S0p1o11Rf/o1R1PfPaP`PECcRX;7XR:1o99R{/o9RjP{PgQ0JPLCURP;7PS0J%n5#@#N#@$0?>0804RS=7=SRTP0P[Q0C00<YP4CSRW=7=WS0CP`PEQ0EPgQ0GQ1@#1#K#8Rw'CRhPgPkQ0}#N#IRDPYQ1B#8,CbRpQ0_Q1;PpQ0oQ0qQ0`Q0aQ0bQ19P~PYQ0c#:Q0dQ0eQ0fQ0gQ0hQ0iQ15PtPsQ0~PYPDPLQ0>PYPMQ0jQ0kQ0lQ0m00Br3GCsD`D`3G3G3GD`3GCsH0APxPyPzQ1=Q1?Q1AQ1CQ0HP|PlPiQ1HQ1IQ1JQ1KQ1MPbQ0O#1#=PBP}Q1OQ1PQ1LQ0zPbQ1DPBPLC^PbQ1E#JPBPLPbQ0K#1R}PBPLPb%0}R}#FPBPLPbQ0LPBPLPb%JoPBPLPbQ1QPBQ1UPb%0qPBQ0uPbQ0NPBQ0tPb%0QPBPvPbPRPBQ0|#0#<#IPb%0ePBPsPbQ11PB&0M5#B#=#H#iPnD3D3DeD3DeD3DeD3DeD3DeD35ldDED3DEDEDEDERdM<u,W^Rn=7_nS11PfQ0EP`PECcRB=71BS0E1oj9ReP{PgPhPDCU=jjYRh;7hS0|P`PEPaPgPgPgPkPLPLPmQ0v203zc9lxyM<u,W^Rc=7_cS0tP{PgPgPLCURR=7jRS0NP0P[20<UJQ0?CSRv=7=vS0?P`PE%]5#Y#B#D#4R5Pg1CbwRQPgPkPNPJPpQ0P%85PpQ0oQ0qQ0QQ0RQ0SQ19P~PJQ0T#:Q0UQ0VQ0WQ0XQ0YQ0ZPLPYPsPDPLPNPLQ0>Q0rPMQ0[Q0\Q0]Q0^00Br3GCsD`D`3G3G3GD`3GCsH0APdM<u,W^Rd=7_dS0SPfP5P`PECcR5=715S0R20VgQRr=j{NS0V=jjJRJ=7eJS0UP`PEPaPgPQPgPkPLPLPmQ0vPxPyPzQ1G%]}#B#@#@#@#=#R#9#R#H#;#480OAQ10Q12Q13Q16Q17Q1:Q1<Q1=Q1?Q1AQ1CQ0H203iu9l|lDEDEDEDEM<u,W^Rl=7_lS0HAj{rLRr=7jrS1C/6TS1A,6:S1?'6S1=,6]S1<,6HS1:'6S17'6R|'6Ru'6Ri,6TRA'6R},6:Rz'6Ry,6]Rx'6Rm'6Rk'6RQ'6Ra'6RE'6R`'6RM'6Rs'6R~'6Rp'6Rq'6Ro'6Rt'6P=PFPHPt1p=GRtQ04PoP=PIQ0<PqP=POQ0@PpP=PVQ0DP~P=PZP]Ps1p=\RsQ0pPMP_P;P:P`1p1XR`Q0JPEPjPPPTPa1p=SRaQ0CPQP=PWQ11PkP_PnQ0EPmP1PBQ0|PxPePhP]PyPsQ0tPzP_PcP:P}P`Q0NPAPjPRPTPiPaQ0?PuP=PvQ0SP|P_PdQ0RQ17P1P5Q0UQ1:PePJPHQ1<PtP]Q1=PsQ0HQ1?P_PlP:Q1AP`Q1CPTPjPrPaGgDPK0UDPDPDPGgGgGgDPDPDPGgGgGgDPDPDPGgDPP=P0P01o@0R@g00d1Rag00e=3?RTP0PTPFP=P0P0g00f69?@aRFP0PFPGP=P0P0g00fo9?@aRFP0PFPIP=P0P0g00gh9?@aRIP0PIP0P3P<Q05g00haRI>0@6LRFPICaB0:6NI/MKP?P<PLH0K0044CSP=P0P0g00iX9?@aR?P0P?P0P3P7P8PUPICaP7Q0=P7P2P>PIH0I1rFLCa0044RFCSP=P0P0g00jQ9?@aR>P0P>P0P3Q0AQ0B<0HI/CUR300;YP4CSP=P0P0g00kJ9?@aR>P0P>P\P_g00lCR>g00m;R2PCg00n5g00noDyg00oiR7,W^P1Pf%v7%x7&007CcPXPjP{%z7%w7%|7CUP{PgB0:6bIRbQ0I'CPLCUP=P0P0g010c9?@aRL1}0LH02PSP=P0P0g011\9?@aRLP0PLP0P[20<3YP4CSP_P>P2Q0_g012Vg013QDyg014LR4,W^P1Pf%v4%x4&004CcPBPeP{%z4%w4&0G4CU%|45jjP{Pg1CbwPDCU=jjYP=P0P0g015G9?@aRY1}0YH02P\P_P>P2PCg016Ag017<Dyg0187RY,W^P1Pf%vY%xY&00YCcPXPjP{%zY%wY%|YCUPRP=P0P0g01929?@aRR1}0RH02PSP=P0P0g019l9?@aRRP0PRP0P[P<P8PUPICaPFCSP_P>P2Q0Pg01:fg01;aDyg01<\RF,W^P1Pf%vF%xF&00FCcP5PeP{%zF%wF&0GFCU%|F5jjPjP9Q0VPICOP=P0P0g01=W9?@aRI1}0IH02PGP=P0P0g01>Q9?@aRGP0PGP\P_P>P2PCg01?Kg01@FDyg01AARC,W^P1Pf%vC%xC&00CCcPXPjP{%zC%wC%|CCUPrP=P0g01B<9?@aRa-0S01}0aPSI0RH0QFZGXFZFZGXFZFZFZFZGXFZFZGXGXGXGXGXGXGXdo"). Qed.
End VP1.
