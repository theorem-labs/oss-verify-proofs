(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rG3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2PXC5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_datac5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4srG3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4knG3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4scG3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rH3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4srH3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4knH3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4scH3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rI3c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rF4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4srF4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4knF4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4scF4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rG4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rH4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4srH4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4knH4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4scH4c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3rI4K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rAc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rBc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rCc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rDc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rEc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rFc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rGc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rHc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3srHc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3knHc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs4scOFc5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs2rI".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x4347c; 0x43880; 0x43a08; 0x433b0; 0x12afc; 0x12c88; 0x3d914; 0x3bef8; 0x3e37c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
(* [comment removed for export] *)
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
(* [comment removed for export] *)
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x77000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x17868 sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x43d68 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x3e75c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x3e75c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x3f0ec srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x3e75c srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x3e75c srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x3e75c srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x3ea4c srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x3ea4c srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0x3e75c srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x3ea4c srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Section VP1.
Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x3e37c%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x3ec1c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x11d14, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x3e37c%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x3ea4c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x3bef8%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x3e37c%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x3f63c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x3e37c%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x3ea4c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x3bef8%Z, []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.

Section VP2.
Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x43d64%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x4347c%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x43a08%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x4347c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x4347c%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x4347c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x3e37c%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x3ea4c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x3bef8%Z, []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP2.
