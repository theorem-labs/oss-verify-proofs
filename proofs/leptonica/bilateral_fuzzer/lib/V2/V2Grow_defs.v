(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs V2Open_defs V2Oom_defs V2DirRead_defs V2ReadLoop_defs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Grow_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K47Corelib7Numbers7BinNums1Z03K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs8kn_afterC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC5ARocqVerifyHarness?AgentSubmission2V2:V2Oom_defs8kn_acallK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01C47Corelib5Lists7ListDef3nthI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_sr1c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs6g_sr1tI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_r1nc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs6cap2_xc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_r1tC5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5kn_MLc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_kn1c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_knMC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:sr_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive?sr_after_call_jC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall7kn_callc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_sr2K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs4g_r2c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_kn2C5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs7KEPT_MCc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs6g_sr3iC5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3IHIc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs6g_kn3iC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_sr3I47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs4g_r3c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_kn3c5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_knLc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_rvlC5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission2V2;V2Grow_defs5g_srLC5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4sr_L".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSG : list Z := (0x17ab0 :: STOPSL)%Z.
Definition runG (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSG scr ss [].

(* [comment removed for export] *)
Definition g_ss1 : sym_state := SS 0x178fc sr_F [] kn_ML NXL.
Definition g_r1n := Eval vm_compute in runG (SCR [false] [] []) g_ss1.    (* [comment removed for export] *)
Definition g_r1t := Eval vm_compute in runG (SCR [true] [] []) g_ss1.     (* [comment removed for export] *)
Definition g_sr1 : list expr := Eval vm_compute in s_regs (fst (fst g_r1n)).
Definition g_kn1 : list kentry := Eval vm_compute in kn_after g_r1n kn_ML.
Definition g_sr1t : list expr := Eval vm_compute in s_regs (fst (fst g_r1t)).
Definition cap2_x : expr := Eval vm_compute in nth 10 g_sr1 (ELit 0).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition g_srM : list expr := sr_after_call_j g_sr1 KEPT_AL 41.
Definition g_knM : list kentry := Eval vm_compute in kn_acall g_kn1.
(* [comment removed for export] *)
Definition g_knOK : list kentry :=
  KRange (EVar 51) 0x77000 0x7fffff7f0000 :: KAlign (EVar 51) 16 :: KWr (SA (EVar 51) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 51) 0) 65536 :: g_knM.

(* [comment removed for export] *)
Definition g_r2 := Eval vm_compute in runG (SCR [false; false] [] []) (SS 0x17910 g_srM [] g_knOK 73).
Definition g_sr2 : list expr := Eval vm_compute in s_regs (fst (fst g_r2)).
Definition g_kn2 : list kentry := Eval vm_compute in kn_after g_r2 g_knOK.

(* [comment removed for export] *)
Definition g_sr3i : list expr := Eval vm_compute in sr_after_call_j g_sr2 KEPT_MC 73.
Definition g_kn3i : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x45000 g_kn2.
Definition g_r3 := Eval vm_compute in runG scr0 (SS 0x1792c g_sr3i [] g_kn3i 105).
Definition g_sr3 : list expr := Eval vm_compute in s_regs (fst (fst g_r3)).
Definition g_kn3 : list kentry := Eval vm_compute in kn_after g_r3 g_kn3i.

(* [comment removed for export] *)
Definition g_srL : list expr := Eval vm_compute in sr_after_call_j g_sr3 KEPT_AL 105.
Definition g_knL : list kentry := Eval vm_compute in kn_acall g_kn3.
Definition g_rvl : list expr := rvl9 (EVar 51) (EVar 8) cap2_x g_srL.

Section VP1.
Lemma g_itin1 :
  (s_pc (fst (fst g_r1n)), snd (fst g_r1n), s_log (fst (fst g_r1n)))
    = (0x3c370%Z, [SCBr false BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ (nth 1 g_sr1 (ELit 0), nth 10 g_sr1 (ELit 0), nth 2 g_sr1 (ELit 0), nth 4 g_sr1 (ELit 0))
     = (ELit 0x17910, cap2_x, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x56270)
  /\ cap2_x = EMd M_MUL (ELit 2) (EVar 8)
  /\ (s_pc (fst (fst g_r1t)), snd (fst g_r1t), s_log (fst (fst g_r1t)))
    = (0x17ab0%Z, [SCBr true BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ kn_after g_r1t kn_ML = kn_ML
  /\ (nth 2 g_sr1t (ELit 0), nth 3 g_sr1t (ELit 0), nth 4 g_sr1t (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x56270)
  /\ kn_vars_lt 41 g_kn1 = true /\ kn_acall g_kn1 = g_knM.
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma g_itin2 :
  (s_pc (fst (fst g_r2)), snd (fst g_r2), s_log (fst (fst g_r2))) = (0x4347c%Z, [SCBr false BC_EQ (EVar 8) (ELit 0)], [])
  /\ (nth 1 g_sr2 (ELit 0), nth 10 g_sr2 (ELit 0), nth 11 g_sr2 (ELit 0), nth 12 g_sr2 (ELit 0))
     = (ELit 0x1792c, EVar 51, EVar 6, EVar 8)
  /\ sr_vars_lt 73 g_sr2 = true /\ kn_vars_lt 73 g_kn2 = true
  /\ sr_after_call_j g_sr2 KEPT_MC 73 = g_sr3i /\ kn_call [] 0 0 IHI 0x45000 g_kn2 = g_kn3i /\ kn_vars_lt 73 g_kn3i = true.
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma g_itin3 :
  (s_pc (fst (fst g_r3)), snd (fst g_r3), s_log (fst (fst g_r3))) = (0x3c230%Z, [], [])
  /\ (nth 1 g_sr3 (ELit 0), nth 10 g_sr3 (ELit 0), nth 2 g_sr3 (ELit 0), nth 4 g_sr3 (ELit 0))
     = (ELit 0x17934, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x56270)
  /\ kn_vars_lt 105 g_kn3 = true /\ kn_acall g_kn3 = g_knL
  /\ (sr_mismatch g_rvl idb g_srL sr_L 0, kn_missing g_knL (map (kmap g_rvl idb) kn_ML)) = ([0%nat], [KWr (SA (EVar 51) 0) 65536]).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.
