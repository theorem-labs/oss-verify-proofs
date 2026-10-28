(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs V2Open_defs V2Oom_defs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2DirRead_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib7Numbers7BinNums8positive02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00c5ARocqVerifyHarness?AgentSubmission2V2>V2DirRead_defs6d_srR0c5ARocqVerifyHarness?AgentSubmission2V2>V2DirRead_defs6d_srR1I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2>V2DirRead_defs5d_rR0K47Corelib7Numbers7BinNums1Z01c5ARocqVerifyHarness?AgentSubmission2V2>V2DirRead_defs5d_rR1".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS3 : list Z := (0x17a94 :: STOPS2)%Z.
Definition run3 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS3 scr ss [].

(* [comment removed for export] *)
Definition ok_sr : list expr := sr_after_call_j o_srB KEPT_AL 38.
Definition ok_kn : list kentry :=
  KRange (EVar 48) 0x77000 0x7fffff7f0000 :: KAlign (EVar 48) 16 :: KWr (SA (EVar 48) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 48) 0) 65536 :: kn_acall o_knB.

(* [comment removed for export] *)
Definition d_ssR0 : sym_state := SS 0x178bc ok_sr [] ok_kn 70.
Definition d_scrR0 : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition d_rR0 := Eval vm_compute in run3 d_scrR0 d_ssR0.
Definition d_srR0 : list expr := Eval vm_compute in s_regs (fst (fst d_rR0)).
Definition d_knR0 : list kentry := Eval vm_compute in kn_after d_rR0 ok_kn.

(* [comment removed for export] *)
Definition d_srR10 : list expr := sr_upd d_srR0 (ridx 10) (ELit (2 ^ 64 - 21)).
Definition d_ssR1 : sym_state := SS 0x43d68 d_srR10 [] d_knR0 70.
Definition d_rR1 := Eval vm_compute in run3 scr0 d_ssR1.
Definition d_srR1 : list expr := Eval vm_compute in s_regs (fst (fst d_rR1)).
Definition d_knR1 : list kentry := Eval vm_compute in kn_after d_rR1 d_knR0.

Section VP1.
Lemma d_itin :
  (s_pc (fst (fst d_rR0)), snd (fst d_rR0)) = (0x43d64%Z, [])
  /\ (nth 17 d_srR0 (ELit 0), nth 10 d_srR0 (ELit 0), nth 11 d_srR0 (ELit 0), nth 12 d_srR0 (ELit 0))
     = (ELit 63, ELit 3, ELit 0x46169, ELit 65536)
  /\ (s_pc (fst (fst d_rR1)), snd (fst d_rR1)) = (0x17a94%Z, [])
  /\ (nth 2 d_srR1 (ELit 0), nth 3 d_srR1 (ELit 0), nth 4 d_srR1 (ELit 0), nth 18 d_srR1 (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x56270, EVar 2).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.
