(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Open_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic3and00C47Corelib5Lists7ListDef3nthI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00c5ARocqVerifyHarness?AgentSubmission2V2;V2Open_defs5o_srBI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2;V2Open_defs4o_rBK47Corelib7Numbers7BinNums1Z01".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS2 : list Z := (0x3c370 :: 0x3c230 :: 0x17d08 :: STOPS)%Z.
Definition run2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS2 scr ss [].

(* [comment removed for export] *)
Definition o_srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition o_ssB0 : sym_state := SS 0x43d68 o_srB0 [] knA 38.
Definition o_rB := Eval vm_compute in run2 scr0 o_ssB0.
Definition o_srB : list expr := Eval vm_compute in s_regs (fst (fst o_rB)).
Definition o_knB : list kentry := Eval vm_compute in kn_after o_rB knA.

Section VP1.
Lemma o_itinB :
  (s_pc (fst (fst o_rB)), snd (fst o_rB)) = (0x3c370%Z, [])
  /\ (nth 10 o_srB (ELit 0), nth 1 o_srB (ELit 0), nth 2 o_srB (ELit 0), nth 3 o_srB (ELit 0))
     = (ELit 65536, ELit 0x178bc, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.
