(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA Overlay U1StartInit_defs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1StartInit_eqs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init7Decimal4uint02K47Corelib4Init7Decimal4uint04K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib3Drv8SymExecA3SXA9sym_execAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib3Drv@U1StartInit_defs4MAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs8CXX_INITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs3sr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs3kn8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs8init_runC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Drv@U1StartInit_defs8init_scsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs7init_srC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs8init_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay8abs_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs3SLOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs3SHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs4DLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv@U1StartInit_defs9init_runsC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope. Import SX2. Import SXA.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma init_run_eq :
  sym_execA SEGS 20000 true [MAIN] (SCR [] [] []) (SS CXX_INIT sr8 [] kn8 41) [] = init_run.
Proof.
vm_compute. reflexivity. Qed.

Lemma init_run_shape :
  init_run = (fst (fst init_run), init_scs, snd init_run)
  /\ s_pc (fst (fst init_run)) = MAIN
  /\ s_regs (fst (fst init_run)) = init_sr
  /\ s_log (fst (fst init_run)) = init_log.
Proof.
split; [|split; [|split]]; vm_compute; reflexivity. Qed.

Lemma init_runs_eq : abs_runs 0 SLO SHI DLIM init_log = init_runs.
Proof.
vm_compute. reflexivity. Qed.
