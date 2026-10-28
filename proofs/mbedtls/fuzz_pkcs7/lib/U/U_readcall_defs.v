(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SpecConsts SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entry.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_readcall_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS_RC : list Z := [0x1d334; 0x1d348]%Z.
Definition FUEL_RC : nat := 200.
Definition scr0 : scripts := SCR [] [] [].
Definition runRC (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL_RC true STOPS_RC scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition sr_RD : list expr := ltac2:(CDefT.buildp (gd_tbl_P_readcall_defs ()) "(0.$1.(2.=)(0.$1.(2.+1=334.)(0.$1.(3.$4.(5.#0.)(2.-80.))(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(5.#8.)(0.$1.(5.#9.)(0.$1.(5.#:.)(0.$1.(5.#;.)(0.$1.(5.#<.)(0.$1.(2.+3.)(0.$1.(5.#1.)(0.$1.(5.#2.)(0.$1.(5.#10.)(0.$1.(5.#11.)(0.$1.(5.#12.)(0.$1.(5.#13.)(0.$1.(5.#14.)(0.$1.(5.#15.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#1>.)(0.$1.(5.#1?.)(0.$1.(5.#20.)(0.$1.(5.#21.)(0.$1.(5.#22.)(6.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition kn_RD : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_readcall_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(6.$7.))))")
(* [comment removed for export] *).
Definition rdA := Eval vm_compute in runRC scr0 (SS 0x4731c sr_RD [] kn_RD 35).
Definition srRDA : list expr := Eval vm_compute in s_regs (fst (fst rdA)).
Definition logRDA : list sentry := Eval vm_compute in s_log (fst (fst rdA)).
(* [comment removed for export] *)
Definition srRDB0 : list expr := sr_upd srRDA (ridx 10) (EVar 35).
Definition kn_RDB : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_readcall_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(<.(;.(5.#0.)-88.)#8.(2.+1=334.))(0.$7.(9.(5.#23.)=+10000.)(6.$7.)))))")
(* [comment removed for export] *).
Definition rdB := Eval vm_compute in runRC scr0 (SS 0x4729c srRDB0 [] kn_RDB 36).
Definition srRDB : list expr := Eval vm_compute in s_regs (fst (fst rdB)).
Definition logRDB : list sentry := Eval vm_compute in s_log (fst (fst rdB)).

(* [comment removed for export] *)
Definition sr_CL : list expr := ltac2:(CDefT.buildp (gd_tbl_P_readcall_defs ()) "(0.$1.(2.=)(0.$1.(2.+1=348.)(0.$1.(3.$4.(5.#0.)(2.-80.))(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(5.#6.)(0.$1.(5.#7.)(0.$1.(5.#8.)(0.$1.(5.#9.)(0.$1.(5.#:.)(0.$1.(2.+3.)(0.$1.(5.#<.)(0.$1.(5.#=.)(0.$1.(5.#>.)(0.$1.(5.#?.)(0.$1.(5.#10.)(0.$1.(5.#11.)(0.$1.(5.#12.)(0.$1.(5.#13.)(0.$1.(5.#14.)(0.$1.(5.#15.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#1>.)(0.$1.(5.#1?.)(0.$1.(5.#20.)(6.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition clA := Eval vm_compute in runRC scr0 (SS 0x472bc sr_CL [] kn_RD 33).
Definition srCLA : list expr := Eval vm_compute in s_regs (fst (fst clA)).
Definition logCLA : list sentry := Eval vm_compute in s_log (fst (fst clA)).
Definition knCLA : list kentry := Eval vm_compute in kn_after clA kn_RD.
Definition srCLB0 : list expr := sr_upd srCLA (ridx 10) (ELit 0).
Definition clB := Eval vm_compute in runRC scr0 (SS (s_pc (fst (fst clA)) + 4) srCLB0 [] knCLA 33).
Definition srCLB : list expr := Eval vm_compute in s_regs (fst (fst clB)).
Definition logCLB : list sentry := Eval vm_compute in s_log (fst (fst clB)).

(* [comment removed for export] *)
Definition srRDD0 : list expr := sr_upd srRDA (ridx 10) (ELit (2 ^ 64 - 21)).
Definition kn_RDD : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_readcall_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(<.(;.(5.#0.)-88.)#8.(2.+1=334.))(0.$7.(:.(;.(2.=)+4<000.)+32000.)(6.$7.))))))")
(* [comment removed for export] *).
Definition rdD := Eval vm_compute in runRC scr0 (SS 0x4729c srRDD0 [] kn_RDD 35).
Definition srRDD : list expr := Eval vm_compute in s_regs (fst (fst rdD)).
Definition logRDD : list sentry := Eval vm_compute in s_log (fst (fst rdD)).
