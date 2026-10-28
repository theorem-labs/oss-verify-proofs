(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFhz AFkp.
Import ListNotations. Open Scope Z_scope.
Definition hJ0 : nat := aHAV.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition RJ2 : sstate := Eval vm_compute in noconds (forget (runto 0x36124 SS0R) hJ0 CLOB_INIT).
Definition RS_10 : sstate := Eval vm_compute in runto 0x36128 RJ2.
Definition RS_1 : sstate := Eval vm_compute in pin RS_10 9%bv (SOff rN 0).
Definition RS_A0 : sstate := Eval vm_compute in runto 0x36284 RS_1.
Definition RS_A : sstate := Eval vm_compute in pin (pin RS_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0).
Definition RS_B : sstate := Eval vm_compute in runto 0x36358 RS_A.
Definition RS_B2 : sstate := Eval vm_compute in arm BC_LTU false (SOff rNF 0) (SOff rN 0) RS_B.
Definition RS_C0 : sstate := Eval vm_compute in runto 0x36378 RS_B2.
Definition CLOB_CP : list (bv 5) := [12; 13; 20]%bv.
Definition hCP2 : nat := 74.
Definition RS_C : sstate := Eval vm_compute in ss_after_stretch RS_C0 (ss_mem RS_C0) hCP2 CLOB_CP 0x3638c.
Definition RS_RET : sstate := Eval vm_compute in runto 0x7ffffff0 RS_C.
Lemma segr_stops :
ss_pc RS_10 = 0x36128 /\ sr_get (ss_regs RS_10) 9%bv = SAluw ALU_SRL (SOff rMAX 0) (SLit 1) /\
ss_pc RS_A0 = 0x36284 /\
sr_get (ss_regs RS_A0) 8%bv = SAlu ALU_ADD (SOff rSB 137438953472) (SAlu ALU_SLL (SOff rCL 0) (SLit 7)) /\
sr_get (ss_regs RS_A0) 20%bv = SAlu ALU_ADD (SOff rSB 3758096384) (SAlu ALU_SLL (SOff rCL 0) (SLit 32)) /\
sr_get (ss_regs RS_A0) 14%bv = SOff rN 0 /\
ss_pc RS_B = 0x36358 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 RS_A) = RS_stopped (SR_branch BC_LTU (SOff rNF 0) (SOff rN 0)) /\
ss_pc RS_C0 = 0x36378 /\
sr_get (ss_regs RS_C0) 20%bv = SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rN 0) (SLit 18446744073709551612)) (SOff rFA 0)) (SAlu ALU_SLL (SOff rNF 0) (SLit 2)) /\
sr_get (ss_regs RS_C0) 13%bv = SOff rP 16 /\
sr_get (ss_regs RS_C0) 11%bv = SAlu ALU_ADD (SOff rP 16) (SAlu ALU_SLL (SOff rN 0) (SLit 2)) /\
ss_pc RS_RET = 0x3615c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 RS_C) = RS_stopped (SR_jalr (SOff 1 0)) /\
sr_get (ss_regs RS_RET) 10%bv = SLit 1 /\ sr_get (ss_regs RS_RET) 1%bv = SOff 1 0 /\ sr_get (ss_regs RS_RET) 2%bv = SOff 2 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
