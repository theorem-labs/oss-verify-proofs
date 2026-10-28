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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFhz AFkp AFk6 AFk8 AFhm.
Import ListNotations. Open Scope Z_scope.
Definition REG0U3 : smem := replAt 35 headc0 REG0R3.
Definition SS0U3 : sstate := mkSS 0x36104 REGS0R REG0U3 None FR3.
Lemma REG0U3_len : length REG0U3 = 41%nat. Proof. reflexivity. Qed.
Lemma REG0R3_35 : nth_error REG0R3 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U1 : sstate := Eval vm_compute in runto 0x36160 SS0U3.
Lemma R3_U1_35 : nth_error (ss_mem R3_U1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition R3_U2 : sstate := Eval vm_compute in mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Lemma R3_U2_eq : R3_U2 = mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U3 : sstate := Eval vm_compute in runto 0x361fc R3_U2.
Lemma R3_U3_split : ss_mem R3_U3 = firstn 41 (ss_mem R3_U3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35 : nth_error (firstn 41 (ss_mem R3_U3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_ext : map ext3 (dropAt 35 (firstn 41 (ss_mem R3_U3))) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Definition R3_U4 : sstate := Eval vm_compute in mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Lemma R3_U4_eq : R3_U4 = mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Proof. vm_compute. reflexivity. Qed.
Lemma R3_U4_mem : ss_mem R3_U4 = insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3))). Proof. vm_compute. reflexivity. Qed.
Definition R3_U5 : sstate := Eval vm_compute in runto 0x36124 R3_U4.
Lemma R3_UJ : noconds (forget R3_U5 hJ0 CLOB_INIT) = R3_J. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_ext : map ext3 (dropAt 35 (ss_mem R3_U1)) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_len : length (ss_mem R3_U1) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U2_mem : ss_mem R3_U2 = replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35' : nth_error (ss_mem R3_U3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_len : length (firstn 41 (ss_mem R3_U3)) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U5_eq : runto 0x36124 (mkSS (ss_pc R3_U3) (ss_regs R3_U3) (insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3)))) (ss_resv R3_U3) (ss_facts R3_U3)) = R3_U5.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_J_0 : exists cs, nth_error (ss_mem R3_J) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma R3_J_35 : nth_error (ss_mem R3_J) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
