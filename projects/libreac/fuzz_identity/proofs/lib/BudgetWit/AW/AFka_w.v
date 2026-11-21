(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFka.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFka.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFhz_w AFkp_w AFk6_w AFk8_w AFhm_w.
Import ListNotations. Open Scope Z_scope.
Definition REG0U3 : smem := replAt 35 headc0 REG0R3.
Definition SS0U3 : sstate := mkSS 0x367e0 REGS0R REG0U3 None FR3.
Definition R3_U1 : sstate := Eval vm_compute in runto 0x3683c SS0U3.
Lemma R3_U1_35 : nth_error (ss_mem R3_U1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition R3_U2 : sstate := Eval vm_compute in mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Lemma R3_U2_eq : R3_U2 = mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U3 : sstate := Eval vm_compute in runto 0x368d8 R3_U2.
Lemma R3_U3_split : ss_mem R3_U3 = firstn 41 (ss_mem R3_U3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_ext : map ext3 (dropAt 35 (firstn 41 (ss_mem R3_U3))) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Definition R3_U4 : sstate := Eval vm_compute in mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Lemma R3_U4_eq : R3_U4 = mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Proof. vm_compute. reflexivity. Qed.
Lemma R3_U4_mem : ss_mem R3_U4 = insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3))). Proof. vm_compute. reflexivity. Qed.
Definition R3_U5 : sstate := Eval vm_compute in runto 0x36800 R3_U4.
Lemma R3_UJ : noconds (forget R3_U5 hJ0 CLOB_INIT) = R3_J. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_ext : map ext3 (dropAt 35 (ss_mem R3_U1)) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_len : length (ss_mem R3_U1) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35' : nth_error (ss_mem R3_U3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_len : length (firstn 41 (ss_mem R3_U3)) = 41%nat. Proof. vm_compute. reflexivity. Qed.
