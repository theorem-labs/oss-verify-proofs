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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFhz AFkp AFkr AFhm.
Import ListNotations. Open Scope Z_scope.
Definition REG0U2 : smem := replAt 35 headc0 REG0R.
Definition SS0U2 : sstate := mkSS 0x36104 REGS0R REG0U2 None FR.
Lemma REG0U2_len : length REG0U2 = 37%nat. Proof. reflexivity. Qed.
Lemma REG0R_35 : nth_error REG0R 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition RU_1 : sstate := Eval vm_compute in runto 0x36160 SS0U2.
Lemma RU_1_35 : nth_error (ss_mem RU_1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition RU_2 : sstate := Eval vm_compute in mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Lemma RU_2_eq : RU_2 = mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Proof. vm_compute. reflexivity. Qed.
Definition RU_3 : sstate := Eval vm_compute in runto 0x361fc RU_2.
Lemma RU_3_split : ss_mem RU_3 = firstn 37 (ss_mem RU_3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35 : nth_error (firstn 37 (ss_mem RU_3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_ext : map ext3 (dropAt 35 (firstn 37 (ss_mem RU_3))) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Definition RU_4 : sstate := Eval vm_compute in mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Lemma RU_4_eq : RU_4 = mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Proof. vm_compute. reflexivity. Qed.
Lemma RU_4_mem : ss_mem RU_4 = insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3))). Proof. vm_compute. reflexivity. Qed.
Definition RU_5 : sstate := Eval vm_compute in runto 0x36124 RU_4.
Lemma RU_J : noconds (forget RU_5 hJ0 CLOB_INIT) = RJ2. Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_ext : map ext3 (dropAt 35 (ss_mem RU_1)) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_len : length (ss_mem RU_1) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_2_mem : ss_mem RU_2 = replAt 35 headcnt (ss_mem RU_1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35' : nth_error (ss_mem RU_3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_len : length (firstn 37 (ss_mem RU_3)) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_5_eq : runto 0x36124 (mkSS (ss_pc RU_3) (ss_regs RU_3) (insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3)))) (ss_resv RU_3) (ss_facts RU_3)) = RU_5.
Proof. vm_compute. reflexivity. Qed.
Lemma RJ2_0 : exists cs, nth_error (ss_mem RJ2) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma RJ2_35 : nth_error (ss_mem RJ2) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
