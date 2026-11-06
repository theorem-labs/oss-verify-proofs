(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFka.v (that path at 25e3d17bdb50; donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan+UBSan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/B/YFka.v at 4f87de75d67 (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0f YG0d. From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YB1q YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YFhy YFhz YFkp YFk6 YFk8 YFhm.
Import ListNotations. Open Scope Z_scope.
Definition REG0U3 : smem := replAt 35 headc0 REG0R3.
Definition SS0U3 : sstate := mkSS 0x35d84 REGS0R REG0U3 None FR3.
Lemma REG0U3_len : length REG0U3 = 41%nat. Proof. reflexivity. Qed.
Lemma REG0R3_35 : nth_error REG0R3 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U1 : sstate := Eval vm_compute in runto 0x35de0 SS0U3.
Lemma R3_U1_35 : nth_error (ss_mem R3_U1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition R3_U2 : sstate := Eval vm_compute in mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Lemma R3_U2_eq : R3_U2 = mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U3 : sstate := Eval vm_compute in runto 0x35e7c R3_U2.
Lemma R3_U3_split : ss_mem R3_U3 = firstn 41 (ss_mem R3_U3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35 : nth_error (firstn 41 (ss_mem R3_U3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_ext : map ext3 (dropAt 35 (firstn 41 (ss_mem R3_U3))) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Definition R3_U4 : sstate := Eval vm_compute in mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Lemma R3_U4_eq : R3_U4 = mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Proof. vm_compute. reflexivity. Qed.
Lemma R3_U4_mem : ss_mem R3_U4 = insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3))). Proof. vm_compute. reflexivity. Qed.
Definition R3_U5 : sstate := Eval vm_compute in runto 0x35da4 R3_U4.
Lemma R3_UJ : noconds (forget R3_U5 hJ0 CLOB_INIT) = R3_J. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_ext : map ext3 (dropAt 35 (ss_mem R3_U1)) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_len : length (ss_mem R3_U1) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U2_mem : ss_mem R3_U2 = replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35' : nth_error (ss_mem R3_U3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_len : length (firstn 41 (ss_mem R3_U3)) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U5_eq : runto 0x35da4 (mkSS (ss_pc R3_U3) (ss_regs R3_U3) (insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3)))) (ss_resv R3_U3) (ss_facts R3_U3)) = R3_U5.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_J_0 : exists cs, nth_error (ss_mem R3_J) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma R3_J_35 : nth_error (ss_mem R3_J) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
