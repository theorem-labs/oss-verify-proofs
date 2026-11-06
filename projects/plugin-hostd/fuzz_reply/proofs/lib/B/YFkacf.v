(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkacf.v (commit f01d79f3fb5, cf refill round 3; file sha256 99335ab14aca) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 5 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (ReallocPrimary.CfW, lane W, cf refill re-base, B3 half; base a working branch on a working branch d50ec3c8a93a): YFkacf, the cf twin of YFka.v (this tree's copy, = c5 8d6c9f45705b).
   A hand port of YFka.v at commit 8d6c9f45705b (its mechanical part scripted outside the tree): imports YFkpcf / YFhmcf / YFhncf and the B3 cf twins; RI+68 is the junk
   atom rJEX = 55 of YFkpcf with value jex (0 <= jex < 2 ^ 8), so the B3 atoms are 56..69; the text is otherwise YFka.v verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, EV_BIG, mtr_ok, aregime, refill_reg, qloosem or non-cf abudget.
   rule 24: no function proved (kind: re-base of the proved refill walk onto the cf instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFhy YFhz YFkpcf YFk6cf YFk8cf YFhmcf.
Import ListNotations. Open Scope Z_scope.
Definition REG0U3 : smem := replAt 35 headc0 REG0R3.
Definition SS0U3 : sstate := mkSS 0x36a20 REGS0R REG0U3 None FR3.
Lemma REG0U3_len : length REG0U3 = 41%nat. Proof. reflexivity. Qed.
Lemma REG0R3_35 : nth_error REG0R3 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U1 : sstate := Eval vm_compute in runto 0x36a7c SS0U3.
Lemma R3_U1_35 : nth_error (ss_mem R3_U1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition R3_U2 : sstate := Eval vm_compute in mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Lemma R3_U2_eq : R3_U2 = mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Proof. vm_compute. reflexivity. Qed.
Definition R3_U3 : sstate := Eval vm_compute in runto 0x36b18 R3_U2.
Lemma R3_U3_split : ss_mem R3_U3 = firstn 41 (ss_mem R3_U3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35 : nth_error (firstn 41 (ss_mem R3_U3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_ext : map ext3 (dropAt 35 (firstn 41 (ss_mem R3_U3))) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Definition R3_U4 : sstate := Eval vm_compute in mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Lemma R3_U4_eq : R3_U4 = mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Proof. vm_compute. reflexivity. Qed.
Lemma R3_U4_mem : ss_mem R3_U4 = insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3))). Proof. vm_compute. reflexivity. Qed.
Definition R3_U5 : sstate := Eval vm_compute in runto 0x36a40 R3_U4.
Lemma R3_UJ : noconds (forget R3_U5 hJ0 CLOB_INIT) = R3_J. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_ext : map ext3 (dropAt 35 (ss_mem R3_U1)) = map ext3 (dropAt 35 REG0R3). Proof. vm_compute. reflexivity. Qed.
Lemma R3_U1_len : length (ss_mem R3_U1) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U2_mem : ss_mem R3_U2 = replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_35' : nth_error (ss_mem R3_U3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U3_len : length (firstn 41 (ss_mem R3_U3)) = 41%nat. Proof. vm_compute. reflexivity. Qed.
Lemma R3_U5_eq : runto 0x36a40 (mkSS (ss_pc R3_U3) (ss_regs R3_U3) (insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3)))) (ss_resv R3_U3) (ss_facts R3_U3)) = R3_U5.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_J_0 : exists cs, nth_error (ss_mem R3_J) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma R3_J_35 : nth_error (ss_mem R3_J) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
