(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFks.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AFks.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFks.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFks.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YB1q YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import YFhy YFhz YFkp YFkr YFhm.
Import ListNotations. Open Scope Z_scope.
Definition REG0U2 : smem := replAt 35 headc0 REG0R.
Definition SS0U2 : sstate := mkSS 0x35814 REGS0R REG0U2 None FR.
Lemma REG0U2_len : length REG0U2 = 37%nat. Proof. reflexivity. Qed.
Lemma REG0R_35 : nth_error REG0R 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition RU_1 : sstate := Eval vm_compute in runto 0x35870 SS0U2.
Lemma RU_1_35 : nth_error (ss_mem RU_1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition RU_2 : sstate := Eval vm_compute in mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Lemma RU_2_eq : RU_2 = mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Proof. vm_compute. reflexivity. Qed.
Definition RU_3 : sstate := Eval vm_compute in runto 0x3590c RU_2.
Lemma RU_3_split : ss_mem RU_3 = firstn 37 (ss_mem RU_3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35 : nth_error (firstn 37 (ss_mem RU_3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_ext : map ext3 (dropAt 35 (firstn 37 (ss_mem RU_3))) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Definition RU_4 : sstate := Eval vm_compute in mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Lemma RU_4_eq : RU_4 = mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Proof. vm_compute. reflexivity. Qed.
Lemma RU_4_mem : ss_mem RU_4 = insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3))). Proof. vm_compute. reflexivity. Qed.
Definition RU_5 : sstate := Eval vm_compute in runto 0x35834 RU_4.
Lemma RU_J : noconds (forget RU_5 hJ0 CLOB_INIT) = RJ2. Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_ext : map ext3 (dropAt 35 (ss_mem RU_1)) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_len : length (ss_mem RU_1) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_2_mem : ss_mem RU_2 = replAt 35 headcnt (ss_mem RU_1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35' : nth_error (ss_mem RU_3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_len : length (firstn 37 (ss_mem RU_3)) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_5_eq : runto 0x35834 (mkSS (ss_pc RU_3) (ss_regs RU_3) (insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3)))) (ss_resv RU_3) (ss_facts RU_3)) = RU_5.
Proof. vm_compute. reflexivity. Qed.
Lemma RJ2_0 : exists cs, nth_error (ss_mem RJ2) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma RJ2_35 : nth_error (ss_mem RJ2) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
