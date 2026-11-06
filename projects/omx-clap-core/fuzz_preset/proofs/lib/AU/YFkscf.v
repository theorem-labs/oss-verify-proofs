(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YFkscf.v (commit 4d286b2e618d, file sha256 d779d1900c8f) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 5 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkscf.v (commit f01d79f3fb5, cf refill round 3; file sha256 230986465f1a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 5 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker for a Theorem Labs lane, lane refill-b2, base d50ec3c8a93a): YFkscf, the cf
   twin of YFks.v (this tree's copy, = c5 8d6c9f45705b).  Imports the cf twins (YFkpcf, YFhmcf, ...) for their sources;
   the symbolic runs are re-run on YFkpcf's seed (RI+68 = rJEX).  Text otherwise verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, refill_reg, qloosem or non-cf abudget.  rule 24: no function proved (kind:
   re-base of the proved refill walk onto the cf instance). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhy YFhz. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFkpcf YFkrcf YFhmcf.
Import ListNotations. Open Scope Z_scope.
Definition REG0U2 : smem := replAt 35 headc0 REG0R.
Definition SS0U2 : sstate := mkSS 0x37494 REGS0R REG0U2 None FR.
Lemma REG0U2_len : length REG0U2 = 37%nat. Proof. reflexivity. Qed.
Lemma REG0R_35 : nth_error REG0R 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
Definition RU_1 : sstate := Eval vm_compute in runto 0x374f0 SS0U2.
Lemma RU_1_35 : nth_error (ss_mem RU_1) 35 = Some headc0. Proof. vm_compute. reflexivity. Qed.
Definition RU_2 : sstate := Eval vm_compute in mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Lemma RU_2_eq : RU_2 = mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Proof. vm_compute. reflexivity. Qed.
Definition RU_3 : sstate := Eval vm_compute in runto 0x3758c RU_2.
Lemma RU_3_split : ss_mem RU_3 = firstn 37 (ss_mem RU_3) ++ TBLSF. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35 : nth_error (firstn 37 (ss_mem RU_3)) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_ext : map ext3 (dropAt 35 (firstn 37 (ss_mem RU_3))) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Definition RU_4 : sstate := Eval vm_compute in mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Lemma RU_4_eq : RU_4 = mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Proof. vm_compute. reflexivity. Qed.
Lemma RU_4_mem : ss_mem RU_4 = insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3))). Proof. vm_compute. reflexivity. Qed.
Definition RU_5 : sstate := Eval vm_compute in runto 0x374b4 RU_4.
Lemma RU_J : noconds (forget RU_5 hJ0 CLOB_INIT) = RJ2. Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_ext : map ext3 (dropAt 35 (ss_mem RU_1)) = map ext3 (dropAt 35 REG0R). Proof. vm_compute. reflexivity. Qed.
Lemma RU_1_len : length (ss_mem RU_1) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_2_mem : ss_mem RU_2 = replAt 35 headcnt (ss_mem RU_1) ++ TBLS0. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_35' : nth_error (ss_mem RU_3) 35 = Some headcnt. Proof. vm_compute. reflexivity. Qed.
Lemma RU_3_len : length (firstn 37 (ss_mem RU_3)) = 37%nat. Proof. vm_compute. reflexivity. Qed.
Lemma RU_5_eq : runto 0x374b4 (mkSS (ss_pc RU_3) (ss_regs RU_3) (insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3)))) (ss_resv RU_3) (ss_facts RU_3)) = RU_5.
Proof. vm_compute. reflexivity. Qed.
Lemma RJ2_0 : exists cs, nth_error (ss_mem RJ2) 0 = Some (YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 cs). Proof. eexists. vm_compute. reflexivity. Qed.
Lemma RJ2_35 : nth_error (ss_mem RJ2) 35 = Some (YP09.mkRegion (Some rP) 0 16 0 16
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))]).
Proof. vm_compute. reflexivity. Qed.
