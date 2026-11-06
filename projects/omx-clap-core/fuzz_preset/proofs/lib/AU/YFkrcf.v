(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YFkrcf.v (commit 4d286b2e618d, file sha256 3a4d376eb1f9) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 11 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkrcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 675930f74e92) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 11 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 4 code pcs the tool read as sizes, by the pair); 3 hand maps (the internal file resolve-run-f01d79f3fb5.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker for a Theorem Labs lane, lane refill-b2, base d50ec3c8a93a): YFkrcf, the cf
   twin of YFkr.v (this tree's copy, = c5 8d6c9f45705b).  Imports the cf twins (YFkpcf, YFhmcf, ...) for their sources;
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhy YFhz. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFkpcf.
Import ListNotations. Open Scope Z_scope.
Definition hJ0 : nat := aHAV.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition RJ2 : sstate := Eval vm_compute in noconds (forget (runto 0x374b4 SS0R) hJ0 CLOB_INIT).
Definition RS_10 : sstate := Eval vm_compute in runto 0x374b8 RJ2.
Definition RS_1 : sstate := Eval vm_compute in pin RS_10 9%bv (SOff rN 0).
Definition RS_A0 : sstate := Eval vm_compute in runto 0x37614 RS_1.
Definition RS_A : sstate := Eval vm_compute in pin (pin RS_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0).
Definition RS_B : sstate := Eval vm_compute in runto 0x376e8 RS_A.
Definition RS_B2 : sstate := Eval vm_compute in arm BC_LTU false (SOff rNF 0) (SOff rN 0) RS_B.
Definition RS_C0 : sstate := Eval vm_compute in runto 0x37708 RS_B2.
Definition CLOB_CP : list (bv 5) := [12; 13; 20]%bv.
Definition hCP2 : nat := 74.
Definition RS_C : sstate := Eval vm_compute in ss_after_stretch RS_C0 (ss_mem RS_C0) hCP2 CLOB_CP 0x3771c.
Definition RS_RET : sstate := Eval vm_compute in runto 0x7ffffff0 RS_C.
Lemma segr_stops :
ss_pc RS_10 = 0x374b8 /\ sr_get (ss_regs RS_10) 9%bv = SAluw ALU_SRL (SOff rMAX 0) (SLit 1) /\
ss_pc RS_A0 = 0x37614 /\
sr_get (ss_regs RS_A0) 8%bv = SAlu ALU_ADD (SOff rSB 137438953472) (SAlu ALU_SLL (SOff rCL 0) (SLit 7)) /\
sr_get (ss_regs RS_A0) 20%bv = SAlu ALU_ADD (SOff rSB 3758096384) (SAlu ALU_SLL (SOff rCL 0) (SLit 32)) /\
sr_get (ss_regs RS_A0) 14%bv = SOff rN 0 /\
ss_pc RS_B = 0x376e8 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 RS_A) = RS_stopped (SR_branch BC_LTU (SOff rNF 0) (SOff rN 0)) /\
ss_pc RS_C0 = 0x37708 /\
sr_get (ss_regs RS_C0) 20%bv = SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff rN 0) (SLit 18446744073709551612)) (SOff rFA 0)) (SAlu ALU_SLL (SOff rNF 0) (SLit 2)) /\
sr_get (ss_regs RS_C0) 13%bv = SOff rP 16 /\
sr_get (ss_regs RS_C0) 11%bv = SAlu ALU_ADD (SOff rP 16) (SAlu ALU_SLL (SOff rN 0) (SLit 2)) /\
ss_pc RS_RET = 0x374ec /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 RS_C) = RS_stopped (SR_jalr (SOff 1 0)) /\
sr_get (ss_regs RS_RET) 10%bv = SLit 1 /\ sr_get (ss_regs RS_RET) 1%bv = SOff 1 0 /\ sr_get (ss_regs RS_RET) 2%bv = SOff 2 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
