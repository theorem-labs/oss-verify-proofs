(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdK.v (commit 67deba317dfb, blob 88432a57870b) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 3 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo DMcdGk.
Import ListNotations.
Open Scope Z_scope.
Definition runtoK (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtK FUEL pc ss).
Definition runK (ss : sstate) : sstate := fst (sym_runN_sh tfibsegs tfibtbl_rtK FUEL ss).
Definition pinK (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition addregK (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition armK (c : branch_cond) (taken : bool) (a b : sv) (ss : sstate) : sstate := add_cond ss (mkAC (if taken then c else neg_bc c) a b).
Definition K0 : sstate := Eval vm_compute in addregK R_RGA (addregK R_RGB (addregK R_RGC SS0)).
Definition K1 : sstate := Eval vm_compute in runtoK 0x34c48 K0.
Definition K2 : sstate := Eval vm_compute in pinK K1 8%bv (SOff 36%nat 0).
Definition K3 : sstate := Eval vm_compute in runK K2.
Definition K4 : sstate := Eval vm_compute in armK BC_EQ true (SOff 37%nat 0) (SOff 38%nat 0) K3.
Definition K5 : sstate := Eval vm_compute in runK K4.
Definition K6 : sstate := Eval vm_compute in armK BC_LTU false (SOff 37%nat 0) (SAlu ALU_SRL (SOff 38%nat 0) (SLit 1)) K5.
Definition K7 : sstate := Eval vm_compute in runtoK 0x351dc K6.
Definition K8 : sstate := Eval vm_compute in pinK K7 8%bv (SOff 41%nat 0).
Definition K9 : sstate := Eval vm_compute in runtoK 0x35474 K8.
