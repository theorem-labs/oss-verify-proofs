(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMcdK.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 2b4f7d0480e7) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 11 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk): the symbolic states of the
   CacheDealloc (0x34234) GROWTH arm, computed.  [K9] is the state at EnsureFreeArraySpace's entry (0x34a94, after
   ReturnToAllocator's jal 0x348cc; ra = 0x348d0), reached from DMcdGk.SS0 exactly as the released YFgz.segK2 reaches it
   (the three region-info regions, the pins at 0x34268 / 0x347fc, the two arms: count = max at 0x34274, not
   count < max / 2 at 0x345fc).  rule 24: proves function SizeClassAllocator64LocalCache::Deallocate (states of its
   growth-arm walk); reuse: the released YFgz.segK2 walks the same prefix (its no-growth arm), and this file recomputes
   it up to the growth arm's call; `proof-index ReturnToAllocator EnsureFreeArraySpace 0x348d0 0x3476c`
   2026-10-30T01:1xZ exit 4 found no released walk of cgif's growth arm (segK2's tail from 0x348d0 is the no-growth one). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo DMcdGk.
Import ListNotations.
Open Scope Z_scope.
Definition runtoK (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtK FUEL pc ss).
Definition runK (ss : sstate) : sstate := fst (sym_runN_sh tfibsegs tfibtbl_rtK FUEL ss).
Definition pinK (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition addregK (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition armK (c : branch_cond) (taken : bool) (a b : sv) (ss : sstate) : sstate := add_cond ss (mkAC (if taken then c else neg_bc c) a b).
Definition K0 : sstate := Eval vm_compute in addregK R_RGA (addregK R_RGB (addregK R_RGC SS0)).
Definition K1 : sstate := Eval vm_compute in runtoK 0x34268 K0.
Definition K2 : sstate := Eval vm_compute in pinK K1 8%bv (SOff 36%nat 0).
Definition K3 : sstate := Eval vm_compute in runK K2.
Definition K4 : sstate := Eval vm_compute in armK BC_EQ true (SOff 37%nat 0) (SOff 38%nat 0) K3.
Definition K5 : sstate := Eval vm_compute in runK K4.
Definition K6 : sstate := Eval vm_compute in armK BC_LTU false (SOff 37%nat 0) (SAlu ALU_SRL (SOff 38%nat 0) (SLit 1)) K5.
Definition K7 : sstate := Eval vm_compute in runtoK 0x347fc K6.
Definition K8 : sstate := Eval vm_compute in pinK K7 8%bv (SOff 41%nat 0).
Definition K9 : sstate := Eval vm_compute in runtoK 0x34a94 K8.
