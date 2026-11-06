(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGbigw.v (commit 8b4ae5e9984e, the Deallocate big arm, closed at cgif; file sha256 1f8824598bb1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 10 image addresses moved by code-verified function pairs (8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 2 code pcs the tool read as sizes, by funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: then from plugin-hostd/fuzz_reply lib/A (commit 29bcc0b4b8f) to image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61) by alreloc 56664a20986eb62e, same unit A -> B. *)
(* Theorem Labs, 2026-10 (the Deallocate big-block arm): the states of the walk of a block above the quarantine's
   max_size, over the seed DGbigm.SS0. DGfw's script up to Quarantine::Put (SS_B, SS_P0), then Put's size test
   (0x35f7c `bgeu max_size, size`), which the seed's ranges decide as NOT taken (kQuarantineMax < nn): the run
   goes on into RecyclePassThrough (compiler-rt llvmorg-20.1.8 asan_allocator.cpp:255-263) and stops at FromPrimary's
   test on the chunk header (0x35f88, SS_P). Its three outcomes (below the primary space, above it, inside it) each
   reach QuarantineCallback::Recycle's entry (0x33e88) with ra = 0x35ffc: inside the primary space FillChunk is vacuous
   (flags()->max_free_fill_size = 0, the cell 0xa4028). Nothing here is a function's proof (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFeq DGbase DGgi DGfv DGbigm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGfw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* At StackDepotPut's entry: DGfw.SS_B's script, over the big seed. *)
Definition SS_B : sstate := Eval vm_compute in
(let s1 := xrun DGbigm.SS0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to 0x74364 (xpin 11 (SLit 3) s4)).
Goal ss_pc SS_B = 0x74364. Proof. reflexivity. Qed.
(* At Quarantine::Put's entry after the depot call (DGfw.SS_P's prefix). *)
Definition SS_P0 : sstate := Eval vm_compute in
(xpin 15 (SOff 39%nat 0) (xrun_to 0x35f3c (xadd DGfw.R_SCR2 (DGfw.xafterD 86 0x35e1c SS_B)))).
(* Put's size test decided as not taken; at FromPrimary's lower test (m < space beg). *)
Definition SS_P : sstate := Eval vm_compute in (xrun SS_P0).
(* the chunk below the primary space *)
Definition SS_Q1 : sstate := Eval vm_compute in (xrun (DGfw.xtake SS_P)).
(* at FromPrimary's upper test (m >= space beg + kSpaceSize) *)
Definition SS_P2 : sstate := Eval vm_compute in (xrun (DGfw.xfall SS_P)).
(* the chunk above the primary space *)
Definition SS_Q2 : sstate := Eval vm_compute in (xrun (DGfw.xtake SS_P2)).
(* the chunk inside the primary space: FillChunk's test finds max_free_fill_size = 0 *)
Definition SS_Q3 : sstate := Eval vm_compute in (xrun (DGfw.xfall SS_P2)).
Goal ss_pc SS_P0 = 0x35f3c /\ ss_pc SS_P = 0x35f88 /\ ss_pc SS_P2 = 0x35f98 /\
  ss_pc SS_Q1 = 0x33e88 /\ ss_pc SS_Q2 = 0x33e88 /\ ss_pc SS_Q3 = 0x33e88.
Proof. repeat split; reflexivity. Qed.
Goal (match sym_step_sh tfibsegs tfibtbl_rtF SS_P with SStop (SR_branch BC_LTU (SOff 10 (-16)) (SOff 34 0)) => true | _ => false end) = true.
Proof. reflexivity. Qed.
Goal (match sym_step_sh tfibsegs tfibtbl_rtF SS_P2 with SStop (SR_branch BC_GEU (SOff 10 (-16)) (SOff 34 137438953472)) => true | _ => false end) = true.
Proof. reflexivity. Qed.
(* The common state at Recycle's entry: the three outcomes differ only in a3 (x13: the stack object's address, or
   max_free_fill_size = 0 inside the primary space), which Recycle does not read; it is forgotten into the fresh atom
   102, and the facts are those of SS_P (before FromPrimary's tests). *)
Definition F_Q : facts := Eval vm_compute in ss_facts SS_P.
Definition SS_Q : sstate := Eval vm_compute in set_facts (xpin 13 (SOff 102%nat 0) SS_Q1) F_Q.
Goal set_facts (xpin 13 (SOff 102%nat 0) SS_Q2) F_Q = SS_Q /\ set_facts (xpin 13 (SOff 102%nat 0) SS_Q3) F_Q = SS_Q.
Proof. split; vm_compute; reflexivity. Qed.
Goal facts_leb F_Q (ss_facts SS_Q1) = true /\ facts_leb F_Q (ss_facts SS_Q2) = true /\ facts_leb F_Q (ss_facts SS_Q3) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
