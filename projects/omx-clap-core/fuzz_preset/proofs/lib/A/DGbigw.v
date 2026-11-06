(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DGbigw.v (commit eb934de95d13, blob 214bd208cc7d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 10 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeq DGbase DGgi DGfv DGbigm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGfw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition SS_B : sstate := Eval vm_compute in
(let s1 := xrun DGbigm.SS0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to 0x73600 (xpin 11 (SLit 3) s4)).
Goal ss_pc SS_B = 0x73600. Proof. reflexivity. Qed.

Definition SS_P0 : sstate := Eval vm_compute in
(xpin 15 (SOff 39%nat 0) (xrun_to 0x368c4 (xadd DGfw.R_SCR2 (DGfw.xafterD 86 0x367a4 SS_B)))).

Definition SS_P : sstate := Eval vm_compute in (xrun SS_P0).

Definition SS_Q1 : sstate := Eval vm_compute in (xrun (DGfw.xtake SS_P)).

Definition SS_P2 : sstate := Eval vm_compute in (xrun (DGfw.xfall SS_P)).

Definition SS_Q2 : sstate := Eval vm_compute in (xrun (DGfw.xtake SS_P2)).

Definition SS_Q3 : sstate := Eval vm_compute in (xrun (DGfw.xfall SS_P2)).
Goal ss_pc SS_P0 = 0x368c4 /\ ss_pc SS_P = 0x36910 /\ ss_pc SS_P2 = 0x36920 /\
  ss_pc SS_Q1 = 0x34810 /\ ss_pc SS_Q2 = 0x34810 /\ ss_pc SS_Q3 = 0x34810.
Proof. repeat split; reflexivity. Qed.
Goal (match sym_step_sh tfibsegs tfibtbl_rtF SS_P with SStop (SR_branch BC_LTU (SOff 10 (-16)) (SOff 34 0)) => true | _ => false end) = true.
Proof. reflexivity. Qed.
Goal (match sym_step_sh tfibsegs tfibtbl_rtF SS_P2 with SStop (SR_branch BC_GEU (SOff 10 (-16)) (SOff 34 137438953472)) => true | _ => false end) = true.
Proof. reflexivity. Qed.

Definition F_Q : facts := Eval vm_compute in ss_facts SS_P.
Definition SS_Q : sstate := Eval vm_compute in set_facts (xpin 13 (SOff 102%nat 0) SS_Q1) F_Q.
Goal set_facts (xpin 13 (SOff 102%nat 0) SS_Q2) F_Q = SS_Q /\ set_facts (xpin 13 (SOff 102%nat 0) SS_Q3) F_Q = SS_Q.
Proof. split; vm_compute; reflexivity. Qed.
Goal facts_leb F_Q (ss_facts SS_Q1) = true /\ facts_leb F_Q (ss_facts SS_Q2) = true /\ facts_leb F_Q (ss_facts SS_Q3) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
