(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for libreac/fuzz_disco's ASan+UBSan build: the 50 hand-off states collected by a Theorem Labs lane's start-up collector (both arms of every mmap node; pass 2, side B) on fuzz_disco.asan-ubsan, all at main 0x80b1c, formed by hsform.py hs with no fill; KImg and descriptor-array gates PASS, codeptr.py 0 findings, the redzone shadow and the bss cells equal to YF0m in all 50; the donor checker gives COk startup_shape on them *)
(* Modified by Theorem Labs, 2026-11: the computations of this unit's Reusable/YB01r.v at CONFIG_RSEQ flag 1 (Reusable/YB01r0.v holds flag 0): the band join state and the hand-off states, collected arm by arm (Reusable/YB01rb.v), each arm's in one run of the check; the layout of plugin-hostd/fuzz_command's A/AB01r0.v and A/AB01r1.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_disco.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB12 YB1h YB1l YB05.
Import ListNotations. Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB01rb.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
