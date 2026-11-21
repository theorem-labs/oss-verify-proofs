(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states (and the pass-1 join state) are fuzz_rate.asan-ubsan's own, collected by the start-up collector (tools/startup, coq/ColA.v d198e5a14160) running the donor checker (cgif_file_fuzzer) on this image with the plan probed for it (tail XMemset*58); header and Requires from proofs/libreac/fuzz_knock/lib/AU *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states and band join state of YB01.v and YB03.v: both computed in the build from the start-up run by the certificate's own check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's variables renumbered by a map read from this unit's own probe; split per flag (definitions, flag 0, flag 1, joined) as reac-pw/fuzz_role's copy of plugin-hostd/fuzz_command's AB01rb.v, AB01r0.v, AB01r1.v and AB01r.v; internal commit ids in comments replaced by public commits or removed. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_rate.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
