(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Od_defsB Od_arm_dbl_defsB Od_arm_dbl_exitB Od_arm_dblB Od_arm_dbl_fheadB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem arm_dbl_evt_closed : forall E, od_oka E -> od_shb E -> arm_dbl_evt E.
Proof. intros E OK _. exact (arm_dbl_evt_of_fhead E OK (dbl_fhead E OK)). Qed.

Theorem dbl_resume_closed : forall E, od_oka E -> od_shb E -> dbl_resume_stmt E.
Proof. intros E OK _. exact (dbl_resume E OK). Qed.
