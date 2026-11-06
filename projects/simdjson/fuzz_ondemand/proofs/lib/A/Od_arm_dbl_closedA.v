(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Od_defsA Od_cpsA Od_arm_dbl_defsA Od_arm_dblA Od_arm_dbl_fheadA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem arm_dbl_evt_closed : forall E, od_oka E -> arm_dbl_evt E.
Proof. intros E OK. exact (arm_dbl_evt_of_fhead E OK (dbl_fhead E OK)). Qed.
