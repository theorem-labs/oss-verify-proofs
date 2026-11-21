(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan: every one of the 50 hand-off states is the state the plan checker's own executor reaches at that hole on fuzz_manifest.asan (the start-up collector walks both arms of every mmap node; the checker itself reaches holes 0 1 8 9 16 17 24 25 32 36), read off and printed. *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's A/AB01r.v for LPS 727298f3, with its module paths changed: the hand-off states of AB01.v and the join state of AB03.v computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the fresh-variable renumbering vsh is this unit's own; its definitions are in A/AB01rb.v and its computations in A/AB01r0.v and A/AB01r1.v, one per flag, which collect the hand-off states arm by arm, in one run of the check each (the layout of plugin-hostd/fuzz_command's A/AB01r.v). *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01r0.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w): the computations of BudgetWit/AW/AB01r_w.v at CONFIG_RSEQ flag 0 (AB01r1_w.v holds flag 1), the hand-off states collected arm by arm in one run of the check each (AB01rb_w.v); taken from projects/omx-clap-core/fuzz_manifest/proofs/lib/A/AB01r.v, lines 12-25, as in the LPS 727298f3 update. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0, at the
   16 GiB limit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import AB01rb_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
