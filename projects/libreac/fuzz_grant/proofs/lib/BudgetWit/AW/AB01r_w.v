(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v, with its module paths changed; all 50 hand-off states are collected from fuzz_grant.asan's start-up run (a Theorem Labs lane's tools/startup collector, pass 2, both arms of every mmap node). *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from libreac/fuzz_boxreg's A/AB01r.v, in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with the plan's variables renumbered by a map read from this unit's probes and the hand-off states collected in one run of the check; its definitions are in A/AB01rb.v and its computations in A/AB01r0.v and A/AB01r1.v, one per flag, in the layout of plugin-hostd/fuzz_command's A/AB01r.v; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from this unit's A/AB01r.v for the ASan run at the 16 GiB limit, in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with the plan's variables renumbered by a map read from this unit's probes and the hand-off states collected in one run of the check; its definitions are in BudgetWit/AW/AB01rb_w.v and its computations in BudgetWit/AW/AB01r0_w.v and BudgetWit/AW/AB01r1_w.v, one per flag, in the layout of plugin-hostd/fuzz_command's A/AB01r.v; the modules it imports from that set renamed to their twins (suffix _w); taken from projects/libreac/fuzz_grant/proofs/lib/A/AB01r.v, lines 11-16 and 20-42, as in the LPS 727298f3 update. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded (BudgetWit/AW/AB01rb_w.v, computed
   in BudgetWit/AW/AB01r0_w.v and BudgetWit/AW/AB01r1_w.v).  The recorded plan [AB05_w.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen.pvia_set]); the recorded
   [AB01_w.HS_tfib] and [AB03_w.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_grant.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0c YK09 YA01. From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB12. From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Export AB01rb_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Export AB01r0_w AB01r1_w.
Open Scope Z_scope.

Definition JS_tfib_r (r : Z) : acs := if Z.eqb r 1 then JS_1 else JS_0.
Definition startup_plan_tfib_r (r : Z) : plan := plan_r (JS_tfib_r r).
Definition HSL_r (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_1 else HSL_0.
(* The hand-offs the run reaches, and only those: a hand-off the check never reaches has no
   state. *)
Definition HS_tfib_r (r : Z) (h : nat) : option acs := hlookup (HSL_r r) h.
Definition HS_tfib_list_r (r : Z) : list acs := map snd (HSL_r r).
(* Both flags' hand-off states in one list, which the driver's computed checks run over. *)
Definition HS_tfib_list_all : list acs := HS_tfib_list_r 0 ++ HS_tfib_list_r 1.
Lemma HS_tfib_r_In : forall r h ch, HS_tfib_r r h = Some ch -> In ch HS_tfib_list_all.
Proof.
intros r h ch H. unfold HS_tfib_r, hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _].
unfold HS_tfib_list_all, HS_tfib_list_r. apply in_or_app. unfold HSL_r in F |- *.
destruct (Z.eqb r 1); [right | left]; exact (in_map snd _ _ F).
Qed.
