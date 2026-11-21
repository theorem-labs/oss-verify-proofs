(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states (and the pass-1 join state) are fuzz_qdisc.asan's own, collected by port-reply's start-up collector (tools/startup, set startup-set-2026-10-29) running the donor checker on this image with the plan probed for it (tail XMemset*2); header and Requires from proofs/libreac/fuzz_knock/lib/A (h-small-a3) *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's BudgetWit/AW/AB01r_wb.v, AB01r_w0.v and AB01r_w1.v (the hand-off states collected arm by arm of the continuation's first case split), from reac-pw/fuzz_role's copy; internal commit ids in comments replaced by public commits or removed. *)
(* The start-up run's hand-off states and its band join state, per CONFIG_RSEQ flag, computed in
   AB01r_w0.v and AB01r_w1.v from the definitions of AB01r_wb.v, put together here under the names
   the rest of the unit reads. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Export AB01r_wb.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Export AB01r_w0 AB01r_w1.
Import ListNotations.
Import AX2. Import APG.
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
