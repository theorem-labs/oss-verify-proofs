(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states are collector pass 2's own (coq/ColA.v d198e5a14160 through colrun 59778df6f00b, HSDUMP of ZStartColL/Pass2.vo on reac-pw/fuzz_link's asan image with the plan lib/A/AB05.v and its measured tail of 44 XMemset pairs: 220 leaves, 0 failure leaves, every hole walked), formed by hsform.py eb5d13059ca8 of the start-up tool set (sha256 c99b47f502d4; internal record); nothing is filled *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v (the shape of libreac/fuzz_boxreg's A/AB01r.v, through reac-pw/fuzz_role's A/AB01r.v); the plan's variable renumbering read from this unit's start-up probe. The computation is split per CONFIG_RSEQ flag (AB01rb: the definitions; AB01r0, AB01r1: one flag each, compiled in parallel; AB01r: both, under the names the unit reads), as reac-pw/fuzz_role's working copy took it from plugin-hostd/fuzz_command. *)
(* The start-up run's hand-off states and its band join state, per CONFIG_RSEQ flag, computed in
   AB01r0.v and AB01r1.v from the definitions of AB01rb.v, put together here under the names
   the rest of the unit reads. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Export AB01rb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Export AB01r0 AB01r1.
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
