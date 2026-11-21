(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's asan image from the start-up collector (tools/startup, both-arms ColA d198e5a14160) run in the donor workspace with fuzz_codec's image, relocated plan (itabranges whole .text; probe-measured tail 41 x XMemset) and table; the pass-2 collector log, sha256 f163ffd6f97b *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag (split per flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v), with Reusable/PlanRegen.v (the shape of libreac/fuzz_boxreg's A/AB01r.v; the hand-off states collected in one run of the check), the plan's variables renumbered by values read from probes of this unit's run. *)
(* The start-up run's hand-off states and its band join state, per CONFIG_RSEQ flag, computed in
   AB01r0.v and AB01r1.v from the definitions of AB01rb.v, put together here under the names
   the rest of the unit reads. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Asan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Export AB01rb.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Export AB01r0 AB01r1.
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
