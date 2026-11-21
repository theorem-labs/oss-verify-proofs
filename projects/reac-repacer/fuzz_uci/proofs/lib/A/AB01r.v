(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci's asan image from the start-up collector (tools/startup, both-arms ColA d198e5a14160) run in the donor workspace with fuzz_uci's image, relocated plan (itabranges whole .text; probe-measured tail 2 x XMemset) and table; the pass-2 collector log, sha256 70c3f021088b *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of this unit's recorded hand-off states (AB01.v) and recorded band join state (AB03.v), from libreac/fuzz_decode's A/AB01r.v (made from libreac/fuzz_boxreg's): both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the recorded plan's variables renumbered by a map read from this unit's probes; its definitions are in A/AB01rb.v and its computations in A/AB01r0.v and A/AB01r1.v, as plugin-hostd/fuzz_command's A/AB01r.v. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded (A/AB01rb.v, computed
   in A/AB01r0.v and A/AB01r1.v).  The recorded plan [AB05.startup_plan_tfib] is checked with
   its fresh variables renumbered ([vsh]) and its one [PVia] join state and floor replaced
   ([PlanRegen.pvia_set]); the recorded [AB01.HS_tfib] and [AB03.JS_tfib_band] were written
   against the released model's launch. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Export AB01rb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Export AB01r0 AB01r1.
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
