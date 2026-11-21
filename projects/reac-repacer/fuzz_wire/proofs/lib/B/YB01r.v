(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire image B (asan-ubsan) from its own collector run (pass 2: 70 leaves = 50 hand-offs all at main 0x7f758 + 18 spins + 2 merges, 0 failure leaves; log pass2.B.log, sha256 d7e2ca50de48, not in the published tree) on fuzz_wire.asan-ubsan; the donor file's form, this image's states. *)
(* Modified by Theorem Labs, 2026-11: made in place of YB01.v's recorded hand-off states and YB03.v's recorded join state for LPS 727298f3: both computed in the build from the start-up run by the certificate's own check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's fresh variables renumbered by a map read from this unit's own start-up probe; shape of libreac/fuzz_boxreg's B/AB01r.v; then split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v (the hand-off states collected arm by arm of the continuation's first case split; the hand-off states collected in one run of the check), after reac-pw/fuzz_role's copy. *)
(* The start-up run's hand-off states and its band join state, per CONFIG_RSEQ flag, computed in
   YB01r0.v and YB01r1.v from the definitions of YB01rb.v, put together here under the names
   the rest of the unit reads. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Export YB01rb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Export YB01r0 YB01r1.
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
