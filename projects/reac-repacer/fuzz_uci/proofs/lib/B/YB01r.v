(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci image B (asan-ubsan) from its own collector run (pass 2, provenance/startup-gen/B/logs/pass2.B.log: 220 leaves = 50 hand-offs at main 0x7ee48 + 168 spins + 2 merges, 0 failure leaves) on the pinned fuzz_uci.asan-ubsan (sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc); the donor file's form, this image's states. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of this unit's recorded hand-off states (YB01.v) and recorded band join state (YB03.v), from libreac/fuzz_decode's B/YB01r.v (made from libreac/fuzz_boxreg's B/AB01r.v): both computed in the build from the image-B start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the recorded plan's variables renumbered by a map read from this unit's probes; its definitions are in B/YB01rb.v and its computations in B/YB01r0.v and B/YB01r1.v, as plugin-hostd/fuzz_command's B/YB01r.v; internal commit ids in comments replaced by public commits or removed. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded (B/YB01rb.v, computed
   in B/YB01r0.v and B/YB01r1.v).  The recorded plan [YB05.startup_plan_tfib] is checked with
   its fresh variables renumbered ([vsh]) and its one [PVia] join state and floor replaced
   ([PlanRegen.pvia_set]); the recorded [YB01.HS_tfib] and [YB03.JS_tfib_band] were written
   against the released model's launch. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Export YB01rb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Export YB01r0 YB01r1.
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
