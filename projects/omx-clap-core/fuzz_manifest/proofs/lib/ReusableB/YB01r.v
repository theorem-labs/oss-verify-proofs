(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB01.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan-ubsan: the 50 hand-off states of a Theorem Labs lane's collector pass 2 on this image (both mmap arms, no fill) *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's B/AB01r.v for LPS 727298f3, with its module paths changed: the hand-off states of YB01.v and the join state of YB03.v computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the fresh-variable renumbering vsh is this unit's own; its definitions are in ReusableB/YB01rb.v and its computations in ReusableB/YB01r0.v and YB01r1.v, one per flag, which collect the hand-off states arm by arm, in one run of the check each (the layout of plugin-hostd/fuzz_command's B/YB01r.v). *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded (ReusableB/YB01rb.v,
   computed in ReusableB/YB01r0.v and YB01r1.v).  The recorded plan [YB05.startup_plan_tfib]
   is checked with its fresh variables renumbered ([vsh]) and its one [PVia] join state and
   floor replaced ([PlanRegen.pvia_set]); the recorded [YB01.HS_tfib] and [YB03.JS_tfib_band]
   were written against the released model's launch. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Export YB01rb.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Export YB01r0 YB01r1.
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
