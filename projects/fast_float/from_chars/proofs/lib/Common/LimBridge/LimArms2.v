(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable Dispatch.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv LimVp LimMm LimMremap LimArm.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma arm_83_frame : arm_frame_ok (mkSpecArm 83%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (fsync_spec (fd32 (in_arg i0 0))) (fsync_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_83_lpres : arm_lpres_ok (mkSpecArm 83%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (fsync_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_83_inv : arm_inv_ok (mkSpecArm 83%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (fsync_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_85_frame : arm_frame_ok (mkSpecArm 85%Z (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (timerfd_create_spec (clockid32 (in_arg i0 0)) (flag32 (in_arg i0 1))) (timerfd_create_spec (clockid32 (in_arg i0 0)) (flag32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_85_lpres : arm_lpres_ok (mkSpecArm 85%Z (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (timerfd_create_spec (clockid32 (in_arg i0 0)) (flag32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_85_inv : arm_inv_ok (mkSpecArm 85%Z (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (timerfd_create_spec (clockid32 (in_arg i0 0)) (flag32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_93_frame : arm_frame_ok (mkSpecArm 93%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (exit_spec (in_arg i0 0)) (exit_spec (in_arg i0 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_93_lpres : arm_lpres_ok (mkSpecArm 93%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (exit_spec (in_arg i0 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_93_inv : arm_inv_ok (mkSpecArm 93%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (exit_spec (in_arg i0 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_94_frame : arm_frame_ok (mkSpecArm 94%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (exit_spec (in_arg i0 0)) (exit_spec (in_arg i0 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_94_lpres : arm_lpres_ok (mkSpecArm 94%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (exit_spec (in_arg i0 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_94_inv : arm_inv_ok (mkSpecArm 94%Z (fun i => exit_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (exit_spec (in_arg i0 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_96_frame : arm_frame_ok (mkSpecArm 96%Z (fun i => set_tid_address_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (set_tid_address_spec) (set_tid_address_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_96_lpres : arm_lpres_ok (mkSpecArm 96%Z (fun i => set_tid_address_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (set_tid_address_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_96_inv : arm_inv_ok (mkSpecArm 96%Z (fun i => set_tid_address_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (set_tid_address_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_98_frame : arm_frame_ok (mkSpecArm 98%Z (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (futex_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (futex_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_98_lpres : arm_lpres_ok (mkSpecArm 98%Z (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (futex_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_98_inv : arm_inv_ok (mkSpecArm 98%Z (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (futex_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_101_frame : arm_frame_ok (mkSpecArm 101%Z (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (nanosleep_spec (in_arg i0 0) (in_arg i0 1)) (nanosleep_spec (in_arg i0 0) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_101_lpres : arm_lpres_ok (mkSpecArm 101%Z (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (nanosleep_spec (in_arg i0 0) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_101_inv : arm_inv_ok (mkSpecArm 101%Z (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (nanosleep_spec (in_arg i0 0) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_113_frame : arm_frame_ok (mkSpecArm 113%Z (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (clock_gettime_spec (clockid32 (in_arg i0 0)) (in_arg i0 1)) (clock_gettime_spec (clockid32 (in_arg i0 0)) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_113_lpres : arm_lpres_ok (mkSpecArm 113%Z (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (clock_gettime_spec (clockid32 (in_arg i0 0)) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_113_inv : arm_inv_ok (mkSpecArm 113%Z (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (clock_gettime_spec (clockid32 (in_arg i0 0)) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_119_frame : arm_frame_ok (mkSpecArm 119%Z (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sched_setscheduler_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2)) (sched_setscheduler_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_119_lpres : arm_lpres_ok (mkSpecArm 119%Z (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sched_setscheduler_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_119_inv : arm_inv_ok (mkSpecArm 119%Z (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sched_setscheduler_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_123_frame : arm_frame_ok (mkSpecArm 123%Z (fun i => sched_getaffinity_spec (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sched_getaffinity_spec (in_arg i0 1)) (sched_getaffinity_spec (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_123_lpres : arm_lpres_ok (mkSpecArm 123%Z (fun i => sched_getaffinity_spec (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sched_getaffinity_spec (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_123_inv : arm_inv_ok (mkSpecArm 123%Z (fun i => sched_getaffinity_spec (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sched_getaffinity_spec (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_124_frame : arm_frame_ok (mkSpecArm 124%Z (fun i => sched_yield_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sched_yield_spec) (sched_yield_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_124_lpres : arm_lpres_ok (mkSpecArm 124%Z (fun i => sched_yield_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sched_yield_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_124_inv : arm_inv_ok (mkSpecArm 124%Z (fun i => sched_yield_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sched_yield_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_130_frame : arm_frame_ok (mkSpecArm 130%Z (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (tkill_spec (pid32 (in_arg i0 0)) (sig32 (in_arg i0 1))) (tkill_spec (pid32 (in_arg i0 0)) (sig32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_130_lpres : arm_lpres_ok (mkSpecArm 130%Z (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (tkill_spec (pid32 (in_arg i0 0)) (sig32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_130_inv : arm_inv_ok (mkSpecArm 130%Z (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (tkill_spec (pid32 (in_arg i0 0)) (sig32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_131_frame : arm_frame_ok (mkSpecArm 131%Z (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (tgkill_spec (pid32 (in_arg i0 0)) (pid32 (in_arg i0 1)) (sig32 (in_arg i0 2))) (tgkill_spec (pid32 (in_arg i0 0)) (pid32 (in_arg i0 1)) (sig32 (in_arg i0 2)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_131_lpres : arm_lpres_ok (mkSpecArm 131%Z (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (tgkill_spec (pid32 (in_arg i0 0)) (pid32 (in_arg i0 1)) (sig32 (in_arg i0 2)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_131_inv : arm_inv_ok (mkSpecArm 131%Z (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (tgkill_spec (pid32 (in_arg i0 0)) (pid32 (in_arg i0 1)) (sig32 (in_arg i0 2)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_132_frame : arm_frame_ok (mkSpecArm 132%Z (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sigaltstack_spec (in_arg i0 0) (in_arg i0 1)) (sigaltstack_spec (in_arg i0 0) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_132_lpres : arm_lpres_ok (mkSpecArm 132%Z (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sigaltstack_spec (in_arg i0 0) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_132_inv : arm_inv_ok (mkSpecArm 132%Z (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sigaltstack_spec (in_arg i0 0) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_134_frame : arm_frame_ok (mkSpecArm 134%Z (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (rt_sigaction_spec (sig32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (rt_sigaction_spec (sig32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_134_lpres : arm_lpres_ok (mkSpecArm 134%Z (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (rt_sigaction_spec (sig32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_134_inv : arm_inv_ok (mkSpecArm 134%Z (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (rt_sigaction_spec (sig32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_135_frame : arm_frame_ok (mkSpecArm 135%Z (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (rt_sigprocmask_spec (how32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (rt_sigprocmask_spec (how32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_135_lpres : arm_lpres_ok (mkSpecArm 135%Z (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (rt_sigprocmask_spec (how32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_brute).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_135_inv : arm_inv_ok (mkSpecArm 135%Z (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (rt_sigprocmask_spec (how32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_144_frame : arm_frame_ok (mkSpecArm 144%Z (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0))) (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_144_lpres : arm_lpres_ok (mkSpecArm 144%Z (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_144_inv : arm_inv_ok (mkSpecArm 144%Z (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_146_frame : arm_frame_ok (mkSpecArm 146%Z (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0))) (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_146_lpres : arm_lpres_ok (mkSpecArm 146%Z (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_146_inv : arm_inv_ok (mkSpecArm 146%Z (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_147_frame : arm_frame_ok (mkSpecArm 147%Z (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2))) (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_147_lpres : arm_lpres_ok (mkSpecArm 147%Z (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_147_inv : arm_inv_ok (mkSpecArm 147%Z (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_149_frame : arm_frame_ok (mkSpecArm 149%Z (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2))) (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_149_lpres : arm_lpres_ok (mkSpecArm 149%Z (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_149_inv : arm_inv_ok (mkSpecArm 149%Z (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i0 0)) (uid32 (in_arg i0 1)) (uid32 (in_arg i0 2)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_157_frame : arm_frame_ok (mkSpecArm 157%Z (fun i => setsid_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setsid_spec) (setsid_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_157_lpres : arm_lpres_ok (mkSpecArm 157%Z (fun i => setsid_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setsid_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_157_inv : arm_inv_ok (mkSpecArm 157%Z (fun i => setsid_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setsid_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_158_frame : arm_frame_ok (mkSpecArm 158%Z (fun i => getgroups_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getgroups_spec (in_arg i0 0)) (getgroups_spec (in_arg i0 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_158_lpres : arm_lpres_ok (mkSpecArm 158%Z (fun i => getgroups_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getgroups_spec (in_arg i0 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_158_inv : arm_inv_ok (mkSpecArm 158%Z (fun i => getgroups_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getgroups_spec (in_arg i0 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_159_frame : arm_frame_ok (mkSpecArm 159%Z (fun i => setgroups_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setgroups_spec) (setgroups_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_159_lpres : arm_lpres_ok (mkSpecArm 159%Z (fun i => setgroups_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setgroups_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_159_inv : arm_inv_ok (mkSpecArm 159%Z (fun i => setgroups_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setgroups_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_160_frame : arm_frame_ok (mkSpecArm 160%Z (fun i => uname_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (uname_spec (in_arg i0 0)) (uname_spec (in_arg i0 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_160_lpres : arm_lpres_ok (mkSpecArm 160%Z (fun i => uname_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (uname_spec (in_arg i0 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_160_inv : arm_inv_ok (mkSpecArm 160%Z (fun i => uname_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (uname_spec (in_arg i0 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_167_frame : arm_frame_ok (mkSpecArm 167%Z (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (prctl_spec (int32 (in_arg i0 0)) (in_arg i0 1)) (prctl_spec (int32 (in_arg i0 0)) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_167_lpres : arm_lpres_ok (mkSpecArm 167%Z (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (prctl_spec (int32 (in_arg i0 0)) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_167_inv : arm_inv_ok (mkSpecArm 167%Z (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (prctl_spec (int32 (in_arg i0 0)) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_169_frame : arm_frame_ok (mkSpecArm 169%Z (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (gettimeofday_spec (in_arg i0 0) (in_arg i0 1)) (gettimeofday_spec (in_arg i0 0) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_169_lpres : arm_lpres_ok (mkSpecArm 169%Z (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (gettimeofday_spec (in_arg i0 0) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_169_inv : arm_inv_ok (mkSpecArm 169%Z (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (gettimeofday_spec (in_arg i0 0) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_172_frame : arm_frame_ok (mkSpecArm 172%Z (fun i => getpid_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getpid_spec) (getpid_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_172_lpres : arm_lpres_ok (mkSpecArm 172%Z (fun i => getpid_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getpid_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_172_inv : arm_inv_ok (mkSpecArm 172%Z (fun i => getpid_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getpid_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_174_frame : arm_frame_ok (mkSpecArm 174%Z (fun i => getid_spec cr_uid i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getid_spec cr_uid) (getid_spec cr_uid)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_174_lpres : arm_lpres_ok (mkSpecArm 174%Z (fun i => getid_spec cr_uid i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getid_spec cr_uid)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_174_inv : arm_inv_ok (mkSpecArm 174%Z (fun i => getid_spec cr_uid i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getid_spec cr_uid)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_175_frame : arm_frame_ok (mkSpecArm 175%Z (fun i => getid_spec cr_euid i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getid_spec cr_euid) (getid_spec cr_euid)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_175_lpres : arm_lpres_ok (mkSpecArm 175%Z (fun i => getid_spec cr_euid i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getid_spec cr_euid)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_175_inv : arm_inv_ok (mkSpecArm 175%Z (fun i => getid_spec cr_euid i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getid_spec cr_euid)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_176_frame : arm_frame_ok (mkSpecArm 176%Z (fun i => getid_spec cr_gid i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getid_spec cr_gid) (getid_spec cr_gid)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_176_lpres : arm_lpres_ok (mkSpecArm 176%Z (fun i => getid_spec cr_gid i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getid_spec cr_gid)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_176_inv : arm_inv_ok (mkSpecArm 176%Z (fun i => getid_spec cr_gid i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getid_spec cr_gid)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.
