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
Lemma arm_17_frame : arm_frame_ok (mkSpecArm 17%Z (fun i => getcwd_spec (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getcwd_spec (in_arg i0 1)) (getcwd_spec (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_17_lpres : arm_lpres_ok (mkSpecArm 17%Z (fun i => getcwd_spec (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getcwd_spec (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_17_inv : arm_inv_ok (mkSpecArm 17%Z (fun i => getcwd_spec (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getcwd_spec (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_19_frame : arm_frame_ok (mkSpecArm 19%Z (fun i => eventfd2_spec (flag32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (eventfd2_spec (flag32 (in_arg i0 1))) (eventfd2_spec (flag32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_19_lpres : arm_lpres_ok (mkSpecArm 19%Z (fun i => eventfd2_spec (flag32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (eventfd2_spec (flag32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_19_inv : arm_inv_ok (mkSpecArm 19%Z (fun i => eventfd2_spec (flag32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (eventfd2_spec (flag32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_20_frame : arm_frame_ok (mkSpecArm 20%Z (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (epoll_create1_spec (flag32 (in_arg i0 0))) (epoll_create1_spec (flag32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_20_lpres : arm_lpres_ok (mkSpecArm 20%Z (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (epoll_create1_spec (flag32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_20_inv : arm_inv_ok (mkSpecArm 20%Z (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (epoll_create1_spec (flag32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_21_frame : arm_frame_ok (mkSpecArm 21%Z (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (epoll_ctl_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (fd32 (in_arg i0 2)) (in_arg i0 3)) (epoll_ctl_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (fd32 (in_arg i0 2)) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_21_lpres : arm_lpres_ok (mkSpecArm 21%Z (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (epoll_ctl_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (fd32 (in_arg i0 2)) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_21_inv : arm_inv_ok (mkSpecArm 21%Z (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (epoll_ctl_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (fd32 (in_arg i0 2)) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_22_frame : arm_frame_ok (mkSpecArm 22%Z (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (epoll_pwait_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (int32 (in_arg i0 2)) (in_arg i0 4) (in_arg i0 5)) (epoll_pwait_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (int32 (in_arg i0 2)) (in_arg i0 4) (in_arg i0 5))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_22_lpres : arm_lpres_ok (mkSpecArm 22%Z (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (epoll_pwait_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (int32 (in_arg i0 2)) (in_arg i0 4) (in_arg i0 5))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_22_inv : arm_inv_ok (mkSpecArm 22%Z (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (epoll_pwait_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (int32 (in_arg i0 2)) (in_arg i0 4) (in_arg i0 5))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_23_frame : arm_frame_ok (mkSpecArm 23%Z (fun i => dup_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (dup_spec (fd32 (in_arg i0 0))) (dup_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_23_lpres : arm_lpres_ok (mkSpecArm 23%Z (fun i => dup_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (dup_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_23_inv : arm_inv_ok (mkSpecArm 23%Z (fun i => dup_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (dup_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_24_frame : arm_frame_ok (mkSpecArm 24%Z (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (dup3_spec (fd32 (in_arg i0 0)) (fd32 (in_arg i0 1)) (in_arg i0 2)) (dup3_spec (fd32 (in_arg i0 0)) (fd32 (in_arg i0 1)) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_24_lpres : arm_lpres_ok (mkSpecArm 24%Z (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (dup3_spec (fd32 (in_arg i0 0)) (fd32 (in_arg i0 1)) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_24_inv : arm_inv_ok (mkSpecArm 24%Z (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (dup3_spec (fd32 (in_arg i0 0)) (fd32 (in_arg i0 1)) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_25_frame : arm_frame_ok (mkSpecArm 25%Z (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (fcntl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)) (in_arg i0 2)) (fcntl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_25_lpres : arm_lpres_ok (mkSpecArm 25%Z (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (fcntl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_25_inv : arm_inv_ok (mkSpecArm 25%Z (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (fcntl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_29_frame : arm_frame_ok (mkSpecArm 29%Z (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (ioctl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1))) (ioctl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_29_lpres : arm_lpres_ok (mkSpecArm 29%Z (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (ioctl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_29_inv : arm_inv_ok (mkSpecArm 29%Z (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (ioctl_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_32_frame : arm_frame_ok (mkSpecArm 32%Z (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (flock_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1))) (flock_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_32_lpres : arm_lpres_ok (mkSpecArm 32%Z (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (flock_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_32_inv : arm_inv_ok (mkSpecArm 32%Z (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (flock_spec (fd32 (in_arg i0 0)) (cmd32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_35_frame : arm_frame_ok (mkSpecArm 35%Z (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (unlinkat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (unlinkat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_35_lpres : arm_lpres_ok (mkSpecArm 35%Z (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (unlinkat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_35_inv : arm_inv_ok (mkSpecArm 35%Z (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (unlinkat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_46_frame : arm_frame_ok (mkSpecArm 46%Z (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (ftruncate_spec (fd32 (in_arg i0 0)) (in_arg i0 1)) (ftruncate_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_46_lpres : arm_lpres_ok (mkSpecArm 46%Z (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (ftruncate_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_46_inv : arm_inv_ok (mkSpecArm 46%Z (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (ftruncate_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_48_frame : arm_frame_ok (mkSpecArm 48%Z (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (faccessat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (faccessat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_48_lpres : arm_lpres_ok (mkSpecArm 48%Z (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (faccessat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_48_inv : arm_inv_ok (mkSpecArm 48%Z (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (faccessat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_56_frame : arm_frame_ok (mkSpecArm 56%Z (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (openat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (openat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_56_lpres : arm_lpres_ok (mkSpecArm 56%Z (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (openat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_56_inv : arm_inv_ok (mkSpecArm 56%Z (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (openat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_57_frame : arm_frame_ok (mkSpecArm 57%Z (fun i => close_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (close_spec (fd32 (in_arg i0 0))) (close_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_57_lpres : arm_lpres_ok (mkSpecArm 57%Z (fun i => close_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (close_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_57_inv : arm_inv_ok (mkSpecArm 57%Z (fun i => close_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (close_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_59_frame : arm_frame_ok (mkSpecArm 59%Z (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (pipe2_spec (in_arg i0 0) (pipe_flags32 (in_arg i0 1))) (pipe2_spec (in_arg i0 0) (pipe_flags32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_59_lpres : arm_lpres_ok (mkSpecArm 59%Z (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (pipe2_spec (in_arg i0 0) (pipe_flags32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_59_inv : arm_inv_ok (mkSpecArm 59%Z (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (pipe2_spec (in_arg i0 0) (pipe_flags32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_61_frame : arm_frame_ok (mkSpecArm 61%Z (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getdents64_spec (fd32 (in_arg i0 0)) (in_arg i0 2)) (getdents64_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_61_lpres : arm_lpres_ok (mkSpecArm 61%Z (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getdents64_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_61_inv : arm_inv_ok (mkSpecArm 61%Z (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getdents64_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_62_frame : arm_frame_ok (mkSpecArm 62%Z (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (lseek_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (whence32 (in_arg i0 2))) (lseek_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (whence32 (in_arg i0 2)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_62_lpres : arm_lpres_ok (mkSpecArm 62%Z (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (lseek_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (whence32 (in_arg i0 2)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_62_inv : arm_inv_ok (mkSpecArm 62%Z (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (lseek_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (whence32 (in_arg i0 2)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_63_frame : arm_frame_ok (mkSpecArm 63%Z (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (read_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (read_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_63_lpres : arm_lpres_ok (mkSpecArm 63%Z (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (read_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_63_inv : arm_inv_ok (mkSpecArm 63%Z (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (read_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_64_frame : arm_frame_ok (mkSpecArm 64%Z (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (write_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (write_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_64_lpres : arm_lpres_ok (mkSpecArm 64%Z (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (write_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_64_inv : arm_inv_ok (mkSpecArm 64%Z (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (write_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_65_frame : arm_frame_ok (mkSpecArm 65%Z (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (readv_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (readv_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_65_lpres : arm_lpres_ok (mkSpecArm 65%Z (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (readv_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_65_inv : arm_inv_ok (mkSpecArm 65%Z (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (readv_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_66_frame : arm_frame_ok (mkSpecArm 66%Z (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (writev_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (writev_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_66_lpres : arm_lpres_ok (mkSpecArm 66%Z (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (writev_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_66_inv : arm_inv_ok (mkSpecArm 66%Z (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (writev_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_67_frame : arm_frame_ok (mkSpecArm 67%Z (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (pread64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (pread64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_67_lpres : arm_lpres_ok (mkSpecArm 67%Z (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (pread64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_67_inv : arm_inv_ok (mkSpecArm 67%Z (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (pread64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_68_frame : arm_frame_ok (mkSpecArm 68%Z (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (pwrite64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (pwrite64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_68_lpres : arm_lpres_ok (mkSpecArm 68%Z (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (pwrite64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_68_inv : arm_inv_ok (mkSpecArm 68%Z (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (pwrite64_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_72_frame : arm_frame_ok (mkSpecArm 72%Z (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (pselect6_spec (nfds32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5)) (pselect6_spec (nfds32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_72_lpres : arm_lpres_ok (mkSpecArm 72%Z (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (pselect6_spec (nfds32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_72_inv : arm_inv_ok (mkSpecArm 72%Z (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (pselect6_spec (nfds32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_73_frame : arm_frame_ok (mkSpecArm 73%Z (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (ppoll_spec (in_arg i0 0) (unfds32 (in_arg i0 1)) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4)) (ppoll_spec (in_arg i0 0) (unfds32 (in_arg i0 1)) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_73_lpres : arm_lpres_ok (mkSpecArm 73%Z (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (ppoll_spec (in_arg i0 0) (unfds32 (in_arg i0 1)) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_73_inv : arm_inv_ok (mkSpecArm 73%Z (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (ppoll_spec (in_arg i0 0) (unfds32 (in_arg i0 1)) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_78_frame : arm_frame_ok (mkSpecArm 78%Z (fun i => readlinkat_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (readlinkat_spec (fd32 (in_arg i0 0))) (readlinkat_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_78_lpres : arm_lpres_ok (mkSpecArm 78%Z (fun i => readlinkat_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (readlinkat_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_78_inv : arm_inv_ok (mkSpecArm 78%Z (fun i => readlinkat_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (readlinkat_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_79_frame : arm_frame_ok (mkSpecArm 79%Z (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (newfstatat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (flag32 (in_arg i0 3))) (newfstatat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (flag32 (in_arg i0 3)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_79_lpres : arm_lpres_ok (mkSpecArm 79%Z (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (newfstatat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (flag32 (in_arg i0 3)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_79_inv : arm_inv_ok (mkSpecArm 79%Z (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (newfstatat_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (flag32 (in_arg i0 3)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_80_frame : arm_frame_ok (mkSpecArm 80%Z (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (fstat_spec (fd32 (in_arg i0 0)) (in_arg i0 1)) (fstat_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_80_lpres : arm_lpres_ok (mkSpecArm 80%Z (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (fstat_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_80_inv : arm_inv_ok (mkSpecArm 80%Z (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (fstat_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_82_frame : arm_frame_ok (mkSpecArm 82%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (fsync_spec (fd32 (in_arg i0 0))) (fsync_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_82_lpres : arm_lpres_ok (mkSpecArm 82%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (fsync_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_82_inv : arm_inv_ok (mkSpecArm 82%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (fsync_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.
