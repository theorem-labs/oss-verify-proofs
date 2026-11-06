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
Lemma arm_177_frame : arm_frame_ok (mkSpecArm 177%Z (fun i => getid_spec cr_egid i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getid_spec cr_egid) (getid_spec cr_egid)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_177_lpres : arm_lpres_ok (mkSpecArm 177%Z (fun i => getid_spec cr_egid i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getid_spec cr_egid)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_177_inv : arm_inv_ok (mkSpecArm 177%Z (fun i => getid_spec cr_egid i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getid_spec cr_egid)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_178_frame : arm_frame_ok (mkSpecArm 178%Z (fun i => gettid_spec i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (gettid_spec) (gettid_spec)) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_178_lpres : arm_lpres_ok (mkSpecArm 178%Z (fun i => gettid_spec i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (gettid_spec)) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_178_inv : arm_inv_ok (mkSpecArm 178%Z (fun i => gettid_spec i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (gettid_spec)) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_198_frame : arm_frame_ok (mkSpecArm 198%Z (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (socket_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2)) (socket_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_198_lpres : arm_lpres_ok (mkSpecArm 198%Z (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (socket_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_198_inv : arm_inv_ok (mkSpecArm 198%Z (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (socket_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_199_frame : arm_frame_ok (mkSpecArm 199%Z (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (socketpair_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (socketpair_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_199_lpres : arm_lpres_ok (mkSpecArm 199%Z (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (socketpair_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_199_inv : arm_inv_ok (mkSpecArm 199%Z (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (socketpair_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_200_frame : arm_frame_ok (mkSpecArm 200%Z (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (bind_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (bind_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_200_lpres : arm_lpres_ok (mkSpecArm 200%Z (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (bind_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_200_inv : arm_inv_ok (mkSpecArm 200%Z (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (bind_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_201_frame : arm_frame_ok (mkSpecArm 201%Z (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (listen_spec (fd32 (in_arg i0 0)) (in_arg i0 1)) (listen_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_201_lpres : arm_lpres_ok (mkSpecArm 201%Z (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (listen_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_201_inv : arm_inv_ok (mkSpecArm 201%Z (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (listen_spec (fd32 (in_arg i0 0)) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_202_frame : arm_frame_ok (mkSpecArm 202%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (Z_to_bv 64 0)) (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (Z_to_bv 64 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_202_lpres : arm_lpres_ok (mkSpecArm 202%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (Z_to_bv 64 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_202_inv : arm_inv_ok (mkSpecArm 202%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (Z_to_bv 64 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_203_frame : arm_frame_ok (mkSpecArm 203%Z (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (connect_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (connect_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_203_lpres : arm_lpres_ok (mkSpecArm 203%Z (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (connect_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_203_inv : arm_inv_ok (mkSpecArm 203%Z (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (connect_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_204_frame : arm_frame_ok (mkSpecArm 204%Z (fun i => getsockname_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getsockname_spec (fd32 (in_arg i0 0))) (getsockname_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_204_lpres : arm_lpres_ok (mkSpecArm 204%Z (fun i => getsockname_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getsockname_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_204_inv : arm_inv_ok (mkSpecArm 204%Z (fun i => getsockname_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getsockname_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_205_frame : arm_frame_ok (mkSpecArm 205%Z (fun i => getpeername_spec (fd32 (in_arg i 0)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getpeername_spec (fd32 (in_arg i0 0))) (getpeername_spec (fd32 (in_arg i0 0)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_205_lpres : arm_lpres_ok (mkSpecArm 205%Z (fun i => getpeername_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getpeername_spec (fd32 (in_arg i0 0)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_205_inv : arm_inv_ok (mkSpecArm 205%Z (fun i => getpeername_spec (fd32 (in_arg i 0)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getpeername_spec (fd32 (in_arg i0 0)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_206_frame : arm_frame_ok (mkSpecArm 206%Z (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sendto_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5)) (sendto_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_206_lpres : arm_lpres_ok (mkSpecArm 206%Z (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sendto_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_206_inv : arm_inv_ok (mkSpecArm 206%Z (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sendto_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_207_frame : arm_frame_ok (mkSpecArm 207%Z (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (recvfrom_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (recvfrom_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_207_lpres : arm_lpres_ok (mkSpecArm 207%Z (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (recvfrom_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_207_inv : arm_inv_ok (mkSpecArm 207%Z (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (recvfrom_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_208_frame : arm_frame_ok (mkSpecArm 208%Z (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (setsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (int32 (in_arg i0 4))) (setsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (int32 (in_arg i0 4)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_208_lpres : arm_lpres_ok (mkSpecArm 208%Z (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (setsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (int32 (in_arg i0 4)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_208_inv : arm_inv_ok (mkSpecArm 208%Z (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (setsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (int32 (in_arg i0 4)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_209_frame : arm_frame_ok (mkSpecArm 209%Z (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (in_arg i0 4)) (getsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (in_arg i0 4))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_209_lpres : arm_lpres_ok (mkSpecArm 209%Z (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (in_arg i0 4))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_209_inv : arm_inv_ok (mkSpecArm 209%Z (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getsockopt_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)) (in_arg i0 4))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_210_frame : arm_frame_ok (mkSpecArm 210%Z (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (shutdown_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1))) (shutdown_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_210_lpres : arm_lpres_ok (mkSpecArm 210%Z (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (shutdown_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_210_inv : arm_inv_ok (mkSpecArm 210%Z (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (shutdown_spec (fd32 (in_arg i0 0)) (int32 (in_arg i0 1)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_211_frame : arm_frame_ok (mkSpecArm 211%Z (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (sendmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2)) (sendmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_211_lpres : arm_lpres_ok (mkSpecArm 211%Z (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (sendmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_211_inv : arm_inv_ok (mkSpecArm 211%Z (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (sendmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_212_frame : arm_frame_ok (mkSpecArm 212%Z (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (recvmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 2)) (recvmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_212_lpres : arm_lpres_ok (mkSpecArm 212%Z (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (recvmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_212_inv : arm_inv_ok (mkSpecArm 212%Z (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (recvmsg_spec (fd32 (in_arg i0 0)) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_214_frame : arm_frame_ok (mkSpecArm 214%Z (fun i => brk_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o Hno HI H G0 G1. cbn [sa_spec sa_no] in *.
  rewrite (gate_214 i0 (m_relim L m) Hno) in G1. exact (brk_frame L _ i0 m o H G1).
Qed.
Lemma arm_214_lpres : arm_lpres_ok (mkSpecArm 214%Z (fun i => brk_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (brk_spec (in_arg i0 0))) by (apply brk_lpres).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_214_inv : arm_inv_ok (mkSpecArm 214%Z (fun i => brk_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  exact (brk_inv _ i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_215_frame : arm_frame_ok (mkSpecArm 215%Z (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (munmap_spec (in_arg i0 0) (in_arg i0 1)) (munmap_spec (in_arg i0 0) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_215_lpres : arm_lpres_ok (mkSpecArm 215%Z (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (munmap_spec (in_arg i0 0) (in_arg i0 1))) by (lpres_brute).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_215_inv : arm_inv_ok (mkSpecArm 215%Z (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  exact (munmap_inv _ _ i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_216_frame : arm_frame_ok (mkSpecArm 216%Z (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o Hno HI H G0 G1. cbn [sa_spec sa_no] in *.
  rewrite (gate_216 i0 m Hno) in G0. rewrite (gate_216 i0 (m_relim L m) Hno) in G1. exact (mremap_frame L _ _ _ _ i0 m o H HI G0 G1).
Qed.
Lemma arm_216_lpres : arm_lpres_ok (mkSpecArm 216%Z (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (mremap_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (apply mremap_lpres).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_216_inv : arm_inv_ok (mkSpecArm 216%Z (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  exact (mremap_inv _ _ _ _ i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_220_frame : arm_frame_ok (mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (clone_spec (in_arg i0 0)) (clone_spec (in_arg i0 0))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_220_lpres : arm_lpres_ok (mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (clone_spec (in_arg i0 0))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_220_inv : arm_inv_ok (mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (clone_spec (in_arg i0 0))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_222_frame : arm_frame_ok (mkSpecArm 222%Z (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  intros L i0 m o Hno HI H G0 G1. cbn [sa_spec sa_no] in *.
  rewrite (gate_222 i0 m Hno) in G0. rewrite (gate_222 i0 (m_relim L m) Hno) in G1. exact (mmap_frame L _ _ _ _ _ _ i0 m o H G0 G1).
Qed.
Lemma arm_222_lpres : arm_lpres_ok (mkSpecArm 222%Z (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (mmap_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3) (in_arg i0 4) (in_arg i0 5))) by (apply mmap_lpres).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_222_inv : arm_inv_ok (mkSpecArm 222%Z (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  exact (mmap_inv _ _ _ _ _ _ i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_226_frame : arm_frame_ok (mkSpecArm 226%Z (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o Hno HI H G0 G1. cbn [sa_spec sa_no] in *.
  rewrite (gate_226 i0 (m_relim L m) Hno) in G1. exact (mprotect_frame L _ _ _ i0 m o H G1).
Qed.
Lemma arm_226_lpres : arm_lpres_ok (mkSpecArm 226%Z (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (mprotect_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (apply mprotect_lpres).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_226_inv : arm_inv_ok (mkSpecArm 226%Z (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  exact (mprotect_inv _ _ _ i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_233_frame : arm_frame_ok (mkSpecArm 233%Z (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (madvise_spec (in_arg i0 0) (in_arg i0 1) (int32 (in_arg i0 2))) (madvise_spec (in_arg i0 0) (in_arg i0 1) (int32 (in_arg i0 2)))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_233_lpres : arm_lpres_ok (mkSpecArm 233%Z (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (madvise_spec (in_arg i0 0) (in_arg i0 1) (int32 (in_arg i0 2)))) by (lpres_brute).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_233_inv : arm_inv_ok (mkSpecArm 233%Z (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (madvise_spec (in_arg i0 0) (in_arg i0 1) (int32 (in_arg i0 2)))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_242_frame : arm_frame_ok (mkSpecArm 242%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_242_lpres : arm_lpres_ok (mkSpecArm 242%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_242_inv : arm_inv_ok (mkSpecArm 242%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (accept4_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_260_frame : arm_frame_ok (mkSpecArm 260%Z (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (wait4_spec (pid32 (in_arg i0 0)) (in_arg i0 1) (waitopts32 (in_arg i0 2)) (in_arg i0 3)) (wait4_spec (pid32 (in_arg i0 0)) (in_arg i0 1) (waitopts32 (in_arg i0 2)) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_260_lpres : arm_lpres_ok (mkSpecArm 260%Z (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (wait4_spec (pid32 (in_arg i0 0)) (in_arg i0 1) (waitopts32 (in_arg i0 2)) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_260_inv : arm_inv_ok (mkSpecArm 260%Z (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (wait4_spec (pid32 (in_arg i0 0)) (in_arg i0 1) (waitopts32 (in_arg i0 2)) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_261_frame : arm_frame_ok (mkSpecArm 261%Z (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (prlimit64_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (prlimit64_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_261_lpres : arm_lpres_ok (mkSpecArm 261%Z (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (prlimit64_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_261_inv : arm_inv_ok (mkSpecArm 261%Z (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (prlimit64_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_278_frame : arm_frame_ok (mkSpecArm 278%Z (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (getrandom_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2)) (getrandom_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_278_lpres : arm_lpres_ok (mkSpecArm 278%Z (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (getrandom_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_278_inv : arm_inv_ok (mkSpecArm 278%Z (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (getrandom_spec (in_arg i0 0) (in_arg i0 1) (in_arg i0 2))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_435_frame : arm_frame_ok (mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (clone3_spec (in_arg i0 0) (in_arg i0 1)) (clone3_spec (in_arg i0 0) (in_arg i0 1))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_435_lpres : arm_lpres_ok (mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (clone3_spec (in_arg i0 0) (in_arg i0 1))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_435_inv : arm_inv_ok (mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (clone3_spec (in_arg i0 0) (in_arg i0 1))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.

(* [comment removed for export] *)
Lemma arm_439_frame : arm_frame_ok (mkSpecArm 439%Z (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  intros L i0 m o _ _ H _ _. cbn [sa_spec] in *.
  assert (HL : lrel L (faccessat2_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3)) (faccessat2_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lrel_go; try assumption).
  exact (HL i0 m o H).
Qed.
Lemma arm_439_lpres : arm_lpres_ok (mkSpecArm 439%Z (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_lpres_ok. cbn [sa_spec]. intros i0 m x m' evs H.
  assert (HP : lpres (faccessat2_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (lpres_go).
  exact (HP i0 m x m' evs H).
Qed.
Lemma arm_439_inv : arm_inv_ok (mkSpecArm 439%Z (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof.
  unfold arm_inv_ok. cbn [sa_spec]. intros i0 m x m' evs H HI.
  assert (HV : vpres (faccessat2_spec (fd32 (in_arg i0 0)) (in_arg i0 1) (in_arg i0 2) (in_arg i0 3))) by (first [ solve [vpres_go] | vpres_brute ]).
  exact (vpres_inv _ HV i0 m x m' evs H HI).
Qed.
