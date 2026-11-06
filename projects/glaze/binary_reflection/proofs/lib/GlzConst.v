(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RunCeil.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Abbreviation CEIL0 := 140735332483072.     (* [comment removed for export] *)
Abbreviation CEILMAX := 140737479966720.   (* [comment removed for export] *)

Class run_ceil := RUNCEIL { CEIL : Z ; ceil_rng : CEIL0 <= CEIL <= CEILMAX ; ceil_pg : CEIL mod 4096 = 0 }.

(* [comment removed for export] *)
Ltac ceil := lazymatch goal with
             | CR : CEIL0 <= CEIL <= CEILMAX |- _ => idtac
             | |- _ => pose proof ceil_rng; pose proof ceil_pg
             end.


(* [comment removed for export] *)
Definition page_floor (z : Z) : Z := z - z mod 4096.

Lemma page_floor_le : forall z, page_floor z <= z.
Proof. intros z. unfold page_floor. pose proof (Z.mod_pos_bound z 4096). lia. Qed.

Lemma page_floor_aligned : forall z, page_floor z mod 4096 = 0.
Proof.
  intros z. unfold page_floor. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma page_floor_ge : forall z, z - 4095 <= page_floor z.
Proof. intros z. unfold page_floor. pose proof (Z.mod_pos_bound z 4096). lia. Qed.

(* [comment removed for export] *)
Lemma page_floor_bound : forall e z, e mod 4096 = 0 -> e <= z -> e <= page_floor z.
Proof.
  intros e z He Hz. unfold page_floor.
  pose proof (Z.mod_pos_bound z 4096). pose proof (Z.mod_pos_bound e 4096).
  assert (E : e = 4096 * (e / 4096)) by (pose proof (Z.div_mod e 4096); lia).
  assert (Zq : z = 4096 * (z / 4096) + z mod 4096) by (apply Z.div_mod; lia).
  assert (e / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
  nia.
Qed.

Lemma run_ceil_of_top_ok : forall top : Z,
  CEIL0 <= top <= CEILMAX -> CEIL0 <= page_floor top <= CEILMAX /\ page_floor top mod 4096 = 0.
Proof.
  intros top H. pose proof (page_floor_le top). pose proof (page_floor_ge top). pose proof (page_floor_aligned top).
  assert (CEIL0 mod 4096 = 0) by reflexivity.
  pose proof (page_floor_bound CEIL0 top ltac:(reflexivity) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition run_ceil_of_top (top : Z) (H : CEIL0 <= top <= CEILMAX) : run_ceil :=
  RUNCEIL (page_floor top) (proj1 (run_ceil_of_top_ok top H)) (proj2 (run_ceil_of_top_ok top H)).

Lemma alloc_top_rng_of_valid_sp : forall sp : word, valid_sp sp ->
  CEIL0 <= bv_unsigned sp - stack_max_size <= CEILMAX.
Proof. intros sp (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia. Qed.
End RunCeil.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Export RunCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition HI47 : Z := 2 ^ 47.
Definition PTRLO : Z := 0x1010.
Definition PTRHI : Z := 140737479966720.   (* [comment removed for export] *)
Definition WSTK : Z := 2 ^ 62.

(* [comment removed for export] *)
Notation CEIL_run := CEIL.

(* [comment removed for export] *)
Lemma ceil_lo {RC : run_ceil} : CEIL0 <= CEIL.
Proof. pose proof ceil_rng. lia. Qed.
Lemma ceil_hi {RC : run_ceil} : CEIL <= PTRHI.
Proof. pose proof ceil_rng. unfold PTRHI. lia. Qed.
Lemma ceil_pos {RC : run_ceil} : 0 < CEIL.
Proof. pose proof ceil_rng. lia. Qed.




