(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia. From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
Module Footprint.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.

(* [comment removed for export] *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.

(* [comment removed for export] *)
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
  rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.

(* [comment removed for export] *)
Lemma covers_same_disj : forall r a1 n1 a2 n2,
  covers r a1 n1 -> covers r a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : forall base cur cur' a n,
  cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
  intros base cur cur' a n Hle H.
  apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).

End Footprint.
From Stdlib Require ZArith Lia. From LinuxProcessSemantics.LinuxProcessSem Require Specs. From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Module SpecConsts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.

End SpecConsts.
From Stdlib Require ZArith NArith Lia. From stdpp.bitvector Require definitions.
Module BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma za_step (P : nat -> Prop) (i i' : N) :
  N.succ i = i' -> P (N.to_nat i) -> (forall j, P (N.to_nat i' + j)%nat) -> forall j, P (N.to_nat i + j)%nat.
Proof.
  intros <- H0 HS [|j].
  - rewrite Nat.add_0_r. exact H0.
  - specialize (HS j). rewrite N2Nat.inj_succ in HS. rewrite <- plus_n_Sm. exact HS.
Qed.

Lemma za_start (P : nat -> Prop) : (forall j, P (N.to_nat 0 + j)%nat) -> forall j, P j.
Proof. intros H j. exact (H j). Qed.

Lemma za_lit a : 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros H. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Ltac za_leaf Vz i :=
  first [ exact (@eq_refl Z (Vz (N.to_nat i)))
        | let a := eval cbv beta iota delta [Vz N.to_nat Pos.to_nat Pos.iter_op Nat.add] in (Vz (N.to_nat i)) in
          exact (za_lit a ltac:(split; assumption)) ].
Ltac za_loop P Vz k i :=
  lazymatch k with
  | O => let j := fresh "j" in intro j; exact (@eq_refl Z (Vz (N.to_nat i + j)%nat))
  | S ?k' => let i' := eval vm_compute in (N.succ i) in
             refine (za_step P i i' (@eq_refl N i') _ _); [ za_leaf Vz i | za_loop P Vz k' i' ]
  end.
(* [comment removed for export] *)
Ltac za_tac Vz K :=
  lazymatch goal with
  | |- forall j, @?P j => let Pn := fresh "PZA" in pose (Pn := P); refine (za_start Pn _); za_loop Pn Vz K 0%N
  end.
(* [comment removed for export] *)
Ltac za_tac0 K :=
  lazymatch goal with
  | |- forall j : nat, bv_unsigned (?f j) = @?F j =>
      let Vz := fresh "VZA" in pose (Vz := F);
      change (forall j : nat, bv_unsigned (f j) = Vz j); za_tac Vz K
  end.

End BigLinkZA.
