(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
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

Ltac za_tac Vz K :=
  lazymatch goal with
  | |- forall j, @?P j => let Pn := fresh "PZA" in pose (Pn := P); refine (za_start Pn _); za_loop Pn Vz K 0%N
  end.

Ltac za_tac0 K :=
  lazymatch goal with
  | |- forall j : nat, bv_unsigned (?f j) = @?F j =>
      let Vz := fresh "VZA" in pose (Vz := F);
      change (forall j : nat, bv_unsigned (f j) = Vz j); za_tac Vz K
  end.
