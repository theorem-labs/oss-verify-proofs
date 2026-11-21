(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition UNIT : Z := 16.
Definition IB : Z := 4.

Definition size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63; 72; 84; 102; 127;
   146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818; 1023; 1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].

Definition size_class (sc : Z) : Z := nth (Z.to_nat sc) size_classes 0.

Definition slot_start (M stride idx : Z) : Z := M + UNIT + stride * idx.
Lemma size_class_pos : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (E : exists k, (k < 48)%nat /\ Z.to_nat sc = k) by (exists (Z.to_nat sc); split; [lia|reflexivity]).
  destruct E as (k & Hk & ->).
  do 48 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.


Definition smear (slack : Z) : Z :=
  let m1 := Z.lor slack (slack / 2) in
  let m2 := Z.lor m1 (m1 / 4) in
  Z.lor m2 (m2 / 16).
