(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition UNIT : Z := 16.
Definition IB : Z := 4.

(* [comment removed for export] *)
Definition size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63; 72; 84; 102; 127;
   146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818; 1023; 1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].

Definition size_class (sc : Z) : Z := nth (Z.to_nat sc) size_classes 0.

(* [comment removed for export] *)
Definition w_lastidx (W : Z) : Z := W mod 32.
Definition w_freeable (W : Z) : Z := (W / 32) mod 2.
Definition w_sizeclass (W : Z) : Z := (W / 64) mod 64.
Definition w_maplen (W : Z) : Z := W / 4096.

(* [comment removed for export] *)
Definition slot_stride (maplen lastidx sc : Z) : Z :=
  if (negb (maplen =? 0)) && (lastidx =? 0) then maplen * 4096 - UNIT else UNIT * size_class sc.

(* [comment removed for export] *)
Definition slot_start (M stride idx : Z) : Z := M + UNIT + stride * idx.
Definition slot_end (M stride idx : Z) : Z := slot_start M stride idx + stride - IB.

Lemma size_class_pos : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (E : exists k, (k < 48)%nat /\ Z.to_nat sc = k) by (exists (Z.to_nat sc); split; [lia|reflexivity]).
  destruct E as (k & Hk & ->).
  do 48 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slack_of (stride n : Z) : Z := (stride - IB - n) / UNIT.

(* [comment removed for export] *)
Definition smear (slack : Z) : Z :=
  let m1 := Z.lor slack (slack / 2) in
  let m2 := Z.lor m1 (m1 / 4) in
  Z.lor m2 (m2 / 16).

(* [comment removed for export] *)
Definition enframe_off (slack off0 : Z) : Z :=
  if off0 <=? slack then off0
  else let om := Z.land off0 (smear slack) in
       if slack <? om then om - slack - 1 else om.

(* [comment removed for export] *)
Definition reserved_of (stride n off : Z) : Z := stride - IB - n - UNIT * off.
Definition res_code (reserved : Z) : Z := if reserved <? 5 then reserved else 5.

(* [comment removed for export] *)
Definition inband_off (stride idx off : Z) : Z := (stride * idx) / UNIT + off.
