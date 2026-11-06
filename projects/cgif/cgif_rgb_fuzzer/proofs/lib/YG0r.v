(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0n YG0o YG0t YG0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition EV_RLIBV : Z := 32000.
Definition CN_RLIB : Z := 13400.
Definition WT_RLIB : Z := 2 ^ 17 * 4050.
Definition HL_RLIB : Z := HULL_UNIT * 1510.
Definition rbud (s : astate) (r d : Z) : Prop := dbud EV_RLIBV CN_RLIB WT_RLIB HL_RLIB s r d.
Lemma rlib_nonneg : 0 <= EV_RLIBV /\ 0 <= CN_RLIB /\ 0 <= WT_RLIB /\ 0 <= HL_RLIB.
Proof. unfold EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT. lia. Qed.
Lemma rbud_enter : forall s r, dev s <= 65 -> 0 <= r <= 4 -> rbud s r 3.
Proof.
intros s r Hd Hr. apply (dbud_of_dev _ _ _ _ s r 3 65 Hd); unfold EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT, EV_BIG, NREC_MAX, WPOT_MAX, HPOT_MAX; lia.
Qed.
Lemma rbud_lib_pre : forall s r d, rbud s r d -> 1 <= r -> 0 <= d -> bud_ok s EV_RLIBV CN_RLIB WT_RLIB HL_RLIB.
Proof. intros s r d B Hr Hd. destruct rlib_nonneg as (E & C & W & H). exact (dbud_lib_pre _ _ _ _ s r d E C W H Hr Hd B). Qed.
Lemma rbud_lib_post : forall s s' r d, rbud s (r + 1) d -> bud_le s s' EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> rbud s' r d.
Proof. intros s s' r d B D. exact (dbud_lib_post _ _ _ _ s s' r d B D). Qed.

Lemma rbud_vev : forall s r d, rbud s r d -> 0 <= r -> vev s + d <= VEV_MAX.
Proof. intros s r d B Hr. destruct rlib_nonneg as (E & C & W & H). exact (dbud_vev _ _ _ _ s r d E C W H Hr B). Qed.
Ltac rbud_facts :=
repeat match goal with
| H : rbud ?s ?r ?d |- _ => lazymatch goal with _ : vev s + d <= VEV_MAX |- _ => fail | _ => pose proof (rbud_vev s r d H ltac:(lia)) end
end.
Ltac rdrv_lia := rbud_facts; drv_lia.
Goal forall s s' (r : nat), rbud s (Z.of_nat r) 3 -> jbud s s' 1 -> vev s < VEV_MAX /\ vev s' + 2 <= VEV_MAX.
Proof. intros s s' r B J. split; rdrv_lia. Qed.
