(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma cdivZ_ub : forall a b q, 0 < b -> a <= b * q -> cdivZ a b <= q.
Proof.
intros a b q Hb H. unfold cdivZ. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Theorem vev_of_bud : forall s e, bud_ok s e e (2 ^ 17 * e) (HULL_UNIT * e + 2 ^ 24) -> vev s + e <= VEV_MAX.
Proof.
intros s e (B1 & B2 & B3 & B4). unfold vev.
assert (C3 : cdivZ (wpot s) (2 ^ 17) <= WPOT_MAX / 2 ^ 17 - e).
{ apply cdivZ_ub; [lia|]. unfold WPOT_MAX in *. change ((2 ^ 31 - 2 ^ 23) / 2 ^ 17) with 16320. lia. }
assert (C4 : cdivZ (sec_hulls s) HULL_UNIT <= HPOT_MAX / HULL_UNIT - e).
{ apply cdivZ_ub; [unfold HULL_UNIT; lia|]. unfold HPOT_MAX, HULL_UNIT in *. change (3 * 2 ^ 36 / (2 ^ 25 + 2 ^ 14)) with 6141. lia. }
unfold EV_BIG, NREC_MAX, VEV_MAX in *. lia.
Qed.
Theorem vev_lt_of_bud : forall S Sc E C W H e c w h,
bud_ok S E C W H -> bud_le S Sc e c w h ->
e + 1 <= E -> c + 1 <= C -> w + 2 ^ 17 <= W -> h + HULL_UNIT + 2 ^ 24 <= H -> vev Sc < VEV_MAX.
Proof.
intros S Sc E C W H e c w h (A1 & A2 & A3 & A4) (D1 & D2 & D3 & D4) He Hc Hw Hh.
pose proof (vev_of_bud Sc 1) as V. unfold bud_ok in V. specialize (V ltac:(lia)). lia.
Qed.
Theorem vev_room_of_bud : forall S Sc E C W H e c w h j,
bud_ok S E C W H -> bud_le S Sc e c w h ->
e + j <= E -> c + j <= C -> w + 2 ^ 17 * j <= W -> h + HULL_UNIT * j + 2 ^ 24 <= H -> vev Sc + j <= VEV_MAX.
Proof.
intros S Sc E C W H e c w h j (A1 & A2 & A3 & A4) (D1 & D2 & D3 & D4) He Hc Hw Hh.
apply vev_of_bud. unfold bud_ok. lia.
Qed.
Theorem bud_ok_at : forall S Sc E C W H e c w h E1 C1 W1 H1,
bud_ok S E C W H -> bud_le S Sc e c w h -> e + E1 <= E -> c + C1 <= C -> w + W1 <= W -> h + H1 <= H -> bud_ok Sc E1 C1 W1 H1.
Proof. intros S Sc E C W H e c w h E1 C1 W1 H1 (A1 & A2 & A3 & A4) (D1 & D2 & D3 & D4) He Hc Hw Hh. unfold bud_ok. lia. Qed.

