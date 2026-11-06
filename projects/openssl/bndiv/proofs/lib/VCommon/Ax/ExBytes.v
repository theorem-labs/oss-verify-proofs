(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma phi_of_Z_small' (z : Z) : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). exact H. Qed.

(* [comment removed for export] *)
Definition zbyte (z : Z) (i : nat) : Z := (z / 2 ^ (8 * Z.of_nat i)) mod 256.

Lemma zbyte_range (z : Z) (i : nat) : 0 <= zbyte z i < 256.
Proof. unfold zbyte. apply Z.mod_pos_bound. lia. Qed.

Lemma pow8 (i : nat) : 2 ^ (8 * Z.of_nat (S i)) = 256 * 2 ^ (8 * Z.of_nat i).
Proof. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. ring. Qed.

Lemma zbyte_S (z : Z) (i : nat) : 0 <= z -> zbyte z (S i) = zbyte (z / 256) i.
Proof.
  intros Hz. unfold zbyte. rewrite pow8. rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_comm. reflexivity.
Qed.

Lemma zbyte_0 (z : Z) : zbyte z 0 = z mod 256.
Proof. unfold zbyte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint zcombine (l : list Z) : Z :=
  match l with
  | [] => 0
  | b :: r => b + 256 * zcombine r
  end.

Lemma zcombine_range (l : list Z) : Forall (fun b => 0 <= b < 256) l -> 0 <= zcombine l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction 1 as [|b r Hb Hr IH]; cbn [zcombine length]; [cbn; lia|].
  rewrite pow8. lia.
Qed.

(* [comment removed for export] *)
Lemma zcombine_bytes (z : Z) (n : nat) : 0 <= z ->
  zcombine (map (zbyte z) (seq 0 n)) = z mod 2 ^ (8 * Z.of_nat n).
Proof.
  revert z. induction n as [|n IH]; intros z Hz; cbn [seq map zcombine].
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - rewrite <- seq_shift, map_map.
    rewrite (map_ext (fun x => zbyte z (S x)) (zbyte (z / 256))) by (intros; apply zbyte_S; exact Hz).
    rewrite IH by (apply Z.div_pos; lia). rewrite zbyte_0. rewrite pow8.
    rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia). ring.
Qed.

(* [comment removed for export] *)
Lemma zbyte_zcombine (l : list Z) (i : nat) :
  Forall (fun b => 0 <= b < 256) l -> (i < length l)%nat -> zbyte (zcombine l) i = nth i l 0.
Proof.
  intros Hl. revert i. induction Hl as [|b r Hb Hr IH]; intros i Hi; cbn [length] in Hi; [lia|].
  pose proof (zcombine_range r Hr).
  destruct i as [|i]; cbn [zcombine nth].
  - rewrite zbyte_0. replace (b + 256 * zcombine r) with (b + zcombine r * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite zbyte_S by lia. replace (b + 256 * zcombine r) with (b + zcombine r * 256) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bshift (i : nat) : int :=
  match i with 0%nat => 0 | 1%nat => 8 | 2%nat => 16 | 3%nat => 24 | 4%nat => 32 | 5%nat => 40 | 6%nat => 48 | _ => 56 end%uint63.

Definition w_byte (w : w64) (i : nat) : int :=
  match i with
  | 7%nat => (((wl w >> 56) land 127) + (if wh w then 128 else 0))%uint63
  | _ => ((wl w >> bshift i) land 255)%uint63
  end.

Lemma phi_land_ones (x : int) (k : Z) (m : int) : 0 <= k -> to_Z m = 2 ^ k - 1 -> to_Z (x land m)%uint63 = to_Z x mod 2 ^ k.
Proof.
  intros Hk Hm. rewrite land_spec', Hm. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma w_byte_spec (w : w64) (i : nat) : (i < 8)%nat -> to_Z (w_byte w i) = zbyte (wZ w) i.
Proof.
  intros Hi. pose proof (phi_range (wl w)) as Hl. rewrite wZ_split.
  assert (Hlow : forall i, (i < 7)%nat -> zbyte (Z.b2z (wh w) * two63 + to_Z (wl w)) i = zbyte (to_Z (wl w)) i).
  { intros j Hj. unfold zbyte.
    replace (Z.b2z (wh w) * two63 + to_Z (wl w)) with (to_Z (wl w) + (Z.b2z (wh w) * 2 ^ (63 - 8 * Z.of_nat j)) * 2 ^ (8 * Z.of_nat j)).
    2:{ rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. replace (63 - 8 * Z.of_nat j + 8 * Z.of_nat j) with 63 by lia. unfold two63. ring. }
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    replace (63 - 8 * Z.of_nat j) with (8 + (55 - 8 * Z.of_nat j)) by lia. rewrite Z.pow_add_r by lia.
    change (2 ^ 8) with 256.
    replace (to_Z (wl w) / 2 ^ (8 * Z.of_nat j) + Z.b2z (wh w) * (256 * 2 ^ (55 - 8 * Z.of_nat j)))
      with (to_Z (wl w) / 2 ^ (8 * Z.of_nat j) + (Z.b2z (wh w) * 2 ^ (55 - 8 * Z.of_nat j)) * 256) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; unfold w_byte.
  1-7: (rewrite Hlow by lia; unfold zbyte;
            rewrite (phi_land_ones _ 8 255) by (try lia; reflexivity);
            rewrite lsr_spec; reflexivity).
  (* [comment removed for export] *)
  unfold zbyte. cbn [Z.of_nat]. change (8 * 7) with 56.
  rewrite add_spec, (phi_land_ones _ 7 127) by (try lia; reflexivity). rewrite lsr_spec.
  change (to_Z 56%uint63) with 56. change wB with (2 ^ 63).
  assert (H56 : to_Z (wl w) / 2 ^ 56 < 128) by (apply Z.div_lt_upper_bound; [lia|]; change (2^56 * 128) with two63; lia).
  assert (H560 : 0 <= to_Z (wl w) / 2 ^ 56) by (apply Z.div_pos; lia).
  rewrite Z.mod_small with (a := to_Z (wl w) / 2 ^ 56) by lia.
  replace (Z.b2z (wh w) * two63 + to_Z (wl w)) with (to_Z (wl w) + (Z.b2z (wh w) * 128) * 2 ^ 56) by (unfold two63; ring).
  rewrite Z.div_add by lia.
  destruct (wh w); cbn [Z.b2z].
  - change (to_Z 128%uint63) with 128. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
  - change (to_Z 0%uint63) with 0. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition w_of_bytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : int) : w64 :=
  W (128 <=? b7)%uint63
    (b0 lor (b1 << 8) lor (b2 << 16) lor (b3 << 24) lor (b4 << 32) lor (b5 << 40) lor (b6 << 48) lor ((b7 land 127) << 56))%uint63.


