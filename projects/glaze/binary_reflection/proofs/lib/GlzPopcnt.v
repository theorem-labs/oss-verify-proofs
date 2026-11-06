(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= lia_nd.
Import ListNotations.
Open Scope Z_scope.

Definition M55 : Z := 0x5555555555555555.
Definition M33 : Z := 0x3333333333333333.
Definition M0f : Z := 0x0f0f0f0f0f0f0f0f.
Definition M01 : Z := 0x0101010101010101.
Definition MFE : Z := 2 ^ 64 - 2.

Definition swar_popc (x : Z) : Z :=
  let m := Z.land (Z.shiftr x 1) M55 in
  let x1 := Z.land x MFE in
  let z := (x1 - m) mod 2 ^ 64 in
  let y := (Z.land z M33 + Z.land (Z.shiftr z 2) M33) mod 2 ^ 64 in
  let t := Z.land ((y + Z.shiftr y 4) mod 2 ^ 64) M0f in
  Z.shiftr ((t * M01) mod 2 ^ 64) 56.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint from_bytes (bs : list Z) : Z :=
  match bs with [] => 0 | b :: r => b + 256 * from_bytes r end.

Fixpoint to_bytes (n : nat) (v : Z) : list Z :=
  match n with O => [] | S n' => v mod 256 :: to_bytes n' (v / 256) end.

Definition digits_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma to_bytes_length : forall n v, length (to_bytes n v) = n.
Proof. induction n; intros; cbn; [reflexivity | f_equal; apply IHn]. Qed.

Lemma to_bytes_ok : forall n v, digits_ok (to_bytes n v).
Proof.
  induction n; intros v; cbn; [constructor|]. constructor; [apply Z.mod_pos_bound; lia | apply IHn].
Qed.

Lemma from_to_bytes : forall n v, 0 <= v < 256 ^ Z.of_nat n -> from_bytes (to_bytes n v) = v.
Proof.
  induction n as [|n IH]; intros v Hv.
  - cbn in *. lia.
  - cbn [to_bytes from_bytes]. rewrite IH.
    + pose proof (Z.div_mod v 256 ltac:(lia)). lia.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma to_from_bytes : forall bs, digits_ok bs -> to_bytes (length bs) (from_bytes bs) = bs.
Proof.
  induction bs as [|b r IH]; intros Hok; cbn [length to_bytes from_bytes]; [reflexivity|].
  apply Forall_cons_iff in Hok as [Hb Hr]. f_equal.
  - replace (b + 256 * from_bytes r) with (b + from_bytes r * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (b + 256 * from_bytes r) with (b + from_bytes r * 256) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small b 256) by lia. rewrite Z.add_0_l. apply IH. exact Hr.
Qed.

Lemma from_bytes_nonneg : forall bs, digits_ok bs -> 0 <= from_bytes bs.
Proof. induction bs as [|b r IH]; intros H; cbn [from_bytes]; [lia|]. apply Forall_cons_iff in H as [Hb Hr]. specialize (IH Hr). lia. Qed.

Lemma from_bytes_bound : forall bs, digits_ok bs -> 0 <= from_bytes bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b r IH]; intros H; cbn [from_bytes length]; [rewrite Z.pow_0_r; lia|].
  apply Forall_cons_iff in H as [Hb Hr]. specialize (IH Hr). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
Definition bytes8 (v : Z) : list Z := to_bytes 8 v.
Lemma bytes8_recompose : forall v, 0 <= v < 2 ^ 64 -> from_bytes (bytes8 v) = v.
Proof. intros v Hv. apply from_to_bytes. change (256 ^ Z.of_nat 8) with (2 ^ 64). exact Hv. Qed.
Lemma bytes8_length : forall v, length (bytes8 v) = 8%nat.
Proof. intros. apply to_bytes_length. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mod256 : forall a b, 0 <= a -> 0 <= b -> Z.land a b mod 256 = Z.land (a mod 256) (b mod 256).
Proof.
  intros a b Ha Hb. change 256 with (2 ^ 8). rewrite <- !Z.land_ones by (try apply Z.land_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 8) n); reflexivity.
Qed.

Lemma land_div256 : forall a b, Z.land a b / 256 = Z.land (a / 256) (b / 256).
Proof.
  intros a b. change 256 with (2 ^ 8). rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.shiftr_land.
Qed.

Lemma to_bytes_land : forall n a b, 0 <= a -> 0 <= b ->
  to_bytes n (Z.land a b) = map (fun p => Z.land (fst p) (snd p)) (combine (to_bytes n a) (to_bytes n b)).
Proof.
  induction n as [|n IH]; intros a b Ha Hb; cbn [to_bytes combine map fst snd]; [reflexivity|].
  f_equal; [apply land_mod256; assumption|].
  rewrite land_div256. apply IH; apply Z.div_pos; lia.
Qed.

(* [comment removed for export] *)
Fixpoint rep (n : nat) (b : Z) : list Z := match n with O => [] | S n' => b :: rep n' b end.

Lemma rep_length : forall n b, length (rep n b) = n.
Proof. induction n; intros; cbn; [reflexivity | f_equal; apply IHn]. Qed.
Lemma rep_ok : forall n b, 0 <= b < 256 -> digits_ok (rep n b).
Proof. induction n; intros b Hb; cbn; constructor; [lia | apply IHn; exact Hb]. Qed.

Lemma to_bytes_rep : forall n mb, 0 <= mb < 256 -> to_bytes n (from_bytes (rep n mb)) = rep n mb.
Proof.
  intros n mb H. pose proof (to_from_bytes (rep n mb) (rep_ok n mb H)) as X. rewrite rep_length in X. exact X.
Qed.

Lemma map_combine_rep : forall (f : Z -> Z -> Z) bs n mb, length bs = n ->
  map (fun p => f (fst p) (snd p)) (combine bs (rep n mb)) = map (fun b => f b mb) bs.
Proof.
  intros f bs. induction bs as [|b r IH]; intros n mb Hl; cbn in *; [reflexivity|].
  destruct n as [|n]; [discriminate|]. cbn. f_equal. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes8_land_rep : forall x mb, 0 <= x < 2 ^ 64 -> 0 <= mb < 256 ->
  bytes8 (Z.land x (from_bytes (rep 8 mb))) = map (fun b => Z.land b mb) (bytes8 x).
Proof.
  intros x mb Hx Hmb. unfold bytes8. rewrite to_bytes_land by (try lia; apply from_bytes_nonneg; apply rep_ok; lia).
  rewrite to_bytes_rep by lia. apply map_combine_rep. apply to_bytes_length.
Qed.

(* [comment removed for export] *)
Lemma nth_to_bytes : forall i k w, 0 <= w -> (i < k)%nat -> nth i (to_bytes k w) 0 = (w / 2 ^ (8 * Z.of_nat i)) mod 256.
Proof.
  induction i as [|i IH]; intros k w Hw Hik.
  - destruct k; [lia|]. cbn [to_bytes nth]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - destruct k; [lia|]. cbn [to_bytes nth]. rewrite IH by (try apply Z.div_pos; lia).
    f_equal. rewrite Z.div_div by lia. f_equal. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat i)) with (8 + 8 * Z.of_nat i) by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_byte : forall v i n, 0 <= v -> 0 <= n -> (i < 8)%nat ->
  Z.testbit (nth i (bytes8 v) 0) n = if n <? 8 then Z.testbit v (8 * Z.of_nat i + n) else false.
Proof.
  intros v i n Hv Hn Hi. unfold bytes8. rewrite (nth_to_bytes i 8 v Hv Hi). change 256 with (2 ^ 8).
  destruct (n <? 8) eqn:Hn8.
  - apply Z.ltb_lt in Hn8. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. f_equal. lia.
  - apply Z.ltb_ge in Hn8. apply Z.mod_pow2_bits_high. lia.
Qed.


(* [comment removed for export] *)
Lemma map_nth_Z : forall (f : Z -> Z) l i, (i < length l)%nat -> nth i (map f l) 0 = f (nth i l 0).
Proof.
  intros f l. induction l as [|a r IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes8_shr_mask : forall x s mb, 0 <= x < 2 ^ 64 -> 0 < s < 8 -> 0 <= mb < 2 ^ (8 - s) ->
  bytes8 (Z.land (Z.shiftr x s) (from_bytes (rep 8 mb))) = map (fun b => Z.land (Z.shiftr b s) mb) (bytes8 x).
Proof.
  intros x s mb Hx Hs Hmb.
  assert (Hmb8 : mb < 256).
  { apply Z.lt_le_trans with (2 ^ (8 - s)); [lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
  assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hxs : 0 <= Z.shiftr x s < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; nia]. }
  rewrite bytes8_land_rep by lia.
  apply (nth_ext _ _ 0 0); [rewrite !length_map, !bytes8_length; reflexivity|].
  intros i Hi. rewrite length_map, bytes8_length in Hi.
  rewrite !map_nth_Z by (rewrite bytes8_length; exact Hi).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases n (8 - s)) as [Hlt|Hge].
  - rewrite Z.shiftr_spec by lia. rewrite !testbit_byte by lia. rewrite Z.shiftr_spec by lia.
    destruct (n <? 8) eqn:E1; [|apply Z.ltb_ge in E1; lia].
    destruct (n + s <? 8) eqn:E2; [|apply Z.ltb_ge in E2; lia].
    f_equal. f_equal. lia.
  - assert (Hmbn : Z.testbit mb n = false).
    { destruct (Z.eq_dec mb 0) as [->|Hnz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with (8 - s); [|lia]. apply Z.log2_lt_pow2; lia. }
    rewrite Hmbn. rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint shr4_bytes (bs : list Z) : list Z :=
  match bs with
  | [] => []
  | [b] => [b / 16]
  | b :: ((c :: _) as r) => (b / 16 + 16 * (c mod 16)) :: shr4_bytes r
  end.

Lemma shr4_bytes_length : forall bs, length (shr4_bytes bs) = length bs.
Proof. induction bs as [|b [|c r] IH]; [reflexivity | reflexivity |]. cbn [shr4_bytes length] in *. rewrite IH. reflexivity. Qed.

Lemma shr4_bytes_ok : forall bs, digits_ok bs -> digits_ok (shr4_bytes bs).
Proof.
  induction bs as [|b [|c r] IH]; intros H; cbn [shr4_bytes]; [constructor| |].
  - apply Forall_cons_iff in H as [Hb _]. constructor; [|constructor].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - apply Forall_cons_iff in H as [Hb Hr]. pose proof Hr as Hr'. apply Forall_cons_iff in Hr as [Hc _].
    constructor; [|apply IH; exact Hr'].
    pose proof (Z.mod_pos_bound c 16 ltac:(lia)). assert (b / 16 < 16) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= b / 16) by (apply Z.div_pos; lia). lia.
Qed.

Lemma shr4_bytes_val : forall bs, digits_ok bs -> from_bytes (shr4_bytes bs) = from_bytes bs / 16.
Proof.
  induction bs as [|b [|c r] IH]; intros H.
  - cbn. reflexivity.
  - cbn [shr4_bytes from_bytes]. apply Forall_cons_iff in H as [Hb _]. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity.
  - apply Forall_cons_iff in H as [Hb Hr]. specialize (IH Hr).
    change (from_bytes (shr4_bytes (b :: c :: r))) with (b / 16 + 16 * (c mod 16) + 256 * from_bytes (shr4_bytes (c :: r))).
    rewrite IH. cbn [from_bytes].
    apply Forall_cons_iff in Hr as [Hc Hr2]. pose proof (from_bytes_nonneg r Hr2) as HR.
    set (R := from_bytes r) in *.
    replace (b + 256 * (c + 256 * R)) with (b + (16 * c + 4096 * R) * 16) by lia. rewrite Z.div_add by lia.
    replace (c + 256 * R) with (c + (16 * R) * 16) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_mod c 16 ltac:(lia)). lia.
Qed.

Lemma bytes8_shr4 : forall y, 0 <= y < 2 ^ 64 -> bytes8 (Z.shiftr y 4) = shr4_bytes (bytes8 y).
Proof.
  intros y Hy. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  rewrite <- (bytes8_recompose y Hy) at 1. rewrite <- shr4_bytes_val by apply to_bytes_ok.
  unfold bytes8 at 1. pose proof (to_from_bytes (shr4_bytes (bytes8 y)) (shr4_bytes_ok _ (to_bytes_ok 8 y))) as X.
  rewrite shr4_bytes_length, bytes8_length in X. exact X.
Qed.

(* [comment removed for export] *)
Fixpoint map2 (f : Z -> Z -> Z) (xs ys : list Z) : list Z :=
  match xs, ys with x :: xr, y :: yr => f x y :: map2 f xr yr | _, _ => [] end.

Lemma map2_length : forall f xs ys, length xs = length ys -> length (map2 f xs ys) = length xs.
Proof. induction xs as [|x xr IH]; intros [|y yr] H; cbn in *; try lia. rewrite IH; lia. Qed.

Lemma from_bytes_map2_add : forall xs ys, length xs = length ys ->
  from_bytes (map2 Z.add xs ys) = from_bytes xs + from_bytes ys.
Proof. induction xs as [|x xr IH]; intros [|y yr] H; cbn [map2 from_bytes length] in *; try lia. rewrite IH; lia. Qed.

Lemma from_bytes_map2_sub : forall xs ys, length xs = length ys ->
  from_bytes (map2 Z.sub xs ys) = from_bytes xs - from_bytes ys.
Proof. induction xs as [|x xr IH]; intros [|y yr] H; cbn [map2 from_bytes length] in *; try lia. rewrite IH; lia. Qed.

Lemma bytes8_add_nocarry : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  digits_ok (map2 Z.add (bytes8 a) (bytes8 b)) ->
  bytes8 ((a + b) mod 2 ^ 64) = map2 Z.add (bytes8 a) (bytes8 b).
Proof.
  intros a b Ha Hb Hok.
  assert (L : length (map2 Z.add (bytes8 a) (bytes8 b)) = 8%nat) by (rewrite map2_length; rewrite !bytes8_length; reflexivity).
  pose proof (from_bytes_bound _ Hok) as B. rewrite L in B. change (256 ^ Z.of_nat 8) with (2 ^ 64) in B.
  rewrite from_bytes_map2_add in B by (rewrite !bytes8_length; reflexivity). rewrite !bytes8_recompose in B by assumption.
  rewrite Z.mod_small by lia.
  rewrite <- (bytes8_recompose a Ha) at 1. rewrite <- (bytes8_recompose b Hb) at 1.
  rewrite <- from_bytes_map2_add by (rewrite !bytes8_length; reflexivity).
  pose proof (to_from_bytes _ Hok) as X. rewrite L in X. exact X.
Qed.

Lemma bytes8_sub_noborrow : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  digits_ok (map2 Z.sub (bytes8 a) (bytes8 b)) ->
  bytes8 ((a - b) mod 2 ^ 64) = map2 Z.sub (bytes8 a) (bytes8 b).
Proof.
  intros a b Ha Hb Hok.
  assert (L : length (map2 Z.sub (bytes8 a) (bytes8 b)) = 8%nat) by (rewrite map2_length; rewrite !bytes8_length; reflexivity).
  pose proof (from_bytes_bound _ Hok) as B. rewrite L in B. change (256 ^ Z.of_nat 8) with (2 ^ 64) in B.
  rewrite from_bytes_map2_sub in B by (rewrite !bytes8_length; reflexivity). rewrite !bytes8_recompose in B by assumption.
  rewrite Z.mod_small by lia.
  rewrite <- (bytes8_recompose a Ha) at 1. rewrite <- (bytes8_recompose b Hb) at 1.
  rewrite <- from_bytes_map2_sub by (rewrite !bytes8_length; reflexivity).
  pose proof (to_from_bytes _ Hok) as X. rewrite L in X. exact X.
Qed.

(* [comment removed for export] *)
Fixpoint zsum (bs : list Z) : Z := match bs with [] => 0 | b :: r => b + zsum r end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma mul_M01_shr56 : forall t0 t1 t2 t3 t4 t5 t6 t7,
  digits_ok [t0; t1; t2; t3; t4; t5; t6; t7] ->
  zsum [t0; t1; t2; t3; t4; t5; t6; t7] < 256 ->
  Z.shiftr ((from_bytes [t0; t1; t2; t3; t4; t5; t6; t7] * M01) mod 2 ^ 64) 56 = zsum [t0; t1; t2; t3; t4; t5; t6; t7].
Proof.
  intros t0 t1 t2 t3 t4 t5 t6 t7 Hok Hs. unfold digits_ok in Hok.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end.
  cbn [zsum from_bytes] in *. rewrite !Z.mul_0_r, !Z.add_0_r in *.
  pose (L := t0 + 256 * ((t0 + t1) + 256 * ((t0 + t1 + t2) + 256 * ((t0 + t1 + t2 + t3) +
           256 * ((t0 + t1 + t2 + t3 + t4) + 256 * ((t0 + t1 + t2 + t3 + t4 + t5) + 256 * ((t0 + t1 + t2 + t3 + t4 + t5 + t6)
           + 256 * (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7)))))))).
  pose (Hh := (t1 + t2 + t3 + t4 + t5 + t6 + t7) + 256 * ((t2 + t3 + t4 + t5 + t6 + t7) + 256 * ((t3 + t4 + t5 + t6 + t7) +
              256 * ((t4 + t5 + t6 + t7) + 256 * ((t5 + t6 + t7) + 256 * ((t6 + t7) + 256 * t7)))))).
  assert (E : (t0 + 256 * (t1 + 256 * (t2 + 256 * (t3 + 256 * (t4 + 256 * (t5 + 256 * (t6 + 256 * t7))))))) * M01
              = L + Hh * 2 ^ 64) by (unfold L, Hh, M01; lia).
  rewrite E. rewrite Z.mod_add by lia.
  assert (HL : 0 <= L < 2 ^ 64) by (unfold L; lia).
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. unfold L. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Zf (b : Z) : Z := b - Z.land (Z.shiftr b 1) 85.                 (* [comment removed for export] *)
Definition Zf0 (b : Z) : Z := Z.land b 254 - Z.land (Z.shiftr b 1) 85.    (* [comment removed for export] *)
Definition Yf (u : Z) : Z := Z.land u 51 + Z.land (Z.shiftr u 2) 51.      (* [comment removed for export] *)
Definition Tf (w : Z) : Z := (w + w / 16) mod 16.                          (* [comment removed for export] *)

Definition byte_okb (u : Z) : bool :=
  (0 <=? u) && (u <? 256) && (Yf u <=? 68) && (Yf u mod 16 <=? 4) && (Tf (Yf u) <=? 8).
Definition check_byte (b : Z) : bool := byte_okb (Zf b) && byte_okb (Zf0 b).

Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zrange (lo + 1) n' end.
Lemma zrange_forallb : forall f n lo, forallb f (zrange lo n) = true -> forall b, lo <= b < lo + Z.of_nat n -> f b = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H b Hb; [lia|].
  cbn [zrange forallb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec b lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1)); [exact H2 | lia].
Qed.

Lemma check_all_bytes : forallb check_byte (zrange 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma byte_ok_spec : forall u, byte_okb u = true -> 0 <= u < 256 /\ Yf u <= 68 /\ Yf u mod 16 <= 4 /\ Tf (Yf u) <= 8.
Proof.
  intros u H. unfold byte_okb in H. repeat (apply andb_prop in H as [H ?]).
  repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G end.
  lia.
Qed.

Lemma byte_facts : forall b, 0 <= b < 256 ->
  (0 <= Zf b < 256 /\ Yf (Zf b) <= 68 /\ Yf (Zf b) mod 16 <= 4 /\ Tf (Yf (Zf b)) <= 8)
  /\ (0 <= Zf0 b < 256 /\ Yf (Zf0 b) <= 68 /\ Yf (Zf0 b) mod 16 <= 4 /\ Tf (Yf (Zf0 b)) <= 8).
Proof.
  intros b Hb. pose proof (zrange_forallb check_byte 256 0 check_all_bytes b ltac:(lia)) as H.
  unfold check_byte in H. apply andb_prop in H as [H1 H2]. split; apply byte_ok_spec; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition B (i : nat) (x : Z) : Z := nth i (bytes8 x) 0.

Lemma bytes8_explicit : forall x, bytes8 x = [B 0 x; B 1 x; B 2 x; B 3 x; B 4 x; B 5 x; B 6 x; B 7 x].
Proof.
  intros x. unfold B. pose proof (bytes8_length x) as L.
  destruct (bytes8 x) as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 r]]]]]]]]]; cbn in L; try lia. reflexivity.
Qed.

Lemma B_range : forall x i, 0 <= B i x < 256.
Proof.
  intros x i. unfold B. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
  - pose proof (to_bytes_ok 8 x) as H. unfold bytes8. eapply (Forall_nth (fun b => 0 <= b < 256)) in H; [apply H|].
    rewrite to_bytes_length. exact Hi.
  - rewrite nth_overflow by (rewrite bytes8_length; lia). lia.
Qed.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb. rewrite Z.land_comm. pose proof (Z.sub_land_same_l b a).
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia). lia.
Qed.
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof. intros. rewrite Z.land_comm. apply land_le_r. assumption. Qed.

Lemma Yf_lt256 : forall u, 0 <= u -> 0 <= Yf u < 256.
Proof.
  intros u Hu. unfold Yf.
  pose proof (Z.land_nonneg u 51). pose proof (Z.land_nonneg (Z.shiftr u 2) 51).
  assert (0 <= Z.shiftr u 2) by (apply Z.shiftr_nonneg; lia).
  pose proof (land_le_r u 51 ltac:(lia)).
  pose proof (land_le_r (Z.shiftr u 2) 51 ltac:(lia)). lia.
Qed.

Lemma land15_mod : forall s k, 0 <= s -> 0 <= k -> Z.land (s + 16 * k) 15 = s mod 16.
Proof.
  intros s k Hs Hk. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  replace (s + 16 * k) with (s + k * 16) by lia. apply Z.mod_add. lia.
Qed.

Lemma M55_rep : M55 = from_bytes (rep 8 85). Proof. reflexivity. Qed.
Lemma M33_rep : M33 = from_bytes (rep 8 51). Proof. reflexivity. Qed.
Lemma M0f_rep : M0f = from_bytes (rep 8 15). Proof. reflexivity. Qed.
Lemma MFE_bytes : MFE = from_bytes [254; 255; 255; 255; 255; 255; 255; 255]. Proof. reflexivity. Qed.

Lemma land255 : forall b, 0 <= b < 256 -> Z.land b 255 = b.
Proof. intros b Hb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.

Theorem swar_popc_bound : forall x, 0 <= x < 2 ^ 64 -> 0 <= swar_popc x <= 64.
Proof.
  intros x Hx. unfold swar_popc.
  pose proof (bytes8_explicit x) as HX.
  pose proof (B_range x 0) as R0. pose proof (B_range x 1) as R1. pose proof (B_range x 2) as R2. pose proof (B_range x 3) as R3.
  pose proof (B_range x 4) as R4. pose proof (B_range x 5) as R5. pose proof (B_range x 6) as R6. pose proof (B_range x 7) as R7.
  set (b0 := B 0 x) in *. set (b1 := B 1 x) in *. set (b2 := B 2 x) in *. set (b3 := B 3 x) in *.
  set (b4 := B 4 x) in *. set (b5 := B 5 x) in *. set (b6 := B 6 x) in *. set (b7 := B 7 x) in *.
  clearbody b0 b1 b2 b3 b4 b5 b6 b7.
  destruct (byte_facts b0 R0) as [_ [F0a [F0b [F0c F0d]]]]. destruct (byte_facts b1 R1) as [[F1a [F1b [F1c F1d]]] _].
  destruct (byte_facts b2 R2) as [[F2a [F2b [F2c F2d]]] _]. destruct (byte_facts b3 R3) as [[F3a [F3b [F3c F3d]]] _].
  destruct (byte_facts b4 R4) as [[F4a [F4b [F4c F4d]]] _]. destruct (byte_facts b5 R5) as [[F5a [F5b [F5c F5d]]] _].
  destruct (byte_facts b6 R6) as [[F6a [F6b [F6c F6d]]] _]. destruct (byte_facts b7 R7) as [[F7a [F7b [F7c F7d]]] _].
  (* [comment removed for export] *)
  set (x1 := Z.land x MFE).
  assert (Rx1 : 0 <= x1 < 2 ^ 64).
  { subst x1. split; [apply Z.land_nonneg; lia|]. unfold MFE.
    apply Z.le_lt_trans with x; [apply land_le_l; lia | lia]. }
  assert (Hx1 : bytes8 x1 = [Z.land b0 254; b1; b2; b3; b4; b5; b6; b7]).
  { subst x1. rewrite MFE_bytes. unfold bytes8. rewrite to_bytes_land by (cbn; lia).
    change (to_bytes 8 x) with (bytes8 x). rewrite HX.
    replace (to_bytes 8 (from_bytes [254; 255; 255; 255; 255; 255; 255; 255])) with [254; 255; 255; 255; 255; 255; 255; 255] by reflexivity.
    cbn [combine map fst snd]. rewrite !land255 by assumption. reflexivity. }
  (* [comment removed for export] *)
  set (m := Z.land (Z.shiftr x 1) M55).
  assert (Hm : bytes8 m = map (fun b => Z.land (Z.shiftr b 1) 85) [b0; b1; b2; b3; b4; b5; b6; b7]).
  { subst m. rewrite M55_rep. rewrite bytes8_shr_mask by (cbn; lia). rewrite HX. reflexivity. }
  assert (Rm : 0 <= m < 2 ^ 64).
  { subst m. split; [apply Z.land_nonneg; right; unfold M55; lia|].
    apply Z.le_lt_trans with M55; [apply land_le_r; unfold M55; lia | unfold M55; lia]. }
  (* [comment removed for export] *)
  set (z := (x1 - m) mod 2 ^ 64).
  assert (Hz : bytes8 z = [Zf0 b0; Zf b1; Zf b2; Zf b3; Zf b4; Zf b5; Zf b6; Zf b7]).
  { subst z. rewrite bytes8_sub_noborrow; [rewrite Hx1, Hm; reflexivity | exact Rx1 | exact Rm |].
    rewrite Hx1, Hm. change (digits_ok [Zf0 b0; Zf b1; Zf b2; Zf b3; Zf b4; Zf b5; Zf b6; Zf b7]).
    repeat (constructor; [assumption|]). constructor. }
  assert (Rz : 0 <= z < 2 ^ 64) by (subst z; apply Z.mod_pos_bound; lia).
  clear Hx1 Hm Rx1 Rm HX.
  (* [comment removed for export] *)
  pose proof (Yf_lt256 (Zf0 b0) ltac:(lia)) as Q0. pose proof (Yf_lt256 (Zf b1) ltac:(lia)) as Q1.
  pose proof (Yf_lt256 (Zf b2) ltac:(lia)) as Q2. pose proof (Yf_lt256 (Zf b3) ltac:(lia)) as Q3.
  pose proof (Yf_lt256 (Zf b4) ltac:(lia)) as Q4. pose proof (Yf_lt256 (Zf b5) ltac:(lia)) as Q5.
  pose proof (Yf_lt256 (Zf b6) ltac:(lia)) as Q6. pose proof (Yf_lt256 (Zf b7) ltac:(lia)) as Q7.
  set (y := (Z.land z M33 + Z.land (Z.shiftr z 2) M33) mod 2 ^ 64).
  assert (Hy : bytes8 y = [Yf (Zf0 b0); Yf (Zf b1); Yf (Zf b2); Yf (Zf b3); Yf (Zf b4); Yf (Zf b5); Yf (Zf b6); Yf (Zf b7)]).
  { subst y.
    assert (A1 : bytes8 (Z.land z M33) = map (fun u => Z.land u 51) (bytes8 z)) by (rewrite M33_rep; apply bytes8_land_rep; lia).
    assert (A2 : bytes8 (Z.land (Z.shiftr z 2) M33) = map (fun u => Z.land (Z.shiftr u 2) 51) (bytes8 z))
      by (rewrite M33_rep; apply bytes8_shr_mask; cbn; lia).
    assert (RA1 : 0 <= Z.land z M33 < 2 ^ 64).
    { split; [apply Z.land_nonneg; lia|]. apply Z.le_lt_trans with M33; [apply land_le_r; unfold M33; lia | unfold M33; lia]. }
    assert (RA2 : 0 <= Z.land (Z.shiftr z 2) M33 < 2 ^ 64).
    { split; [apply Z.land_nonneg; right; unfold M33; lia|].
      apply Z.le_lt_trans with M33; [apply land_le_r; unfold M33; lia | unfold M33; lia]. }
    rewrite bytes8_add_nocarry; [rewrite A1, A2, Hz; reflexivity | exact RA1 | exact RA2 |].
    rewrite A1, A2, Hz.
    change (digits_ok [Yf (Zf0 b0); Yf (Zf b1); Yf (Zf b2); Yf (Zf b3); Yf (Zf b4); Yf (Zf b5); Yf (Zf b6); Yf (Zf b7)]).
    repeat (constructor; [assumption|]). constructor. }
  assert (Ry : 0 <= y < 2 ^ 64) by (subst y; apply Z.mod_pos_bound; lia).
  clearbody y. clear Hz Rz z m x1.
  set (y0 := Yf (Zf0 b0)) in *. set (y1 := Yf (Zf b1)) in *. set (y2 := Yf (Zf b2)) in *. set (y3 := Yf (Zf b3)) in *.
  set (y4 := Yf (Zf b4)) in *. set (y5 := Yf (Zf b5)) in *. set (y6 := Yf (Zf b6)) in *. set (y7 := Yf (Zf b7)) in *.
  clearbody y0 y1 y2 y3 y4 y5 y6 y7.
  clear F0a F1a F2a F3a F4a F5a F6a F7a R0 R1 R2 R3 R4 R5 R6 R7.
  (* [comment removed for export] *)
  assert (Hs4 : bytes8 (Z.shiftr y 4) = [y0 / 16 + 16 * (y1 mod 16); y1 / 16 + 16 * (y2 mod 16); y2 / 16 + 16 * (y3 mod 16);
                                         y3 / 16 + 16 * (y4 mod 16); y4 / 16 + 16 * (y5 mod 16); y5 / 16 + 16 * (y6 mod 16);
                                         y6 / 16 + 16 * (y7 mod 16); y7 / 16]).
  { rewrite bytes8_shr4 by exact Ry. rewrite Hy. reflexivity. }
  assert (Rs4 : 0 <= Z.shiftr y 4 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. clear -Ry. lia. }
  assert (Hsum : bytes8 ((y + Z.shiftr y 4) mod 2 ^ 64) =
     [y0 + (y0 / 16 + 16 * (y1 mod 16)); y1 + (y1 / 16 + 16 * (y2 mod 16)); y2 + (y2 / 16 + 16 * (y3 mod 16));
      y3 + (y3 / 16 + 16 * (y4 mod 16)); y4 + (y4 / 16 + 16 * (y5 mod 16)); y5 + (y5 / 16 + 16 * (y6 mod 16));
      y6 + (y6 / 16 + 16 * (y7 mod 16)); y7 + y7 / 16]).
  { rewrite bytes8_add_nocarry; [rewrite Hy, Hs4; reflexivity | exact Ry | exact Rs4 |].
    rewrite Hy, Hs4. cbn [map2]. clear Hy Hs4 Ry Rs4. repeat constructor; lia. }
  set (sm := (y + Z.shiftr y 4) mod 2 ^ 64) in *.
  assert (Rsm : 0 <= sm < 2 ^ 64) by (subst sm; apply Z.mod_pos_bound; lia).
  clearbody sm. clear Hy Hs4 Rs4 Ry y.
  set (t := Z.land sm M0f).
  assert (Ht : bytes8 t = [Tf y0; Tf y1; Tf y2; Tf y3; Tf y4; Tf y5; Tf y6; Tf y7]).
  { subst t. rewrite M0f_rep. rewrite bytes8_land_rep by lia. rewrite Hsum. cbn [map].
    rewrite !Z.add_assoc. rewrite !land15_mod by (clear Hsum; lia).
    replace (y7 + y7 / 16) with (y7 + y7 / 16 + 16 * 0) by lia. rewrite land15_mod by (clear Hsum; lia).
    unfold Tf. reflexivity. }
  assert (Rt : 0 <= t < 2 ^ 64).
  { subst t. split; [apply Z.land_nonneg; lia|]. apply Z.le_lt_trans with M0f; [apply land_le_r; unfold M0f; lia | unfold M0f; lia]. }
  rewrite <- (bytes8_recompose t Rt). rewrite Ht. clear Ht Rt Hsum Rsm t.
  assert (Tpos : forall w, 0 <= Tf w < 16) by (intros; unfold Tf; apply Z.mod_pos_bound; lia).
  pose proof (Tpos y0). pose proof (Tpos y1). pose proof (Tpos y2). pose proof (Tpos y3).
  pose proof (Tpos y4). pose proof (Tpos y5). pose proof (Tpos y6). pose proof (Tpos y7).
  set (u0 := Tf y0) in *. set (u1 := Tf y1) in *. set (u2 := Tf y2) in *. set (u3 := Tf y3) in *.
  set (u4 := Tf y4) in *. set (u5 := Tf y5) in *. set (u6 := Tf y6) in *. set (u7 := Tf y7) in *.
  clearbody u0 u1 u2 u3 u4 u5 u6 u7. clear Tpos F0b F0c F1b F1c F2b F2c F3b F3c F4b F4c F5b F5c F6b F6c F7b F7c Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7.
  rewrite mul_M01_shr56.
  - cbn [zsum]. lia.
  - repeat constructor; lia.
  - cbn [zsum]. lia.
Qed.
