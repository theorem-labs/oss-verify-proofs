(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_split : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

(* [comment removed for export] *)
Lemma mod_mul_add : forall x y M N, 0 < M -> 0 < N -> 0 <= y < M ->
  (x * M + y) mod (N * M) = (x mod N) * M + y.
Proof.
  intros x y M N HM HN Hy.
  rewrite (Z.div_mod x N) at 1 by lia.
  replace ((N * (x / N) + x mod N) * M + y) with ((x mod N) * M + y + (x / N) * (N * M)) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small.
  pose proof (Z.mod_pos_bound x N HN). nia.
Qed.

(* [comment removed for export] *)
Lemma div_mul_add : forall x y M N, 0 < M -> 0 < N -> 0 <= y < M ->
  (x * M + y) / (N * M) = x / N.
Proof.
  intros x y M N HM HN Hy.
  rewrite (Z.mul_comm N M), <- Z.div_div by lia. f_equal.
  rewrite Z_div_plus_full_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma div_mod_pow2 : forall a m n, 0 <= m -> 0 <= n ->
  (a mod 2 ^ (m + n)) / 2 ^ m = (a / 2 ^ m) mod 2 ^ n.
Proof.
  intros a m n Hm Hn.
  pose proof (pow2_pos m Hm) as Pm. pose proof (pow2_pos n Hn) as Pn.
  rewrite pow2_split by lia.
  pose proof (Z.div_mod a (2 ^ m) ltac:(lia)) as E. pose proof (Z.mod_pos_bound a (2 ^ m) Pm) as R.
  set (q := a / 2 ^ m) in *. set (r := a mod 2 ^ m) in *.
  replace (a mod (2 ^ m * 2 ^ n)) with ((q * 2 ^ m + r) mod (2 ^ n * 2 ^ m)) by (rewrite E; f_equal; lia).
  rewrite mod_mul_add by lia.
  rewrite Z_div_plus_full_l by lia. rewrite (Z.div_small r) by lia. lia.
Qed.

Lemma mod_pow2_mod_pow2 : forall a k m, 0 <= k <= m -> (a mod 2 ^ m) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros a k m Hkm. apply Z.mod_mod_divide; try (apply Z.pow_nonzero; lia).
  exists (2 ^ (m - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma land_disjoint : forall a x k, 0 <= k -> 0 <= a -> a mod 2 ^ k = 0 -> 0 <= x < 2 ^ k -> Z.land a x = 0.
Proof.
  intros a x k Hk Ha Hm Hx.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec i k) as [Hi2|Hi2].
  - rewrite <- (Z.mod_pow2_bits_low a k i) by lia. rewrite Hm, Z.bits_0. reflexivity.
  - assert (T : Z.testbit x i = false).
    { apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia. }
    rewrite T. apply Bool.andb_false_r.
Qed.
Lemma lor_disjoint : forall a x k, 0 <= k -> 0 <= a -> a mod 2 ^ k = 0 -> 0 <= x < 2 ^ k -> Z.lor a x = a + x.
Proof.
  intros a x k Hk Ha Hm Hx. pose proof (land_disjoint a x k Hk Ha Hm Hx) as L.
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma land_ones' : forall a n, 0 <= n -> Z.land a (Z.shiftl 1 n - 1) = a mod 2 ^ n.
Proof.
  intros a n Hn. replace (Z.shiftl 1 n - 1) with (Z.ones n) by (unfold Z.ones; lia). apply Z.land_ones. exact Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bytes_val (l : list Z) : Z :=
  match l with [] => 0 | b :: r => b * 2 ^ (8 * Z.of_nat (length r)) + bytes_val r end.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

Lemma bytes_val_app : forall l1 l2, bytes_val (l1 ++ l2) = bytes_val l1 * 2 ^ (8 * Z.of_nat (length l2)) + bytes_val l2.
Proof.
  induction l1 as [|b l1 IH]; intros l2; cbn [bytes_val app]; [lia|].
  rewrite IH, length_app, Nat2Z.inj_add, Z.mul_add_distr_l, pow2_split by lia. lia.
Qed.
Lemma bytes_val_app1 : forall l b, bytes_val (l ++ [b]) = bytes_val l * 256 + b.
Proof. intros. rewrite bytes_val_app. cbn [bytes_val length Z.of_nat]. change (2 ^ (8 * 1)) with 256. lia. Qed.
Lemma bytes_val_range : forall l, bytes_ok l -> 0 <= bytes_val l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l as [|b l IH]; intros Hl; cbn [bytes_val length]; [lia|].
  apply Forall_cons_iff in Hl as [Hb Hl]. specialize (IH Hl).
  rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite pow2_split by lia. change (2 ^ 8) with 256. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bits := Bits { b_len : Z; b_val : Z }.
Definition bits_ok (x : bits) : Prop := 0 <= b_len x /\ 0 <= b_val x < 2 ^ b_len x.
Definition bnil : bits := Bits 0 0.
Definition bapp (x y : bits) : bits := Bits (b_len x + b_len y) (b_val x * 2 ^ b_len y + b_val y).
Definition btake (n : Z) (x : bits) : Z := b_val x / 2 ^ (b_len x - n).
Definition bdrop (n : Z) (x : bits) : bits := Bits (b_len x - n) (b_val x mod 2 ^ (b_len x - n)).
Definition bytes_bits (l : list Z) : bits := Bits (8 * Z.of_nat (length l)) (bytes_val l).

Lemma bapp_ok : forall x y, bits_ok x -> bits_ok y -> bits_ok (bapp x y).
Proof. intros [lx vx] [ly vy] [Hx1 Hx2] [Hy1 Hy2]; unfold bits_ok, bapp in *; cbn in *.
  pose proof (pow2_pos ly Hy1). rewrite pow2_split by lia. nia. Qed.
Lemma bapp_assoc : forall x y z, 0 <= b_len y -> 0 <= b_len z -> bapp (bapp x y) z = bapp x (bapp y z).
Proof. intros [lx vx] [ly vy] [lz vz] Hy Hz; unfold bapp; cbn in *. f_equal; [lia|]. rewrite pow2_split by lia. lia. Qed.
Lemma bapp_bnil_l : forall x, bapp bnil x = x. Proof. intros [l v]; unfold bapp, bnil; cbn; f_equal; lia. Qed.
Lemma btake_bapp : forall x y, bits_ok x -> bits_ok y -> btake (b_len x) (bapp x y) = b_val x.
Proof. intros [lx vx] [ly vy] [Hx1 Hx2] [Hy1 Hy2]; unfold btake, bapp; cbn in *.
  replace (lx + ly - lx) with ly by lia. rewrite Z_div_plus_full_l by (pose proof (pow2_pos ly Hy1); lia).
  rewrite Z.div_small by lia. lia. Qed.
Lemma bdrop_bapp : forall x y, bits_ok x -> bits_ok y -> bdrop (b_len x) (bapp x y) = y.
Proof. intros [lx vx] [ly vy] [Hx1 Hx2] [Hy1 Hy2]; unfold bdrop, bapp; cbn in *.
  replace (lx + ly - lx) with ly by lia. f_equal. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma btake_bapp_l : forall n x y, bits_ok x -> bits_ok y -> 0 <= n <= b_len x -> btake n (bapp x y) = btake n x.
Proof. intros n [lx vx] [ly vy] [Hx1 Hx2] [Hy1 Hy2] Hn; unfold btake, bapp; cbn in *.
  replace (lx + ly - n) with ((lx - n) + ly) by lia. rewrite (pow2_split (lx - n) ly) by lia.
  apply div_mul_add; try apply pow2_pos; lia. Qed.
Lemma bdrop_bapp_l : forall n x y, bits_ok x -> bits_ok y -> 0 <= n <= b_len x -> bdrop n (bapp x y) = bapp (bdrop n x) y.
Proof. intros n [lx vx] [ly vy] [Hx1 Hx2] [Hy1 Hy2] Hn; unfold bdrop, bapp; cbn in *. f_equal; [lia|].
  replace (lx + ly - n) with ((lx - n) + ly) by lia. rewrite (pow2_split (lx - n) ly) by lia.
  apply mod_mul_add; try apply pow2_pos; lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bw_abs (b : bw) : bits :=
  Bits (8 * bw_numZ b + bw_live b) (bytes_val (bw_bytes b) * 2 ^ bw_live b + bw_buff b / 2 ^ (32 - bw_live b)).
Definition bw_clean (b : bw) : Prop :=
  0 <= bw_live b <= 32 /\ 0 <= bw_buff b < 2 ^ 32 /\ bw_buff b mod 2 ^ (32 - bw_live b) = 0 /\ 0 <= bw_numZ b /\ bytes_ok (bw_bytes b).

Lemma zarr_to_list_zset_out : forall a k v lo n, (k < lo \/ lo + Z.of_nat n <= k) -> zarr_to_list (zset a k v) lo n = zarr_to_list a lo n.
Proof.
  intros a k v lo n. revert lo. induction n as [|n IH]; intros lo Hk; cbn [zarr_to_list]; [reflexivity|].
  rewrite zget_zset_other by lia. f_equal. apply IH. lia.
Qed.
Lemma zarr_to_list_S : forall a lo n, zarr_to_list a lo (S n) = zarr_to_list a lo n ++ [zget a (lo + Z.of_nat n)].
Proof.
  intros a lo n. revert lo. induction n as [|n IH]; intros lo.
  - cbn. f_equal. f_equal. lia.
  - change (zarr_to_list a lo (S (S n))) with (zget a lo :: zarr_to_list a (lo + 1) (S n)). rewrite IH.
    change (zarr_to_list a lo (S n)) with (zget a lo :: zarr_to_list a (lo + 1) n). cbn [app].
    f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bw_emit_bytes : forall b, 0 <= bw_numZ b -> bw_bytes (bw_emit b) = bw_bytes b ++ [Z.shiftr (bw_buff b) 24].
Proof.
  intros b Hn. unfold bw_bytes, bw_emit. cbn [bw_zb bw_numZ].
  replace (Z.to_nat (bw_numZ b + 1)) with (S (Z.to_nat (bw_numZ b))) by lia.
  rewrite zarr_to_list_S, zarr_to_list_zset_out by lia. rewrite Z2Nat.id, Z.add_0_l, zget_zset_same by lia. reflexivity.
Qed.

Lemma bw_emit_abs : forall b, bw_clean b -> 8 <= bw_live b -> bw_abs (bw_emit b) = bw_abs b /\ bw_clean (bw_emit b).
Proof.
  (intros b; cps_intros (L & B & M & N & BY); intros H8).
  assert (HB : bw_bytes (bw_emit b) = bw_bytes b ++ [Z.shiftr (bw_buff b) 24]) by (apply bw_emit_bytes; lia).
  unfold bw_abs, bw_clean. rewrite HB. unfold bw_emit; cbn [bw_buff bw_live bw_numZ bw_zb].
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. change 4294967296 with (2 ^ 32).
  set (live := bw_live b) in *. set (buff := bw_buff b) in *.
  (* [comment removed for export] *)
  pose proof (Z.div_mod buff (2 ^ 24) ltac:(lia)) as E1.
  pose proof (Z.mod_pos_bound buff (2 ^ 24) ltac:(lia)) as R1.
  set (hi := buff / 2 ^ 24) in *. set (lo := buff mod 2 ^ 24) in *.
  assert (Hhi : 0 <= hi < 256) by (subst hi; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (pow2_pos (32 - live) ltac:(lia)) as P1. pose proof (pow2_pos (live - 8) ltac:(lia)) as P2.
  assert (E24 : 2 ^ 24 = 2 ^ (live - 8) * 2 ^ (32 - live)) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (Hlo : lo mod 2 ^ (32 - live) = 0).
  { rewrite <- M, E1. replace (2 ^ 24 * hi + lo) with (lo + (hi * 2 ^ (live - 8)) * 2 ^ (32 - live)) by (rewrite E24; lia).
    rewrite Z_mod_plus_full. reflexivity. }
  pose proof (Z.div_mod lo (2 ^ (32 - live)) ltac:(lia)) as E2. rewrite Hlo, Z.add_0_r in E2.
  set (q := lo / 2 ^ (32 - live)) in *.
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Emod : (buff * 256) mod 2 ^ 32 = lo * 256).
  { rewrite E1. replace ((2 ^ 24 * hi + lo) * 256) with (lo * 256 + hi * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite Emod.
  assert (Ediv1 : buff / 2 ^ (32 - live) = hi * 2 ^ (live - 8) + q).
  { rewrite E1, E24, E2. replace (2 ^ (live - 8) * 2 ^ (32 - live) * hi + 2 ^ (32 - live) * q) with ((hi * 2 ^ (live - 8) + q) * 2 ^ (32 - live)) by lia.
    apply Z.div_mul. lia. }
  assert (Ediv2 : lo * 256 / 2 ^ (32 - (live - 8)) = q).
  { replace (32 - (live - 8)) with (8 + (32 - live)) by lia. rewrite pow2_split by lia. change (2 ^ 8) with 256.
    rewrite E2. replace (2 ^ (32 - live) * q * 256) with (q * (256 * 2 ^ (32 - live))) by lia. apply Z.div_mul. lia. }
  rewrite Ediv1, Ediv2.
  split.
  - f_equal; [lia|]. rewrite bytes_val_app1.
    assert (EL : 2 ^ live = 256 * 2 ^ (live - 8)) by (change 256 with (2 ^ 8); rewrite <- pow2_split by lia; f_equal; lia).
    rewrite EL. lia.
  - split; [lia|]. split; [lia|]. split.
    + replace (32 - (live - 8)) with (8 + (32 - live)) by lia. rewrite pow2_split by lia. change (2 ^ 8) with 256.
      rewrite E2. replace (2 ^ (32 - live) * q * 256) with ((q) * (256 * 2 ^ (32 - live))) by lia. apply Z_mod_mult.
    + split; [lia|]. unfold bytes_ok. apply Forall_app. split; [exact BY|]. constructor; [lia| constructor].
Qed.

Lemma bs_needw_abs : forall f b, bw_clean b -> bw_live b < 8 * Z.of_nat f ->
  bw_abs (bs_needw f b) = bw_abs b /\ bw_clean (bs_needw f b) /\ bw_live (bs_needw f b) = bw_live b mod 8.
Proof.
  induction f as [|f IH]; intros b C L.
  - destruct C as (C1 & _). cbn in L. lia.
  - rewrite bs_needw_S. destruct (Z.leb_spec 8 (bw_live b)) as [H8|H8].
    + destruct (bw_emit_abs b C H8) as [E C']. cps_destruct (IH (bw_emit b) C') as (E' & C'' & L').
      { unfold bw_emit; cbn [bw_live]. lia. }
      rewrite E', E, L'. split; [reflexivity|]. split; [exact C''|].
      unfold bw_emit; cbn [bw_live]. rewrite <- (Z_mod_plus_full (bw_live b - 8) 1 8). f_equal. lia.
    + split; [reflexivity|]. split; [exact C|]. destruct C as (C1 & _). symmetry. apply Z.mod_small. lia.
Qed.

Theorem bsW_abs : forall b n v, bw_clean b -> 1 <= n <= 24 -> 0 <= v < 2 ^ n ->
  bw_abs (bsW b n v) = bapp (bw_abs b) (Bits n v) /\ bw_clean (bsW b n v).
Proof.
  intros b n v C Hn Hv.
  cps_destruct (bs_needw_abs BS_FUEL b C) as (E & C1 & L1); [destruct C as (C0 & _); unfold BS_FUEL; cbn; lia|].
  pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as L8. rewrite <- L1 in L8.
  unfold bsW. rewrite <- E. set (b1 := bs_needw BS_FUEL b) in *. clearbody b1. clear E C L1 b.
  cps_destruct C1 as (L & B & M & N & BY).
  set (live := bw_live b1) in *. set (buff := bw_buff b1) in *.
  set (k := 32 - live - n). assert (Hk : 1 <= k <= 31) by (subst k; lia).
  pose proof (pow2_pos k ltac:(lia)) as Pk. pose proof (pow2_pos n ltac:(lia)) as Pn.
  assert (Ek : 2 ^ (32 - live) = 2 ^ n * 2 ^ k) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (X : (Z.shiftl v k) mod 4294967296 = v * 2 ^ k).
  { rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. change 4294967296 with (2 ^ 32).
    split; [nia|]. replace 32 with ((32 - k) + k) by lia. rewrite pow2_split by lia.
    apply Z.mul_lt_mono_pos_r; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
  unfold bw_abs, bw_clean, bapp; cbn [bw_buff bw_live bw_numZ bw_zb b_len b_val]. fold live buff.
  change (bw_bytes {| bw_buff := Z.lor buff (Z.shiftl v k mod 4294967296); bw_live := live + n; bw_numZ := bw_numZ b1; bw_zb := bw_zb b1 |})
    with (bw_bytes b1).
  rewrite X.
  pose proof (Z.div_mod buff (2 ^ (32 - live)) ltac:(lia)) as E1. rewrite M, Z.add_0_r in E1.
  set (q := buff / 2 ^ (32 - live)) in *.
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (OR : Z.lor buff (v * 2 ^ k) = buff + v * 2 ^ k).
  { apply (lor_disjoint buff (v * 2 ^ k) (32 - live)); try lia.
    rewrite Ek. split; [nia|]. apply Z.mul_lt_mono_pos_r; lia. }
  rewrite OR.
  assert (D : (buff + v * 2 ^ k) / 2 ^ (32 - (live + n)) = q * 2 ^ n + v).
  { replace (32 - (live + n)) with k by lia. rewrite E1, Ek.
    replace (2 ^ n * 2 ^ k * q + v * 2 ^ k) with ((q * 2 ^ n + v) * 2 ^ k) by lia. apply Z.div_mul. lia. }
  rewrite D. split.
  - f_equal; [lia|]. rewrite pow2_split by lia. lia.
  - split; [lia|]. split.
    + change 4294967296 with (2 ^ 32) in B. split; [nia|].
      rewrite E1, Ek. replace (2 ^ n * 2 ^ k * q + v * 2 ^ k) with ((q * 2 ^ n + v) * 2 ^ k) by lia.
      assert (q < 2 ^ live).
      { apply (Z.mul_lt_mono_pos_r (2 ^ (32 - live))); [lia|]. rewrite <- pow2_split by lia. replace (live + (32 - live)) with 32 by lia. lia. }
      replace 32 with ((live + n) + k) by lia. rewrite (pow2_split (live + n) k) by lia.
      apply Z.mul_lt_mono_pos_r; [lia|]. rewrite pow2_split by lia. nia.
    + split; [| split; [exact N| exact BY]].
      replace (32 - (live + n)) with k by lia. rewrite E1, Ek.
      replace (2 ^ n * 2 ^ k * q + v * 2 ^ k) with ((q * 2 ^ n + v) * 2 ^ k) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Theorem bs_finish_abs : forall b, bw_clean b ->
  let b' := bs_finish BS_FUEL b in
  exists pad, 0 <= pad < 8 /\
    bytes_bits (bw_bytes b') = bapp (bw_abs b) (Bits pad 0) /\ bytes_ok (bw_bytes b') /\ bw_live b' <= 0.
Proof.
  intros b C.
  (* [comment removed for export] *)
  assert (STEP : forall f c, bw_clean c -> 8 <= bw_live c -> bs_finish (S f) c = bs_finish f (bw_emit c)).
  { intros f c Cc H. rewrite bs_finish_S. destruct (Z.ltb_spec 0 (bw_live c)); [reflexivity| lia]. }
  assert (GEN : forall f c, bw_clean c -> bw_live c < 8 * Z.of_nat f ->
            let c' := bs_finish f c in
            exists pad, 0 <= pad < 8 /\ bytes_bits (bw_bytes c') = bapp (bw_abs c) (Bits pad 0) /\ bytes_ok (bw_bytes c') /\ bw_live c' <= 0).
  { induction f as [|f IH]; intros c Cc Lc.
    - destruct Cc as (C1 & _). cbn in Lc. lia.
    - destruct (Z.leb_spec 8 (bw_live c)) as [H8|H8].
      + rewrite STEP by assumption. destruct (bw_emit_abs c Cc H8) as [E C']. rewrite <- E. apply IH; [exact C'|].
        unfold bw_emit; cbn [bw_live]. lia.
      + cbv zeta. rewrite bs_finish_S. cps_destruct Cc as (L & B & M & N & BY).
        destruct (Z.ltb_spec 0 (bw_live c)) as [H0|H0].
        * (* [comment removed for export] *)
          assert (FIN : bs_finish f (bw_emit c) = bw_emit c).
          { destruct f; [reflexivity|]. rewrite bs_finish_S. change (bw_live (bw_emit c)) with (bw_live c - 8).
            destruct (Z.ltb_spec 0 (bw_live c - 8)); [lia| reflexivity]. }
          rewrite FIN. exists (8 - bw_live c). split; [lia|].
          rewrite bw_emit_bytes by lia. unfold bw_emit; cbn [bw_live].
          set (live := bw_live c) in *. set (buff := bw_buff c) in *.
          pose proof (Z.div_mod buff (2 ^ (32 - live)) ltac:(lia)) as E1. rewrite M, Z.add_0_r in E1.
          set (q := buff / 2 ^ (32 - live)) in *.
          assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
          assert (Hq2 : q < 2 ^ live).
          { apply (Z.mul_lt_mono_pos_r (2 ^ (32 - live))); [apply pow2_pos; lia|]. rewrite <- pow2_split by lia.
            replace (live + (32 - live)) with 32 by lia. change 4294967296 with (2 ^ 32) in B. lia. }
          assert (SH : Z.shiftr buff 24 = q * 2 ^ (8 - live)).
          { rewrite Z.shiftr_div_pow2 by lia. rewrite E1.
            replace (32 - live) with ((8 - live) + 24) by lia. rewrite pow2_split by lia.
            replace (2 ^ (8 - live) * 2 ^ 24 * q) with ((q * 2 ^ (8 - live)) * 2 ^ 24) by lia. apply Z.div_mul. lia. }
          rewrite SH. split; [| split; [| lia]].
          -- unfold bytes_bits, bapp, bw_abs; cbn [b_len b_val]. rewrite length_app; cbn [length].
             unfold bw_bytes at 1. rewrite zarr_to_list_length, Nat2Z.inj_add, Z2Nat.id by lia. cbn [Z.of_nat Pos.of_succ_nat].
             f_equal; [lia|]. rewrite bytes_val_app1. fold live. fold buff. fold q.
             replace 256 with (2 ^ live * 2 ^ (8 - live)) by (rewrite <- pow2_split by lia; replace (live + (8 - live)) with 8 by lia; reflexivity).
             nia.
          -- unfold bytes_ok. apply Forall_app. split; [exact BY|]. constructor; [|constructor].
             pose proof (pow2_pos (8 - live) ltac:(lia)). split; [nia|].
             replace 256 with (2 ^ live * 2 ^ (8 - live)) by (rewrite <- pow2_split by lia; replace (live + (8 - live)) with 8 by lia; reflexivity).
             apply Z.mul_lt_mono_pos_r; lia.
        * exists 0. assert (live0 : bw_live c = 0) by lia.
          split; [lia|]. split; [| split; [exact BY| lia]].
          unfold bytes_bits, bapp, bw_abs; cbn [b_len b_val]. rewrite live0.
          unfold bw_bytes at 1. rewrite zarr_to_list_length, Z2Nat.id by lia.
          replace (32 - 0) with 32 by lia. change (2 ^ 32) with 4294967296. rewrite Z.div_small by lia.
          f_equal; [lia|]. change (2 ^ 0) with 1. lia. }
  apply GEN; [exact C|]. destruct C as (C1 & _). unfold BS_FUEL. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma bw_clean_init : forall zb numZ, 0 <= numZ -> bytes_ok (zarr_to_list zb 0 (Z.to_nat numZ)) -> bw_clean (BW 0 0 numZ zb).
Proof. intros. unfold bw_clean; cbn. unfold bw_bytes; cbn. repeat split; try lia; try assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rd_abs (d : dst) (s : dstrm) : bits :=
  Bits (d_bsLive d + 8 * Z.of_nat (length (s_in s)))
       ((d_bsBuff d mod 2 ^ d_bsLive d) * 2 ^ (8 * Z.of_nat (length (s_in s))) + bytes_val (s_in s)).
Definition rd_ok (d : dst) (s : dstrm) : Prop := 0 <= d_bsLive d <= 32 /\ 0 <= d_bsBuff d /\ bytes_ok (s_in s).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rd_pull (d : dst) (s : dstrm) : dst * dstrm :=
  match s_in s with
  | [] => (d, s)
  | b :: rest => (d_set_bsLive (d_set_bsBuff d (u32 (Z.lor (Z.shiftl (d_bsBuff d) 8) b))) (d_bsLive d + 8),
                  s_set_tin (s_set_in s rest) (s_tin s + 1))
  end.

Lemma rd_pull_abs : forall d s b rest, rd_ok d s -> s_in s = b :: rest -> d_bsLive d <= 24 ->
  let '(d1, s1) := rd_pull d s in
  rd_abs d1 s1 = rd_abs d s /\ rd_ok d1 s1 /\ d_bsLive d1 = d_bsLive d + 8 /\ s_in s1 = rest.
Proof.
  (intros d s b rest; cps_intros (L & B & BY); intros Hs L24). unfold rd_pull. rewrite Hs.
  rewrite Hs in BY. apply Forall_cons_iff in BY as [Hb BY].
  cbn [d_bsLive d_bsBuff d_set_bsLive d_set_bsBuff s_in s_set_tin s_set_in].
  assert (OR : Z.lor (Z.shiftl (d_bsBuff d) 8) b = d_bsBuff d * 256 + b).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. apply (lor_disjoint _ _ 8); change (2 ^ 8) with 256; try lia.
    apply Z_mod_mult. }
  unfold u32. rewrite OR.
  split; [| split; [| split; [reflexivity| reflexivity]]].
  - unfold rd_abs; cbn [d_bsLive d_bsBuff d_set_bsLive d_set_bsBuff s_in s_set_tin s_set_in]. rewrite Hs. cbn [length bytes_val].
    rewrite Nat2Z.inj_succ. f_equal; [lia|].
    change 4294967296 with (2 ^ 32). rewrite mod_pow2_mod_pow2 by lia.
    rewrite (pow2_split (d_bsLive d) 8) by lia. change (2 ^ 8) with 256.
    rewrite mod_mul_add by (try apply pow2_pos; lia).
    replace (8 * Z.succ (Z.of_nat (length rest))) with (8 + 8 * Z.of_nat (length rest)) by lia.
    rewrite (pow2_split 8) by lia. change (2 ^ 8) with 256. lia.
  - unfold rd_ok; cbn [d_bsLive d_bsBuff d_set_bsLive d_set_bsBuff s_in s_set_tin s_set_in].
    split; [lia|]. split; [apply Z.mod_pos_bound; lia| exact BY].
Qed.

(* [comment removed for export] *)
Definition rd_extract (n : Z) (d : dst) : Z * dst :=
  (Z.land (Z.shiftr (d_bsBuff d) (d_bsLive d - n)) (Z.shiftl 1 n - 1), d_set_bsLive d (d_bsLive d - n)).

Lemma rd_extract_abs : forall n d s, rd_ok d s -> 0 <= n <= d_bsLive d ->
  let '(v, d1) := rd_extract n d in
  v = btake n (rd_abs d s) /\ rd_abs d1 s = bdrop n (rd_abs d s) /\ rd_ok d1 s /\ 0 <= v < 2 ^ n.
Proof.
  (intros n d s; cps_intros (L & B & BY); intros Hn). unfold rd_extract.
  rewrite land_ones', Z.shiftr_div_pow2 by lia.
  set (K := 8 * Z.of_nat (length (s_in s))). pose proof (bytes_val_range _ BY) as BV. fold K in BV.
  assert (HK : 0 <= K) by (subst K; lia). pose proof (pow2_pos K HK).
  split; [| split; [| split]].
  - unfold btake, rd_abs; cbn [b_val b_len]. fold K.
    replace (d_bsLive d + K - n) with ((d_bsLive d - n) + K) by lia. rewrite (pow2_split (d_bsLive d - n) K) by lia.
    rewrite div_mul_add by (try apply pow2_pos; lia).
    replace (2 ^ d_bsLive d) with (2 ^ ((d_bsLive d - n) + n)) by (f_equal; lia). symmetry. apply div_mod_pow2; lia.
  - unfold bdrop, rd_abs; cbn [b_val b_len d_bsLive d_bsBuff d_set_bsLive]. fold K. f_equal; [lia|].
    replace (d_bsLive d + K - n) with ((d_bsLive d - n) + K) by lia. rewrite (pow2_split (d_bsLive d - n) K) by lia.
    rewrite mod_mul_add by (try apply pow2_pos; lia).
    rewrite mod_pow2_mod_pow2 by lia. reflexivity.
  - unfold rd_ok; cbn [d_bsLive d_bsBuff d_set_bsLive]. repeat split; try lia. exact BY.
  - apply Z.mod_pos_bound. apply pow2_pos. lia.
Qed.

Definition dgo (f : nat) (r : dres) : dres :=
  match r with DGo l' L' d' s' => drun f l' L' d' s' | r => r end.

(* [comment removed for export] *)
Lemma drun_pull1 : forall f lbl L d s b rest, s_in s = b :: rest -> d_bsLive d < gb_bits lbl L ->
  drun (S f) lbl L d s = let '(d1, s1) := rd_pull (d_set_state d lbl) s in drun f lbl L d1 s1.
Proof.
  intros f lbl L d s b rest Hs Hl. cbn [drun]. change (d_bsLive (d_set_state d lbl)) with (d_bsLive d).
  destruct (Z.leb_spec (gb_bits lbl L) (d_bsLive d)); [lia|]. unfold rd_pull. rewrite Hs. reflexivity.
Qed.
Lemma drun_extract1 : forall f lbl L d s, gb_bits lbl L <= d_bsLive d ->
  drun (S f) lbl L d s = let '(v, d1) := rd_extract (gb_bits lbl L) (d_set_state d lbl) in dgo f (gb_after lbl v L d1 s).
Proof.
  intros f lbl L d s Hl. cbn [drun]. change (d_bsLive (d_set_state d lbl)) with (d_bsLive d).
  destruct (Z.leb_spec (gb_bits lbl L) (d_bsLive d)); [|lia]. unfold rd_extract, dgo.
  change (d_bsBuff (d_set_state d lbl)) with (d_bsBuff d). change (d_bsLive (d_set_state d lbl)) with (d_bsLive d).
  destruct (gb_after lbl _ L _ s); reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_bits (lbl : Z) (d d1 : dst) : Prop :=
  d1 = d_set_bsLive (d_set_bsBuff (d_set_state d lbl) (d_bsBuff d1)) (d_bsLive d1).
(* [comment removed for export] *)
Definition consumed_from (k : nat) (s s1 : dstrm) : Prop :=
  s1 = s_set_tin (s_set_in s (skipn k (s_in s))) (s_tin s + Z.of_nat k).

Lemma sbb_state : forall lbl d d0, same_but_bits lbl d d0 -> d_set_state d0 lbl = d0.
Proof. intros lbl d d0 E. rewrite E. destruct d; reflexivity. Qed.
Lemma rd_abs_state : forall d lbl s, rd_abs (d_set_state d lbl) s = rd_abs d s.
Proof. reflexivity. Qed.
Lemma rd_ok_state : forall d lbl s, rd_ok d s -> rd_ok (d_set_state d lbl) s.
Proof. intros d lbl s H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
