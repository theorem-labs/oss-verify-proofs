(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Bool Lia Znumtheory.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition zwrap (n : Z) (z : Z) : Z := z mod 2 ^ n.
Definition zswrap (n : Z) (z : Z) : Z := (z + 2 ^ (n - 1)) mod 2 ^ n - 2 ^ (n - 1).

Definition M64 : Z := 2 ^ 64.
Definition M32 : Z := 2 ^ 32.
Definition H64 : Z := 2 ^ 63.
Definition H32 : Z := 2 ^ 31.

Lemma pow2_pos n : 0 <= n -> 0 < 2 ^ n.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_le n m : 0 <= n <= m -> 2 ^ n <= 2 ^ m.
Proof. intros; apply Z.pow_le_mono_r; lia. Qed.

Lemma pow2_divide n m : 0 <= n <= m -> (2 ^ n | 2 ^ m).
Proof.
  intros. exists (2 ^ (m - n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma pow2_half n : 0 < n -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof.
  intros. replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zwrap_range n z : 0 <= n -> 0 <= zwrap n z < 2 ^ n.
Proof. intros. unfold zwrap. apply Z.mod_pos_bound. now apply pow2_pos. Qed.

Lemma zwrap_id n z : 0 <= z < 2 ^ n -> zwrap n z = z.
Proof. intros. unfold zwrap. now apply Z.mod_small. Qed.

Lemma zwrap_id_iff n z : 0 <= n -> (zwrap n z = z <-> 0 <= z < 2 ^ n).
Proof.
  intros Hn. split; [|apply zwrap_id]. intros E. rewrite <- E. now apply zwrap_range.
Qed.

Lemma zwrap_zwrap n m z : 0 <= n <= m -> zwrap n (zwrap m z) = zwrap n z.
Proof. intros. unfold zwrap. apply Z.mod_mod_divide. now apply pow2_divide. Qed.

Lemma zwrap_idem n z : 0 <= n -> zwrap n (zwrap n z) = zwrap n z.
Proof. intros; apply zwrap_zwrap; lia. Qed.

Lemma zwrap_congr n a b : 0 <= n -> (2 ^ n | a - b) -> zwrap n a = zwrap n b.
Proof.
  intros Hn [q Hq]. unfold zwrap. replace a with (b + q * 2 ^ n) by lia.
  now rewrite Z.mod_add by (pose proof (pow2_pos n Hn); lia).
Qed.

Lemma zwrap_eq_iff n a b : 0 <= n -> (zwrap n a = zwrap n b <-> (2 ^ n | a - b)).
Proof.
  intros Hn. split; [|now apply zwrap_congr].
  unfold zwrap. intros E. pose proof (pow2_pos n Hn).
  exists (a / 2 ^ n - b / 2 ^ n).
  pose proof (Z.div_mod a (2 ^ n) ltac:(lia)). pose proof (Z.div_mod b (2 ^ n) ltac:(lia)). nia.
Qed.

Lemma zwrap_divide_self n z : 0 <= n -> (2 ^ n | zwrap n z - z).
Proof.
  intros Hn. unfold zwrap. pose proof (pow2_pos n Hn).
  exists (- (z / 2 ^ n)). pose proof (Z.div_mod z (2 ^ n) ltac:(lia)). nia.
Qed.

Lemma zwrap_plus_k n z k : 0 <= n -> zwrap n (z + k * 2 ^ n) = zwrap n z.
Proof. intros. apply zwrap_congr; auto. exists k. lia. Qed.

(* [comment removed for export] *)
Lemma zwrap_add n a b : 0 <= n -> zwrap n (zwrap n a + zwrap n b) = zwrap n (a + b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. pose proof (zwrap_divide_self n b Hn) as [q Hq].
  exists (p + q). lia.
Qed.

Lemma zwrap_add_l n a b : 0 <= n -> zwrap n (zwrap n a + b) = zwrap n (a + b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. exists p. lia.
Qed.

Lemma zwrap_add_r n a b : 0 <= n -> zwrap n (a + zwrap n b) = zwrap n (a + b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n b Hn) as [p Hp]. exists p. lia.
Qed.

Lemma zwrap_sub n a b : 0 <= n -> zwrap n (zwrap n a - zwrap n b) = zwrap n (a - b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. pose proof (zwrap_divide_self n b Hn) as [q Hq].
  exists (p - q). lia.
Qed.

Lemma zwrap_sub_l n a b : 0 <= n -> zwrap n (zwrap n a - b) = zwrap n (a - b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. exists p. lia.
Qed.

Lemma zwrap_sub_r n a b : 0 <= n -> zwrap n (a - zwrap n b) = zwrap n (a - b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n b Hn) as [p Hp]. exists (- p). lia.
Qed.

Lemma zwrap_neg n a : 0 <= n -> zwrap n (- zwrap n a) = zwrap n (- a).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. exists (- p). lia.
Qed.

Lemma zwrap_mul n a b : 0 <= n -> zwrap n (zwrap n a * zwrap n b) = zwrap n (a * b).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp]. pose proof (zwrap_divide_self n b Hn) as [q Hq].
  assert (Ea : zwrap n a = a + p * 2 ^ n) by lia.
  assert (Eb : zwrap n b = b + q * 2 ^ n) by lia.
  rewrite Ea, Eb. exists (a * q + p * b + p * q * 2 ^ n). nia.
Qed.

Lemma zwrap_mul_l n a k : 0 <= n -> zwrap n (zwrap n a * k) = zwrap n (a * k).
Proof.
  intros Hn. apply zwrap_congr; auto.
  pose proof (zwrap_divide_self n a Hn) as [p Hp].
  assert (Ea : zwrap n a = a + p * 2 ^ n) by lia. rewrite Ea. exists (p * k). nia.
Qed.

Lemma zwrap_mul_r n k a : 0 <= n -> zwrap n (k * zwrap n a) = zwrap n (k * a).
Proof.
  intros Hn. rewrite (Z.mul_comm k (zwrap n a)), (Z.mul_comm k a). now apply zwrap_mul_l.
Qed.

Lemma zwrap_shiftl n a k : 0 <= n -> 0 <= k -> zwrap n (Z.shiftl (zwrap n a) k) = zwrap n (a * 2 ^ k).
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. now apply zwrap_mul_l. Qed.

(* [comment removed for export] *)
Lemma zwrap_ltb n a b : 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> (zwrap n a <? zwrap n b) = (a <? b).
Proof. intros. now rewrite !zwrap_id. Qed.

Lemma zwrap_leb n a b : 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> (zwrap n a <=? zwrap n b) = (a <=? b).
Proof. intros. now rewrite !zwrap_id. Qed.

Lemma zwrap_eqb n a b : 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> (zwrap n a =? zwrap n b) = (a =? b).
Proof. intros. now rewrite !zwrap_id. Qed.

(* [comment removed for export] *)
Lemma zwrap_eqb_congr n a b : 0 <= n ->
  (zwrap n a =? zwrap n b) = true <-> (2 ^ n | a - b).
Proof. intros. rewrite Z.eqb_eq. now apply zwrap_eq_iff. Qed.

Lemma zwrap_neq_of_range n a b : 0 <= n ->
  0 < Z.abs (a - b) < 2 ^ n -> (zwrap n a =? zwrap n b) = false.
Proof.
  intros Hn Hab. destruct (Z.eqb_spec (zwrap n a) (zwrap n b)) as [E|E]; auto.
  exfalso. apply (zwrap_eq_iff n a b Hn) in E. destruct E as [q Hq].
  pose proof (pow2_pos n Hn). assert (q = 0 \/ q >= 1 \/ q <= -1) by lia. nia.
Qed.

(* [comment removed for export] *)
Lemma zwrap_neq_pos n a b : 0 <= n -> 0 < a - b < 2 ^ n -> zwrap n a <> zwrap n b.
Proof.
  intros Hn H E. pose proof (zwrap_neq_of_range n a b Hn ltac:(lia)) as X.
  rewrite E, Z.eqb_refl in X. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zwrap_trunc w n z : 0 <= w <= n -> zwrap w (zwrap n z) = zwrap w z.
Proof. apply zwrap_zwrap. Qed.

(* [comment removed for export] *)
Lemma zwrap_widen w n z : 0 <= w <= n -> zwrap n (zwrap w z) = zwrap w z.
Proof.
  intros. apply zwrap_id. pose proof (zwrap_range w z ltac:(lia)). pose proof (pow2_le w n ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma land_ones_zwrap k a : 0 <= k -> 0 <= a -> Z.land a (Z.ones k) = zwrap k a.
Proof. intros. unfold zwrap. now rewrite Z.land_ones. Qed.

Lemma land_mask_zwrap k a : 0 <= k -> Z.land a (2 ^ k - 1) = zwrap k a.
Proof.
  intros. replace (2 ^ k - 1) with (Z.ones k).
  - unfold zwrap. now rewrite Z.land_ones.
  - unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma land_mask_zwrap64 k a : 0 <= k <= 64 -> Z.land (zwrap 64 a) (2 ^ k - 1) = zwrap k a.
Proof. intros. rewrite land_mask_zwrap by lia. apply zwrap_zwrap. lia. Qed.

(* [comment removed for export] *)
Lemma align_down_spec k z : 0 <= k ->
  let y := z - zwrap k z in (2 ^ k | y) /\ z - 2 ^ k < y <= z.
Proof.
  intros Hk. cbn. pose proof (zwrap_range k z Hk). split; [|lia].
  pose proof (zwrap_divide_self k z Hk) as [p Hp]. exists (- p). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zswrap_range n z : 0 < n -> - 2 ^ (n - 1) <= zswrap n z < 2 ^ (n - 1).
Proof.
  intros. unfold zswrap. pose proof (pow2_half n H).
  pose proof (Z.mod_pos_bound (z + 2 ^ (n - 1)) (2 ^ n) ltac:(apply pow2_pos; lia)). lia.
Qed.

Lemma zswrap_divide_self n z : 0 < n -> (2 ^ n | zswrap n z - z).
Proof.
  intros. unfold zswrap.
  pose proof (zwrap_divide_self n (z + 2 ^ (n - 1)) ltac:(lia)) as [p Hp]. unfold zwrap in Hp.
  exists p. lia.
Qed.

Lemma zswrap_id n z : 0 < n -> - 2 ^ (n - 1) <= z < 2 ^ (n - 1) -> zswrap n z = z.
Proof.
  intros Hn Hz. unfold zswrap. pose proof (pow2_half n Hn).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma zswrap_congr n a b : 0 < n -> (2 ^ n | a - b) -> zswrap n a = zswrap n b.
Proof.
  intros Hn Hd. unfold zswrap. f_equal.
  change ((a + 2 ^ (n - 1)) mod 2 ^ n) with (zwrap n (a + 2 ^ (n - 1))).
  change ((b + 2 ^ (n - 1)) mod 2 ^ n) with (zwrap n (b + 2 ^ (n - 1))).
  apply zwrap_congr; [lia|]. destruct Hd as [q Hq]; exists q; lia.
Qed.

Lemma zswrap_zwrap n m z : 0 < n <= m -> zswrap n (zwrap m z) = zswrap n z.
Proof.
  intros. apply zswrap_congr; [lia|].
  pose proof (zwrap_divide_self m z ltac:(lia)) as [p Hp].
  pose proof (pow2_divide n m ltac:(lia)) as [q Hq].
  exists (p * q). lia.
Qed.

(* [comment removed for export] *)
Lemma zswrap_zwrap_id n e : 0 < n -> - 2 ^ (n - 1) <= e < 2 ^ (n - 1) -> zswrap n (zwrap n e) = e.
Proof. intros. rewrite zswrap_zwrap by lia. now apply zswrap_id. Qed.

(* [comment removed for export] *)
Lemma zswrap_of_small_unsigned n e : 0 < n -> 0 <= e < 2 ^ (n - 1) -> zswrap n (zwrap n e) = e.
Proof. intros. apply zswrap_zwrap_id; lia. Qed.

Lemma zwrap_of_zswrap n z : 0 < n -> zwrap n (zswrap n z) = zwrap n z.
Proof.
  intros. apply zwrap_congr; [lia|]. now apply zswrap_divide_self.
Qed.

(* [comment removed for export] *)
Lemma zswrap_ltb n a b : 0 < n ->
  - 2 ^ (n - 1) <= a < 2 ^ (n - 1) -> - 2 ^ (n - 1) <= b < 2 ^ (n - 1) ->
  (zswrap n (zwrap n a) <? zswrap n (zwrap n b)) = (a <? b).
Proof. intros. now rewrite !zswrap_zwrap_id. Qed.

Lemma zswrap_leb n a b : 0 < n ->
  - 2 ^ (n - 1) <= a < 2 ^ (n - 1) -> - 2 ^ (n - 1) <= b < 2 ^ (n - 1) ->
  (zswrap n (zwrap n a) <=? zswrap n (zwrap n b)) = (a <=? b).
Proof. intros. now rewrite !zswrap_zwrap_id. Qed.

(* [comment removed for export] *)
Lemma wop_exact x : - 2 ^ 31 <= x < 2 ^ 31 -> zwrap 64 (zswrap 32 (zwrap 64 x)) = zwrap 64 x.
Proof.
  intros. rewrite zswrap_zwrap by lia. rewrite zswrap_id by (try lia; simpl; lia). reflexivity.
Qed.

Lemma wop_exact32 x : - 2 ^ 31 <= x < 2 ^ 31 -> zwrap 64 (zswrap 32 (zwrap 32 x)) = zwrap 64 x.
Proof.
  intros. rewrite zswrap_zwrap by lia. rewrite zswrap_id by (try lia; simpl; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wop_congr x : (2 ^ 32 | zswrap 32 (zwrap 64 x) - x).
Proof.
  pose proof (zswrap_divide_self 32 (zwrap 64 x) ltac:(lia)) as [p Hp].
  pose proof (zwrap_divide_self 64 x ltac:(lia)) as [q Hq].
  exists (p + q * 2 ^ 32). change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in Hq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma remu_bounds a b : 0 <= a -> 0 < b -> 0 <= a mod b < b /\ a mod b <= a.
Proof.
  intros. pose proof (Z.mod_pos_bound a b H0). split; auto.
  apply Z.mod_le; lia.
Qed.

Lemma divu_bounds a b : 0 <= a -> 0 < b -> 0 <= a / b <= a.
Proof.
  intros. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma shiftr_bounds a k : 0 <= a -> 0 <= k -> 0 <= Z.shiftr a k <= a /\ Z.shiftr a k = a / 2 ^ k.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos k H0).
  split; [|reflexivity]. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|nia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma M64_eq : M64 = 18446744073709551616. Proof. reflexivity. Qed.
Lemma M32_eq : M32 = 4294967296. Proof. reflexivity. Qed.

Lemma zwrap64_add a b : zwrap 64 (zwrap 64 a + zwrap 64 b) = zwrap 64 (a + b).
Proof. apply zwrap_add; lia. Qed.
Lemma zwrap64_add_l a b : zwrap 64 (zwrap 64 a + b) = zwrap 64 (a + b).
Proof. apply zwrap_add_l; lia. Qed.
Lemma zwrap64_add_r a b : zwrap 64 (a + zwrap 64 b) = zwrap 64 (a + b).
Proof. apply zwrap_add_r; lia. Qed.
Lemma zwrap64_sub a b : zwrap 64 (zwrap 64 a - zwrap 64 b) = zwrap 64 (a - b).
Proof. apply zwrap_sub; lia. Qed.
Lemma zwrap64_mul a b : zwrap 64 (zwrap 64 a * zwrap 64 b) = zwrap 64 (a * b).
Proof. apply zwrap_mul; lia. Qed.
Lemma zwrap64_mul_l a k : zwrap 64 (zwrap 64 a * k) = zwrap 64 (a * k).
Proof. apply zwrap_mul_l; lia. Qed.
Lemma zwrap64_id a : 0 <= a < 2 ^ 64 -> zwrap 64 a = a.
Proof. apply zwrap_id. Qed.
Lemma zwrap64_idem a : zwrap 64 (zwrap 64 a) = zwrap 64 a.
Proof. apply zwrap_idem; lia. Qed.
Lemma zwrap64_range a : 0 <= zwrap 64 a < 2 ^ 64.
Proof. apply zwrap_range; lia. Qed.
Lemma zswrap64_id a : - 2 ^ 63 <= a < 2 ^ 63 -> zswrap 64 (zwrap 64 a) = a.
Proof. intros; apply zswrap_zwrap_id; simpl; lia. Qed.
Lemma zwrap64_ltb a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (zwrap 64 a <? zwrap 64 b) = (a <? b).
Proof. apply zwrap_ltb. Qed.
Lemma zwrap64_eqb a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (zwrap 64 a =? zwrap 64 b) = (a =? b).
Proof. apply zwrap_eqb. Qed.
Lemma zswrap64_ltb a b : - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  (zswrap 64 (zwrap 64 a) <? zswrap 64 (zwrap 64 b)) = (a <? b).
Proof. intros; apply zswrap_ltb; simpl; lia. Qed.
Lemma zwrap8_of_64 z : zwrap 8 (zwrap 64 z) = zwrap 8 z.   Proof. apply zwrap_zwrap; lia. Qed.
Lemma zwrap16_of_64 z : zwrap 16 (zwrap 64 z) = zwrap 16 z. Proof. apply zwrap_zwrap; lia. Qed.
Lemma zwrap32_of_64 z : zwrap 32 (zwrap 64 z) = zwrap 32 z. Proof. apply zwrap_zwrap; lia. Qed.

(* [comment removed for export] *)
Definition C64 : Z := 18446744073709551616.
Definition wrap64 (x : Z) : Z := if (0 <=? x) && (x <? C64) then x else x mod C64.

Lemma C64_eq : C64 = 2 ^ 64. Proof. reflexivity. Qed.

Lemma wrap64_zwrap x : wrap64 x = zwrap 64 x.
Proof.
  unfold wrap64, zwrap. rewrite C64_eq.
  destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x (2 ^ 64)); simpl; try reflexivity.
  symmetry. apply Z.mod_small. lia.
Qed.
