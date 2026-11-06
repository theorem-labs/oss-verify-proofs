(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Spec/StrWin.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Spec/StrWin.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Spec/StrWin.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

Lemma sw_skipn_map : forall {A B} (f : A -> B) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros A B f n. induction n as [|n IH]; intros [|x l]; cbn; auto. Qed.

Lemma sw_skipn_nth : forall {A} (l : list A) j x, nth_error l j = Some x -> skipn j l = x :: skipn (S j) l.
Proof.
  intros A l. induction l as [|y l IH]; intros [|j] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma sw_prefix_len : forall nd h, prefix_eqb nd h = true -> (length nd <= length h)%nat.
Proof.
  induction nd as [|a nd IH]; intros [|b h] H; cbn in H |- *; try lia; try discriminate.
  apply andb_prop in H. destruct H as [_ H]. apply IH in H. lia.
Qed.

Lemma sw_prefix_short : forall nd h, (length h < length nd)%nat -> prefix_eqb nd h = false.
Proof. intros nd h H. destruct (prefix_eqb nd h) eqn:E; [|reflexivity]. apply sw_prefix_len in E. lia. Qed.

Lemma sw_ff_head : forall h nd, prefix_eqb nd h = true -> find_first h nd = Some 0%nat.
Proof. intros [|x h] nd E; cbn [find_first]; rewrite E; reflexivity. Qed.

Lemma sw_ff_skip : forall i h nd, (forall k, (k < i)%nat -> prefix_eqb nd (skipn k h) = false) ->
  find_first h nd = option_map (Nat.add i) (find_first (skipn i h) nd).
Proof.
  induction i as [|i IH]; intros h nd H.
  - change (skipn 0 h) with h. destruct (find_first h nd); reflexivity.
  - pose proof (H 0%nat ltac:(lia)) as H0. change (skipn 0 h) with h in H0.
    destruct h as [|x h].
    + change (skipn (S i) []) with (@nil Z). cbn [find_first]. rewrite H0. reflexivity.
    + change (skipn (S i) (x :: h)) with (skipn i h). cbn [find_first]. rewrite H0.
      rewrite (IH h nd) by (intros k Hk; exact (H (S k) ltac:(lia))).
      destruct (find_first (skipn i h) nd); reflexivity.
Qed.

Lemma sw_ff_none : forall h nd, (forall k, (k <= length h)%nat -> prefix_eqb nd (skipn k h) = false) ->
  find_first h nd = None.
Proof.
  intros h nd H. rewrite (sw_ff_skip (length h) h nd) by (intros k Hk; apply H; lia).
  pose proof (H (length h) ltac:(lia)) as E. rewrite skipn_all in E |- *.
  cbn [find_first]. rewrite E. reflexivity.
Qed.

Lemma sw_ff_found : forall j h nd, (forall k, (k < j)%nat -> prefix_eqb nd (skipn k h) = false) ->
  prefix_eqb nd (skipn j h) = true -> find_first h nd = Some j.
Proof. intros j h nd H E. rewrite (sw_ff_skip j h nd H), (sw_ff_head _ _ E). cbn. f_equal. lia. Qed.

Lemma sw_ff_short : forall h nd, (length h < length nd)%nat -> find_first h nd = None.
Proof. intros h nd H. apply sw_ff_none. intros k Hk. apply sw_prefix_short. rewrite length_skipn. lia. Qed.

Lemma sw_prefix_head : forall (b0 : byte) nb' (t : list byte) k,
  (forall x, nth_error t k = Some x -> bv_unsigned x <> bv_unsigned b0) ->
  prefix_eqb (map bv_unsigned (b0 :: nb')) (skipn k (map bv_unsigned t)) = false.
Proof.
  intros b0 nb' t k H. rewrite sw_skipn_map. destruct (nth_error t k) as [x|] eqn:E.
  - rewrite (sw_skipn_nth t k x E). cbn [map prefix_eqb].
    replace (bv_unsigned b0 =? bv_unsigned x) with false
      by (symmetry; apply Z.eqb_neq; intros Hc; exact (H x eq_refl (eq_sym Hc))).
    reflexivity.
  - rewrite skipn_all2 by (apply nth_error_None; exact E). reflexivity.
Qed.

Lemma sw_win2 : forall (b0 b1 x y : byte) (t : list byte) k, nth_error t k = Some x -> nth_error t (S k) = Some y ->
  (prefix_eqb (map bv_unsigned [b0; b1]) (skipn k (map bv_unsigned t)) = true <->
   bv_unsigned x = bv_unsigned b0 /\ bv_unsigned y = bv_unsigned b1).
Proof.
  intros b0 b1 x y t k Ex Ey. rewrite sw_skipn_map, (sw_skipn_nth t k x Ex), (sw_skipn_nth t (S k) y Ey).
  cbn [map prefix_eqb]. rewrite !andb_true_iff, !Z.eqb_eq.
  split; [intros (H1 & H2 & _); lia | intros (H1 & H2); split; [lia | split; [lia | reflexivity]]].
Qed.

Lemma sw_win3 : forall (b0 b1 b2 x y z : byte) (t : list byte) k, nth_error t k = Some x -> nth_error t (S k) = Some y ->
  nth_error t (S (S k)) = Some z ->
  (prefix_eqb (map bv_unsigned [b0; b1; b2]) (skipn k (map bv_unsigned t)) = true <->
   bv_unsigned x = bv_unsigned b0 /\ bv_unsigned y = bv_unsigned b1 /\ bv_unsigned z = bv_unsigned b2).
Proof.
  intros b0 b1 b2 x y z t k Ex Ey Ez.
  rewrite sw_skipn_map, (sw_skipn_nth t k x Ex), (sw_skipn_nth t (S k) y Ey), (sw_skipn_nth t (S (S k)) z Ez).
  cbn [map prefix_eqb]. rewrite !andb_true_iff, !Z.eqb_eq.
  split; [intros (H1 & H2 & H3 & _); lia | intros (H1 & H2 & H3); split; [lia | split; [lia | split; [lia | reflexivity]]]].
Qed.

Lemma sw_val_shift : forall A (hb nb : list byte) (b0 : byte) nb' i,
  nb = b0 :: nb' -> find_byte (bv_unsigned b0) hb = Some i ->
  strstr_val A hb nb = strstr_val (A + Z.of_nat i) (skipn i hb) nb.
Proof.
  intros A hb nb b0 nb' i -> F. destruct (find_byte_Some _ _ _ F) as (Hi & _ & Hb).
  unfold strstr_val. rewrite (sw_ff_skip i (map bv_unsigned hb)).
  - rewrite sw_skipn_map. destruct (find_first _ _); cbn; lia.
  - intros k Hk. apply sw_prefix_head. intros x Ex. exact (Hb k x Hk Ex).
Qed.

Lemma sw_val_none : forall A (hb nb : list byte) (b0 : byte) nb',
  nb = b0 :: nb' -> find_byte (bv_unsigned b0) hb = None -> strstr_val A hb nb = 0.
Proof.
  intros A hb nb b0 nb' -> F. unfold strstr_val. rewrite sw_ff_none; [reflexivity|].
  intros k Hk. apply sw_prefix_head. intros x Ex. exact (find_byte_None _ _ F k x Ex).
Qed.

Lemma sw_val_one : forall A (t : list byte) c0 t' (b0 : byte),
  t = c0 :: t' -> bv_unsigned c0 = bv_unsigned b0 -> strstr_val A t [b0] = A.
Proof.
  intros A t c0 t' b0 -> E. unfold strstr_val. cbn [map]. rewrite sw_ff_head; [lia|].
  cbn [prefix_eqb]. rewrite E, Z.eqb_refl. reflexivity.
Qed.

Lemma sw_val_short : forall A (t nb : list byte), (length t < length nb)%nat -> strstr_val A t nb = 0.
Proof. intros A t nb H. unfold strstr_val. rewrite sw_ff_short; [reflexivity|]. rewrite !length_map. exact H. Qed.

Lemma sw_val_found : forall A (t nb : list byte) j,
  (forall k, (k < j)%nat -> prefix_eqb (map bv_unsigned nb) (skipn k (map bv_unsigned t)) = false) ->
  prefix_eqb (map bv_unsigned nb) (skipn j (map bv_unsigned t)) = true ->
  strstr_val A t nb = A + Z.of_nat j.
Proof. intros A t nb j H E. unfold strstr_val. rewrite (sw_ff_found j _ _ H E). reflexivity. Qed.

Lemma sw_val_none_all : forall A (t nb : list byte),
  (forall k, (k <= length t)%nat -> prefix_eqb (map bv_unsigned nb) (skipn k (map bv_unsigned t)) = false) ->
  strstr_val A t nb = 0.
Proof. intros A t nb H. unfold strstr_val. rewrite sw_ff_none; [reflexivity|]. rewrite length_map. exact H. Qed.

Lemma sw_short_at : forall (t nb : list byte) k, (0 < length nb)%nat -> (length t < k + length nb)%nat ->
  prefix_eqb (map bv_unsigned nb) (skipn k (map bv_unsigned t)) = false.
Proof. intros t nb k H0 H. apply sw_prefix_short. rewrite length_skipn, !length_map. lia. Qed.

Lemma sw_nz : forall (t : list byte) j b, ~ In (Z_to_bv 8 0) t -> nth_error t j = Some b -> bv_unsigned b <> 0.
Proof.
  intros t j b NZ E Hb. apply NZ. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|].
  apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma sw_nth_full : forall (t hs : list byte) j, (j <= length t)%nat ->
  exists b, nth_error (t ++ Z_to_bv 8 0 :: hs) j = Some b /\
    ((j < length t)%nat -> nth_error t j = Some b) /\ (j = length t -> b = Z_to_bv 8 0).
Proof.
  intros t hs j Hj. destruct (Nat.eq_dec j (length t)) as [->|NE].
  - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat.sub_diag by lia. split; [reflexivity|]. split; [lia|]. auto.
  - destruct (nth_error t j) as [b|] eqn:E.
    + exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [auto|]. lia.
    + apply nth_error_None in E. lia.
Qed.

Lemma sw_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. Qed.

Lemma sw_land255 : forall b : byte, Z.land (bv_unsigned b) 255 = bv_unsigned b.
Proof.
  intros b. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (sw_byte_range b). change (2 ^ 8) with 256. lia.
Qed.

Lemma sw_lor_add : forall a c k, 0 <= k -> 0 <= c < 2^k -> Z.lor (a * 2^k) c = a * 2^k + c.
Proof.
  intros a c k Hk Hc.
  assert (L : Z.land (Z.shiftl a k) c = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    - rewrite Z.testbit_neg_r by lia. reflexivity.
    - replace (Z.testbit c i) with false; [apply andb_false_r|].
      symmetry. rewrite <- (Z.mod_small c (2^k)) by lia. apply Z.mod_pow2_bits_high. lia. }
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite <- Z.lxor_lor by exact L.
  rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma sw_lor8 : forall a c, 0 <= c < 256 -> Z.lor (a * 256) c = a * 256 + c.
Proof. intros a c Hc. change 256 with (2^8). apply sw_lor_add; lia. Qed.

Lemma sw_lor16 : forall a c, 0 <= c < 65536 -> Z.lor (a * 65536) c = a * 65536 + c.
Proof. intros a c Hc. change 65536 with (2^16). apply sw_lor_add; lia. Qed.

Lemma sw_lor24 : forall a c, 0 <= c < 16777216 -> Z.lor (a * 16777216) c = a * 16777216 + c.
Proof. intros a c Hc. change 16777216 with (2^24). apply sw_lor_add; lia. Qed.

Lemma sw_mod256 : forall a b, 0 <= b < 256 -> (a * 256 + b) mod 256 = b.
Proof. intros a b Hb. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. exact Hb. Qed.

Lemma sw_w2_entry : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (Z.shiftl x 8 mod 18446744073709551616) y = x * 256 + y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_small by lia. apply sw_lor8. exact Hy.
Qed.

Lemma sw_w2_loop : forall W y, 0 <= W -> 0 <= y < 256 ->
  Z.lor (Z.shiftr (Z.shiftl W 56 mod 18446744073709551616) 48) y = (W mod 256) * 256 + y.
Proof.
  intros W y HW Hy. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^56) with 72057594037927936. change (2^48) with 281474976710656.
  change 18446744073709551616 with (256 * 72057594037927936).
  rewrite Z.mul_mod_distr_r by lia.
  replace (W mod 256 * 72057594037927936) with (W mod 256 * 256 * 281474976710656) by lia.
  rewrite Z.div_mul by lia. apply sw_lor8. exact Hy.
Qed.

Definition w3 (x y z : Z) : Z :=
  (if x <? 128 then 0 else 18446744069414584320) + x * 16777216 + y * 65536 + z * 256.

Lemma sw_w3_entry : forall x y z, 0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 ->
  Z.lor (Z.lor (Z.shiftl z 8 mod 18446744073709551616) (Z.shiftl y 16 mod 18446744073709551616))
        (bv_swrap 32 (Z.shiftl x 24) mod 18446744073709551616) = w3 x y z.
Proof.
  intros x y z Hx Hy Hz. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite (Z.mod_small (z * 256)), (Z.mod_small (y * 65536)) by lia.
  assert (E : bv_swrap 32 (x * 16777216) mod 18446744073709551616
              = ((if x <? 128 then 0 else 1099511627520) + x) * 16777216).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    destruct (Z.ltb_spec x 128); Z.div_mod_to_equations; lia. }
  rewrite E, Z.lor_comm, (Z.lor_comm (z * 256)), sw_lor16 by lia. rewrite sw_lor24 by lia.
  unfold w3. destruct (x <? 128); lia.
Qed.

Lemma sw_w3_loop : forall x y z w, 0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 -> 0 <= w < 256 ->
  bv_swrap 32 (Z.shiftl (Z.lor (w3 x y z) w) 8) mod 18446744073709551616 = w3 y z w.
Proof.
  intros x y z w Hx Hy Hz Hw.
  assert (E : Z.lor (w3 x y z) w = w3 x y z + w).
  { unfold w3.
    replace ((if x <? 128 then 0 else 18446744069414584320) + x * 16777216 + y * 65536 + z * 256)
      with (((if x <? 128 then 0 else 72057594021150720) + x * 65536 + y * 256 + z) * 256)
      by (destruct (x <? 128); lia).
    apply sw_lor8. exact Hw. }
  rewrite E, Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  unfold w3. destruct (Z.ltb_spec x 128); destruct (Z.ltb_spec y 128); Z.div_mod_to_equations; lia.
Qed.

Lemma sw_w3_inj : forall x y z x' y' z', 0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 ->
  0 <= x' < 256 -> 0 <= y' < 256 -> 0 <= z' < 256 ->
  (w3 x y z = w3 x' y' z' <-> x = x' /\ y = y' /\ z = z').
Proof. intros. unfold w3. destruct (Z.ltb_spec x 128); destruct (Z.ltb_spec x' 128); split; intros; lia. Qed.

Lemma sw_w3_range : forall x y z, 0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 -> 0 <= w3 x y z < 18446744073709551616.
Proof. intros. unfold w3. destruct (Z.ltb_spec x 128); lia. Qed.

Lemma sw_mask77 : forall v X, 0 <= v -> 0 <= X < 18446744073709551616 ->
  Z.land ((Z.b2z (v <? 1) + -1) mod 18446744073709551616) X = if v =? 0 then 0 else X.
Proof.
  intros v X Hv HX. destruct (Z.ltb_spec v 1); destruct (Z.eqb_spec v 0); try lia; cbn [Z.b2z].
  - change ((1 + -1) mod 18446744073709551616) with 0. apply Z.land_0_l.
  - change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. change (2^64) with 18446744073709551616. lia.
Qed.
