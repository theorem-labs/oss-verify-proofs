(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt CkMultmodp CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkA Require Import CrcAGlue.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition bzp (bs : list Z) (i : Z) : Z := nth (Z.to_nat i) bs 0.

Lemma skipn_bzp : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  skipn (Z.to_nat i) bs = bzp bs i :: skipn (Z.to_nat (i + 1)) bs.
Proof.
  intros bs i Hi. unfold bzp. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (G : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l).
  { induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
  apply G. lia.
Qed.

Definition wdp (bs : list Z) (i : Z) : Z := wle (bzp bs i) (bzp bs (i + 1)) (bzp bs (i + 2)) (bzp bs (i + 3)).

Lemma bzp_range : forall bs i, bytes bs -> 0 <= bzp bs i < 256.
Proof.
  intros bs i F. unfold bzp.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [L|L].
  - apply (proj1 (Forall_forall _ _) F). apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma wdp_range : forall bs i, bytes bs -> 0 <= wdp bs i < 2^32.
Proof. intros bs i F. unfold wdp. apply wle_range; apply bzp_range; exact F. Qed.

Lemma firstn_S_skipn : forall bs n j, 0 <= j < Z.of_nat (length bs) ->
  firstn (S n) (skipn (Z.to_nat j) bs) = bzp bs j :: firstn n (skipn (Z.to_nat (j + 1)) bs).
Proof. intros bs n j Hj. rewrite (skipn_bzp bs j Hj). reflexivity. Qed.

Lemma block20_words : forall bs i, 0 <= i -> i + 20 <= Z.of_nat (length bs) ->
  words_le (firstn 20 (skipn (Z.to_nat i) bs)) = [wdp bs i; wdp bs (i + 4); wdp bs (i + 8); wdp bs (i + 12); wdp bs (i + 16)].
Proof.
  intros bs i Hi Hl.
  do 20 (rewrite firstn_S_skipn by lia).
  cbn [firstn words_le]. unfold wdp.
  repeat (f_equal; try lia).
Qed.


Definition braid_from (c : Z) (bs1 : list Z) : Z * list Z :=
  let blks := Zlen bs1 / 20 in
  let cs := braid_state [c; 0; 0; 0; 0] (Z.to_nat (blks - 1)) bs1 in
  (braid_last cs (block (Z.to_nat (blks - 1)) bs1), skipn (Z.to_nat (20 * blks)) bs1).

Definition crcz_from (adr c : Z) (bs : list Z) (i : Z) : Z :=
  let na := align4 (adr + i) in
  let c' := crc_bytes c (firstn (Z.to_nat na) (skipn (Z.to_nat i) bs)) in
  let r := braid_from c' (skipn (Z.to_nat (i + na)) bs) in
  Z.lxor (crc_bytes (fst r) (snd r)) M32.

Lemma crcz_from_0 : forall adr c bs, 23 <= Zlen bs ->
  crc32_z_model adr c bs = crcz_from adr (crc_pre c) bs 0.
Proof.
  intros adr c bs H. rewrite crc32_z_model_mid, crc_mid_long by exact H.
  unfold crcz_from. rewrite Z.add_0_r. cbn [Z.to_nat skipn]. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma crcz_from_step : forall adr c bs i, 0 <= adr -> 0 <= i < Z.of_nat (length bs) -> (adr + i) mod 4 <> 0 ->
  crcz_from adr c bs i = crcz_from adr (crc_byte c (bzp bs i)) bs (i + 1).
Proof.
  intros adr c bs i Ha Hi Hm. unfold crcz_from.
  rewrite (align4_step (adr + i)) by lia. replace (adr + i + 1) with (adr + (i + 1)) by lia.
  pose proof (align4_spec (adr + (i + 1)) ltac:(lia)) as (_ & R & _).
  set (na := align4 (adr + (i + 1))) in *.
  replace (Z.to_nat (1 + na)) with (S (Z.to_nat na)) by lia.
  rewrite (skipn_bzp bs i) by lia. cbn [firstn]. rewrite crc_bytes_cons.
  replace (i + (1 + na)) with (i + 1 + na) by lia. reflexivity.
Qed.

Lemma crcz_from_aligned : forall adr c bs i, (adr + i) mod 4 = 0 ->
  crcz_from adr c bs i = (let r := braid_from c (skipn (Z.to_nat i) bs) in Z.lxor (crc_bytes (fst r) (snd r)) M32).
Proof.
  intros adr c bs i Hm. unfold crcz_from. rewrite (align4_0 _ Hm). cbn [Z.to_nat firstn]. rewrite crc_bytes_nil, Z.add_0_r. reflexivity.
Qed.


Lemma land_255_low32 : forall y, Z.land y 255 = Z.land (y mod 2^32) 255.
Proof.
  intros y. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.ltb_spec n 8) as [L|L].
  - rewrite testbit_mod32 by lia. reflexivity.
  - replace (Z.testbit 255 n) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. change 255 with (Z.ones 8). apply Z.ones_spec_high. lia.
Qed.

Lemma land_shiftr_255_low32 : forall y k, 0 <= k -> k + 8 <= 32 ->
  Z.land (Z.shiftr y k) 255 = Z.land (Z.shiftr (y mod 2^32) k) 255.
Proof.
  intros y k Hk Hk8. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite testbit_mod32 by lia. reflexivity.
  - replace (Z.testbit 255 n) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. change 255 with (Z.ones 8). apply Z.ones_spec_high. lia.
Qed.

Lemma land_1020_shiftr : forall y k, 2 <= k ->
  Z.land (Z.shiftr y (k - 2)) 1020 = Z.land (Z.shiftr y k) 255 * 4.
Proof.
  intros y k Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  change 4 with (2 ^ 2). rewrite Z.mul_pow2_bits by lia.
  destruct (Z.ltb_spec n 2).
  - replace (Z.testbit 1020 n) with false.
    + rewrite andb_false_r. rewrite Z.testbit_neg_r by lia. reflexivity.
    + assert (E : n = 0 \/ n = 1) by lia. destruct E as [-> | ->]; reflexivity.
  - rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (n - 2 + k) with (n + (k - 2)) by lia. f_equal.
    change 1020 with (255 * 2 ^ 2). rewrite Z.mul_pow2_bits by lia. reflexivity.
Qed.

Lemma shiftr24_low32_range : forall y, 0 <= Z.shiftr (y mod 2^32) 24 < 256.
Proof. intros y. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma land_255_small : forall a, 0 <= a < 256 -> Z.land a 255 = a.
Proof. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma srliw_form : forall y k, 0 < k < 32 -> bv_swrap 32 (bv_wrap 32 y ≫ k) = (y mod 4294967296) ≫ k.
Proof.
  intros y k Hk. rewrite wrap32_eq. change (2^32) with 4294967296. apply swrap32_small.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (P : 2 <= 2 ^ k) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound y 4294967296 ltac:(lia)) as M.
  split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. change (2^31) with 2147483648. nia.
Qed.

Lemma ctab_addr_form : forall y, 135264 + 4 * Z.land y 255 = 135264 + Z.land y 255 ≪ 2.
Proof. intros y. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. ring. Qed.

Lemma srliw8_form : forall y, bv_swrap 32 (bv_wrap 32 y ≫ 8) = (y mod 4294967296) ≫ 8.
Proof. intros y. apply srliw_form. lia. Qed.

Lemma ctab_range64 : forall i, 0 <= ctab i < 2^64.
Proof. intros i. pose proof (ctab_range i). lia. Qed.

Lemma btab_range64 : forall k i, 0 <= btab k i < 2^64.
Proof. intros k i. pose proof (btab_range k i). lia. Qed.

Lemma wdp_range64 : forall bs i, bytes bs -> 0 <= wdp bs i < 2^64.
Proof. intros bs i F. pose proof (wdp_range bs i F). lia. Qed.

Lemma d_len : forall n1 blks r, n1 - 20 * blks = r ->
  Z_to_bv 64 r = Z_to_bv 64 (blks * 18446744073709551596 + n1).
Proof.
  intros n1 blks r H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite <- H.
  replace (blks * 18446744073709551596 + n1) with (n1 - 20 * blks + blks * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition dY0 (w x : Z) : Z := Z.lxor (sxz w) x.

Lemma dY0_range : forall w x, 0 <= x < 2^64 -> 0 <= dY0 w x < 2^64.
Proof. intros w x Hx. unfold dY0. apply lxor_range64; [apply sxz_range| exact Hx]. Qed.

Lemma dY0_mod32 : forall w x, 0 <= w < 2^32 -> dY0 w x mod 2^32 = Z.lxor (x mod 2^32) w.
Proof. intros w x Hw. unfold dY0. rewrite lxor_mod32, sxz_mod32, (Z.mod_small w) by lia. apply Z.lxor_comm. Qed.


Definition dY1 (y : Z) : Z := Z.lxor ((y mod 4294967296) ≫ 8) (sxz (ctab (Z.land y 255))).

Definition dYn (y x w : Z) : Z :=
  Z.lxor (Z.lxor (sxz (ctab (Z.land y 255))) x) (Z.lxor (sxz w) ((y mod 4294967296) ≫ 8)).

Definition dYf (y : Z) : Z := Z.lxor ((y mod 4294967296) ≫ 8) (ctab (Z.land y 255)).

Lemma dY0_unfold : forall w x, dY0 w x = Z.lxor (sxz w) x. Proof. reflexivity. Qed.
Lemma dY1_unfold : forall y, dY1 y = Z.lxor ((y mod 4294967296) ≫ 8) (sxz (ctab (Z.land y 255))). Proof. reflexivity. Qed.
Lemma dYn_unfold : forall y x w, dYn y x w = Z.lxor (Z.lxor (sxz (ctab (Z.land y 255))) x) (Z.lxor (sxz w) ((y mod 4294967296) ≫ 8)).
Proof. reflexivity. Qed.
Lemma dYf_unfold : forall y, dYf y = Z.lxor ((y mod 4294967296) ≫ 8) (ctab (Z.land y 255)). Proof. reflexivity. Qed.

Lemma shr8_low_range : forall y, 0 <= (y mod 4294967296) ≫ 8 < 2^24.
Proof. intros y. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma dY1_range : forall y, 0 <= dY1 y < 2^64.
Proof. intros y. unfold dY1. pose proof (shr8_low_range y). apply lxor_range64; [lia| apply sxz_range]. Qed.

Lemma dY1_mod32 : forall y, dY1 y mod 2^32 = crc_word1 (y mod 2^32).
Proof.
  intros y. unfold dY1, crc_word1. rewrite lxor_mod32, sxz_mod32.
  pose proof (shr8_low_range y). rewrite (Z.mod_small (_ ≫ 8)) by lia.
  rewrite (Z.mod_small (ctab _)) by apply ctab_range. rewrite <- land_255_low32. reflexivity.
Qed.

Lemma dYn_range : forall y x w, 0 <= x < 2^64 -> 0 <= dYn y x w < 2^64.
Proof.
  intros y x w Hx. unfold dYn. pose proof (shr8_low_range y).
  apply lxor_range64; apply lxor_range64; try apply sxz_range; lia.
Qed.

Lemma dYn_mod32 : forall y x w, 0 <= w < 2^32 ->
  dYn y x w mod 2^32 = Z.lxor (Z.lxor (x mod 2^32) w) (crc_word1 (y mod 2^32)).
Proof.
  intros y x w Hw. unfold dYn, crc_word1. rewrite !lxor_mod32, !sxz_mod32.
  pose proof (shr8_low_range y). rewrite (Z.mod_small (_ ≫ 8)) by lia.
  rewrite (Z.mod_small (ctab _)) by apply ctab_range. rewrite (Z.mod_small w) by lia.
  rewrite <- land_255_low32. change 4294967296 with (2^32).
  set (T := ctab (Z.land y 255)). set (X := x mod 2^32). set (S := (y mod 2^32) ≫ 8).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.lxor_spec.
  destruct (Z.testbit T n), (Z.testbit X n), (Z.testbit w n), (Z.testbit S n); reflexivity.
Qed.

Lemma dYf_eq : forall y, dYf y = crc_word1 (y mod 2^32).
Proof. intros y. unfold dYf, crc_word1. rewrite <- land_255_low32. reflexivity. Qed.

Lemma crc_word1_range32 : forall x, 0 <= x < 2^32 -> 0 <= crc_word1 x < 2^32.
Proof.
  intros x Hx. unfold crc_word1. apply lxor_range32; [|apply ctab_range].
  rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.


Definition bI0 (y : Z) : Z := Z.land y 255.
Definition bI1 (y : Z) : Z := Z.land (y ≫ 8) 255.
Definition bI2 (y : Z) : Z := Z.land (y ≫ 16) 255.
Definition bI3 (y : Z) : Z := (y mod 4294967296) ≫ 24.

Lemma bI0_range : forall y, 0 <= bI0 y < 256. Proof. intros. apply land255_range. Qed.
Lemma bI1_range : forall y, 0 <= bI1 y < 256. Proof. intros. apply land255_range. Qed.
Lemma bI2_range : forall y, 0 <= bI2 y < 256. Proof. intros. apply land255_range. Qed.
Lemma bI3_range : forall y, 0 <= bI3 y < 256. Proof. intros. apply shiftr24_low32_range. Qed.

Lemma braid_addr0 : forall y, 136544 + Z.land y 255 ≪ 2 = 136544 + 4 * (256 * 0 + bI0 y).
Proof. intros y. unfold bI0. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.
Lemma braid_addr1 : forall y, 136544 + Z.land (y ≫ 6) 1020 + 1024 = 136544 + 4 * (256 * 1 + bI1 y).
Proof. intros y. unfold bI1. change 6 with (8 - 2). rewrite (land_1020_shiftr y 8) by lia. lia. Qed.
Lemma braid_addr2 : forall y, 136544 + Z.land (y ≫ 14) 1020 + 2048 = 136544 + 4 * (256 * 2 + bI2 y).
Proof. intros y. unfold bI2. change 14 with (16 - 2). rewrite (land_1020_shiftr y 16) by lia. lia. Qed.
Lemma braid_addr3 : forall y, 136544 + ((y mod 4294967296) ≫ 24) ≪ 2 + 3072 = 136544 + 4 * (256 * 3 + bI3 y).
Proof. intros y. unfold bI3. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.

Definition dLane (y : Z) : Z :=
  Z.lxor (Z.lxor (Z.lxor (sxz (btab 0 (bI0 y))) (sxz (btab 1 (bI1 y)))) (sxz (btab 2 (bI2 y)))) (sxz (btab 3 (bI3 y))).

Lemma dLane_range : forall y, 0 <= dLane y < 2^64.
Proof. intros y. unfold dLane. repeat apply lxor_range64; apply sxz_range. Qed.

Lemma dLane_mod32 : forall w x, 0 <= w < 2^32 ->
  dLane (dY0 w x) mod 2^32 = braid1 (x mod 2^32) w.
Proof.
  intros w x Hw. unfold dLane, braid1. cbv zeta. rewrite !lxor_mod32, !sxz_mod32.
  rewrite !(Z.mod_small (btab _ _)) by apply btab_range.
  pose proof (dY0_mod32 w x Hw) as E. set (y := dY0 w x) in *.
  unfold bI0, bI1, bI2, bI3.
  rewrite (land_255_low32 y), (land_shiftr_255_low32 y 8), (land_shiftr_255_low32 y 16) by lia.
  change 4294967296 with (2^32). rewrite E.
  rewrite (land_255_small (_ ≫ 24)) by (rewrite <- E; apply shiftr24_low32_range).
  reflexivity.
Qed.

Ltac lxor_ac :=
  apply Z.bits_inj'; let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; rewrite !Z.lxor_spec;
  repeat match goal with |- context [Z.testbit ?t n] => let b := fresh "b" in set (b := Z.testbit t n); clearbody b end;
  repeat match goal with b : bool |- _ => destruct b end; reflexivity.

Definition dLaneM (y : Z) : Z :=
  Z.lxor (sxz (btab 3 (bI3 y))) (Z.lxor (sxz (btab 2 (bI2 y))) (Z.lxor (sxz (btab 1 (bI1 y))) (sxz (btab 0 (bI0 y))))).

Lemma dLaneM_eq : forall y, dLaneM y = dLane y.
Proof. intros y. unfold dLaneM, dLane. lxor_ac. Qed.

Lemma dLaneM_range : forall y, 0 <= dLaneM y < 2^64.
Proof. intros y. rewrite dLaneM_eq. apply dLane_range. Qed.

Lemma dLaneM_mod32 : forall w x, 0 <= w < 2^32 -> dLaneM (dY0 w x) mod 2^32 = braid1 (x mod 2^32) w.
Proof. intros w x Hw. rewrite dLaneM_eq. apply dLane_mod32. exact Hw. Qed.

Lemma srliw24_form : forall y, bv_swrap 32 (bv_wrap 32 y ≫ 24) = (y mod 4294967296) ≫ 24.
Proof. intros y. apply srliw_form. lia. Qed.

Lemma dLaneM_unfold : forall y, dLaneM y =
  Z.lxor (sxz (btab 3 (bI3 y))) (Z.lxor (sxz (btab 2 (bI2 y))) (Z.lxor (sxz (btab 1 (bI1 y))) (sxz (btab 0 (bI0 y))))).
Proof. reflexivity. Qed.


Lemma block_skipn_words : forall bs i0 t, 0 <= i0 -> 0 <= t -> i0 + 20 * t + 20 <= Z.of_nat (length bs) ->
  words_le (block (Z.to_nat t) (skipn (Z.to_nat i0) bs))
  = [wdp bs (i0 + 20 * t); wdp bs (i0 + 20 * t + 4); wdp bs (i0 + 20 * t + 8); wdp bs (i0 + 20 * t + 12); wdp bs (i0 + 20 * t + 16)].
Proof.
  intros bs i0 t Hi Ht Hl. unfold block. rewrite skipn_skipn.
  replace (20 * Z.to_nat t + Z.to_nat i0)%nat with (Z.to_nat (i0 + 20 * t)) by lia.
  apply block20_words; lia.
Qed.

Lemma braid_lanes_step : forall c bs i0 t x0 x1 x2 x3 x4,
  bytes bs -> 0 <= i0 -> 0 <= t -> i0 + 20 * t + 20 <= Z.of_nat (length bs) ->
  [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
    = braid_state [c; 0; 0; 0; 0] (Z.to_nat t) (skipn (Z.to_nat i0) bs) ->
  [dLaneM (dY0 (wdp bs (i0 + 20 * t)) x0) mod 2^32; dLaneM (dY0 (wdp bs (i0 + 20 * t + 4)) x1) mod 2^32;
   dLaneM (dY0 (wdp bs (i0 + 20 * t + 8)) x2) mod 2^32; dLaneM (dY0 (wdp bs (i0 + 20 * t + 12)) x3) mod 2^32;
   dLaneM (dY0 (wdp bs (i0 + 20 * t + 16)) x4) mod 2^32]
    = braid_state [c; 0; 0; 0; 0] (Z.to_nat (t + 1)) (skipn (Z.to_nat i0) bs).
Proof.
  intros c bs i0 t x0 x1 x2 x3 x4 F Hi Ht Hl E.
  replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
  rewrite braid_state_S, <- E.
  rewrite (braid_step_5 _ _ _ _ _ _ _ _ _ _ _ [] (block_skipn_words bs i0 t Hi Ht Hl)).
  rewrite !dLaneM_mod32 by (apply wdp_range; exact F). reflexivity.
Qed.
