From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import Mem Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
Import ListNotations.
Open Scope Z_scope.

(* Image-free facts check_inject's walks (plain and UBSan) use: want_width's answer, and the harness's w_put (fuzz.h)
   on a frame's byte list, against the braid model slot_write_upto that rp_slot_write's contract states. *)

(* want_width(f, n, slot) answers -1, or an even width 2 .. 40 of a frame of 52 + 36 * nch (+ 2) bytes holding the
   slot. *)
Lemma want_width_cases : forall n bs slot,
  want_width_model n bs slot = -1 \/
  (2 <= want_width_model n bs slot <= 40 /\ want_width_model n bs slot mod 2 = 0 /\
   52 + 36 * want_width_model n bs slot <= n <= 54 + 36 * want_width_model n bs slot /\
   0 <= slot < want_width_model n bs slot).
Proof.
  intros n bs slot. unfold want_width_model, w_width_model.
  destruct (((n - 52) mod 72 =? 0) && (124 <=? n) && (n <=? 1492)) eqn:E1.
  - apply andb_prop in E1 as [E1 E3]. apply andb_prop in E1 as [E1 E2].
    apply Z.eqb_eq in E1. apply Z.leb_le in E2, E3.
    destruct ((n - 52) / 36 <? 0); [left; reflexivity|]. destruct (negb (frame_is_audio bs)); [left; reflexivity|].
    destruct (slot <? 0) eqn:E4; [left; reflexivity|]. destruct ((n - 52) / 36 <=? slot) eqn:E5; [left; reflexivity|].
    cbn [orb]. right. apply Z.ltb_ge in E4. apply Z.leb_gt in E5. Z.div_mod_to_equations. lia.
  - destruct (((n - 54) mod 72 =? 0) && (126 <=? n) && (n <=? 1494)) eqn:E2.
    + apply andb_prop in E2 as [E2 E4]. apply andb_prop in E2 as [E2 E3].
      apply Z.eqb_eq in E2. apply Z.leb_le in E3, E4.
      destruct ((n - 54) / 36 <? 0); [left; reflexivity|]. destruct (negb (frame_is_audio bs)); [left; reflexivity|].
      destruct (slot <? 0) eqn:E5; [left; reflexivity|]. destruct ((n - 54) / 36 <=? slot) eqn:E6; [left; reflexivity|].
      cbn [orb]. right. apply Z.ltb_ge in E5. apply Z.leb_gt in E6. Z.div_mod_to_equations. lia.
    + left. reflexivity.
Qed.

(* w_put's pair group of a time-sample, as the harness writes it back: read as g0 .. g5 (each 16-bit word
   byte-swapped), the slot's three bytes put at be[at .. at + 2] (at = 3 for an odd slot), swapped back. *)
Definition wput_group (p : Z) (g0 g1 g2 g3 g4 g5 lo mid hi : byte) : list byte :=
  if p =? 0 then [mid; hi; g2; lo; g4; g5] else [g0; g1; hi; g3; lo; mid].

Lemma upd_bytes_mid : forall (A X C bs : list byte) k, (k + length bs <= length X)%nat ->
  upd_bytes (A ++ X ++ C) (length A + k) bs = A ++ upd_bytes X k bs ++ C.
Proof.
  intros A X C bs k H. unfold upd_bytes.
  rewrite firstn_app, firstn_all2 by lia. replace (length A + k - length A)%nat with k by lia.
  rewrite firstn_app. replace (k - length X)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all2 by lia. replace (length A + k + length bs - length A)%nat with (k + length bs)%nat by lia.
  rewrite skipn_app. replace (k + length bs - length X)%nat with 0%nat by lia. rewrite skipn_O.
  cbn [app]. rewrite !app_assoc. reflexivity.
Qed.

Lemma group_split : forall (L : list byte) (G : nat), (G + 6 <= length L)%nat ->
  exists A C g0 g1 g2 g3 g4 g5, L = A ++ [g0; g1; g2; g3; g4; g5] ++ C /\ length A = G.
Proof.
  intros L G H. pose proof (firstn_skipn G L) as E. pose proof (length_skipn G L) as HS.
  destruct (skipn G L) as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 C]]]]]]; cbn [length] in HS; try lia.
  exists (firstn G L), C, g0, g1, g2, g3, g4, g5. split; [symmetry; exact E|]. apply firstn_length_le. lia.
Qed.

(* The braid model's step from sample t to t + 1, on a frame whose sample-t pair group is g0 .. g5. *)
Lemma slot_write_upto_S_group : forall nch slot vbs bs (t : nat) (A C : list byte) g0 g1 g2 g3 g4 g5,
  slot_write_upto nch slot vbs bs t = A ++ [g0; g1; g2; g3; g4; g5] ++ C ->
  Z.of_nat (length A) = 50 + 3 * (Z.of_nat t * nch + (slot - slot mod 2)) ->
  slot_write_upto nch slot vbs bs (S t) =
    A ++ wput_group (slot mod 2) g0 g1 g2 g3 g4 g5
           (nth (Z.to_nat (4 * Z.of_nat t)) vbs (Z_to_bv 8 0))
           (nth (Z.to_nat (4 * Z.of_nat t + 1)) vbs (Z_to_bv 8 0))
           (nth (Z.to_nat (4 * Z.of_nat t + 2)) vbs (Z_to_bv 8 0)) ++ C.
Proof.
  intros nch slot vbs bs t A C g0 g1 g2 g3 g4 g5 E HA. cbn [slot_write_upto]. rewrite E. unfold braid_at.
  rewrite <- HA. unfold wput_group.
  assert (P : slot mod 2 = 0 \/ slot mod 2 = 1) by (pose proof (Z.mod_pos_bound slot 2 ltac:(lia)); lia).
  destruct P as [P|P]; rewrite P; cbn [Z.eqb Pos.eqb].
  - replace (Z.to_nat (Z.of_nat (length A) + 3)) with (length A + 3)%nat by lia.
    replace (Z.to_nat (Z.of_nat (length A) + 0)) with (length A + 0)%nat by lia.
    replace (Z.to_nat (Z.of_nat (length A) + 1)) with (length A + 1)%nat by lia.
    rewrite !upd_bytes_mid by (cbn; lia). reflexivity.
  - replace (Z.to_nat (Z.of_nat (length A) + 4)) with (length A + 4)%nat by lia.
    replace (Z.to_nat (Z.of_nat (length A) + 5)) with (length A + 5)%nat by lia.
    replace (Z.to_nat (Z.of_nat (length A) + 2)) with (length A + 2)%nat by lia.
    rewrite !upd_bytes_mid by (cbn; lia). reflexivity.
Qed.

Lemma braid_firstn1 : forall (L : list byte) k d, (k < length L)%nat -> firstn 1 (skipn k L) = [nth k L d].
Proof. induction L as [|b L IH]; intros [|k] d H; cbn in *; try lia; auto. apply IH; lia. Qed.

(* v[t]'s four bytes as one word. A walk's 4-byte load of them reads le4 of it (the load then gives sx32 of it):
   a load of a literal list of symbolic bytes would make the kit's load normalizer (fold_lit_load) vm_compute on
   them. *)
Definition w32 (b0 b1 b2 b3 : byte) : word :=
  Z_to_bv 64 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).

Lemma le4_w32 : forall b0 b1 b2 b3 : byte, le4 (w32 b0 b1 b2 b3) = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in R0, R1, R2, R3.
  unfold le4, w32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 8) with 256; change (2 ^ 8) with 256; Z.div_mod_to_equations; lia.
Qed.

(* One byte of the pair group, read and written in memory. *)
Section Group.
Variable segs : list Segment.

Lemma group_read : forall m e (A X C : list byte) (j : nat) k,
  bytes_at segs m e (A ++ X ++ C) -> (j < length X)%nat -> k = Z.of_nat (length A) + Z.of_nat j ->
  ov_read_bytes segs m (wa (e + k)) 1 = Some [nth j X (Z_to_bv 8 0)].
Proof.
  intros m e A X C j k H Hj ->.
  rewrite (bytes_at_read segs m e _ (Z.of_nat (length A) + Z.of_nat j) 1 H) by (rewrite ?length_app; lia).
  f_equal. replace (Z.to_nat (Z.of_nat (length A) + Z.of_nat j)) with (length A + j)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length A + j - length A)%nat with j by lia. cbn [app].
  rewrite (braid_firstn1 _ j (Z_to_bv 8 0)) by (rewrite length_app; lia).
  rewrite app_nth1 by exact Hj. reflexivity.
Qed.

Lemma group_write : forall m e (A X C : list byte) (j : nat) k b,
  bytes_at segs m e (A ++ X ++ C) -> (j < length X)%nat -> k = Z.of_nat (length A) + Z.of_nat j ->
  bytes_at segs (write_to_mem m (wa (e + k)) [b]) e (A ++ upd_bytes X j [b] ++ C).
Proof.
  intros m e A X C j k b H Hj ->.
  rewrite <- upd_bytes_mid by (cbn; lia).
  replace (length A + j)%nat with (Z.to_nat (Z.of_nat (length A) + Z.of_nat j)) by lia.
  apply bytes_at_write_inside; [exact H | lia | rewrite !length_app; cbn [length]; lia].
Qed.

(* The int32 v[t] of v's bytes, read as one 4-byte load: le4 of the word w32 of its bytes. *)
Lemma word4_read : forall m v (vbs : list byte) (t k : Z),
  bytes_at segs m v vbs -> 0 <= t -> 4 * t + 4 <= Z.of_nat (length vbs) -> k = 4 * t ->
  ov_read_bytes segs m (wa (v + k)) 4 =
    Some (le4 (w32 (nth (Z.to_nat (4 * t)) vbs (Z_to_bv 8 0)) (nth (Z.to_nat (4 * t + 1)) vbs (Z_to_bv 8 0))
                   (nth (Z.to_nat (4 * t + 2)) vbs (Z_to_bv 8 0)) (nth (Z.to_nat (4 * t + 3)) vbs (Z_to_bv 8 0)))).
Proof.
  intros m v vbs t k H Ht Hl ->. rewrite le4_w32.
  rewrite (bytes_at_read segs m v vbs (4 * t) 4 H) by lia. f_equal.
  replace (Z.to_nat (4 * t + 1)) with (S (Z.to_nat (4 * t))) by lia.
  replace (Z.to_nat (4 * t + 2)) with (S (S (Z.to_nat (4 * t)))) by lia.
  replace (Z.to_nat (4 * t + 3)) with (S (S (S (Z.to_nat (4 * t))))) by lia.
  assert (Hk : (Z.to_nat (4 * t) + 4 <= length vbs)%nat) by lia.
  generalize dependent (Z.to_nat (4 * t)). clear Ht Hl H.
  induction vbs as [|x vbs IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k].
  - destruct vbs as [|y0 [|y1 [|y2 vbs]]]; cbn in Hk |- *; try lia. reflexivity.
  - cbn [skipn]. rewrite IH by lia. reflexivity.
Qed.

End Group.

(* The bytes of v[s] the harness puts: the low byte of the loaded int32 (lw sign-extends: sx32) and of it shifted
   right by 8 and 16 (srli shifts the 64-bit register). *)
Lemma sx32_w32_low : forall b0 b1 b2 b3 : byte,
  bv_unsigned (sx32 (w32 b0 b1 b2 b3)) mod 2 ^ 32 =
  bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in R0, R1, R2, R3.
  unfold sx32, w32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change (bv_modulus 64) with (2 ^ 64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma w32_byte : forall b0 b1 b2 b3 : byte, forall k (b : byte),
  (k = 0 /\ b = b0) \/ (k = 8 /\ b = b1) \/ (k = 16 /\ b = b2) ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (w32 b0 b1 b2 b3))) k)) = [b].
Proof.
  intros b0 b1 b2 b3 k b Hk.
  set (X := sx32 (w32 b0 b1 b2 b3)).
  pose proof (sx32_w32_low b0 b1 b2 b3) as E. fold X in E.
  pose proof (bv_unsigned_in_range 64 X) as RX. change (bv_modulus 64) with (2 ^ 64) in RX.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in R0, R1, R2, R3.
  unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  assert (Hk0 : 0 <= k <= 16) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk0)) as Hp.
  assert (Hs : 0 <= bv_unsigned X / 2 ^ k < 2 ^ 64).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; nia. }
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
  rewrite (Z.mod_small (bv_unsigned X / 2 ^ k)) by lia.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite <- (shiftr_mod_mod8 (bv_unsigned X) k 32) by lia.
  rewrite E, Z.shiftr_div_pow2 by lia.
  destruct Hk as [[-> ->]|[[-> ->]|[-> ->]]]; change (2 ^ 0) with 1; change (2 ^ 8) with 256;
    change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia.
Qed.

Lemma w32_le1 : forall b0 b1 b2 b3 : byte, le1 (sx32 (w32 b0 b1 b2 b3)) = [b0].
Proof.
  intros b0 b1 b2 b3. rewrite <- (w32_byte b0 b1 b2 b3 0 b0) by (left; split; reflexivity).
  rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma w32_b1 : forall b0 b1 b2 b3 : byte,
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (w32 b0 b1 b2 b3))) 8)) = [b1].
Proof. intros b0 b1 b2 b3. apply w32_byte. right; left; split; reflexivity. Qed.

Lemma w32_b2 : forall b0 b1 b2 b3 : byte,
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (w32 b0 b1 b2 b3))) 16)) = [b2].
Proof. intros b0 b1 b2 b3. apply w32_byte. right; right; split; reflexivity. Qed.

(* The setup of the harness's w_put loop: slot & ~1 (andi -2) and the be[] offset of an odd slot, (slot << 63 >> 63)
   & 3 (slli 63, srai 63, andi 3). land_hi / land_m2 are Prog/rp_slot_write.v's sw_land_hi / sw_land_m2. *)
Lemma land_hi : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (2^64 - 2^k) = 2^k * (x / 2^k).
Proof.
  intros x k Hx Hk.
  assert (E : 2^64 - 2^k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. unfold Z.pred.
    rewrite Z.mul_add_distr_r, <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. lia. }
  rewrite E, (Z.mul_comm (2^k)), <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i k).
  - rewrite (Z.testbit_neg_r (Z.ones (64 - k)) (i - k)), (Z.testbit_neg_r (Z.shiftr x k) (i - k)) by lia.
    apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    destruct (Z.ltb_spec i 64).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hnz]; [symmetry; apply Z.bits_0|].
      symmetry. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = x - x mod 2.
Proof.
  intros x Hx. pose proof (land_hi x 1 Hx ltac:(lia)) as E. change (2^64 - 2^1) with 18446744073709551614 in E.
  rewrite E. Z.div_mod_to_equations. lia.
Qed.

Lemma par_mask : forall s, 0 <= s < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl s 63))) 63))) 3 =
  if s mod 2 =? 0 then 0 else 3.
Proof.
  intros s Hs. rewrite Z.shiftl_mul_pow2 by lia.
  assert (E : bv_signed (Z_to_bv 64 (s * 2 ^ 63)) = if s mod 2 =? 0 then 0 else - 2 ^ 63).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
    destruct (Z.eqb_spec (s mod 2) 0); Z.div_mod_to_equations; lia. }
  rewrite E. destruct (s mod 2 =? 0); vm_compute; reflexivity.
Qed.
