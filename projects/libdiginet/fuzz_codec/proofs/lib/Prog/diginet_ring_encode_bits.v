From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import MState ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(** One iteration of the loop of diginet_ring_encode (diginet_codec.c:186-191) on one of its two
    bytes: bit off + k of the mask sets bit 6 - k of b (off = 1 for b1, 8 for b2). *)
Definition rstep (mask off k b : Z) : Z := Z.lor b (bit_or_0 (Z.testbit mask (off + k)) (2 ^ (6 - k))).

(** ring_bits is the seven iterations k = 0 .. 6 from (0, 0). *)
Lemma ring_bits_rstep : forall mask, ring_bits mask =
  (rstep mask 1 6 (rstep mask 1 5 (rstep mask 1 4 (rstep mask 1 3 (rstep mask 1 2 (rstep mask 1 1 (rstep mask 1 0 0)))))),
   rstep mask 8 6 (rstep mask 8 5 (rstep mask 8 4 (rstep mask 8 3 (rstep mask 8 2 (rstep mask 8 1 (rstep mask 8 0 0))))))).
Proof. intros mask. reflexivity. Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb.
  assert (E : Z.lor a b = Z.land (Z.lor a b) (Z.ones n)).
  { rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E, Z.land_ones by lia.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as P.
  pose proof (Z.mod_pos_bound (Z.lor a b) (2 ^ n) P). lia.
Qed.

(** Each partial byte is a 7-bit value. *)
Lemma rstep_range : forall mask off k b, 0 <= k <= 6 -> 0 <= b < 128 -> 0 <= rstep mask off k b < 128.
Proof.
  intros mask off k b Hk Hb. unfold rstep, bit_or_0.
  destruct (Z.testbit mask (off + k)).
  - assert (P : 0 <= 2 ^ (6 - k) < 2 ^ 7).
    { split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
    split; [apply Z.lor_nonneg; lia |].
    change 128 with (2 ^ 7). apply lor_lt_pow2; [lia | change (2 ^ 7) with 128; lia | exact P].
  - rewrite Z.lor_0_r. exact Hb.
Qed.

(** `srai x, x, 63` of a word built from y, read back as an unsigned value: all ones when bit 63 of y
    is set, else 0. *)
Lemma sar63_lit : forall y,
  Z.shiftr (bv_signed (Z_to_bv 64 y)) 63 mod 18446744073709551616
  = if Z.testbit y 63 then 18446744073709551615 else 0.
Proof.
  intros y. rewrite zb_signed, unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808.
  assert (T : Z.testbit y 63 = (9223372036854775808 <=? y mod 18446744073709551616)).
  { change 18446744073709551616 with (2 ^ 64).
    rewrite <- (Z.mod_pow2_bits_low y 64 63) by lia.
    pose proof (Z.mod_pos_bound y (2 ^ 64) ltac:(lia)) as R.
    pose proof (Z.testbit_spec' (y mod 2 ^ 64) 63 ltac:(lia)) as B.
    remember (y mod 2 ^ 64) as t eqn:Et. clear Et.
    change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 63) with 9223372036854775808 in *.
    destruct (Z.testbit t 63); cbn [Z.b2z] in B; symmetry;
      [apply Z.leb_le | apply Z.leb_gt]; Z.div_mod_to_equations; lia. }
  rewrite T.
  pose proof (Z.mod_pos_bound y 18446744073709551616 ltac:(lia)) as R.
  remember (y mod 18446744073709551616) as t eqn:Et. clear Et T.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 63) with 9223372036854775808.
  destruct (Z.ltb_spec t 9223372036854775808) as [L|L]; cbv beta iota.
  - replace (9223372036854775808 <=? t) with false by (symmetry; apply Z.leb_gt; exact L).
    rewrite (Z.div_small t) by lia. reflexivity.
  - replace (9223372036854775808 <=? t) with true by (symmetry; apply Z.leb_le; exact L).
    replace ((t - 18446744073709551616) / 9223372036854775808) with (-1)
      by (first [ symmetry; apply Z.div_unique with (r := t - 9223372036854775808); lia
                | apply Z.div_unique with (r := t - 9223372036854775808); lia ]).
    reflexivity.
Qed.

(** One picked bit of the loop body (`srlw` by k, `slli` by s, `srai` by 63, `and` with
    `sllw 1, 6 - k`), as the walk's register forms give it: bit 63 - s + k of the mask, in place
    6 - k. *)
Lemma ring_pick : forall mask k s, 0 <= mask < 65536 -> 0 <= k <= 6 -> 0 <= s <= 63 ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_swrap 32 (Z.shiftr (bv_wrap 32 mask) (k mod 32)) mod 18446744073709551616) s))) 63
            mod 18446744073709551616)
         (bv_swrap 32 (Z.shiftl 1 ((6 - k) mod 32)) mod 18446744073709551616)
  = bit_or_0 (Z.testbit mask (63 - s + k)) (2 ^ (6 - k)).
Proof.
  intros mask k s Hm Hk Hs.
  rewrite (Z.mod_small k 32) by lia. rewrite (Z.mod_small (6 - k) 32) by lia.
  replace (bv_wrap 32 mask) with mask
    by (unfold bv_wrap; change (bv_modulus 32) with 4294967296; symmetry; apply Z.mod_small; lia).
  assert (Bx : 0 <= Z.shiftr mask k < 65536).
  { rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P.
    remember (2 ^ k) as p eqn:Ep. clear Ep.
    Z.div_mod_to_equations. nia. }
  rewrite (bv_swrap_small 32 (Z.shiftr mask k)) by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (Z.mod_small (Z.shiftr mask k)) by lia.
  rewrite Z.shiftl_1_l.
  assert (Bp : 0 < 2 ^ (6 - k) <= 64).
  { split; [apply Z.pow_pos_nonneg; lia |]. change 64 with (2 ^ 6). apply Z.pow_le_mono_r; lia. }
  rewrite (bv_swrap_small 32 (2 ^ (6 - k))) by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (Z.mod_small (2 ^ (6 - k))) by lia.
  rewrite sar63_lit.
  rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
  replace (63 - s + k) with (k + (63 - s)) by lia.
  unfold bit_or_0. destruct (Z.testbit mask (k + (63 - s))).
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. split; [lia | apply (Z.le_lt_trans _ 64); [lia | reflexivity]].
  - apply Z.land_0_l.
Qed.

(** `slli x, mask, 48` read back as unsigned (the bit-15 test). *)
Lemma shl48_mod : forall mask, 0 <= mask < 65536 ->
  Z.shiftl mask 48 mod 18446744073709551616 = mask * 281474976710656.
Proof.
  intros mask Hm. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656.
  apply Z.mod_small. lia.
Qed.

(** `slli a2, a2, 63; srli a2, a2, 57`: bit 0 of the mask in place 6. *)
Lemma shl63_shr57 : forall mask, 0 <= mask ->
  Z.shiftr (Z.shiftl mask 63 mod 18446744073709551616) 57 = bit_or_0 (Z.testbit mask 0) 64.
Proof.
  intros mask Hm. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 63) with 9223372036854775808. change (2 ^ 57) with 144115188075855872.
  pose proof (Z.testbit_spec' mask 0 ltac:(lia)) as B. change (2 ^ 0) with 1 in B. rewrite Z.div_1_r in B.
  unfold bit_or_0. destruct (Z.testbit mask 0); cbn [Z.b2z] in B; Z.div_mod_to_equations; lia.
Qed.

(** The failing returns of ring_spec before the loop. *)
Lemma ring_spec_strips : forall d strip mask, d_strips d <= strip -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
  intros d strip mask H. unfold ring_spec.
  replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma ring_spec_mask : forall d strip mask, 32768 <= mask -> ring_spec (Some d) strip mask = (E_RANGE, None).
Proof.
  intros d strip mask H. unfold ring_spec.
  replace (Z.shiftr mask 15 =? 0) with false.
  - cbn [negb]. rewrite orb_true_r. reflexivity.
  - symmetry. apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 15) with 32768.
    intro E. Z.div_mod_to_equations. lia.
Qed.

(** A strip below 256 with bit 0 of the mask in place 6: the first payload byte. *)
Lemma pl0_range : forall strip mask, 0 <= strip < 256 -> 0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256.
Proof.
  intros strip mask Hs. unfold bit_or_0. destruct (Z.testbit mask 0).
  - split; [apply Z.lor_nonneg; lia |]. change 256 with (2 ^ 8). apply lor_lt_pow2; cbn; lia.
  - rewrite Z.lor_0_r. exact Hs.
Qed.

(** ring_spec past its two range tests: the sysex payload [p0; b1; b2] and the key. *)
Lemma ring_spec_go : forall d strip mask, strip < d_strips d -> 0 <= mask < 32768 ->
  ring_spec (Some d) strip mask =
  with_key (sysex_spec (d_dev d) 0 [u8 (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)); fst (ring_bits mask); snd (ring_bits mask)])
           (KEY 3 strip).
Proof.
  intros d strip mask Hs Hm. unfold ring_spec.
  replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.shiftr mask 15 =? 0) with true
    by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  cbn [orb negb]. destruct (ring_bits mask). reflexivity.
Qed.

Lemma testbit7_lo : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
  intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as B.
  rewrite Z.div_small in B by (cbn; lia). destruct (Z.testbit x 7); [discriminate B | reflexivity].
Qed.

Lemma testbit7_hi : forall x, 128 <= x < 256 -> Z.testbit x 7 = true.
Proof.
  intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as B.
  replace (x / 2 ^ 7) with 1 in B by (apply Z.div_unique with (r := x - 128); cbn; lia).
  destruct (Z.testbit x 7); [reflexivity | discriminate B].
Qed.

(** sysex_spec with fn 0 and a 3-byte payload: device bit 7, then payload bit 7, else success. *)
Lemma sysex_dev_hi : forall dev pl, 128 <= dev -> sysex_spec dev 0 pl = (E_ARG, None).
Proof.
  intros dev pl H. unfold sysex_spec. replace (0x7f <? dev) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma sysex_pl0_hi : forall dev p0 b1 b2, 0 <= dev < 128 -> 128 <= p0 < 256 ->
  sysex_spec dev 0 [p0; b1; b2] = (E_RANGE, None).
Proof.
  intros dev p0 b1 b2 Hd Hp. unfold sysex_spec.
  replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.eqb Z.ltb Z.compare existsb length Z.of_nat Pos.of_succ_nat Z.add].
  rewrite (testbit7_hi p0 Hp). reflexivity.
Qed.

Lemma sysex_ok : forall dev p0 b1 b2, 0 <= dev < 128 -> 0 <= p0 < 128 -> 0 <= b1 < 128 -> 0 <= b2 < 128 ->
  sysex_spec dev 0 [p0; b1; b2] = (0, Some ([0xf0; 0x13; dev; 0; p0; b1; b2; 0xf7], 0, 0)).
Proof.
  intros dev p0 b1 b2 Hd Hp H1 H2. unfold sysex_spec.
  replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.eqb Z.ltb Z.compare existsb length Z.of_nat Pos.of_succ_nat Z.add].
  rewrite (testbit7_lo p0 Hp), (testbit7_lo b1 H1), (testbit7_lo b2 H2). reflexivity.
Qed.

(** u8 of a byte value. *)
Lemma u8_small : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.

(** The key `((strip << 48) >> 48) | 0x30000` of the walks is KEY 3 strip. *)
Lemma key3 : forall strip, Z.lor (strip mod 2 ^ 16) 196608 = KEY 3 strip.
Proof.
  intros strip. unfold KEY. change (3 * 65536) with 196608. change 0xffff with (2 ^ 16 - 1).
  rewrite zb_land_mask by lia. apply Z.lor_comm.
Qed.
