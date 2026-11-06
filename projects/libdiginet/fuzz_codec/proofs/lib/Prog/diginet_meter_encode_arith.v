From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import MState Mem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(** Facts of diginet_meter_encode (diginet_codec.c:217-231) that do not depend on the image: the register
    forms of its arguments and payload, the values of meter_spec and of the sysex_spec call it makes, and
    the bytes its stores write. A byte is written Z_to_bv 8 z here (each image's codec_cells names that b8). *)

(** An unsigned argument loaded with lw is s32 c in the register; its 64-bit unsigned value. *)
Lemma u_s32 : forall c, 0 <= c < 2^32 ->
  s32 c mod 18446744073709551616 = if c <? 2^31 then c else c + 18446744069414584320.
Proof.
  intros c Hc. unfold s32.
  destruct (Z.ltb_spec c (2^31)); [apply Z.mod_small; lia|].
  replace (c - 2^32) with ((c + 18446744069414584320) + (-1) * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma s32_small : forall c, 0 <= c < 2^31 -> s32 c = c.
Proof. intros c Hc. unfold s32. destruct (Z.ltb_spec c (2^31)); lia. Qed.

(** A boolean fact checked on each z in [0, n). *)
Lemma forall_range : forall (P : Z -> bool) (n : Z),
  forallb P (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall z, 0 <= z < n -> P z = true.
Proof.
  intros P n H z Hz. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat z). split; [apply Z2Nat.id; lia|]. apply in_seq. lia.
Qed.

Lemma testbit7_small : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
  intros x Hx.
  pose proof (forall_range (fun y => negb (Z.testbit y 7)) 128 ltac:(vm_compute; reflexivity) x Hx) as K.
  apply negb_true_iff in K. exact K.
Qed.

(** The payload's first byte: channel, with 0x20 when right is not 0. *)
Definition mch (ch r : Z) : Z := Z.lor ch (bit_or_0 (negb (r =? 0)) 0x20).

Lemma mch_range : forall ch r, 0 <= ch < 32 -> 0 <= mch ch r < 64.
Proof.
  intros ch r H. unfold mch, bit_or_0. destruct (negb (r =? 0)).
  - pose proof (forall_range (fun c => (0 <=? Z.lor c 0x20) && (Z.lor c 0x20 <? 64)) 32
                  ltac:(vm_compute; reflexivity) ch H) as K.
    apply andb_true_iff in K as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2. lia.
  - rewrite Z.lor_0_r. lia.
Qed.

Lemma mask_bytes : forall s, 0 <= s < 15 ->
  0 <= Z.shiftr (meter_mask_spec s) 7 < 128 /\ 0 <= Z.land (meter_mask_spec s) 0x7f < 128.
Proof.
  intros s Hs.
  pose proof (forall_range (fun s => (0 <=? Z.shiftr (meter_mask_spec s) 7) && (Z.shiftr (meter_mask_spec s) 7 <? 128)
                                     && (0 <=? Z.land (meter_mask_spec s) 0x7f) && (Z.land (meter_mask_spec s) 0x7f <? 128))
                15 ltac:(vm_compute; reflexivity) s Hs) as K.
  apply andb_true_iff in K as [K K4]. apply andb_true_iff in K as [K K3]. apply andb_true_iff in K as [K1 K2].
  apply Z.leb_le in K1. apply Z.ltb_lt in K2. apply Z.leb_le in K3. apply Z.ltb_lt in K4. lia.
Qed.

(** ---- meter_spec on each path ---- *)

Lemma meter_range_ch : forall d ch r s, 0x20 <= ch -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
  intros d ch r s H. cbv beta iota zeta delta [meter_spec].
  replace (0x20 <=? ch) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma meter_range_seg : forall d ch r s, 14 < s -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
  intros d ch r s H. cbv beta iota zeta delta [meter_spec].
  replace (14 <? s) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity.
Qed.

Lemma meter_dev_hi : forall d ch r s, ch < 0x20 -> s <= 14 -> 0x7f < d_dev d ->
  meter_spec (Some d) ch r s = (E_ARG, None).
Proof.
  intros d ch r s H1 H2 H3. cbv beta iota zeta delta [meter_spec].
  replace (0x20 <=? ch) with false by (symmetry; apply Z.leb_gt; lia).
  replace (14 <? s) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv beta iota zeta delta [orb sysex_spec].
  replace (0x7f <? d_dev d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** sysex_spec on meter's payload: the bit-7 test of the payload never fails. *)
Lemma sysex_meter_hi : forall dev pl, 0x7f < dev -> sysex_spec dev 0x10 pl = (E_ARG, None).
Proof.
  intros dev pl H. unfold sysex_spec. replace (0x7f <? dev) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma sysex_meter_ok : forall dev ch r s, 0 <= dev <= 0x7f -> 0 <= ch < 0x20 -> 0 <= s <= 14 ->
  sysex_spec dev 0x10 [mch ch r; Z.shiftr (meter_mask_spec s) 7; Z.land (meter_mask_spec s) 0x7f] =
  (0, Some ([0xf0; 0x13; dev; 0x10; mch ch r; Z.shiftr (meter_mask_spec s) 7;
             Z.land (meter_mask_spec s) 0x7f; 0xf7], 0, 0)).
Proof.
  intros dev ch r s H1 H2 H3.
  pose proof (mch_range ch r ltac:(lia)) as HM. pose proof (mask_bytes s ltac:(lia)) as [HA HB].
  unfold sysex_spec. replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [existsb].
  rewrite (testbit7_small (mch ch r)), (testbit7_small (Z.shiftr (meter_mask_spec s) 7)),
          (testbit7_small (Z.land (meter_mask_spec s) 0x7f)) by lia.
  reflexivity.
Qed.

Lemma meter_ok_sysex : forall d ch r s, 0 <= ch < 0x20 -> 0 <= s <= 14 ->
  meter_spec (Some d) ch r s =
  with_key (sysex_spec (d_dev d) 0x10 [mch ch r; Z.shiftr (meter_mask_spec s) 7; Z.land (meter_mask_spec s) 0x7f])
           (KEY 4 (mch ch r)).
Proof.
  intros d ch r s H1 H2.
  pose proof (mch_range ch r ltac:(lia)) as HM. pose proof (mask_bytes s ltac:(lia)) as [HA HB].
  cbv beta iota zeta delta [meter_spec].
  replace (0x20 <=? ch) with false by (symmetry; apply Z.leb_gt; lia).
  replace (14 <? s) with false by (symmetry; apply Z.ltb_ge; lia).
  change (Z.lor ch (bit_or_0 (negb (r =? 0)) 0x20)) with (mch ch r).
  unfold u8.
  rewrite (Z.mod_small (mch ch r) 256) by lia.
  rewrite (Z.mod_small (Z.shiftr (meter_mask_spec s) 7) 256) by lia.
  rewrite (Z.mod_small (Z.land (meter_mask_spec s) 0x7f) 256) by lia.
  reflexivity.
Qed.

Lemma meter_ok : forall d ch r s, 0 <= ch < 0x20 -> 0 <= s <= 14 -> 0 <= d_dev d <= 0x7f ->
  meter_spec (Some d) ch r s =
  (0, Some ([0xf0; 0x13; d_dev d; 0x10; mch ch r; Z.shiftr (meter_mask_spec s) 7;
             Z.land (meter_mask_spec s) 0x7f; 0xf7], KEY 4 (mch ch r), 0)).
Proof.
  intros d ch r s H1 H2 H3.
  rewrite meter_ok_sysex by lia. rewrite sysex_meter_ok by lia. reflexivity.
Qed.

(** ---- the machine's forms ---- *)

(** `snez; slli 5; or` on the right and channel registers gives mch. *)
Lemma reg_ch : forall ch r, - 2^31 <= r < 2^31 ->
  Z.lor (Z.shiftl (Z.b2z (0 <? r mod 18446744073709551616)) 5 mod 18446744073709551616) ch = mch ch r.
Proof.
  intros ch r Hr. unfold mch. rewrite Z.lor_comm. f_equal.
  replace (0 <? r mod 18446744073709551616) with (negb (r =? 0)); [destruct (r =? 0); reflexivity|].
  destruct (Z.eqb_spec r 0) as [E|E]; [subst r; reflexivity|].
  symmetry. apply Z.ltb_lt. destruct (Z.ltb_spec r 0).
  - replace r with ((r + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
  - rewrite Z.mod_small; lia.
Qed.

(** `sllw` of -1 by segments, then `not`, gives meter_mask_spec. *)
Lemma reg_mask : forall s, 0 <= s < 15 ->
  Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (s mod 32)) mod 18446744073709551616) 18446744073709551615
  = meter_mask_spec s.
Proof.
  intros s Hs.
  pose proof (forall_range (fun s => Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (s mod 32)) mod 18446744073709551616)
                                            18446744073709551615 =? meter_mask_spec s)
                15 ltac:(vm_compute; reflexivity) s Hs) as K.
  apply Z.eqb_eq in K. exact K.
Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma key_eq : forall c, 0 <= c < 64 -> Z.lor c 262144 = KEY 4 c.
Proof.
  intros c Hc. unfold KEY. rewrite Z.lor_comm. f_equal.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
Qed.

(** ---- bytes ---- *)

Lemma mod64_8 : forall z, (z mod 18446744073709551616) mod 256 = z mod 256.
Proof.
  intros z. rewrite (Z.mod_eq z 18446744073709551616) by lia.
  replace (z - 18446744073709551616 * (z / 18446744073709551616))
    with (z + (- (72057594037927936 * (z / 18446744073709551616))) * 256) by lia.
  apply Z.mod_add. lia.
Qed.

(** The byte a store of the register Z_to_bv 64 z writes. *)
Lemma byte_lit : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  apply mod64_8.
Qed.

Lemma byte_unsigned : forall b : bv 8, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma byte_val : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(** `lb` of a byte z. *)
Lemma sxb_z8 : forall z, 0 <= z < 256 -> sxb (Z_to_bv 8 z) = Z_to_bv 64 (if z <? 128 then z else z - 256).
Proof.
  intros z Hz. unfold sxb. f_equal.
  pose proof (forall_range (fun z => bv_signed (Z_to_bv 8 z) =? (if z <? 128 then z else z - 256)) 256
                ltac:(vm_compute; reflexivity) z Hz) as K.
  apply Z.eqb_eq in K. exact K.
Qed.

Lemma sxb_z8_lo : forall z, 0 <= z < 128 -> sxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. rewrite sxb_z8 by lia. replace (z <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma bytes_eq_of_vals : forall l1 l2 : list (bv 8),
  map (fun b => bv_unsigned b) l1 = map (fun b => bv_unsigned b) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma le2_5104 : le2 (Z_to_bv 64 5104) = [Z_to_bv 8 0xf0; Z_to_bv 8 0x13].
Proof. apply bytes_eq_of_vals. vm_compute. reflexivity. Qed.

Lemma le2_8 : le2 (Z_to_bv 64 8) = [Z_to_bv 8 8; Z_to_bv 8 0].
Proof. apply bytes_eq_of_vals. vm_compute. reflexivity. Qed.

Lemma byte_m9 : Z_to_bv 8 (-9) = Z_to_bv 8 0xf7.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
