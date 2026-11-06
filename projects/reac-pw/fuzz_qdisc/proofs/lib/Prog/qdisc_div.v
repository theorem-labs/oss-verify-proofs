From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec.
Open Scope Z_scope.

(** The arithmetic over Z that the proofs of reac_qdisc_etf_catchup_slots and check_slots share (plain and
    ubsan builds). Both leaves divide by 10^6 with the 8-byte constant at 0x103a8,
    0x431BDE82D7B634DB = 4835703278458516699 = ceil(2^82 / 10^6): `mulhu x, M` gives (x * M) / 2^64 and
    `srli 18` then gives (x * M) / 2^82, which is x / 10^6 on the range the code reaches. The literals
    18446744073709551616 (2^64) and [lead + -300] are the forms the walk's `zstep` leaves in the registers. *)

(** * The division by 10^6 *)

(** 10^6 * M = 2^82 + 175296. *)
Lemma qdisc_magic_qr : forall q r, 0 <= q <= 1000000 -> 0 <= r < 1000000 ->
  (1000000 * q + r) * 4835703278458516699 / 4835703278458516698824704 = q.
Proof.
  intros q r Hq Hr.
  symmetry. apply (Z.div_unique _ _ _ (q * 175296 + r * 4835703278458516699)); [left; lia | lia].
Qed.

Lemma qdisc_magic_div : forall x, 0 <= x <= 1000000999999 ->
  x * 4835703278458516699 / 2^82 = x / 1000000.
Proof.
  intros x Hx.
  assert (Hq : 0 <= x / 1000000 <= 1000000) by (Z.div_mod_to_equations; lia).
  assert (Hr : 0 <= x mod 1000000 < 1000000) by (apply Z.mod_pos_bound; lia).
  assert (E : x = 1000000 * (x / 1000000) + x mod 1000000) by (apply Z.div_mod; lia).
  rewrite E at 1. change (2^82) with 4835703278458516698824704.
  apply qdisc_magic_qr; assumption.
Qed.

(** What `mulhu` then `srli 18` compute: the high word of x * M, wrapped to 64 bits, shifted right by 18. *)
Lemma qdisc_magic_shift : forall x, 0 <= x <= 1000000999999 ->
  Z.shiftr (Z.shiftr (x * 4835703278458516699) 64 mod 18446744073709551616) 18 = x / 1000000.
Proof.
  intros x Hx.
  rewrite !Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^64).
  rewrite (Z.mod_small (x * 4835703278458516699 / 2^64)).
  2:{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite Z.div_div by lia. change (2^64 * 2^18) with (2^82).
  apply qdisc_magic_div; exact Hx.
Qed.

(** * The lead past the qdisc's delta *)

(** `addiw t, lead, -300; sltu c, lead, t; addi c, c, -1; and u, c, t` on a u16 lead: t is lead - 300
    (as an unsigned 64-bit value, lead - 300 mod 2^64); the mask c - 1 is all ones when lead >= 300 and zero
    otherwise; so u = max 0 (lead - 300). *)
Lemma qdisc_usable_z : forall lead, 0 <= lead <= 65535 ->
  Z.land ((Z.b2z (lead <? (lead + -300) mod 18446744073709551616) + -1) mod 18446744073709551616)
         ((lead + -300) mod 18446744073709551616) = Z.max 0 (lead - 300).
Proof.
  intros lead Hl.
  destruct (Z.ltb_spec0 lead 300) as [Hlt|Hge].
  - replace ((lead + -300) mod 18446744073709551616) with (lead + -300 + 18446744073709551616).
    2:{ rewrite <- (Z.mod_add (lead + -300) 1) by lia. rewrite Z.mod_small by lia. lia. }
    replace (lead <? lead + -300 + 18446744073709551616) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0.
    rewrite Z.land_0_l. lia.
  - rewrite (Z.mod_small (lead + -300) 18446744073709551616) by lia.
    replace (lead <? lead + -300) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
Qed.

(** addiw's 32-bit sign wrap does nothing to lead - 300. *)
Lemma qdisc_swrap_lead : forall lead, 0 <= lead <= 65535 -> bv_swrap 32 (lead + -300) = lead + -300.
Proof. intros lead Hl. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. Qed.

Lemma qdisc_usable_bv : forall lead, 0 <= lead <= 65535 ->
  Z.land ((Z.b2z (lead <? bv_swrap 32 (lead + -300) mod 18446744073709551616) + -1) mod 18446744073709551616)
         (bv_swrap 32 (lead + -300) mod 18446744073709551616) = Z.max 0 (lead - 300).
Proof. intros lead Hl. rewrite qdisc_swrap_lead by exact Hl. apply qdisc_usable_z; exact Hl. Qed.

(** * The product and the branches *)

(** The 64-bit product never wraps: usable * fps < 2^47 for a positive int fps. *)
Lemma qdisc_product_range : forall lead fps, 0 <= lead <= 65535 -> 0 < fps < 2^31 ->
  0 <= Z.max 0 (lead - 300) * fps < 2^47.
Proof.
  intros lead fps Hl Hf. assert (0 <= Z.max 0 (lead - 300) <= 65235) by lia.
  split; [nia|]. apply Z.le_lt_trans with (65235 * fps); [nia | lia].
Qed.

Lemma qdisc_n_lt1 : forall p, 0 <= p -> p < 1000000 -> p / 1000000 = 0.
Proof. intros p H1 H2. apply Z.div_small. lia. Qed.

Lemma qdisc_n_ge1 : forall p, 1000000 <= p -> 1 <= p / 1000000.
Proof. intros p H. apply Z.div_le_lower_bound; lia. Qed.

Lemma qdisc_n_gt_cap : forall p, 1000000999999 < p -> 1000000 < p / 1000000.
Proof. intros p H. apply Z.lt_le_trans with 1000001; [lia|]. apply Z.div_le_lower_bound; lia. Qed.

Lemma qdisc_n_le_cap : forall p, 0 <= p -> p <= 1000000999999 -> p / 1000000 <= 1000000.
Proof. intros p H1 H2. assert (p / 1000000 < 1000001) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma qdisc_n_range : forall p, 0 <= p <= 1000000999999 -> 0 <= p / 1000000 <= 1000000.
Proof. intros p Hp. split; [apply Z.div_pos; lia | apply qdisc_n_le_cap; lia]. Qed.

(** slots_spec on each path of the leaves: a frame rate of 0 or less; and for fps > 0, with the product
    p = usable * fps, the three outcomes of the tests p < 10^6 and 10^12 + 999999 < p. *)
Lemma qdisc_spec_nonpos : forall lead fps, fps <= 0 -> slots_spec lead fps = 1.
Proof.
  intros lead fps Hf. unfold slots_spec.
  replace (fps <=? 0) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma qdisc_spec_pos : forall lead fps p, 0 < fps -> p = Z.max 0 (lead - 300) * fps ->
  slots_spec lead fps = (if p / 1000000 <? 1 then 1 else if 1000000 <? p / 1000000 then 1000000 else p / 1000000).
Proof.
  intros lead fps p Hf Hp. unfold slots_spec.
  replace (fps <=? 0) with false by (symmetry; apply Z.leb_gt; lia). subst p. reflexivity.
Qed.

Lemma qdisc_spec_small : forall lead fps p, 0 < fps -> p = Z.max 0 (lead - 300) * fps -> p < 1000000 ->
  slots_spec lead fps = 1.
Proof.
  intros lead fps p Hf Hp Hs. rewrite (qdisc_spec_pos lead fps p Hf Hp).
  assert (0 <= p) by (subst p; nia).
  rewrite qdisc_n_lt1 by lia. reflexivity.
Qed.

Lemma qdisc_spec_cap : forall lead fps p, 0 < fps -> p = Z.max 0 (lead - 300) * fps -> 1000000999999 < p ->
  slots_spec lead fps = 1000000.
Proof.
  intros lead fps p Hf Hp Hs. rewrite (qdisc_spec_pos lead fps p Hf Hp).
  pose proof (qdisc_n_gt_cap p Hs).
  replace (p / 1000000 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (1000000 <? p / 1000000) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma qdisc_spec_mid : forall lead fps p, 0 < fps -> p = Z.max 0 (lead - 300) * fps ->
  1000000 <= p <= 1000000999999 -> slots_spec lead fps = p / 1000000.
Proof.
  intros lead fps p Hf Hp Hs. rewrite (qdisc_spec_pos lead fps p Hf Hp).
  pose proof (qdisc_n_ge1 p (proj1 Hs)). pose proof (qdisc_n_le_cap p ltac:(lia) (proj2 Hs)).
  replace (p / 1000000 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (1000000 <? p / 1000000) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.
