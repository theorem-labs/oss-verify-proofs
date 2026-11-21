(** * KeyBits — bit-plumbing helpers for the ownership S-instance.

    Self-contained over the tree's
    Bits/ItGTblRev/ItGTblGeom stock; consumed by KeyClass's
    own_step_cont/own_step_break (pieces 3-4).


    NOTE [zrev] here is ItGTblRev's (odd/div2 form) — the one CovInv
    speaks.  HuffGenCodes has a different-but-equal zrev; the bridge
    [zrev_agree] lives in KeyClass and is not needed here.

    Landed stock to build on: zrev_split (ItGTblRev:106, THE
    decomposition), zrev_widen (ItGTblGeom:135), zrev_lt/nonneg/zero/
    ones/one, shift_down_spec (ItGTblRev:247, the it_shift_down
    characterization), shift_down_zero, write_bits_testbit (Bits:238),
    write_bits_length, Z.mod_pow2_bits_low (stdlib). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees ItGTblRev ItGTblGeom.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** H1 — reversal is injective on the width's range. *)
Lemma zrev_inj : forall (n : nat) (a b : Z),
  0 <= a < 2 ^ Z.of_nat n ->
  0 <= b < 2 ^ Z.of_nat n ->
  zrev n a = zrev n b ->
  a = b.
Proof.
  induction n as [|k IH]; intros a b Ha Hb Heq.
  - change (Z.of_nat 0) with 0 in Ha, Hb.
    rewrite Z.pow_0_r in Ha, Hb. lia.
  - cbn [zrev] in Heq.
    pose proof (zrev_lt k (Z.div2 a)) as Hla.
    pose proof (zrev_lt k (Z.div2 b)) as Hlb.
    pose proof (zrev_nonneg k (Z.div2 a)) as Hna.
    pose proof (zrev_nonneg k (Z.div2 b)) as Hnb.
    pose proof (Z.div2_odd a) as Hda.
    pose proof (Z.div2_odd b) as Hdb.
    pose proof (pow2_pos_nat k) as Hp.
    rewrite pow2_succ_nat in Ha, Hb.
    assert (Hba : 0 <= Z.div2 a < 2 ^ Z.of_nat k).
    { rewrite Z.div2_div. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    assert (Hbb : 0 <= Z.div2 b < 2 ^ Z.of_nat k).
    { rewrite Z.div2_div. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    revert Heq Hda Hdb.
    destruct (Z.odd a); destruct (Z.odd b); cbn [Z.b2z];
      intros Heq Hda Hdb.
    + assert (Z.div2 a = Z.div2 b)
        by (apply IH; [exact Hba|exact Hbb|lia]).
      lia.
    + exfalso. lia.
    + exfalso. lia.
    + assert (Z.div2 a = Z.div2 b)
        by (apply IH; [exact Hba|exact Hbb|lia]).
      lia.
Qed.

(** H2 — a prefix of an LSB-first expansion is the narrower expansion. *)
Lemma firstn_write_bits : forall (k n : nat) (v : Z),
  (k <= n)%nat ->
  firstn k (write_bits n v) = write_bits k v.
Proof.
  induction k as [|k IH]; intros n v Hk.
  - reflexivity.
  - destruct n as [|n]; [lia|].
    cbn [write_bits firstn]. f_equal. apply IH. lia.
Qed.

(** H3 — write_bits reads only the low bits. *)
Lemma write_bits_mod_low : forall (k : nat) (a b : Z),
  a mod 2 ^ Z.of_nat k = b mod 2 ^ Z.of_nat k ->
  write_bits k a = write_bits k b.
Proof.
  intros k a b Hab.
  rewrite !write_bits_testbit.
  apply map_ext_in. intros i Hi.
  apply in_seq in Hi.
  rewrite <- (Z.mod_pow2_bits_low a (Z.of_nat k) (Z.of_nat i)) by lia.
  rewrite <- (Z.mod_pow2_bits_low b (Z.of_nat k) (Z.of_nat i)) by lia.
  rewrite Hab. reflexivity.
Qed.

(** H6 — splitting an expansion at bit [a]. *)
Lemma write_bits_app_split : forall (a n : nat) (v : Z),
  0 <= v ->
  (a <= n)%nat ->
  write_bits n v
  = write_bits a v ++ write_bits (n - a) (v / 2 ^ Z.of_nat a).
Proof.
  induction a as [|a IH]; intros n v Hv Hn.
  - cbn [write_bits app].
    change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, Z.div_1_r, Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [lia|].
    cbn [write_bits].
    replace (S n - S a)%nat with (n - a)%nat by lia.
    cbn [app]. f_equal.
    assert (Hv2 : 0 <= v / 2) by (apply Z.div_pos; lia).
    rewrite (IH n (v / 2) Hv2 ltac:(lia)).
    f_equal. f_equal.
    pose proof (pow2_pos_nat a) as Hp.
    rewrite Z.div_div by lia.
    f_equal. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** H4' — THE scale-free window-hit characterization: an index [j] of
    width [w] falls in the reversed window of the width-[d] prefix [h]
    exactly when its low [d] bits are [h].  Multiply both sides by the
    ambient [2^(15-...)] scale at each use site. *)
Lemma zrev_window_hit : forall (d w : nat) (h j : Z),
  (d <= w)%nat ->
  0 <= h < 2 ^ Z.of_nat d ->
  0 <= j < 2 ^ Z.of_nat w ->
  ( zrev d h * 2 ^ Z.of_nat (w - d) <= zrev w j
    /\ zrev w j < zrev d h * 2 ^ Z.of_nat (w - d) + 2 ^ Z.of_nat (w - d) )
  <-> j mod 2 ^ Z.of_nat d = h.
Proof.
  intros d w h j Hdw Hh Hj.
  pose proof (pow2_pos_nat d) as Hpd.
  pose proof (pow2_pos_nat (w - d)) as Hpwd.
  assert (Hjlo : 0 <= j mod 2 ^ Z.of_nat d < 2 ^ Z.of_nat d)
    by (apply Z.mod_pos_bound; lia).
  assert (Hjhi : 0 <= j / 2 ^ Z.of_nat d < 2 ^ Z.of_nat (w - d)).
  { split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z.pow_add_r by lia.
      replace (Z.of_nat d + Z.of_nat (w - d)) with (Z.of_nat w) by lia.
      lia. }
  assert (Hdec : zrev w j
      = zrev d (j mod 2 ^ Z.of_nat d) * 2 ^ Z.of_nat (w - d)
        + zrev (w - d) (j / 2 ^ Z.of_nat d)).
  { replace w with (d + (w - d))%nat at 1 by lia.
    rewrite <- (zrev_split d (w - d) (j mod 2 ^ Z.of_nat d)
                  (j / 2 ^ Z.of_nat d) Hjlo).
    f_equal.
    rewrite (Z.div_mod j (2 ^ Z.of_nat d)) at 1 by lia.
    ring. }
  pose proof (zrev_nonneg (w - d) (j / 2 ^ Z.of_nat d)) as Ht0.
  pose proof (zrev_lt (w - d) (j / 2 ^ Z.of_nat d)) as Ht1.
  split.
  - intros [Hlo Hhi].
    rewrite Hdec in Hlo, Hhi.
    assert (Heqr : zrev d (j mod 2 ^ Z.of_nat d) = zrev d h) by nia.
    exact (zrev_inj d _ _ Hjlo Hh Heqr).
  - intro Hmod.
    rewrite Hdec, Hmod.
    split; lia.
Qed.

(** H7 — the reversed increment wraps to 0 exactly at all-ones.
    (Left disjunct of shift_down_spec at j := len-1, n := 17.) *)
Lemma it_rev_incr_ones : forall len,
  1 <= len <= 15 ->
  it_rev_incr (2 ^ len - 1) len = 0.
Proof.
  intros len Hlen.
  assert (Hp : 0 < 2 ^ len) by (apply Z.pow_pos_nonneg; lia).
  unfold it_rev_incr. cbv zeta.
  set (jn := Z.to_nat (len - 1)).
  assert (Hjn : Z.of_nat jn = len - 1) by (unfold jn; lia).
  assert (HSj : Z.of_nat (S jn) = len)
    by (rewrite Nat2Z.inj_succ; lia).
  assert (Hshift : Z.shiftl 1 (len - 1) = 2 ^ Z.of_nat jn)
    by (rewrite Z.shiftl_1_l, Hjn; reflexivity).
  rewrite Hshift.
  pose proof (shift_down_spec jn 17%nat (2 ^ len - 1)
                ltac:(lia) ltac:(lia))
    as [ [Hincr _] | (p & Hple & Hincr & Hmod) ].
  - rewrite Hincr. reflexivity.
  - exfalso.
    rewrite HSj in Hmod.
    pose proof (pow2_pos_nat p) as Hpp.
    assert (Hmm : (2 ^ len - 1) mod 2 ^ len = 2 ^ len - 1)
      by (apply Z.mod_small; lia).
    assert (Hpb : 0 <= (2 ^ len - 1) mod 2 ^ Z.of_nat p < 2 ^ Z.of_nat p)
      by (apply Z.mod_pos_bound; lia).
    rewrite Hmm in Hmod.
    rewrite pow2_succ_nat in Hmod.
    lia.
Qed.

(** H8 — the reversed increment of 0 sets the top bit.
    (First land test is 0, so incr = 2^(len-1) and huff&(incr-1) = 0.) *)
Lemma it_rev_incr_zero : forall len,
  1 <= len ->
  it_rev_incr 0 len = 2 ^ (len - 1).
Proof.
  intros len Hlen.
  assert (Hp : 0 < 2 ^ (len - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hsd : forall (k : nat) (incr : Z),
             it_shift_down (S k) 0 incr = incr).
  { intros k incr. cbn [it_shift_down].
    rewrite Z.land_0_l, Z.eqb_refl. reflexivity. }
  unfold it_rev_incr. cbv zeta.
  rewrite (Hsd 16%nat (Z.shiftl 1 (len - 1))).
  rewrite Z.shiftl_1_l.
  rewrite Z.land_0_l.
  destruct (Z.eqb_spec (2 ^ (len - 1)) 0) as [E|E]; [lia|].
  cbv iota. lia.
Qed.
