(** * Spec.PngModel.ChecksumThy — the braid identity for [crc32_z].

    TRUST BOUNDARY: pure Gallina.  Depends on [Spec.PngModel.Base],
    [Spec.PngModel.Checksum] and Stdlib.

    [Spec/PngModel/Checksum.v] transcribes the braided word-at-a-time
    [crc32_z] the delivered riscv64 binary contains ([crc32.c:693-1029],
    N = 5, W = 4, little endian).  This file proves it computes the ordinary
    byte-at-a-time CRC, at EVERY buffer alignment:

      [crc32_braid_eq : crc32_z_at crc align bs = crc32_ref crc bs]

    which is what the round-trip DAG needs: libpng feeds the same chunk
    bytes to [crc32] on the write and the read side, but at different
    addresses and in different call splits (c5-invariants.md §2.3,
    "Decode-side checks pass by function equality").  Alignment-independence
    ([crc32_z_at_align]) and split-independence ([crc32_ref_app]) are
    corollaries.

    The argument is the standard GF(2) one, done concretely:

    - the shift register [xtime] is linear over [Z.lxor] (case analysis on
      two parity bits), hence so are [crc_e], [crc_word_step] and [advz];
    - [advz_split] decomposes [advz n x] into the surviving high bits plus
      one [crc_e] contribution per consumed byte;
    - [crc_braid_advK] identifies the binary's braid-table entry
      [crc_braid k i] with [advz (19 - k) (crc_e i)] — a finite check over
      all 4*256 entries, so the proof is tied to the SAME table the
      [.rodata] comparison validated;
    - hence [br_one_advz]: one braid trip advances its lane by exactly the
      [N*W = 20] bytes the other four lanes consume meanwhile;
    - [braid_correct] folds the five lanes and the last-block combine
      ([crc32.c:826-844]) into [crc_words], and [crc_words_bytes] turns
      that back into [crc_bytes]. *)

From Stdlib Require Import ZArith List Lia Btauto.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Checksum.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** An associativity/commutativity/nilpotency solver for [Z.lxor] equalities:
    compare the two sides bit by bit and hand the boolean identity to
    [btauto]. *)
Ltac xac :=
  apply Z.bits_inj'; intros ?bi ?bH; rewrite ?Z.lxor_spec, ?Z.bits_0; btauto.

(** ** Bitwise plumbing *)

Lemma shiftr_lxor : forall a b n, 0 <= n ->
  Z.shiftr (Z.lxor a b) n = Z.lxor (Z.shiftr a n) (Z.shiftr b n).
Proof.
  intros a b n Hn. apply Z.bits_inj'; intros m Hm.
  rewrite Z.lxor_spec, !Z.shiftr_spec, Z.lxor_spec by assumption. reflexivity.
Qed.

Lemma land_lxor : forall a b m,
  Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
  intros a b m. apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. btauto.
Qed.

Lemma odd_lxor : forall a b, Z.odd (Z.lxor a b) = xorb (Z.odd a) (Z.odd b).
Proof. intros a b. rewrite <- !Z.bit0_odd, Z.lxor_spec. reflexivity. Qed.

(** ** Linearity of the shift register *)

Lemma xtime_lxor : forall a b, xtime (Z.lxor a b) = Z.lxor (xtime a) (xtime b).
Proof.
  intros a b. unfold xtime.
  rewrite odd_lxor, (shiftr_lxor a b 1) by lia.
  destruct (Z.odd a), (Z.odd b); cbn [xorb]; xac.
Qed.

Lemma xtimes_lxor : forall n a b,
  xtimes n (Z.lxor a b) = Z.lxor (xtimes n a) (xtimes n b).
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  cbn [xtimes]. rewrite xtime_lxor. apply IH.
Qed.

Lemma crc_e_lxor : forall a b, crc_e (Z.lxor a b) = Z.lxor (crc_e a) (crc_e b).
Proof. intros; unfold crc_e; apply xtimes_lxor. Qed.

Lemma crc_e_0 : crc_e 0 = 0.
Proof. reflexivity. Qed.

Lemma step_lxor : forall a b,
  crc_word_step (Z.lxor a b) = Z.lxor (crc_word_step a) (crc_word_step b).
Proof.
  intros a b. unfold crc_word_step, crc_table.
  rewrite (shiftr_lxor a b 8) by lia. rewrite land_lxor, crc_e_lxor. xac.
Qed.

Lemma advz_lxor : forall n a b, advz n (Z.lxor a b) = Z.lxor (advz n a) (advz n b).
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  cbn [advz]. rewrite step_lxor. apply IH.
Qed.

Lemma advz_0 : forall n, advz n 0 = 0.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [advz]. change (crc_word_step 0) with 0. exact IH.
Qed.

Lemma advz_add : forall n m x, advz (m + n) x = advz m (advz n x).
Proof.
  induction n as [|n IH]; intros m x.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. cbn [advz]. apply IH.
Qed.

(** ** 32-bit-ness, tracked as "no bit at index 32 or above" *)

Definition w32 (x : Z) : Prop := Z.shiftr x 32 = 0.

Lemma w32_lxor : forall a b, w32 a -> w32 b -> w32 (Z.lxor a b).
Proof. intros a b Ha Hb; unfold w32; rewrite shiftr_lxor by lia; now rewrite Ha, Hb. Qed.

Lemma w32_0 : w32 0.
Proof. reflexivity. Qed.

Lemma w32_small : forall x, 0 <= x < 4294967296 -> w32 x.
Proof.
  intros x H. unfold w32. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_small. change (2 ^ 32) with 4294967296. lia.
Qed.

Lemma w32_shiftr : forall x n, 0 <= n -> w32 x -> w32 (Z.shiftr x n).
Proof.
  intros x n Hn Hx; unfold w32 in *.
  rewrite Z.shiftr_shiftr by lia.
  replace (n + 32) with (32 + n) by lia.
  rewrite <- Z.shiftr_shiftr by lia. now rewrite Hx, Z.shiftr_0_l.
Qed.

Lemma land255_range : forall x, 0 <= Z.land x 255 < 256.
Proof.
  intro x. assert (H := Z.land_ones x 8 ltac:(lia)).
  change (Z.ones 8) with 255 in H. rewrite H.
  pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)).
  change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma land255_id : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
  intros x Hx. assert (H := Z.land_ones x 8 ltac:(lia)).
  change (Z.ones 8) with 255 in H. rewrite H.
  change (2 ^ 8) with 256. apply Z.mod_small; lia.
Qed.

Lemma w32_xtime : forall x, w32 x -> w32 (xtime x).
Proof.
  intros x Hx; unfold xtime. destruct (Z.odd x).
  - apply w32_lxor; [now apply w32_shiftr | apply w32_small; unfold POLY; lia].
  - now apply w32_shiftr.
Qed.

Lemma w32_xtimes : forall n x, w32 x -> w32 (xtimes n x).
Proof.
  induction n as [|n IH]; intros x Hx; [exact Hx|].
  cbn [xtimes]. apply IH, w32_xtime, Hx.
Qed.

Lemma w32_crc_e : forall x, w32 (crc_e (Z.land x 255)).
Proof.
  intro x; unfold crc_e; apply w32_xtimes, w32_small.
  pose proof (land255_range x); lia.
Qed.

Lemma w32_step : forall x, w32 x -> w32 (crc_word_step x).
Proof.
  intros x Hx; unfold crc_word_step, crc_table.
  apply w32_lxor; [now apply w32_shiftr | apply w32_crc_e].
Qed.

Lemma w32_advz : forall n x, w32 x -> w32 (advz n x).
Proof.
  induction n as [|n IH]; intros x Hx; [exact Hx|].
  cbn [advz]. apply IH, w32_step, Hx.
Qed.

(** ** Decomposing [advz] into per-byte contributions

    [accf n x] is [xor_{k < n} advz (n-1-k) (crc_e (byte k of x))]. *)
Fixpoint accf (n : nat) (x : Z) {struct n} : Z :=
  match n with
  | O => 0
  | S m => Z.lxor (advz m (crc_e (Z.land x 255))) (accf m (Z.shiftr x 8))
  end.

Lemma advz_split : forall n x,
  advz n x = Z.lxor (Z.shiftr x (8 * Z.of_nat n)) (accf n x).
Proof.
  induction n as [|n IH]; intros x.
  - cbn [advz accf]. now rewrite Z.shiftr_0_r, Z.lxor_0_r.
  - cbn [advz accf]. unfold crc_word_step at 1. unfold crc_table.
    rewrite advz_lxor, IH.
    rewrite Z.shiftr_shiftr by lia.
    replace (8 + 8 * Z.of_nat n) with (8 * Z.of_nat (S n)) by lia.
    xac.
Qed.

Lemma advz4_accf : forall x, w32 x -> advz 4 x = accf 4 x.
Proof.
  intros x Hx. rewrite advz_split.
  replace (8 * Z.of_nat 4) with 32 by lia. rewrite Hx. now rewrite Z.lxor_0_l.
Qed.

(** ** The braid table

    A finite check: the value the binary's [crc_braid_table[k][i]] holds is
    "the CRC of the single byte [i], advanced by [19 - k] zero bytes". *)

Fixpoint chk256 (n : nat) (f g : Z -> Z) {struct n} : bool :=
  match n with
  | O => true
  | S m => andb (Z.eqb (f (Z.of_nat m)) (g (Z.of_nat m))) (chk256 m f g)
  end.

(** Stated with [Base]'s canonical range-agreement relation rather than a
    bespoke [forall i, ... -> f i = g i]: this IS an [arr_eq_on] fact, and
    saying so is what lets it compose with the window and table lemmas
    instead of sitting in its own idiom. *)
Lemma chk256_correct : forall n f g,
  chk256 n f g = true -> arr_eq_on f g 0 (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros f g H i Hi; [cbn in Hi; lia|].
  cbn [chk256] in H. apply andb_prop in H as [He Hr].
  destruct (Z.eq_dec i (Z.of_nat n)) as [->|Hne].
  - now apply Z.eqb_eq in He.
  - apply (IH f g Hr); [rewrite Nat2Z.inj_succ in Hi; lia].
Qed.

Lemma crc_braid_adv0 : forall i, 0 <= i < 256 -> crc_braid 0 i = advz 19 (crc_e i).
Proof. apply (chk256_correct 256); vm_compute; reflexivity. Qed.

Lemma crc_braid_adv1 : forall i, 0 <= i < 256 -> crc_braid 1 i = advz 18 (crc_e i).
Proof. apply (chk256_correct 256); vm_compute; reflexivity. Qed.

Lemma crc_braid_adv2 : forall i, 0 <= i < 256 -> crc_braid 2 i = advz 17 (crc_e i).
Proof. apply (chk256_correct 256); vm_compute; reflexivity. Qed.

Lemma crc_braid_adv3 : forall i, 0 <= i < 256 -> crc_braid 3 i = advz 16 (crc_e i).
Proof. apply (chk256_correct 256); vm_compute; reflexivity. Qed.

(** One braid trip advances its lane by exactly [N*W = 20] bytes. *)
Lemma br_one_advz : forall c w, w32 c -> w32 w -> br_one c w = advz 20 (Z.lxor c w).
Proof.
  intros c w Hc Hw.
  assert (Hx : w32 (Z.lxor c w)) by (apply w32_lxor; assumption).
  unfold br_one.
  rewrite crc_braid_adv0 by apply land255_range.
  rewrite crc_braid_adv1 by apply land255_range.
  rewrite crc_braid_adv2 by apply land255_range.
  rewrite crc_braid_adv3 by apply land255_range.
  replace 20%nat with (16 + 4)%nat by reflexivity.
  rewrite advz_add, advz4_accf by exact Hx.
  cbn [accf].
  rewrite !advz_lxor, advz_0, !Z.lxor_0_r.
  rewrite <- !advz_add. cbn [Nat.add].
  rewrite !Z.shiftr_shiftr by lia.
  replace (8 + 8) with 16 by reflexivity.
  replace (16 + 8) with 24 by reflexivity.
  xac.
Qed.

(** ** From bytes to words *)

Lemma crc_byte_step : forall c b, 0 <= b < 256 ->
  crc_byte c b = crc_word_step (Z.lxor c b).
Proof.
  intros c b Hb. unfold crc_byte, crc_word_step.
  rewrite (shiftr_lxor c b 8) by lia.
  replace (Z.shiftr b 8) with 0.
  - now rewrite Z.lxor_0_r.
  - symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small.
    change (2 ^ 8) with 256. lia.
Qed.

Lemma advz1_byte : forall b, 0 <= b < 256 -> advz 1 b = crc_e b.
Proof.
  intros b Hb. cbn [advz]. unfold crc_word_step, crc_table.
  rewrite land255_id by exact Hb.
  replace (Z.shiftr b 8) with 0.
  - now rewrite Z.lxor_0_l.
  - symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small.
    change (2 ^ 8) with 256. lia.
Qed.

Definition bytes (l : list Z) : Prop := forall b, In b l -> 0 <= b < 256.

Lemma crc_bytes_lin : forall l c d, bytes l ->
  crc_bytes (Z.lxor c d) l = Z.lxor (crc_bytes c l) (advz (length l) d).
Proof.
  unfold crc_bytes.
  induction l as [|b r IH]; intros c d Hl; [reflexivity|].
  cbn [fold_left length].
  assert (Hb : 0 <= b < 256) by (apply Hl; now left).
  rewrite !crc_byte_step by exact Hb.
  replace (Z.lxor (Z.lxor c d) b) with (Z.lxor (Z.lxor c b) d) by xac.
  rewrite step_lxor, IH by (intros x Hx; apply Hl; now right).
  (* [advz (S n) d] is [advz n (crc_word_step d)] by definition *)
  now f_equal.
Qed.

Lemma crc_bytes_from0 : forall l c, bytes l ->
  crc_bytes c l = Z.lxor (advz (length l) c) (crc_bytes 0 l).
Proof.
  intros l c Hl. pose proof (crc_bytes_lin l 0 c Hl) as H.
  rewrite Z.lxor_0_l in H. rewrite H. apply Z.lxor_comm.
Qed.

Lemma crc_bytes_app : forall l1 l2 c, bytes (l1 ++ l2) ->
  crc_bytes c (l1 ++ l2)
  = Z.lxor (advz (length l2) (crc_bytes c l1)) (crc_bytes 0 l2).
Proof.
  intros l1 l2 c Hl.
  assert (Hsplit : crc_bytes c (l1 ++ l2) = crc_bytes (crc_bytes c l1) l2)
    by (unfold crc_bytes; apply fold_left_app).
  rewrite Hsplit, crc_bytes_from0
    by (intros x Hx; apply Hl, in_or_app; now right).
  reflexivity.
Qed.

Lemma crc_bytes_one : forall b, 0 <= b < 256 -> crc_bytes 0 [b] = crc_e b.
Proof.
  intros b Hb. unfold crc_bytes; cbn [fold_left].
  rewrite crc_byte_step by exact Hb. rewrite Z.lxor_0_l.
  change (crc_word_step b) with (advz 1 b). now apply advz1_byte.
Qed.

(** ** The little-endian word *)

Lemma byte_at0 : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  Z.land (le32 b0 b1 b2 b3) 255 = b0.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  assert (H := Z.land_ones (le32 b0 b1 b2 b3) 8 ltac:(lia)).
  change (Z.ones 8) with 255 in H. rewrite H. unfold le32.
  change (2 ^ 8) with 256.
  replace (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)
     with (b0 + (b1 + 256 * b2 + 65536 * b3) * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma le32_shift : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 -> 0 <= b2 -> 0 <= b3 ->
  Z.shiftr (le32 b0 b1 b2 b3) 8 = le32 b1 b2 b3 0.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. rewrite Z.shiftr_div_pow2 by lia.
  unfold le32. change (2 ^ 8) with 256.
  replace (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)
     with ((b1 + 256 * b2 + 65536 * b3) * 256 + b0) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small b0 256) by lia. lia.
Qed.

Lemma w32_le32 : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  w32 (le32 b0 b1 b2 b3).
Proof. intros; apply w32_small; unfold le32; lia. Qed.

Lemma word_step : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  crc_bytes 0 [b0; b1; b2; b3] = advz 4 (le32 b0 b1 b2 b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  (* right-hand side: four per-byte contributions *)
  rewrite advz4_accf by (apply w32_le32; assumption).
  cbn [accf].
  rewrite (byte_at0 b0 b1 b2 b3) by lia.
  rewrite (le32_shift b0 b1 b2 b3) by lia.
  rewrite (byte_at0 b1 b2 b3 0) by lia.
  rewrite (le32_shift b1 b2 b3 0) by lia.
  rewrite (byte_at0 b2 b3 0 0) by lia.
  rewrite (le32_shift b2 b3 0 0) by lia.
  rewrite (byte_at0 b3 0 0 0) by lia.
  (* left-hand side: split the list one byte at a time *)
  change [b0; b1; b2; b3] with ([b0] ++ [b1; b2; b3]).
  rewrite crc_bytes_app by (intros x Hx; cbn in Hx; intuition (subst; lia)).
  change [b1; b2; b3] with ([b1] ++ [b2; b3]).
  rewrite crc_bytes_app by (intros x Hx; cbn in Hx; intuition (subst; lia)).
  change [b2; b3] with ([b2] ++ [b3]).
  rewrite crc_bytes_app by (intros x Hx; cbn in Hx; intuition (subst; lia)).
  rewrite !crc_bytes_one by assumption.
  cbn [length app advz].
  xac.
Qed.

(** ** The braid loop *)

Definition crc_words (c : Z) (ws : list Z) : Z :=
  fold_left (fun s w => advz 4 (Z.lxor s w)) ws c.

Lemma crc_words_lin : forall ws c d,
  crc_words (Z.lxor c d) ws = Z.lxor (crc_words c ws) (advz (4 * length ws) d).
Proof.
  unfold crc_words.
  induction ws as [|w r IH]; intros c d; [now rewrite Nat.mul_0_r|].
  cbn [fold_left length].
  replace (Z.lxor (Z.lxor c d) w) with (Z.lxor (Z.lxor c w) d) by xac.
  rewrite advz_lxor, IH. f_equal.
  rewrite <- advz_add. f_equal. lia.
Qed.

Lemma crc_words_from0 : forall l c,
  crc_words c l = Z.lxor (advz (4 * length l) c) (crc_words 0 l).
Proof.
  intros l c. pose proof (crc_words_lin l 0 c) as H.
  rewrite Z.lxor_0_l in H. rewrite H. apply Z.lxor_comm.
Qed.

Lemma crc_words_app : forall l1 l2 c,
  crc_words c (l1 ++ l2)
  = Z.lxor (advz (4 * length l2) (crc_words c l1)) (crc_words 0 l2).
Proof.
  intros l1 l2 c.
  assert (Hsplit : crc_words c (l1 ++ l2) = crc_words (crc_words c l1) l2)
    by (unfold crc_words; apply fold_left_app).
  rewrite Hsplit, crc_words_from0. reflexivity.
Qed.

(** [le_words] turns a byte list whose length is a multiple of 4 into the
    word list the braid consumes, and [crc_bytes] follows. *)
Lemma crc_words_bytes : forall k l c, bytes l -> length l = (4 * k)%nat ->
  crc_bytes c l = crc_words c (le_words l).
Proof.
  induction k as [|k IH]; intros l c Hb Hk.
  - destruct l as [|b r]; [reflexivity | cbn [length] in Hk; lia].
  - destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hk; try lia.
    assert (Hb0 : 0 <= b0 < 256) by (apply Hb; cbn; tauto).
    assert (Hb1 : 0 <= b1 < 256) by (apply Hb; cbn; tauto).
    assert (Hb2 : 0 <= b2 < 256) by (apply Hb; cbn; tauto).
    assert (Hb3 : 0 <= b3 < 256) by (apply Hb; cbn; tauto).
    cbn [le_words crc_words fold_left].
    change (b0 :: b1 :: b2 :: b3 :: r) with ([b0; b1; b2; b3] ++ r).
    unfold crc_bytes at 1. rewrite fold_left_app.
    change (fold_left crc_byte [b0; b1; b2; b3] c)
      with (crc_bytes c [b0; b1; b2; b3]).
    replace (crc_bytes c [b0; b1; b2; b3])
       with (advz 4 (Z.lxor c (le32 b0 b1 b2 b3))).
    2:{ rewrite crc_bytes_from0
          by (intros x Hx; cbn in Hx; intuition (subst; lia)).
        rewrite word_step by assumption. cbn [length].
        rewrite advz_lxor. reflexivity. }
    (* both sides are now the same statement on [r], up to unfolding *)
    apply (IH r); [intros x Hx; apply Hb; cbn; tauto | lia].
Qed.

(** The last-block combine ([crc32.c:826-844]), in closed form. *)
Lemma br_final_combine :
  forall c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 rest,
    br_final {| b_c0 := c0; b_c1 := c1; b_c2 := c2; b_c3 := c3; b_c4 := c4;
                b_ws := w0 :: w1 :: w2 :: w3 :: w4 :: rest |}
    = Z.lxor (advz 20 (Z.lxor c0 w0))
      (Z.lxor (advz 16 (Z.lxor c1 w1))
      (Z.lxor (advz 12 (Z.lxor c2 w2))
      (Z.lxor (advz 8 (Z.lxor c3 w3)) (advz 4 (Z.lxor c4 w4))))).
Proof.
  intros. cbn [br_final b_ws b_c0 b_c1 b_c2 b_c3 b_c4]. unfold crc_word.
  set (x0 := Z.lxor c0 w0). set (x1 := Z.lxor c1 w1). set (x2 := Z.lxor c2 w2).
  set (x3 := Z.lxor c3 w3). set (x4 := Z.lxor c4 w4).
  rewrite (advz_lxor 4 x1), (advz_lxor 4 x2), (advz_lxor 4 x3), (advz_lxor 4 x4).
  rewrite <- !advz_add. cbn [Nat.add].
  rewrite !advz_lxor, <- !advz_add. cbn [Nat.add].
  xac.
Qed.

Lemma crc_words5 : forall w0 w1 w2 w3 w4,
  crc_words 0 [w0; w1; w2; w3; w4]
  = Z.lxor (advz 20 w0)
    (Z.lxor (advz 16 w1)
    (Z.lxor (advz 12 w2) (Z.lxor (advz 8 w3) (advz 4 w4)))).
Proof.
  intros. unfold crc_words; cbn [fold_left]. rewrite Z.lxor_0_l.
  rewrite !advz_lxor, <- !advz_add. cbn [Nat.add]. xac.
Qed.

(** The five-lane invariant.  After [m] trips the braid state holds each
    lane's partial CRC advanced by the bytes the other lanes consumed; the
    last-block combine then folds them back together. *)
Lemma braid_correct : forall m c0 c1 c2 c3 c4 ws,
  length ws = (5 * S m)%nat ->
  (forall w, In w ws -> w32 w) ->
  w32 c0 -> w32 c1 -> w32 c2 -> w32 c3 -> w32 c4 ->
  br_final (br_iter m {| b_c0 := c0; b_c1 := c1; b_c2 := c2;
                         b_c3 := c3; b_c4 := c4; b_ws := ws |})
  = Z.lxor
      (Z.lxor (advz (20 * m + 20) c0)
      (Z.lxor (advz (20 * m + 16) c1)
      (Z.lxor (advz (20 * m + 12) c2)
      (Z.lxor (advz (20 * m + 8) c3) (advz (20 * m + 4) c4)))))
      (crc_words 0 ws).
Proof.
  induction m as [|m IH]; intros c0 c1 c2 c3 c4 ws Hlen Hw H0 H1 H2 H3 H4.
  - destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 r]]]]];
      cbn [length] in Hlen; try lia.
    destruct r as [|w5 r]; [|cbn [length] in Hlen; lia].
    cbn [br_iter]. rewrite br_final_combine, crc_words5.
    cbn [Nat.mul Nat.add].
    rewrite !advz_lxor. xac.
  - destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 r]]]]];
      cbn [length] in Hlen; try lia.
    assert (Hw0 : w32 w0) by (apply Hw; cbn; tauto).
    assert (Hw1 : w32 w1) by (apply Hw; cbn; tauto).
    assert (Hw2 : w32 w2) by (apply Hw; cbn; tauto).
    assert (Hw3 : w32 w3) by (apply Hw; cbn; tauto).
    assert (Hw4 : w32 w4) by (apply Hw; cbn; tauto).
    assert (Hlr : length r = (5 * S m)%nat) by (cbn [length] in Hlen; lia).
    cbn [br_iter br_step b_ws b_c0 b_c1 b_c2 b_c3 b_c4].
    rewrite !br_one_advz by assumption.
    rewrite IH; try (apply w32_advz, w32_lxor; assumption);
      [| exact Hlr | intros x Hx; apply Hw; cbn; tauto].
    change (w0 :: w1 :: w2 :: w3 :: w4 :: r) with ([w0; w1; w2; w3; w4] ++ r).
    rewrite crc_words_app, crc_words5, Hlr.
    rewrite !advz_lxor, <- !advz_add.
    replace (20 * m + 20 + 20)%nat with (4 * (5 * S m) + 20)%nat by lia.
    replace (20 * m + 16 + 20)%nat with (4 * (5 * S m) + 16)%nat by lia.
    replace (20 * m + 12 + 20)%nat with (4 * (5 * S m) + 12)%nat by lia.
    replace (20 * m + 8 + 20)%nat with (4 * (5 * S m) + 8)%nat by lia.
    replace (20 * m + 4 + 20)%nat with (4 * (5 * S m) + 4)%nat by lia.
    replace (20 * S m + 20)%nat with (4 * (5 * S m) + 20)%nat by lia.
    replace (20 * S m + 16)%nat with (4 * (5 * S m) + 16)%nat by lia.
    replace (20 * S m + 12)%nat with (4 * (5 * S m) + 12)%nat by lia.
    replace (20 * S m + 8)%nat with (4 * (5 * S m) + 8)%nat by lia.
    replace (20 * S m + 4)%nat with (4 * (5 * S m) + 4)%nat by lia.
    xac.
Qed.

(** ** From the braid loop back to [crc32_z] *)

Lemma w32_crc_byte : forall c b, w32 c -> w32 (crc_byte c b).
Proof.
  intros c b Hc. unfold crc_byte, crc_table.
  apply w32_lxor; [now apply w32_shiftr | apply w32_crc_e].
Qed.

Lemma w32_crc_bytes : forall l c, w32 c -> w32 (crc_bytes c l).
Proof.
  unfold crc_bytes. induction l as [|b r IH]; intros c Hc; [exact Hc|].
  cbn [fold_left]. apply IH, w32_crc_byte, Hc.
Qed.

Lemma bytes_firstn : forall n l, bytes l -> bytes (firstn n l).
Proof.
  intros n l H x Hx. apply H. rewrite <- (firstn_skipn n l).
  apply in_or_app; now left.
Qed.

Lemma bytes_skipn : forall n l, bytes l -> bytes (skipn n l).
Proof.
  intros n l H x Hx. apply H. rewrite <- (firstn_skipn n l).
  apply in_or_app; now right.
Qed.

Lemma le_words_length : forall k l, length l = (4 * k)%nat -> length (le_words l) = k.
Proof.
  induction k as [|k IH]; intros l Hl.
  - destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hl; try lia; reflexivity.
  - destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hl; try lia.
    cbn [le_words length]. rewrite IH by lia. reflexivity.
Qed.

Lemma le_words_w32 : forall l, bytes l -> forall w, In w (le_words l) -> w32 w.
Proof.
  intro l. remember (length l) as n eqn:Hn. revert l Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros l Hn Hb w Hw.
  destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [le_words] in Hw;
    try (now cbn in Hw).
  destruct Hw as [<-|Hw].
  - apply w32_le32; apply Hb; cbn; tauto.
  - apply (IHn (length r)) with (l := r);
      [ subst n; cbn [length]; lia | reflexivity
      | intros x Hx; apply Hb; cbn; tauto | exact Hw ].
Qed.

Lemma braid_run : forall m c mid,
  bytes mid -> w32 c -> length mid = (20 * S m)%nat ->
  br_final (br_iter m {| b_c0 := c; b_c1 := 0; b_c2 := 0; b_c3 := 0; b_c4 := 0;
                         b_ws := le_words mid |})
  = crc_bytes c mid.
Proof.
  intros m c mid Hb Hc Hlen.
  assert (Hlw : length (le_words mid) = (5 * S m)%nat)
    by (apply le_words_length; lia).
  rewrite braid_correct
    by (assumption || exact Hlw || apply w32_0
        || (intros w Hw; apply (le_words_w32 mid Hb w Hw))).
  rewrite !advz_0, !Z.lxor_0_r.
  rewrite (crc_bytes_from0 mid c Hb), Hlen.
  rewrite (crc_words_bytes (5 * S m) mid 0) by (assumption || lia).
  replace (20 * m + 20)%nat with (20 * S m)%nat by lia.
  reflexivity.
Qed.

(** The braid computes the byte-at-a-time CRC, at every buffer alignment. *)
Theorem crc32_braid_eq : forall crc align bs,
  bytes bs -> crc32_z_at crc align bs = crc32_ref crc bs.
Proof.
  intros crc align bs Hb. unfold crc32_z_at, crc32_ref, NBRAID, WBYTES.
  set (c0 := u32 (Z.lnot crc)).
  assert (Hc0 : w32 c0)
    by (apply w32_small; unfold c0, u32; apply Z.mod_pos_bound; lia).
  destruct (Z.leb_spec (5 * 4 + 4 - 1) (Z.of_nat (length bs))) as [Hlen|Hlen];
    [| now rewrite crc_tail_eq].
  cbv zeta.
  set (npre := (- align) mod 4).
  assert (Hnp : 0 <= npre < 4) by (unfold npre; apply Z.mod_pos_bound; lia).
  set (pre := firstn (Z.to_nat npre) bs).
  set (rst := skipn (Z.to_nat npre) bs).
  assert (Hlpre : Z.of_nat (length pre) = npre)
    by (unfold pre; rewrite firstn_length_le by lia; lia).
  assert (Hlrst : Z.of_nat (length rst) = Z.of_nat (length bs) - npre)
    by (unfold rst; rewrite length_skipn; lia).
  set (blks := (Z.of_nat (length bs) - npre) / (5 * 4)).
  assert (Hb1 : 1 <= blks).
  { assert (H : 0 < (Z.of_nat (length bs) - npre) / (5 * 4))
      by (apply Z.div_str_pos; lia).
    unfold blks; lia. }
  assert (Hbl : 5 * 4 * blks <= Z.of_nat (length bs) - npre)
    by (unfold blks; apply Z.mul_div_le; lia).
  set (nmid := Z.to_nat (blks * 5 * 4)).
  set (mid := firstn nmid rst).
  set (tl := skipn nmid rst).
  assert (Hlmid : length mid = nmid)
    by (unfold mid; apply firstn_length_le; unfold nmid; lia).
  assert (Hbpre : bytes pre) by (apply bytes_firstn, Hb).
  assert (Hbrst : bytes rst) by (apply bytes_skipn, Hb).
  assert (Hbmid : bytes mid) by (apply bytes_firstn, Hbrst).
  assert (Hc1 : w32 (crc_bytes c0 pre)) by (apply w32_crc_bytes, Hc0).
  rewrite (braid_run (Z.to_nat (blks - 1)) (crc_bytes c0 pre) mid Hbmid Hc1)
    by (rewrite Hlmid; unfold nmid; lia).
  assert (Hcat : pre ++ mid ++ tl = bs).
  { unfold mid, tl. rewrite firstn_skipn. unfold pre, rst. apply firstn_skipn. }
  assert (Hsplit : crc_bytes c0 bs
                   = crc_bytes (crc_bytes (crc_bytes c0 pre) mid) tl).
  { rewrite <- Hcat. unfold crc_bytes. rewrite !fold_left_app. reflexivity. }
  rewrite crc_tail_eq, Hsplit. reflexivity.
Qed.

(** Corollaries the round-trip DAG actually consumes. *)
Corollary crc32_z_at_align : forall crc a b bs,
  bytes bs -> crc32_z_at crc a bs = crc32_z_at crc b bs.
Proof. intros; now rewrite !crc32_braid_eq. Qed.

Lemma w32_bound : forall x, w32 x -> 0 <= x < 4294967296.
Proof.
  intros x H. unfold w32 in H. rewrite Z.shiftr_div_pow2 in H by lia.
  change (2 ^ 32) with 4294967296 in H.
  apply Z.div_small_iff in H; [| lia]. destruct H as [H|H]; lia.
Qed.

Lemma u32_lnot_lxor : forall y, u32 (Z.lnot y) = Z.lxor (u32 y) 4294967295.
Proof.
  intro y. unfold u32. change 4294967296 with (2 ^ 32).
  rewrite <- !Z.land_ones by lia.
  change 4294967295 with (Z.ones 32).
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.ltb_spec n 32) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. btauto.
  - rewrite Z.ones_spec_high by lia. btauto.
Qed.

(** zlib's incremental usage: [crc32(crc32(c, a), b) = crc32(c, a ++ b)].
    libpng relies on this at every [png_calculate_crc] call
    ([pngrutil.c] / [pngwutil.c]), and it is what makes the write-side and
    read-side CRCs of one chunk the same number even though the two sides
    split the chunk into different pieces. *)
Corollary crc32_ref_app : forall crc l1 l2,
  crc32_ref crc (l1 ++ l2) = crc32_ref (crc32_ref crc l1) l2.
Proof.
  intros crc l1 l2.
  assert (Hc0 : w32 (u32 (Z.lnot crc)))
    by (apply w32_small; unfold u32; apply Z.mod_pos_bound; lia).
  set (X := crc_bytes (u32 (Z.lnot crc)) l1).
  assert (HX : w32 X) by (unfold X; now apply w32_crc_bytes).
  assert (HXo : w32 (Z.lxor X 4294967295))
    by (apply w32_lxor; [exact HX | apply w32_small; lia]).
  unfold crc32_ref. fold X.
  rewrite (u32_lnot_lxor (Z.lxor X 4294967295)).
  replace (u32 (Z.lxor X 4294967295)) with (Z.lxor X 4294967295)
    by (unfold u32; symmetry; apply Z.mod_small, w32_bound, HXo).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  unfold X, crc_bytes. now rewrite fold_left_app.
Qed.


(** ** 32-bit range of the CRC, which was missing until 2026-08-16

    [crc32_ref]'s outer operation is [Z.lxor _ 4294967295], NOT a [u32], so
    the 32-bit range is not syntactic — which is why wp5-pf, pricing the
    container bridge, could not find it and correctly took it as a
    hypothesis rather than assuming it.  Three lines from the [w32] algebra
    already in this file. *)
Corollary crc32_ref_range : forall crc bs,
  0 <= crc32_ref crc bs < 4294967296.
Proof.
  intros crc bs. apply w32_bound. unfold crc32_ref.
  apply w32_lxor.
  - apply w32_crc_bytes.
    apply w32_small; unfold u32; apply Z.mod_pos_bound; lia.
  - apply w32_small; lia.
Qed.
