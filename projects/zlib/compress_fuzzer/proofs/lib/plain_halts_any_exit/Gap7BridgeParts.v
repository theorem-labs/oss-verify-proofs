(** * Gap7BridgeParts — glue + the min-length regime bound (N1) for the
    r4 characterization bridge.

    OWNER: an earlier development run (lane fork; ladder item (d), piece file 1 of 2).
    Bed-only; lands with the bridge assembly after the r4 REPLACE.

    CONTENT: (i) [it_incomplete_lens_one] — the LENS twin of the landed
    [it_incomplete_dists_one]; (ii) [zlens_bounded] — the entry cap
    gives GtItTotal's [LensBounded] at the [it_pre] call shape;
    (iii) [count_len_filter1] — the r4 statement's filter spelling
    equals the histogram bucket; (iv) [ksum_le1] — under all-lengths<=1
    the Kraft sum is exactly [count_len l 1 * 2^14]; (v) N1,
    [kraft_min_pow_bound] — a COMPLETE code whose histogram is zero
    below bucket [m] has at least [2^m] entries (the regime-split
    arithmetic: completeness + population cap bounds the machine's
    findmin, hence the root, hence the it_enough charge).

    PA-EXPORTS: it_incomplete_lens_one, zlens_bounded,
    count_len_filter1, ksum_le1, kraft_min_pow_bound.
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** (i) zlib's one-bit-incomplete exception, LENS side (mirror of the
    landed [InftreesBridge.it_incomplete_dists_one]). *)
Lemma it_incomplete_lens_one : forall lft, it_incomplete CT_LENS lft 1 = false.
Proof.
  intros lft. unfold it_incomplete, CT_LENS, CT_CODES.
  replace ((1 =? 0) || negb (1 =? 1))%bool with false by reflexivity.
  apply andb_false_r.
Qed.

(** (ii) The entry cap, in [GtItTotal]'s vocabulary at the driver's
    call shape. *)
Lemma zlens_bounded : forall l : list nat,
  (forall len, In len l -> (len <= 15)%nat) ->
  LensBounded (zlens l) (Z.of_nat (length l)).
Proof.
  intros l Hcap i Hi. unfold zlens.
  split; [apply Nat2Z.is_nonneg|].
  assert (Hlt : (Z.to_nat i < length l)%nat) by lia.
  pose proof (Hcap _ (nth_In l 0%nat Hlt)). lia.
Qed.

(** (iii) The r4 statement's filter spelling IS the histogram bucket. *)
Lemma count_len_filter1 : forall l : list nat,
  count_len l 1 = length (filter (Nat.eqb 1%nat) l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  unfold count_len in *. cbn [count_occ filter].
  destruct (Nat.eq_dec x 1) as [->|Hne].
  - cbn [Nat.eqb length]. now rewrite IH.
  - replace (Nat.eqb 1 x) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    exact IH.
Qed.

(** (iv) All lengths <= 1: only bucket 1 contributes. *)
Lemma ksum_le1 : forall l : list nat,
  (forall len, In len l -> (len <= 1)%nat) ->
  (kraft_sum l 15 = count_len l 1 * 2 ^ 14)%nat.
Proof.
  induction l as [|x l IH]; intros Hle; [reflexivity|].
  unfold kraft_sum in *. rewrite kraft_sum_from_cons.
  rewrite (IH (fun y H => Hle y (or_intror H))).
  unfold count_len. cbn [count_occ].
  destruct (Nat.eq_dec x 1) as [->|Hne].
  - unfold kraft_at. cbn [Nat.leb kraft_term].
    rewrite Nat.mul_succ_l.
    replace (15 - 1)%nat with 14%nat by lia. lia.
  - assert (Hx : x = 0%nat)
      by (pose proof (Hle x (or_introl eq_refl)); lia).
    subst x. unfold kraft_at. cbn [Nat.leb kraft_term]. lia.
Qed.

(** (v) N1 — the regime-split arithmetic. *)

Lemma kraft_term_le : forall m x : nat,
  (x <= 15)%nat -> (x = 0%nat \/ (m <= x)%nat) ->
  (kraft_term 15 x <= 2 ^ (15 - m))%nat.
Proof.
  intros m x Hx [->|Hm].
  - cbn [kraft_term]. lia.
  - destruct x as [|k]; cbn [kraft_term]; [lia|].
    apply Nat.pow_le_mono_r; lia.
Qed.

Lemma ksum_entries_bound : forall (L : list nat) (m : nat),
  (forall x, In x L -> (x <= 15)%nat) ->
  (forall x, In x L -> x = 0%nat \/ (m <= x)%nat) ->
  (kraft_sum L 15 <= length L * 2 ^ (15 - m))%nat.
Proof.
  induction L as [|x L IH]; intros m Hcap Hsplit.
  - unfold kraft_sum. rewrite kraft_sum_from_nil. lia.
  - unfold kraft_sum in *. rewrite kraft_sum_from_cons.
    unfold kraft_at. cbn [Nat.leb].
    pose proof (kraft_term_le m x (Hcap x (or_introl eq_refl))
                  (Hsplit x (or_introl eq_refl))).
    specialize (IH m (fun y H => Hcap y (or_intror H))
                  (fun y H => Hsplit y (or_intror H))).
    cbn [length]. rewrite Nat.mul_succ_l. lia.
Qed.

Lemma kraft_min_pow_bound :
  forall (l : list nat) (m : nat),
    (forall len, In len l -> (len <= 15)%nat) ->
    (kraft_sum l 15 = 2 ^ 15)%nat ->
    (1 <= m <= 15)%nat ->
    (forall b, (1 <= b < m)%nat -> count_len l b = 0%nat) ->
    (2 ^ m <= length l)%nat.
Proof.
  intros l m Hcap HK Hm Hzero.
  assert (Hsplit : forall x, In x l -> x = 0%nat \/ (m <= x)%nat).
  { intros x Hin.
    destruct (Nat.eq_dec x 0) as [->|Hx0]; [now left|right].
    destruct (Nat.lt_ge_cases x m) as [Hlt|]; [|assumption].
    exfalso.
    assert (Hc : count_len l x = 0%nat) by (apply Hzero; lia).
    unfold count_len in Hc.
    apply (count_occ_In Nat.eq_dec) in Hin. lia. }
  pose proof (ksum_entries_bound l m Hcap Hsplit) as HB.
  rewrite HK in HB.
  assert (HE : (2 ^ m * 2 ^ (15 - m) = 2 ^ 15)%nat).
  { rewrite <- Nat.pow_add_r. f_equal. lia. }
  assert (Hpos : (2 ^ (15 - m) <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  nia.
Qed.

Set Printing Width 2000.
Print Assumptions it_incomplete_lens_one.
Print Assumptions zlens_bounded.
Print Assumptions count_len_filter1.
Print Assumptions ksum_le1.
Print Assumptions kraft_min_pow_bound.
