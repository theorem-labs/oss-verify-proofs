(** * ZHOCT — the adjust trip's EXACT layer-sum delta.

    OWNER: huffman-opt L4-assembly fork.

    Over an abstract prefix-sum [S] (of the sorted leaf freqs; increments
    nonneg and nondecreasing), the layer total of a histogram is
        layer blc = Sum_{j=1..15} S (cge blc j),
    cge blc j = Sum_{b=j..15} blc b.  ZHOLayer's [pcost_layers] equates
    this with the monotone assignment's cost, so the pass-1 -> pass-2 cost
    delta is [layer blc2 - layer blc1] (assembled in ZHOAsm).

    THE TRIP FORMULA (this file's core export, [zct_trip_layer]): one
    [gba_body] trip at a state whose deepest nonempty level <= 14 is [l]
    (= [gba_bits], with everything in (l, 14] EMPTY — a property of
    [gb_findbits] proven here) changes the layer total by EXACTLY

        phi (blc 15 + 1) - (14 - l) * phi (blc 15),

    where phi r = S r - S (r-1): the trip's cost is one boundary-rank
    increment minus (14 - l) boundary-rank decrements, all at the CURRENT
    deep count [blc 15] — the 1-D walk the cone analysis runs on
    (L4-STICKING-POINT.md).

    TRUST BOUNDARY: pure Gallina over the model + the landed KraftAdjust /
    BtAdjust trip machinery + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin KraftAdjust BtAdjust.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 0. gb_findbits stops at the DEEPEST nonempty level *)

Lemma zct_findbits_above : forall fuel (blc : zarr) bits b,
  gb_findbits fuel blc bits < b <= bits ->
  Z.of_nat fuel >= bits - gb_findbits fuel blc bits ->
  blc b = 0.
Proof.
  induction fuel as [|f IH]; intros blc bits b Hb Hf.
  - cbn [Z.of_nat] in Hf. cbn [gb_findbits] in Hb. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    cbn [gb_findbits] in *.
    destruct (Z.eqb (blc bits) 0) eqn:E.
    + apply Z.eqb_eq in E.
      destruct (Z.eq_dec b bits) as [->|Hne]; [exact E|].
      apply (IH blc (bits - 1) b); lia.
    + apply Z.eqb_neq in E. lia.
Qed.

(** and never less than [bits - fuel] *)
Lemma zct_findbits_ge : forall fuel (blc : zarr) bits,
  bits - Z.of_nat fuel <= gb_findbits fuel blc bits.
Proof.
  induction fuel as [|f IH]; intros blc bits; cbn [gb_findbits].
  - cbn [Z.of_nat]. lia.
  - rewrite Nat2Z.inj_succ.
    destruct (Z.eqb (blc bits) 0); [|lia].
    pose proof (IH blc (bits - 1)). lia.
Qed.

(** [gb_findbits] never returns more than its start *)
Lemma zct_findbits_le : forall fuel (blc : zarr) bits,
  gb_findbits fuel blc bits <= bits.
Proof.
  induction fuel as [|f IH]; intros blc bits; cbn [gb_findbits]; [lia|].
  destruct (Z.eqb (blc bits) 0); [|lia].
  pose proof (IH blc (bits - 1)). lia.
Qed.

(** the emptiness package at [gba_bits] (fuel 16, start 14) *)
Lemma zct_bits_empty : forall (blc : zarr) b,
  gba_bits 15 blc < b <= 14 -> blc b = 0.
Proof.
  intros blc b Hb.
  unfold gba_bits in *.
  replace (15 - 1) with 14 in * by lia.
  apply (zct_findbits_above (Z.to_nat MAX_BITS + 1) blc 14 b); [exact Hb|].
  pose proof (zct_findbits_le (Z.to_nat MAX_BITS + 1) blc 14).
  pose proof (zct_findbits_ge (Z.to_nat MAX_BITS + 1) blc 14).
  unfold MAX_BITS in *.
  rewrite Nat2Z.inj_add, Z2Nat.id in * by lia.
  change (Z.of_nat 1) with 1 in *. lia.
Qed.

(** ** 1. small wsum helpers *)

(** one-step unfold (a bare [cbn] on [wsum f lo (S (S k))] unfolds twice) *)
Lemma zct_wsum_S : forall (f : Z -> Z) lo n,
  wsum f lo (Datatypes.S n) = f lo + wsum f (lo + 1) n.
Proof. reflexivity. Qed.

Lemma zct_wsum_zero : forall lo n, wsum (fun _ : Z => 0) lo n = 0.
Proof.
  intros lo n; revert lo; induction n as [|k IH]; intro lo; cbn [wsum];
    [lia | rewrite IH; lia].
Qed.

Lemma zct_wsum_add' : forall (h f g : Z -> Z) lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> h i = f i + g i) ->
  wsum h lo n = wsum f lo n + wsum g lo n.
Proof.
  intros h f g lo n; revert lo; induction n as [|k IH]; intros lo H;
    cbn [wsum]; [lia|].
  rewrite Nat2Z.inj_succ in H.
  cbv beta.
  rewrite (H lo) by lia.
  rewrite (IH (lo + 1)) by (intros; apply H; lia).
  lia.
Qed.

(** the sum of a unit spike at [c] over a window *)
Lemma zct_wsum_spike : forall (c lo : Z) (n : nat),
  wsum (fun b => if Z.eq_dec b c then 1 else 0) lo n
  = if (lo <=? c) && (c <? lo + Z.of_nat n) then 1 else 0.
Proof.
  intros c lo n; revert lo; induction n as [|k IH]; intro lo.
  - cbn [wsum Z.of_nat].
    destruct (Z.leb_spec lo c); destruct (Z.ltb_spec c (lo + 0));
      cbn [andb]; try reflexivity; lia.
  - cbn [wsum]. cbv beta.
    rewrite IH, Nat2Z.inj_succ.
    destruct (Z.eq_dec lo c) as [->|Hne].
    + replace ((c <=? c) && (c <? c + Z.succ (Z.of_nat k))) with true
        by (symmetry; apply andb_true_iff; split;
            [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace ((c + 1 <=? c) && (c <? c + 1 + Z.of_nat k)) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      lia.
    + destruct (Z.leb_spec (lo + 1) c); destruct (Z.leb_spec lo c);
        destruct (Z.ltb_spec c (lo + 1 + Z.of_nat k));
        destruct (Z.ltb_spec c (lo + Z.succ (Z.of_nat k)));
        cbn [andb]; try lia.
Qed.

(** ** 2. the abstract price and the layer total *)

Section ZHOCT.

Variable S : Z -> Z.
Hypothesis HS_mono : forall a b, a <= b -> S a <= S b.
Hypothesis HS_conv : forall a b, a <= b -> S a - S (a - 1) <= S b - S (b - 1).

Definition phi (r : Z) : Z := S r - S (r - 1).

Lemma phi_nn : forall r, 0 <= phi r.
Proof. intro r. unfold phi. pose proof (HS_mono (r - 1) r ltac:(lia)). lia. Qed.

Lemma phi_mono : forall a b, a <= b -> phi a <= phi b.
Proof. intros a b H. unfold phi. apply HS_conv. exact H. Qed.

Definition cge (blc : zarr) (j : Z) : Z := wsum blc j (Z.to_nat (16 - j)).

Definition layer (blc : zarr) : Z :=
  wsum (fun j => S (cge blc j)) 1 15.

(** ** 3. the trip's effect on the cumulative counts *)

Section OneTrip.

Variable blc : zarr.
Hypothesis Hbits : 1 <= gba_bits 15 blc < 15.
Hypothesis Hat   : 1 <= blc (gba_bits 15 blc).
Hypothesis H15   : 1 <= blc 15.
Hypothesis Hbnd  : forall b, 0 <= blc b <= 32766.

Let l := gba_bits 15 blc.

(** the counts at levels above [l] all equal the deep count *)
Lemma zct_cge_high : forall j, l + 1 <= j <= 15 ->
  cge blc j = blc 15.
Proof.
  intros j Hj. unfold cge.
  replace (Z.to_nat (16 - j)) with (Datatypes.S (Z.to_nat (15 - j))) by lia.
  (* peel from the top: [j..14] are zeros, the last term is blc 15 *)
  revert j Hj.
  assert (GEN : forall (k : nat) (j : Z),
             l + 1 <= j -> j + Z.of_nat k = 15 ->
             wsum blc j (Datatypes.S k) = blc 15).
  { induction k as [|k IH]; intros j Hj Hjk.
    - rewrite zct_wsum_S. cbn [wsum]. assert (j = 15) by lia. subst j. lia.
    - rewrite zct_wsum_S.
      rewrite Nat2Z.inj_succ in Hjk.
      rewrite (IH (j + 1)) by lia.
      rewrite (zct_bits_empty blc j) by (fold l; lia).
      lia. }
  intros j Hj.
  apply GEN; [lia|].
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma zct_cge_step : forall j, 1 <= j <= 15 ->
  cge (gba_body 15 blc) j
  = cge blc j - (if j <=? l then 0 else 1)
    + (if j =? l + 1 then 2 else 0).
Proof.
  intros j Hj. unfold cge.
  rewrite (zct_wsum_add' (gba_body 15 blc) blc
             (fun b => 0 - (if Z.eq_dec b l then 1 else 0)
                       + 2 * (if Z.eq_dec b (l + 1) then 1 else 0)
                       - (if Z.eq_dec b 15 then 1 else 0)) j
             (Z.to_nat (16 - j))).
  2:{ intros b Hb.
      rewrite (gba_body_val 15 blc b Hbits Hat H15 Hbnd).
      fold l.
      destruct (Z.eq_dec b l); destruct (Z.eq_dec b (l + 1));
        destruct (Z.eq_dec b 15); lia. }
  rewrite (zct_wsum_add'
             (fun b => 0 - (if Z.eq_dec b l then 1 else 0)
                       + 2 * (if Z.eq_dec b (l + 1) then 1 else 0)
                       - (if Z.eq_dec b 15 then 1 else 0))
             (fun b => 0 - (if Z.eq_dec b l then 1 else 0)
                       + 2 * (if Z.eq_dec b (l + 1) then 1 else 0))
             (fun b => 0 - (if Z.eq_dec b 15 then 1 else 0)) j
             (Z.to_nat (16 - j)))
    by (intros; lia).
  rewrite (zct_wsum_add'
             (fun b => 0 - (if Z.eq_dec b l then 1 else 0)
                       + 2 * (if Z.eq_dec b (l + 1) then 1 else 0))
             (fun b => 0 - (if Z.eq_dec b l then 1 else 0))
             (fun b => 2 * (if Z.eq_dec b (l + 1) then 1 else 0)) j
             (Z.to_nat (16 - j)))
    by (intros; lia).
  (* generic scaled-spike evaluation *)
  assert (Sq : forall (q c lo : Z) (n : nat),
             wsum (fun b => q * (if Z.eq_dec b c then 1 else 0)) lo n
             = q * wsum (fun b => if Z.eq_dec b c then 1 else 0) lo n).
  { intros q c lo n; revert lo; induction n as [|k IH]; intro lo;
      cbn [wsum]; [lia|]. cbv beta. rewrite IH. lia. }
  assert (E0m : forall (c lo : Z) (n : nat),
             wsum (fun b => 0 - (if Z.eq_dec b c then 1 else 0)) lo n
             = - wsum (fun b => if Z.eq_dec b c then 1 else 0) lo n).
  { intros c lo n.
    rewrite (zct_wsum_add'
               (fun b => 0 - (if Z.eq_dec b c then 1 else 0))
               (fun _ => 0)
               (fun b => (- 1) * (if Z.eq_dec b c then 1 else 0)) lo n)
      by (intros; lia).
    rewrite zct_wsum_zero, Sq. lia. }
  rewrite (E0m l), (E0m 15), Sq, !zct_wsum_spike.
  rewrite Z2Nat.id by lia.
  replace (j + (16 - j)) with 16 by lia.
  destruct (Z.leb_spec j l); destruct (Z.ltb_spec l 16);
    destruct (Z.leb_spec j (l + 1)); destruct (Z.ltb_spec (l + 1) 16);
    destruct (Z.leb_spec j 15); destruct (Z.ltb_spec 15 16);
    destruct (Z.eqb_spec j (l + 1));
    cbn [andb]; try lia.
Qed.

(** ** 4. THE TRIP FORMULA *)

Theorem zct_trip_layer :
  layer (gba_body 15 blc)
  = layer blc + phi (blc 15 + 1) - (14 - l) * phi (blc 15).
Proof.
  unfold layer.
  rewrite (zct_wsum_add' (fun j => S (cge (gba_body 15 blc) j))
             (fun j => S (cge blc j))
             (fun j => S (cge (gba_body 15 blc) j) - S (cge blc j)) 1 15)
    by (intros; lia).
  assert (Hdelta : forall j, 1 <= j <= 15 ->
    S (cge (gba_body 15 blc) j) - S (cge blc j)
    = (if j =? l + 1 then phi (blc 15 + 1) else 0)
      - (if (l + 2 <=? j) && (j <=? 15) then phi (blc 15) else 0)).
  { intros j Hj.
    rewrite (zct_cge_step j Hj).
    destruct (Z.leb_spec j l) as [Hle|Hgt].
    - (* j <= l: count unchanged *)
      replace (Z.eqb j (l + 1)) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace ((l + 2 <=? j) && (j <=? 15)) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      cbn [andb]. cbv iota.
      replace (cge blc j - 0 + 0) with (cge blc j) by lia.
      lia.
    - destruct (Z.eqb_spec j (l + 1)) as [->|Hne].
      + (* the incremented level: count K -> K+1 *)
        rewrite (zct_cge_high (l + 1)) by lia.
        replace ((l + 2 <=? l + 1) && (l + 1 <=? 15)) with false
          by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        cbn [andb]. cbv iota.
        replace (blc 15 - 1 + 2) with (blc 15 + 1) by lia.
        unfold phi.
        replace (blc 15 + 1 - 1) with (blc 15) by lia.
        lia.
      + (* the decremented levels: count K -> K-1 *)
        assert (Hj2 : l + 2 <= j <= 15) by lia.
        rewrite (zct_cge_high j) by lia.
        replace ((l + 2 <=? j) && (j <=? 15)) with true
          by (symmetry; apply andb_true_iff;
              split; [apply Z.leb_le; lia | apply Z.leb_le; lia]).
        cbn [andb]. cbv iota.
        replace (blc 15 - 1 + 0) with (blc 15 - 1) by lia.
        unfold phi. lia. }
  rewrite (zct_wsum_add'
             (fun j => S (cge (gba_body 15 blc) j) - S (cge blc j))
             (fun j => if j =? l + 1 then phi (blc 15 + 1) else 0)
             (fun j => - (if (l + 2 <=? j) && (j <=? 15)
                          then phi (blc 15) else 0)) 1 15)
    by (intros i Hi; rewrite (Hdelta i) by lia; lia).
  (* the spike sum *)
  assert (E1 : wsum (fun j => if j =? l + 1 then phi (blc 15 + 1) else 0)
                    1 15 = phi (blc 15 + 1)).
  { rewrite (zct_wsum_add'
               (fun j => if j =? l + 1 then phi (blc 15 + 1) else 0)
               (fun _ => 0)
               (fun j => phi (blc 15 + 1)
                         * (if Z.eq_dec j (l + 1) then 1 else 0)) 1 15).
    2:{ intros i Hi.
        destruct (Z.eqb_spec i (l + 1));
          destruct (Z.eq_dec i (l + 1)); try congruence; lia. }
    rewrite zct_wsum_zero.
    assert (Smul : forall lo n c q,
               wsum (fun b => q * (if Z.eq_dec b c then 1 else 0)) lo n
               = q * wsum (fun b => if Z.eq_dec b c then 1 else 0) lo n).
    { intros lo n c q; revert lo; induction n as [|k IH]; intro lo;
        cbn [wsum]; [lia|]. cbv beta. rewrite IH. lia. }
    rewrite Smul, zct_wsum_spike.
    change (Z.of_nat 15) with 15.
    replace ((1 <=? l + 1) && (l + 1 <? 1 + 15)) with true
      by (symmetry; apply andb_true_iff;
          split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    lia. }
  (* the band sum *)
  assert (E2 : wsum (fun j => - (if (l + 2 <=? j) && (j <=? 15)
                                 then phi (blc 15) else 0)) 1 15
               = - (14 - l) * phi (blc 15)).
  { assert (GEN : forall L, 1 <= L < 15 ->
        wsum (fun j => - (if (L + 2 <=? j) && (j <=? 15)
                          then phi (blc 15) else 0)) 1 15
        = - (14 - L) * phi (blc 15)).
    { intros L HLr.
      assert (HL : L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/
                   L = 7 \/ L = 8 \/ L = 9 \/ L = 10 \/ L = 11 \/ L = 12 \/
                   L = 13 \/ L = 14) by lia.
      repeat (destruct HL as [HL|HL]); subst L; cbn -[Z.mul]; lia. }
    apply GEN. exact Hbits. }
  rewrite E1, E2. lia.
Qed.

End OneTrip.

End ZHOCT.
