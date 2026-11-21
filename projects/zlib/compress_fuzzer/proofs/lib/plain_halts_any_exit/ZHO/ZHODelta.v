(** * ZHODelta — the adjust-walk cone machinery (L4 delta grind, part 1).

    OWNER: huffman-opt (fork).

    Pure zarr walk mathematics over [gba_body]: the deterministic
    deepest-first adjust walk decomposes into CONES.  A complete cone
    rooted at level [l = 15 - w] runs exactly [2^w - 1] trips, restores
    every level except [l] (down one unit) and [15] (up one unit), and
    pays EXACTLY [w * phi (K + 1)] of layer where [K] is the entry
    15-stock; any [m]-trip prefix pays at most [w * phi (K + 1)], and at
    most ONE [phi (K + 1)] when [m <= 2^(w-1)].  All three clauses fall
    out of one induction on [w] (ZHOCT's [zct_trip_layer] does the
    per-trip bookkeeping).

    TRUST BOUNDARY: pure Gallina over the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin KraftAdjust BtAdjust.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOCT.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Iteration kit *)

Definition zd_iter (n : nat) (blc : zarr) : zarr :=
  Nat.iter n (gba_body 15) blc.

Lemma zd_iter_0 : forall blc, zd_iter 0 blc = blc.
Proof. reflexivity. Qed.

Lemma zd_iter_S : forall n blc,
  zd_iter (S n) blc = gba_body 15 (zd_iter n blc).
Proof. reflexivity. Qed.

Lemma zd_iter_add : forall a b blc,
  zd_iter (a + b) blc = zd_iter a (zd_iter b blc).
Proof.
  intros a b blc. induction a as [|a IH]; [reflexivity|].
  cbn [Nat.add]. rewrite !zd_iter_S, IH. reflexivity.
Qed.

Lemma zd_iter_S_in : forall n blc,
  zd_iter (S n) blc = zd_iter n (gba_body 15 blc).
Proof.
  intros n blc. replace (S n) with (n + 1)%nat by lia.
  rewrite zd_iter_add. reflexivity.
Qed.

(** ** Nat-pow kit *)

Lemma zd_pow_pos : forall w, (1 <= Nat.pow 2 w)%nat.
Proof.
  induction w as [|w IH]; cbn [Nat.pow]; lia.
Qed.

Lemma zd_pow_S : forall w, (Nat.pow 2 (S w) = 2 * Nat.pow 2 w)%nat.
Proof. reflexivity. Qed.

Lemma zd_pow_lin : forall w, (w + 1 <= Nat.pow 2 w)%nat.
Proof.
  induction w as [|w IH]; cbn [Nat.pow]; lia.
Qed.

Lemma zd_zksum_ext : forall (blc blc' : zarr),
  (forall b, 1 <= b <= 15 -> blc b = blc' b) ->
  zksum 15 blc = zksum 15 blc'.
Proof.
  intros blc blc' He. unfold zksum, zksum_over.
  f_equal. apply map_ext_in. intros j Hj.
  apply in_seq in Hj. rewrite He by lia. reflexivity.
Qed.

(** ** The deepest-nonempty computation *)

Lemma zd_findbits_hit : forall fuel (blc : zarr) bits l,
  l <= bits -> bits - l < Z.of_nat fuel ->
  blc l <> 0 ->
  (forall b, l < b <= bits -> blc b = 0) ->
  gb_findbits fuel blc bits = l.
Proof.
  induction fuel as [|f IH]; intros blc bits l Hlb Hf Hnz Hemp.
  - cbn [Z.of_nat] in Hf. lia.
  - cbn [gb_findbits].
    destruct (Z.eqb_spec (blc bits) 0) as [Ez|Enz].
    + assert (Hgt : l < bits).
      { destruct (Z.eqb_spec bits l) as [->|]; [congruence|lia]. }
      rewrite Nat2Z.inj_succ in Hf.
      apply IH; [lia|lia|exact Hnz|].
      intros b Hb. apply Hemp. lia.
    + destruct (Z.eqb_spec bits l) as [->|Hne]; [reflexivity|].
      exfalso. apply Enz. apply Hemp. lia.
Qed.

Lemma zd_bits_at : forall (blc : zarr) l,
  1 <= l <= 14 -> 1 <= blc l ->
  (forall b, l < b <= 14 -> blc b = 0) ->
  gba_bits 15 blc = l.
Proof.
  intros blc l Hl H1 Hemp. unfold gba_bits.
  apply zd_findbits_hit.
  - lia.
  - rewrite Nat2Z.inj_add, Z2Nat.id by (unfold MAX_BITS; lia).
    unfold MAX_BITS. lia.
  - lia.
  - intros b Hb. apply Hemp. lia.
Qed.

(** ** The cone

    Section-parametric in the layer profile [Sf] through the two phi
    facts the walk needs (the assembly instantiates them from the sorted
    prefix sums via HS_mono/HS_conv). *)

Section ZHODelta.

Variable Sf : Z -> Z.
Hypothesis Hphi_nn   : forall r, 0 <= phi Sf r.
Hypothesis Hphi_mono : forall a b, a <= b -> phi Sf a <= phi Sf b.

Theorem zd_cone : forall w (blc : zarr) (m : nat),
  (1 <= w)%nat -> Z.of_nat w <= 14 ->
  gba_bits 15 blc = 15 - Z.of_nat w ->
  1 <= blc (15 - Z.of_nat w) ->
  Z.of_nat (Nat.min w m) <= blc 15 ->
  (forall b, b < 1 \/ 15 < b -> blc b = 0) ->
  (forall b, 0 <= blc b <= 32764) ->
  (m <= Nat.pow 2 w - 1)%nat ->
  (* 1: any prefix pays at most w phis at the entry+1 rank *)
  layer Sf (zd_iter m blc)
    <= layer Sf blc + Z.of_nat w * phi Sf (blc 15 + 1)
  (* 2: a short prefix pays at most ONE *)
  /\ ((m <= Nat.pow 2 (w - 1))%nat ->
      layer Sf (zd_iter m blc) <= layer Sf blc + phi Sf (blc 15 + 1))
  (* 3: the complete cone, exact state and payment *)
  /\ ((m = Nat.pow 2 w - 1)%nat ->
      (forall b, b <> 15 - Z.of_nat w -> b <> 15 ->
         zd_iter m blc b = blc b)
      /\ zd_iter m blc (15 - Z.of_nat w) = blc (15 - Z.of_nat w) - 1
      /\ zd_iter m blc 15 = blc 15 + 1
      /\ layer Sf (zd_iter m blc)
         = layer Sf blc + Z.of_nat w * phi Sf (blc 15 + 1)).
Proof.
  induction w as [|w IHw]; intros blc m Hw1 Hw14 Hbits Hat H15 Hz Hbnd Hm.
  { lia. }
  destruct m as [|m'].
  { (* m = 0 *)
    split; [|split].
    - rewrite zd_iter_0.
      pose proof (Hphi_nn (blc 15 + 1)). nia.
    - intros _. rewrite zd_iter_0.
      pose proof (Hphi_nn (blc 15 + 1)). lia.
    - intros He. exfalso.
      rewrite zd_pow_S in He. pose proof (zd_pow_pos w). lia. }
  (* the first trip *)
  assert (Hzw : Z.of_nat (S w) = Z.of_nat w + 1)
    by (rewrite Nat2Z.inj_succ; lia).
  assert (Hbr : 1 <= gba_bits 15 blc < 15) by (rewrite Hbits; lia).
  assert (Hat' : 1 <= blc (gba_bits 15 blc)) by (rewrite Hbits; exact Hat).
  assert (Hbnd' : forall b, 0 <= blc b <= 32766)
    by (intro b; pose proof (Hbnd b); lia).
  pose proof (zct_trip_layer Sf blc Hbr Hat' ltac:(lia) Hbnd') as Htrip.
  rewrite Hbits in Htrip.
  replace (14 - (15 - Z.of_nat (S w))) with (Z.of_nat w) in Htrip by lia.
  assert (Hemp : forall b, 15 - Z.of_nat (S w) < b <= 14 -> blc b = 0)
    by (intros b Hb; apply (zct_bits_empty blc b); rewrite Hbits; lia).
  assert (Hval : forall b, gba_body 15 blc b
            = blc b
              - (if Z.eq_dec b (15 - Z.of_nat (S w)) then 1 else 0)
              + (if Z.eq_dec b (15 - Z.of_nat (S w) + 1) then 2 else 0)
              - (if Z.eq_dec b 15 then 1 else 0)).
  { intro b.
    rewrite (gba_body_val 15 blc b Hbr Hat' ltac:(lia) Hbnd').
    rewrite Hbits. reflexivity. }
  destruct w as [|w].
  { (* w = 1 in the paper: l = 14, the single-trip cone *)
    assert (Hm1 : m' = O) by (cbn [Nat.pow] in Hm; lia).
    subst m'.
    assert (E1 : zd_iter 1 blc = gba_body 15 blc) by reflexivity.
    split; [|split].
    - rewrite E1, Htrip.
      pose proof (Hphi_nn (blc 15)). lia.
    - intros _. rewrite E1, Htrip.
      pose proof (Hphi_nn (blc 15)). lia.
    - intros _. rewrite E1.
      split; [|split; [|split]].
      + intros b Hb1 Hb2. rewrite Hval.
        destruct (Z.eq_dec b (15 - Z.of_nat 1)) as [e|n1]; [lia|].
        destruct (Z.eq_dec b (15 - Z.of_nat 1 + 1)) as [e|n2]; [lia|].
        destruct (Z.eq_dec b 15) as [e|n3]; [lia|]. lia.
      + rewrite Hval.
        destruct (Z.eq_dec (15 - Z.of_nat 1) (15 - Z.of_nat 1)); [|congruence].
        destruct (Z.eq_dec (15 - Z.of_nat 1) (15 - Z.of_nat 1 + 1)); [lia|].
        destruct (Z.eq_dec (15 - Z.of_nat 1) 15); [lia|]. lia.
      + rewrite Hval.
        destruct (Z.eq_dec 15 (15 - Z.of_nat 1)); [lia|].
        destruct (Z.eq_dec 15 (15 - Z.of_nat 1 + 1)); [|lia].
        destruct (Z.eq_dec 15 15); [|congruence]. lia.
      + rewrite Htrip. lia. }
  (* w >= 2 in this arm: l = 15 - (S (S w)) <= 13, so l+1 <= 14 and the
     three written indices are distinct *)
  set (l := 15 - Z.of_nat (S (S w))) in *.
  assert (Hl : 1 <= l <= 13) by (unfold l; lia).
  assert (El1 : l + 1 = 15 - Z.of_nat (S w)) by (unfold l; lia).
  (* the post-trip state *)
  set (blc1 := gba_body 15 blc) in *.
  assert (Hv1_l : blc1 l = blc l - 1).
  { rewrite Hval.
    destruct (Z.eq_dec l l); [|congruence].
    destruct (Z.eq_dec l (l + 1)); [lia|].
    destruct (Z.eq_dec l 15); [lia|]. lia. }
  assert (Hv1_l1 : blc1 (l + 1) = 2).
  { rewrite Hval.
    destruct (Z.eq_dec (l + 1) l); [lia|].
    destruct (Z.eq_dec (l + 1) (l + 1)); [|congruence].
    destruct (Z.eq_dec (l + 1) 15); [lia|].
    rewrite (Hemp (l + 1)) by lia. lia. }
  assert (Hv1_15 : blc1 15 = blc 15 - 1).
  { rewrite Hval.
    destruct (Z.eq_dec 15 l); [lia|].
    destruct (Z.eq_dec 15 (l + 1)); [lia|].
    destruct (Z.eq_dec 15 15); [|congruence]. lia. }
  assert (Hv1_oth : forall b, b <> l -> b <> l + 1 -> b <> 15 ->
            blc1 b = blc b).
  { intros b Hb1 Hb2 Hb3. rewrite Hval.
    destruct (Z.eq_dec b l); [congruence|].
    destruct (Z.eq_dec b (l + 1)); [congruence|].
    destruct (Z.eq_dec b 15); [congruence|]. lia. }
  assert (Hz1 : forall b, b < 1 \/ 15 < b -> blc1 b = 0).
  { intros b Hb. rewrite Hv1_oth by lia. apply Hz. exact Hb. }
  assert (Hbnd1 : forall b, 0 <= blc1 b <= 32764).
  { intro b.
    destruct (Z.eq_dec b l) as [->|n1];
      [rewrite Hv1_l; pose proof (Hbnd l); lia|].
    destruct (Z.eq_dec b (l + 1)) as [->|n2];
      [rewrite Hv1_l1; lia|].
    destruct (Z.eq_dec b 15) as [->|n3];
      [rewrite Hv1_15; pose proof (Hbnd 15); lia|].
    rewrite Hv1_oth by congruence. apply Hbnd. }
  assert (Hemp1 : forall b, l + 1 < b <= 14 -> blc1 b = 0).
  { intros b Hb. rewrite Hv1_oth by lia. apply Hemp. lia. }
  assert (Hbits1 : gba_bits 15 blc1 = 15 - Z.of_nat (S w)).
  { rewrite <- El1. apply zd_bits_at; [lia|rewrite Hv1_l1; lia|exact Hemp1]. }
  assert (Hstep : zd_iter (S m') blc = zd_iter m' blc1)
    by (rewrite zd_iter_S_in; reflexivity).
  assert (Hmm : (m' <= Nat.pow 2 (S (S w)) - 2)%nat) by lia.
  pose proof (zd_pow_pos w) as Hpw.
  destruct (le_lt_dec m' (Nat.pow 2 (S w) - 1)) as [Hsmall|Hbig].
  - (* the whole remainder sits inside the first inner cone *)
    pose proof (IHw blc1 m' ltac:(lia) ltac:(lia) Hbits1
                  ltac:(rewrite El1 in Hv1_l1; rewrite Hv1_l1; lia)
                  ltac:(rewrite Hv1_15; lia)
                  Hz1 Hbnd1 Hsmall) as (IH1 & IH1s & _).
    rewrite Hv1_15 in IH1, IH1s.
    replace (blc 15 - 1 + 1) with (blc 15) in IH1, IH1s by lia.
    split; [|split].
    + rewrite Hstep. eapply Z.le_trans; [exact IH1|].
      rewrite Htrip.
      pose proof (Hphi_mono (blc 15) (blc 15 + 1) ltac:(lia)).
      pose proof (Hphi_nn (blc 15 + 1)). nia.
    + intros _. rewrite Hstep. eapply Z.le_trans; [exact IH1|].
      rewrite Htrip. lia.
    + intros He. exfalso.
      rewrite zd_pow_S in He. rewrite zd_pow_S in Hsmall.
      pose proof (zd_pow_pos (S w)). rewrite zd_pow_S in *. lia.
  - (* the first inner cone completes; the rest runs in the second *)
    pose proof (zd_pow_lin (S w)) as Hplin.
    pose proof (IHw blc1 ((Nat.pow 2 (S w) - 1)%nat) ltac:(lia) ltac:(lia) Hbits1
                  ltac:(rewrite El1 in Hv1_l1; rewrite Hv1_l1; lia)
                  ltac:(rewrite Hv1_15; lia)
                  Hz1 Hbnd1 ltac:(lia)) as (_ & _ & IHC).
    destruct (IHC eq_refl) as (HC_oth & HC_l & HC_15 & HC_lay).
    rewrite <- El1 in HC_l.
    set (blc2 := zd_iter ((Nat.pow 2 (S w) - 1)%nat) blc1) in *.
    rewrite Hv1_15 in HC_15, HC_lay.
    replace (blc 15 - 1 + 1) with (blc 15) in HC_15, HC_lay by lia.
    (* the second inner cone's entry *)
    assert (Hb2_l1 : blc2 (l + 1) = 1)
      by (rewrite HC_l, Hv1_l1; lia).
    assert (Hb2_15 : blc2 15 = blc 15) by exact HC_15.
    assert (Hb2_oth : forall b, b <> l + 1 -> b <> 15 -> blc2 b = blc1 b).
    { intros b Hb1 Hb2. apply HC_oth; [rewrite <- El1; exact Hb1|exact Hb2]. }
    assert (Hemp2 : forall b, l + 1 < b <= 14 -> blc2 b = 0).
    { intros b Hb. rewrite Hb2_oth by lia. apply Hemp1. exact Hb. }
    assert (Hbits2 : gba_bits 15 blc2 = 15 - Z.of_nat (S w)).
    { rewrite <- El1. apply zd_bits_at; [lia|rewrite Hb2_l1; lia|exact Hemp2]. }
    assert (Hz2 : forall b, b < 1 \/ 15 < b -> blc2 b = 0).
    { intros b Hb. rewrite Hb2_oth by lia. apply Hz1. exact Hb. }
    assert (Hbnd2 : forall b, 0 <= blc2 b <= 32764).
    { intro b.
      destruct (Z.eq_dec b (l + 1)) as [->|n1]; [rewrite Hb2_l1; lia|].
      destruct (Z.eq_dec b 15) as [->|n2];
        [rewrite Hb2_15; pose proof (Hbnd 15); lia|].
      rewrite Hb2_oth by congruence. apply Hbnd1. }
    set (r := (m' - (Nat.pow 2 (S w) - 1))%nat).
    assert (Hr : (r <= Nat.pow 2 (S w) - 1)%nat).
    { unfold r. rewrite zd_pow_S in Hm. lia. }
    assert (Hsplit : zd_iter m' blc1 = zd_iter r blc2).
    { unfold blc2. rewrite <- zd_iter_add. f_equal. unfold r. lia. }
    pose proof (IHw blc2 r ltac:(lia) ltac:(lia) Hbits2
                  ltac:(rewrite El1 in Hb2_l1; rewrite Hb2_l1; lia)
                  ltac:(rewrite Hb2_15; lia)
                  Hz2 Hbnd2 Hr) as (IH2 & _ & IH2C).
    rewrite Hb2_15 in IH2, IH2C.
    split; [|split].
    + rewrite Hstep, Hsplit. eapply Z.le_trans; [exact IH2|].
      rewrite HC_lay, Htrip.
      pose proof (Hphi_nn (blc 15 + 1)). lia.
    + intros Hm1. exfalso.
      cbn [Nat.sub] in Hm1. rewrite zd_pow_S in Hbig, Hm1. lia.
    + intros He.
      assert (Hrc : (r = Nat.pow 2 (S w) - 1)%nat).
      { unfold r. rewrite zd_pow_S in He. lia. }
      destruct (IH2C Hrc) as (HF_oth & HF_l & HF_15 & HF_lay).
      rewrite <- El1 in HF_l.
      rewrite Hb2_l1 in HF_l.
      split; [|split; [|split]].
      * intros b Hb1 Hb2.
        rewrite Hstep, Hsplit.
        fold r blc2.
        destruct (Z.eq_dec b (l + 1)) as [->|n1].
        { replace (zd_iter r blc2 (l + 1)) with 0 by (rewrite HF_l; lia).
          rewrite (Hemp (l + 1)) by lia. reflexivity. }
        rewrite HF_oth; [|rewrite <- El1; exact n1|exact Hb2].
        rewrite Hb2_oth by congruence.
        rewrite Hv1_oth; [reflexivity| |exact n1|exact Hb2].
        unfold l. lia.
      * rewrite Hstep, Hsplit.
        replace (15 - Z.of_nat (S (S w))) with l by reflexivity.
        rewrite HF_oth; [|rewrite <- El1; lia|lia].
        rewrite Hb2_oth by lia.
        exact Hv1_l.
      * rewrite Hstep, Hsplit. rewrite HF_15. lia.
      * rewrite Hstep, Hsplit. rewrite HF_lay, HC_lay, Htrip. lia.
Qed.

(** ** The walk

    Peels the deterministic v-trip walk into complete cones plus at most
    one truncated tail, with payments already capped through [Hcap]
    against the caller's ORIGINAL suffix counts [cge1]: the rank paid by
    the p-th complete cone is (entry 15-stock) + p, and the invariant
    [blc 15 + wsum blc j .. <= cge1 j] (for j at or above the current
    deepest level) rides along the walk unchanged. *)

Variable cge1 : Z -> Z.
Variable CAPF : Z -> Z.
Hypothesis Hcap : forall lv r, 1 <= lv <= 14 -> 1 <= r <= cge1 lv ->
                  phi Sf r <= CAPF lv.
Hypothesis Hcapnn : forall lv, 1 <= lv <= 14 -> 0 <= CAPF lv.

Definition zd_sumC (peels : list Z) : Z :=
  fold_right (fun lv acc => 2 ^ (15 - lv) - 1 + acc) 0 peels.
Definition zd_sumP (peels : list Z) : Z :=
  fold_right (fun lv acc => (15 - lv) * CAPF lv + acc) 0 peels.

Lemma zd_sumC_nil : zd_sumC [] = 0.
Proof. reflexivity. Qed.
Lemma zd_sumC_cons : forall lv ps,
  zd_sumC (lv :: ps) = 2 ^ (15 - lv) - 1 + zd_sumC ps.
Proof. reflexivity. Qed.
Lemma zd_sumP_nil : zd_sumP [] = 0.
Proof. reflexivity. Qed.
Lemma zd_sumP_cons : forall lv ps,
  zd_sumP (lv :: ps) = (15 - lv) * CAPF lv + zd_sumP ps.
Proof. reflexivity. Qed.

(** one unit dropped inside a window *)
Lemma zd_wsum_drop : forall (f g : zarr) (l lo : Z) (n : nat),
  lo <= l < lo + Z.of_nat n ->
  g l = f l - 1 ->
  (forall b, lo <= b < lo + Z.of_nat n -> b <> l -> g b = f b) ->
  wsum g lo n = wsum f lo n - 1.
Proof.
  intros f g l lo n Hl Hgl Hoth.
  assert (E : wsum f lo n
              = wsum g lo n
                + wsum (fun b => if Z.eq_dec b l then 1 else 0) lo n).
  { apply zct_wsum_add'. intros i Hi.
    destruct (Z.eq_dec i l) as [->|Hne]; [lia|].
    rewrite (Hoth i Hi Hne). lia. }
  rewrite E, zct_wsum_spike.
  replace ((lo <=? l) && (l <? lo + Z.of_nat n)) with true
    by (symmetry; apply andb_true_iff;
        split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
  lia.
Qed.

Theorem zd_walk : forall (n v : nat) (L : Z) (blc : zarr),
  (v <= n)%nat ->
  (forall b, b < 1 \/ 15 < b -> blc b = 0) ->
  (forall b, 0 <= blc b <= 32764 - Z.of_nat v) ->
  Z.of_nat v <= blc 15 ->
  zksum 15 blc = 2 ^ 15 + Z.of_nat v ->
  ((0 < v)%nat -> gba_bits 15 blc <= L) ->
  (forall j, 1 <= j -> (0 < v)%nat -> j <= gba_bits 15 blc ->
     blc 15 + wsum blc j (Z.to_nat (15 - j)) <= cge1 j) ->
  exists (peels : list Z) (m : nat) (ltr : Z) (TR : Z) (blcT : zarr),
    (forall lv, In lv peels -> 1 <= lv <= 14 /\ lv <= L)
    /\ zd_sumC peels + Z.of_nat m = Z.of_nat v
    /\ layer Sf (zd_iter v blc) <= layer Sf blc + zd_sumP peels + TR
    /\ 0 <= TR
    /\ ((m = O /\ TR = 0)
        \/ (1 <= ltr <= 14 /\ ltr <= L
            /\ 1 <= Z.of_nat m <= 2 ^ (15 - ltr) - 1
            /\ TR <= (15 - ltr) * CAPF ltr
            /\ (Z.of_nat m <= 2 ^ (14 - ltr) -> TR <= CAPF ltr)
            /\ blcT 15 = blc 15 + Z.of_nat (length peels)
            /\ zksum 15 blcT = 2 ^ 15 + Z.of_nat m
            /\ (forall j, 1 <= j < ltr -> blcT j = blc j)
            /\ (forall j, ltr < j <= 14 -> blcT j = 0)
            /\ (forall b, b < 1 \/ 15 < b -> blcT b = 0)
            /\ 1 <= blcT ltr <= blc ltr
            /\ wsum blcT 1 15 = wsum blc 1 15)).
Proof.
  induction n as [|n IHn]; intros v L blc Hn Hz Hbnd Hstock Hzk HL Hinv;
    destruct v as [|v'].
  - (* n = 0, v = 0 *)
    exists [], O, 0, 0, blc.
    split; [intros lv Hin; destruct Hin|].
    split; [rewrite zd_sumC_nil; cbn [Z.of_nat]; lia|].
    split; [rewrite zd_iter_0, zd_sumP_nil; lia|].
    split; [lia|].
    left. split; reflexivity.
  - lia.
  - (* n = S n, v = 0 *)
    exists [], O, 0, 0, blc.
    split; [intros lv Hin; destruct Hin|].
    split; [rewrite zd_sumC_nil; cbn [Z.of_nat]; lia|].
    split; [rewrite zd_iter_0, zd_sumP_nil; lia|].
    split; [lia|].
    left. split; reflexivity.
  - (* n = S n, v = S v' : peel one cone *)
    assert (E215 : (2:Z) ^ 15 = 32768) by reflexivity.
    assert (Hv1 : 1 <= Z.of_nat (S v')) by lia.
    (* the deepest nonempty level *)
    assert (Hpop : exists b, 1 <= b <= 14 /\ blc b <> 0).
    { destruct (populated_low_level 15 blc ltac:(lia)
          ltac:(intro b; pose proof (Hbnd b); lia)
          ltac:(pose proof (Hbnd 15); lia)) as (b & Hb & Hnz).
      exists b. split; [lia|exact Hnz]. }
    destruct Hpop as (b0 & Hb0 & Hb0nz).
    assert (Hfb : 1 <= gba_bits 15 blc <= 14 /\ blc (gba_bits 15 blc) <> 0).
    { unfold gba_bits.
      destruct (gb_findbits_spec (Z.to_nat MAX_BITS + 1) blc (15 - 1)
          ltac:(rewrite Nat2Z.inj_add, Z2Nat.id by (unfold MAX_BITS; lia);
                unfold MAX_BITS; lia)
          ltac:(exists b0; split; [lia | exact Hb0nz])) as (Hr & Hnz).
      split; [lia | exact Hnz]. }
    destruct Hfb as (Hlr & Hlnz).
    set (l := gba_bits 15 blc) in *.
    assert (Hl1 : 1 <= blc l) by (pose proof (Hbnd l); lia).
    assert (HlL : l <= L) by (apply HL; lia).
    assert (Hemp : forall b, l < b <= 14 -> blc b = 0)
      by (intros b Hb; apply (zct_bits_empty blc b); lia).
    set (w := Z.to_nat (15 - l)).
    assert (Ew : Z.of_nat w = 15 - l) by (unfold w; lia).
    assert (Hw1 : (1 <= w)%nat) by (unfold w; lia).
    set (C := (Nat.pow 2 w - 1)%nat).
    pose proof (zd_pow_pos w) as Hpp.
    pose proof (zd_pow_lin w) as Hpl.
    assert (EC : Z.of_nat C = 2 ^ (15 - l) - 1).
    { unfold C. rewrite Nat2Z.inj_sub by exact Hpp.
      rewrite Nat2Z.inj_pow, Ew.
      change (Z.of_nat 2) with 2. change (Z.of_nat 1) with 1.
      reflexivity. }
    assert (Hp2 : 2 <= 2 ^ (15 - l)).
    { replace (15 - l) with (1 + (14 - l)) by lia.
      rewrite Z.pow_add_r by lia.
      pose proof (Z.pow_pos_nonneg 2 (14 - l) ltac:(lia) ltac:(lia)). lia. }
    assert (HC1 : 1 <= Z.of_nat C) by lia.
    (* the rank cap at this boundary *)
    assert (Hrank : blc 15 + 1 <= cge1 l).
    { assert (Hwtail : 0 <= wsum blc (l + 1) (Z.to_nat (15 - (l + 1)))).
      { apply wsum_nonneg. intros i Hi. pose proof (Hbnd i). lia. }
      assert (Hsplit1 : wsum blc l (Z.to_nat (15 - l))
                        = blc l + wsum blc (l + 1) (Z.to_nat (15 - (l + 1)))).
      { replace (Z.to_nat (15 - l))
          with (Datatypes.S (Z.to_nat (15 - (l + 1)))) by lia.
        rewrite zct_wsum_S. reflexivity. }
      pose proof (Hinv l ltac:(lia) ltac:(lia) ltac:(lia)) as HI.
      lia. }
    assert (Hphicap : phi Sf (blc 15 + 1) <= CAPF l).
    { apply (Hcap l); [lia | split; lia]. }
    destruct (le_lt_dec C (S v')) as [Hcomp|Htrunc].
    + (* a complete cone at l *)
      destruct (zd_cone w blc C Hw1 ltac:(lia)
                  ltac:(rewrite Ew; replace (15 - (15 - l)) with l by lia;
                        reflexivity)
                  ltac:(rewrite Ew; replace (15 - (15 - l)) with l by lia;
                        exact Hl1)
                  ltac:(lia)
                  Hz ltac:(intro b; pose proof (Hbnd b); lia)
                  ltac:(unfold C; lia)) as (_ & _ & CC).
      destruct (CC eq_refl) as (Coth & Cl & C15 & Clay).
      rewrite Ew in Coth, Cl, Clay.
      replace (15 - (15 - l)) with l in Coth, Cl by lia.
      set (blc' := zd_iter C blc) in *.
      assert (EvC : Z.of_nat (S v' - C) = Z.of_nat (S v') - Z.of_nat C)
        by (rewrite Nat2Z.inj_sub by exact Hcomp; reflexivity).
      (* recursion premises at blc' *)
      assert (Hz' : forall b, b < 1 \/ 15 < b -> blc' b = 0).
      { intros b Hb.
        rewrite (Coth b ltac:(lia) ltac:(lia)). apply Hz. exact Hb. }
      assert (Hbnd' : forall b, 0 <= blc' b <= 32764 - Z.of_nat (S v' - C)).
      { intro b.
        destruct (Z.eq_dec b l) as [->|n1];
          [rewrite Cl; pose proof (Hbnd l); lia|].
        destruct (Z.eq_dec b 15) as [->|n2];
          [rewrite C15; pose proof (Hbnd 15); lia|].
        rewrite (Coth b n1 n2). pose proof (Hbnd b). lia. }
      assert (Hstock' : Z.of_nat (S v' - C) <= blc' 15)
        by (rewrite C15; lia).
      assert (Ezk' : zksum 15 blc' = 2 ^ 15 + Z.of_nat (S v' - C)).
      { assert (Eext : zksum 15 blc'
                = zksum 15 (zset (zset blc l (blc l - 1)) 15 (blc 15 + 1))).
        { apply zd_zksum_ext. intros b Hb.
          destruct (Z.eq_dec b 15) as [->|Hb15].
          - rewrite zset_same. exact C15.
          - rewrite zset_other by lia.
            destruct (Z.eq_dec b l) as [->|Hbl].
            + rewrite zset_same. exact Cl.
            + rewrite zset_other by lia.
              apply Coth; congruence. }
        rewrite Eext.
        rewrite (zksum_zset_Z 15 (zset blc l (blc l - 1)) 15 (blc 15 + 1)
                   ltac:(lia)).
        rewrite (zksum_zset_Z 15 blc l (blc l - 1) ltac:(lia)).
        rewrite (zset_other blc l (blc l - 1) 15) by lia.
        replace (2 ^ (15 - 15)) with 1 by reflexivity.
        rewrite Hzk, EvC, EC. ring_simplify. lia. }
      assert (HL' : (0 < S v' - C)%nat -> gba_bits 15 blc' <= l).
      { intros Hv2.
        assert (Hpop' : exists b, 1 <= b <= 14 /\ blc' b <> 0).
        { destruct (populated_low_level 15 blc' ltac:(lia)
              ltac:(intro b; pose proof (Hbnd' b); lia)
              ltac:(rewrite Ezk'; pose proof (Hbnd' 15); lia))
            as (b & Hb & Hnz).
          exists b. split; [lia|exact Hnz]. }
        destruct Hpop' as (b1 & Hb1 & Hb1nz).
        assert (Hfb' : 1 <= gba_bits 15 blc' <= 14
                       /\ blc' (gba_bits 15 blc') <> 0).
        { unfold gba_bits.
          destruct (gb_findbits_spec (Z.to_nat MAX_BITS + 1) blc' (15 - 1)
              ltac:(rewrite Nat2Z.inj_add, Z2Nat.id by (unfold MAX_BITS; lia);
                    unfold MAX_BITS; lia)
              ltac:(exists b1; split; [lia | exact Hb1nz])) as (Hr' & Hnz').
          split; [lia | exact Hnz']. }
        destruct Hfb' as (Hlr' & Hlnz').
        destruct (Z.le_gt_cases (gba_bits 15 blc') l) as [Hle|Hgt];
          [exact Hle|].
        exfalso. apply Hlnz'.
        rewrite (Coth (gba_bits 15 blc') ltac:(lia) ltac:(lia)).
        apply Hemp. lia. }
      assert (Hinv' : forall j, 1 <= j -> (0 < S v' - C)%nat ->
                j <= gba_bits 15 blc' ->
                blc' 15 + wsum blc' j (Z.to_nat (15 - j)) <= cge1 j).
      { intros j Hj1 Hv2 Hjle.
        pose proof (HL' Hv2) as Hle_l.
        assert (Hjl : j <= l) by lia.
        assert (Ed : wsum blc' j (Z.to_nat (15 - j))
                     = wsum blc j (Z.to_nat (15 - j)) - 1).
        { apply (zd_wsum_drop blc blc' l); [lia|exact Cl|].
          intros b Hb Hne. apply Coth; [exact Hne|lia]. }
        rewrite Ed, C15.
        pose proof (Hinv j Hj1 ltac:(lia) ltac:(lia)) as HI.
        lia. }
      destruct (IHn (S v' - C)%nat l blc'
                  ltac:(lia) Hz' Hbnd' Hstock' Ezk' HL' Hinv')
        as (peels' & m & ltr & TR & blcT
            & Hprng & HsC & Hlay & Htnn & Hpkg).
      assert (Esplit : zd_iter (S v') blc = zd_iter (S v' - C) blc').
      { unfold blc'. rewrite <- zd_iter_add. f_equal. lia. }
      exists (l :: peels'), m, ltr, TR, blcT.
      split; [|split; [|split; [|split]]].
      * intros lv [->|Hin]; [split; [lia|exact HlL]|].
        destruct (Hprng lv Hin) as (Hr1 & Hr2). split; [exact Hr1|lia].
      * rewrite zd_sumC_cons. rewrite EvC in HsC. rewrite EC in HsC. lia.
      * rewrite Esplit. eapply Z.le_trans; [exact Hlay|].
        rewrite Clay, zd_sumP_cons.
        assert (Hmul : (15 - l) * phi Sf (blc 15 + 1)
                       <= (15 - l) * CAPF l)
          by (apply Z.mul_le_mono_nonneg_l; [lia|exact Hphicap]).
        lia.
      * exact Htnn.
      * destruct Hpkg as [Hleft|Hright]; [left; exact Hleft|right].
        destruct Hright as (Hltr & HltrL & Hm1 & Htrb & Htrs
                            & HT15 & HTzk & HTlow & HThigh & HTz & HTl
                            & HTcons).
        assert (Econs : wsum blc' 1 15 = wsum blc 1 15).
        { assert (E : wsum (fun b => blc' b
                            + (if Z.eq_dec b l then 1 else 0)) 1 15
                      = wsum (fun b => blc b
                            + (if Z.eq_dec b 15 then 1 else 0)) 1 15).
          { apply wsum_ext. intros i Hi.
            destruct (Z.eq_dec i l) as [->|n1].
            - destruct (Z.eq_dec l 15) as [e|n2]; [lia|].
              rewrite Cl. lia.
            - destruct (Z.eq_dec i 15) as [->|n2].
              + rewrite C15.
                destruct (Z.eq_dec 15 l); [lia|]. lia.
              + rewrite (Coth i n1 n2).
                destruct (Z.eq_dec i 15); [lia|]. lia. }
          rewrite (zct_wsum_add'
                     (fun b => blc' b + (if Z.eq_dec b l then 1 else 0))
                     blc' (fun b => if Z.eq_dec b l then 1 else 0) 1 15
                     ltac:(intros; reflexivity)) in E.
          rewrite (zct_wsum_add'
                     (fun b => blc b + (if Z.eq_dec b 15 then 1 else 0))
                     blc (fun b => if Z.eq_dec b 15 then 1 else 0) 1 15
                     ltac:(intros; reflexivity)) in E.
          rewrite !zct_wsum_spike in E.
          replace ((1 <=? l) && (l <? 1 + Z.of_nat 15)) with true in E
            by (symmetry; apply andb_true_iff;
                split; [apply Z.leb_le; lia
                       |apply Z.ltb_lt; cbn [Z.of_nat]; lia]).
          replace ((1 <=? 15) && (15 <? 1 + Z.of_nat 15)) with true in E
            by reflexivity.
          lia. }
        split; [exact Hltr|].
        split; [lia|].
        split; [exact Hm1|].
        split; [exact Htrb|].
        split; [exact Htrs|].
        split.
        { rewrite HT15, C15. cbn [length].
          rewrite Nat2Z.inj_succ. lia. }
        split; [exact HTzk|].
        split.
        { intros j Hj. rewrite (HTlow j Hj).
          apply Coth; lia. }
        split; [exact HThigh|].
        split; [exact HTz|].
        split.
        { destruct (Z.eq_dec ltr l) as [->|Hne].
          - rewrite Cl in HTl. lia.
          - rewrite (Coth ltr Hne ltac:(lia)) in HTl. exact HTl. }
        rewrite HTcons. exact Econs.
    + (* the truncated tail at l *)
      destruct (zd_cone w blc (S v') Hw1 ltac:(lia)
                  ltac:(rewrite Ew; replace (15 - (15 - l)) with l by lia;
                        reflexivity)
                  ltac:(rewrite Ew; replace (15 - (15 - l)) with l by lia;
                        exact Hl1)
                  ltac:(lia)
                  Hz ltac:(intro b; pose proof (Hbnd b); lia)
                  ltac:(unfold C in Htrunc; lia)) as (CT & CTs & _).
      exists [], (S v'), l,
        (Z.max (layer Sf (zd_iter (S v') blc) - layer Sf blc) 0), blc.
      split; [intros lv Hin; destruct Hin|].
      split; [rewrite zd_sumC_nil; lia|].
      split; [rewrite zd_sumP_nil; lia|].
      split; [lia|].
      right.
      assert (Hcnn : 0 <= CAPF l) by (apply Hcapnn; lia).
      split; [lia|].
      split; [exact HlL|].
      split.
      { split; [lia|].
        unfold C in Htrunc.
        assert (Z.of_nat (S v') < Z.of_nat (Nat.pow 2 w - 1)) by lia.
        rewrite Nat2Z.inj_sub in * by exact Hpp.
        rewrite Nat2Z.inj_pow, Ew in *.
        change (Z.of_nat 2) with 2 in *. change (Z.of_nat 1) with 1 in *.
        lia. }
      split.
      { assert (Hmul : Z.of_nat w * phi Sf (blc 15 + 1)
                       <= (15 - l) * CAPF l).
        { rewrite Ew. apply Z.mul_le_mono_nonneg_l; [lia|exact Hphicap]. }
        pose proof (Hphi_nn (blc 15 + 1)). nia. }
      split.
      { intros Hms.
        assert (Hsm : (S v' <= Nat.pow 2 (w - 1))%nat).
        { assert (E1 : Z.of_nat (Nat.pow 2 (w - 1)) = 2 ^ (14 - l)).
          { rewrite Nat2Z.inj_pow, Nat2Z.inj_sub by lia.
            rewrite Ew.
            change (Z.of_nat 2) with 2. change (Z.of_nat 1) with 1.
            f_equal. lia. }
          lia. }
        pose proof (CTs Hsm) as HT1.
        pose proof (Hphi_nn (blc 15 + 1)). lia. }
      split; [cbn [length]; cbn [Z.of_nat]; lia|].
      split; [rewrite Hzk; reflexivity|].
      split; [intros j Hj; reflexivity|].
      split; [intros j Hj; apply Hemp; lia|].
      split; [exact Hz|].
      split; [lia|reflexivity].
Qed.

End ZHODelta.
