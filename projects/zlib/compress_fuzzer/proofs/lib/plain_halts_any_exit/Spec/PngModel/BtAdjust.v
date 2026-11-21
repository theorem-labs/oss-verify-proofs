(** * BtAdjust — the overflow-adjust chain is realisable, and lands EXACTLY
      on the Kraft budget.

    OWNER: an earlier development run.

    KraftAdjust (ported) proved each trip costs exactly one, UNDER [GbaChain]
    — the side conditions along the reached arrays.  This file discharges the
    chain from what BtLevels established at the pass-1 exit:

        zksum M blc = 2^M + v,  ov = 2v,  v <= blc M

    plus a slack bound [blc b <= K - 2v] with [K < 2^M].  The bound does the
    two jobs the w8 lane showed cannot come from [gb_adjust] itself: it keeps
    every count inside [u16] across the +2-per-trip growth, and it makes "no
    populated level below M" contradict [zksum > 2^M] — which is what makes
    [gb_findbits] land.  [K < 2^M] is REAL for every tree kind: the histogram
    and the trip count are both bounded by the parked window, and even the
    BL tree's [2^7 = 128] clears [4*19] with room.

    Conclusion: [zksum M (gb_adjust (S f) M blc (2v)) = 2^M] — equality, zero
    slack, matching w8's measured [rbt_exact]/[rfb_exact]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  KraftAdjust BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtPass1 BtLevels.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** [gb_findbits] lands on a populated level *)

Lemma gb_findbits_spec : forall fuel (blc : zarr) bits,
  bits < Z.of_nat fuel ->
  (exists b, 1 <= b <= bits /\ blc b <> 0) ->
  1 <= gb_findbits fuel blc bits <= bits
  /\ blc (gb_findbits fuel blc bits) <> 0.
Proof.
  induction fuel as [|f IH]; intros blc bits Hf [b [Hb Hnz]].
  - cbn [Z.of_nat] in Hf. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    cbn [gb_findbits].
    destruct (Z.eqb (blc bits) 0) eqn:E.
    + apply Z.eqb_eq in E.
      assert (Hbb : b <> bits) by (intro He; subst b; auto).
      assert (Hlt : 1 <= gb_findbits f blc (bits - 1) <= bits - 1
                    /\ blc (gb_findbits f blc (bits - 1)) <> 0).
      { apply IH; [lia | exists b; split; [lia | exact Hnz]]. }
      lia.
    + apply Z.eqb_neq in E. split; [lia | exact E].
Qed.

(** ** Histogram decompositions *)

Lemma zksum_over_zero : forall M (blc : zarr) l,
  (forall j, In j l -> blc (Z.of_nat j) = 0) ->
  zksum_over M blc l = 0.
Proof.
  intros M blc l H.
  induction l as [|a l IH].
  - apply zksum_over_nil.
  - rewrite zksum_over_cons.
    rewrite (H a (or_introl eq_refl)).
    rewrite IH by (intros j Hj; apply H; right; exact Hj).
    lia.
Qed.

Lemma zksum_split_top : forall M (blc : zarr),
  1 <= M ->
  zksum M blc = zksum_over M blc (seq 1 (Z.to_nat (M - 1))) + blc M.
Proof.
  intros M blc HM.
  unfold zksum.
  replace (Z.to_nat M) with (S (Z.to_nat (M - 1)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite seq_S, zksum_over_app, zksum_over_cons, zksum_over_nil.
  replace (Z.of_nat (1 + Z.to_nat (M - 1))) with M
    by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
  replace (M - M) with 0 by lia.
  lia.
Qed.

Lemma zksum_over_pos_ex : forall M (blc : zarr) l,
  (forall b, 0 <= blc b) ->
  0 < zksum_over M blc l ->
  exists j, In j l /\ blc (Z.of_nat j) <> 0.
Proof.
  intros M blc l Hnn.
  induction l as [|a l IH]; intro Hpos.
  - rewrite zksum_over_nil in Hpos. lia.
  - rewrite zksum_over_cons in Hpos.
    destruct (Z.eq_dec (blc (Z.of_nat a)) 0) as [Ez|Enz].
    + destruct IH as [j [Hj Hnz]].
      * rewrite Ez in Hpos. lia.
      * exists j. split; [right; exact Hj | exact Hnz].
    + exists a. split; [left; reflexivity | exact Enz].
Qed.

Lemma populated_low_level : forall M (blc : zarr),
  1 <= M ->
  (forall b, 0 <= blc b) ->
  blc M < zksum M blc ->
  exists b, 1 <= b <= M - 1 /\ blc b <> 0.
Proof.
  intros M blc HM Hnn Hlt.
  rewrite (zksum_split_top M blc HM) in Hlt.
  destruct (zksum_over_pos_ex M blc (seq 1 (Z.to_nat (M - 1))) Hnn
              ltac:(lia)) as [j [Hj Hnz]].
  apply in_seq in Hj.
  exists (Z.of_nat j). split; [lia | exact Hnz].
Qed.

(** ** One body trip, pointwise

    The exact per-slot value first ([gba_body_val], with decidable-equality
    ifs a consumer can destruct), then the four bounds the chain needs. *)

Lemma gba_body_val : forall M (blc : zarr) b,
  1 <= gba_bits M blc < M ->
  1 <= blc (gba_bits M blc) ->
  1 <= blc M ->
  (forall b', 0 <= blc b' <= 32766) ->
  gba_body M blc b
  = blc b
    - (if Z.eq_dec b (gba_bits M blc) then 1 else 0)
    + (if Z.eq_dec b (gba_bits M blc + 1) then 2 else 0)
    - (if Z.eq_dec b M then 1 else 0).
Proof.
  intros M blc b Hbits Hb1 HbM Hbnd.
  unfold gba_body. cbv zeta.
  set (i := gba_bits M blc) in *.
  assert (Hu1 : u16 (blc i - 1) = blc i - 1)
    by (unfold u16; apply Z.mod_small; specialize (Hbnd i); lia).
  set (blc1 := zset blc i (u16 (blc i - 1))) in *.
  assert (E1 : forall x, blc1 x = if Z.eq_dec x i then blc i - 1 else blc x).
  { intro x. unfold blc1. destruct (Z.eq_dec x i) as [->|Hne].
    - rewrite zset_same. exact Hu1.
    - apply zset_other. exact Hne. }
  assert (Hu2 : u16 (blc1 (i + 1) + 2) = blc (i + 1) + 2).
  { rewrite E1. destruct (Z.eq_dec (i + 1) i) as [?|_]; [lia|].
    unfold u16. apply Z.mod_small. specialize (Hbnd (i + 1)). lia. }
  set (blc2 := zset blc1 (i + 1) (u16 (blc1 (i + 1) + 2))) in *.
  assert (E2 : forall x, blc2 x
               = if Z.eq_dec x (i + 1) then blc (i + 1) + 2 else blc1 x).
  { intro x. unfold blc2. destruct (Z.eq_dec x (i + 1)) as [->|Hne].
    - rewrite zset_same. exact Hu2.
    - apply zset_other. exact Hne. }
  assert (E2M : blc2 M = blc M + (if Z.eq_dec M (i + 1) then 2 else 0)).
  { rewrite E2. destruct (Z.eq_dec M (i + 1)) as [EMi|EMi].
    - rewrite <- EMi. lia.
    - rewrite E1. destruct (Z.eq_dec M i) as [?|_]; lia. }
  assert (Hu3 : u16 (blc2 M - 1) = blc2 M - 1).
  { rewrite E2M. destruct (Z.eq_dec M (i + 1));
      unfold u16; apply Z.mod_small; specialize (Hbnd M); lia. }
  destruct (Z.eq_dec b M) as [->|HbnM].
  - rewrite zset_same, Hu3, E2M.
    destruct (Z.eq_dec M i) as [?|_]; [lia|].
    destruct (Z.eq_dec M (i + 1)); lia.
  - rewrite zset_other by exact HbnM.
    rewrite E2. destruct (Z.eq_dec b (i + 1)) as [->|Hne1].
    + destruct (Z.eq_dec (i + 1) i) as [?|_]; [lia|].
      destruct (Z.eq_dec (i + 1) M) as [?|_]; lia.
    + rewrite E1. destruct (Z.eq_dec b i) as [->|Hne2].
      * destruct (Z.eq_dec i (i + 1)) as [?|_]; [lia|].
        destruct (Z.eq_dec i M) as [?|_]; lia.
      * destruct (Z.eq_dec b M) as [?|_]; lia.
Qed.

Lemma gba_body_pointwise : forall M (blc : zarr) b,
  1 <= gba_bits M blc < M ->
  1 <= blc (gba_bits M blc) ->
  1 <= blc M ->
  (forall b', 0 <= blc b' <= 32766) ->
  blc b - 1 <= gba_body M blc b
  /\ gba_body M blc b <= blc b + 2
  /\ 0 <= gba_body M blc b
  /\ (b < 1 \/ M < b -> gba_body M blc b = blc b).
Proof.
  intros M blc b Hbits Hb1 HbM Hbnd.
  rewrite (gba_body_val M blc b Hbits Hb1 HbM Hbnd).
  pose proof (Hbnd b) as Hbb.
  repeat split;
  [ | | | intro Hb ];
  destruct (Z.eq_dec b (gba_bits M blc)) as [e1|n1];
  destruct (Z.eq_dec b (gba_bits M blc + 1)) as [e2|n2];
  destruct (Z.eq_dec b M) as [e3|n3];
  try (rewrite e1 in * );
  try (rewrite e3 in * );
  lia.
Qed.


(** ** Sum bookkeeping for one trip *)

Lemma wsum_sub : forall f g lo n,
  wsum (fun i => f i - g i) lo n = wsum f lo n - wsum g lo n.
Proof.
  intros f g lo n; revert lo.
  induction n as [|k IH]; intro lo; cbn [wsum]; [lia|].
  rewrite IH. lia.
Qed.

Lemma wsum_ind_eqb_one : forall (v lo : Z) (n : nat),
  lo <= v < lo + Z.of_nat n ->
  wsum (fun b => ind (Z.eqb b v)) lo n = 1.
Proof.
  intros v lo n; revert lo.
  induction n as [|k IH]; intros lo Hv.
  - cbn [Z.of_nat] in Hv. lia.
  - rewrite Nat2Z.inj_succ in Hv. cbn [wsum].
    destruct (Z.eq_dec lo v) as [->|Hne].
    + rewrite Z.eqb_refl. cbn [ind].
      assert (Hz : wsum (fun b => ind (Z.eqb b v)) (v + 1) k = 0).
      { transitivity (wsum (fun _ : Z => 0) (v + 1) k); [|apply wsum_zero].
        apply wsum_ext. intros b Hb.
        replace (Z.eqb b v) with false
          by (symmetry; apply Z.eqb_neq; lia).
        reflexivity. }
      rewrite Hz. lia.
    + replace (Z.eqb lo v) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [ind]. rewrite (IH (lo + 1)) by lia. lia.
Qed.

Lemma gba_body_sum : forall M (blc : zarr),
  1 <= M <= 15 ->
  1 <= gba_bits M blc < M ->
  1 <= blc (gba_bits M blc) ->
  1 <= blc M ->
  (forall b', 0 <= blc b' <= 32766) ->
  wsum (gba_body M blc) 1 (Z.to_nat M) = wsum blc 1 (Z.to_nat M).
Proof.
  intros M blc HM Hbits Hb1 HbM Hbnd.
  set (i := gba_bits M blc) in *.
  rewrite (wsum_ext (gba_body M blc)
             (fun b => (blc b + 2 * ind (Z.eqb b (i + 1)))
                       - (ind (Z.eqb b i) + ind (Z.eqb b M)))
             1 (Z.to_nat M)).
  - rewrite wsum_sub, !wsum_add.
    rewrite (wsum_ext (fun b => 2 * ind (Z.eqb b (i + 1)))
               (fun b => ind (Z.eqb b (i + 1)) + ind (Z.eqb b (i + 1)))
               1 (Z.to_nat M))
      by (intros b _; lia).
    rewrite wsum_add.
    rewrite !wsum_ind_eqb_one by (rewrite Z2Nat.id by lia; lia).
    lia.
  - intros b Hb.
    rewrite (gba_body_val M blc b Hbits Hb1 HbM Hbnd). fold i.
    destruct (Z.eq_dec b i) as [e1|n1];
      destruct (Z.eq_dec b (i + 1)) as [e2|n2];
      destruct (Z.eq_dec b M) as [e3|n3];
      repeat match goal with
             | |- context [Z.eqb ?x ?y] =>
                 let E := fresh in
                 destruct (Z.eqb x y) eqn:E;
                 [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
             end;
      cbn [ind]; lia.
Qed.

(** ** The chain, and the exact trip count *)

Lemma adjust_chain : forall (fuel : nat) (M K : Z) (blc : zarr) (v : Z),
  1 <= M <= 15 ->
  0 <= K < 2 ^ M ->
  1 <= v <= Z.of_nat fuel ->
  zksum M blc = 2 ^ M + v ->
  v <= blc M ->
  (forall b, b < 1 \/ M < b -> blc b = 0) ->
  (forall b, 0 <= blc b <= K - 2 * v) ->
  GbaChain fuel M blc (2 * v) /\ gba_trips fuel (2 * v) = v
  /\ (forall b, 0 <= gb_adjust fuel M blc (2 * v) b)
  /\ (forall b, b < 1 \/ M < b -> gb_adjust fuel M blc (2 * v) b = blc b)
  /\ wsum (gb_adjust fuel M blc (2 * v)) 1 (Z.to_nat M)
     = wsum blc 1 (Z.to_nat M).
Proof.
  induction fuel as [|f IH]; intros M K blc v HM HK Hv Hzk HvM Hz Hbnd.
  - cbn [Z.of_nat] in Hv. lia.
  - rewrite Nat2Z.inj_succ in Hv.
    assert (Hpow : 2 ^ M <= 32768).
    { replace 32768 with (2 ^ 15) by reflexivity.
      apply Z.pow_le_mono_r; lia. }
    assert (Hnn : forall b, 0 <= blc b)
      by (intro b; specialize (Hbnd b); lia).
    assert (Hex : exists b, 1 <= b <= M - 1 /\ blc b <> 0).
    { apply populated_low_level; [lia | exact Hnn |].
      specialize (Hbnd M). lia. }
    assert (Hbits : 1 <= gba_bits M blc <= M - 1
                    /\ blc (gba_bits M blc) <> 0).
    { unfold gba_bits.
      apply gb_findbits_spec; [|exact Hex].
      unfold MAX_BITS.
      rewrite Nat2Z.inj_add, Z2Nat.id by lia.
      change (Z.of_nat 1) with 1. lia. }
    destruct Hbits as [Hbr Hbnz].
    assert (Hok : GbaOk M blc).
    { split; [lia|]. split; [pose proof (Hnn (gba_bits M blc)); lia|].
      split; [lia|].
      intro b. specialize (Hbnd b). lia. }
    assert (Hbody : forall b,
      blc b - 1 <= gba_body M blc b
      /\ gba_body M blc b <= blc b + 2
      /\ 0 <= gba_body M blc b
      /\ (b < 1 \/ M < b -> gba_body M blc b = blc b)).
    { intro b. apply gba_body_pointwise; try lia.
      - pose proof (Hnn (gba_bits M blc)). lia.
      - intro b'. specialize (Hbnd b'). lia. }
    assert (HbodyM : v - 1 <= gba_body M blc M).
    { destruct (Hbody M) as [Hlo _]. lia. }
    assert (Hzk' : zksum M (gba_body M blc) = 2 ^ M + (v - 1))
      by (rewrite (zksum_gba_body M blc Hok); lia).
    assert (Hsum : wsum (gba_body M blc) 1 (Z.to_nat M)
                   = wsum blc 1 (Z.to_nat M)).
    { apply gba_body_sum; try lia.
      - pose proof (Hnn (gba_bits M blc)). lia.
      - intro b'. specialize (Hbnd b'). lia. }
    destruct (Z.eq_dec v 1) as [->|Hv1].
    + (* last trip: 2*1 = 2, the loop does not recurse *)
      assert (Hun : gb_adjust (S f) M blc (2 * 1) = gba_body M blc)
        by (apply gb_adjust_unfold_last; lia).
      split; [|split; [|split; [|split]]].
      * cbn [GbaChain].
        replace (Z.ltb 2 (2 * 1)) with false
          by (symmetry; apply Z.ltb_ge; lia).
        split; [exact Hok | exact I].
      * apply gba_trips_last. lia.
      * intro b. rewrite Hun. destruct (Hbody b) as [_ [_ [Hpos _]]].
        exact Hpos.
      * intros b Hb. rewrite Hun. destruct (Hbody b) as [_ [_ [_ Hfr]]].
        apply Hfr. exact Hb.
      * rewrite Hun. exact Hsum.
    + (* more trips *)
      assert (Hrec : GbaChain f M (gba_body M blc) (2 * (v - 1))
                     /\ gba_trips f (2 * (v - 1)) = v - 1
                     /\ (forall b, 0 <= gb_adjust f M (gba_body M blc)
                                          (2 * (v - 1)) b)
                     /\ (forall b, b < 1 \/ M < b ->
                         gb_adjust f M (gba_body M blc) (2 * (v - 1)) b
                         = gba_body M blc b)
                     /\ wsum (gb_adjust f M (gba_body M blc) (2 * (v - 1)))
                            1 (Z.to_nat M)
                        = wsum (gba_body M blc) 1 (Z.to_nat M)).
      { apply (IH M K (gba_body M blc) (v - 1)); try lia.
        - intros b Hb. destruct (Hbody b) as [_ [_ [_ Hfr]]].
          rewrite Hfr by exact Hb. apply Hz. exact Hb.
        - intros b. destruct (Hbody b) as [_ [Hup [Hlo _]]].
          specialize (Hbnd b). lia. }
      destruct Hrec as [Hch [Htr [Hpos' [Hfr' Hsum']]]].
      assert (Hun : gb_adjust (S f) M blc (2 * v)
                    = gb_adjust f M (gba_body M blc) (2 * v - 2))
        by (apply gb_adjust_unfold_step; lia).
      replace (2 * v - 2) with (2 * (v - 1)) in Hun by lia.
      split; [|split; [|split; [|split]]].
      * cbn [GbaChain].
        replace (Z.ltb 2 (2 * v)) with true
          by (symmetry; apply Z.ltb_lt; lia).
        split; [exact Hok|].
        replace (2 * v - 2) with (2 * (v - 1)) by lia.
        exact Hch.
      * rewrite gba_trips_step by lia.
        replace (2 * v - 2) with (2 * (v - 1)) by lia.
        lia.
      * intro b. rewrite Hun. apply Hpos'.
      * intros b Hb. rewrite Hun. rewrite (Hfr' b Hb).
        destruct (Hbody b) as [_ [_ [_ Hfr]]]. apply Hfr. exact Hb.
      * rewrite Hun, Hsum'. exact Hsum.
Qed.

(** ** The exact landing *)

Theorem adjust_exact : forall (f : nat) (M K : Z) (blc : zarr) (v : Z),
  1 <= M <= 15 ->
  0 <= K < 2 ^ M ->
  1 <= v <= Z.of_nat f ->
  zksum M blc = 2 ^ M + v ->
  v <= blc M ->
  (forall b, b < 1 \/ M < b -> blc b = 0) ->
  (forall b, 0 <= blc b <= K - 2 * v) ->
  zksum M (gb_adjust (S f) M blc (2 * v)) = 2 ^ M.
Proof.
  intros f M K blc v HM HK Hv Hzk HvM Hz Hbnd.
  destruct (adjust_chain (S f) M K blc v HM HK ltac:(lia) Hzk HvM Hz Hbnd)
    as [Hch [Htr _]].
  rewrite (zksum_gb_adjust f M blc (2 * v) Hch).
  rewrite Htr. lia.
Qed.

(** The array-level facts BtPass2's entry consumes. *)
Corollary adjust_facts : forall (f : nat) (M K : Z) (blc : zarr) (v : Z),
  1 <= M <= 15 ->
  0 <= K < 2 ^ M ->
  1 <= v <= Z.of_nat f ->
  zksum M blc = 2 ^ M + v ->
  v <= blc M ->
  (forall b, b < 1 \/ M < b -> blc b = 0) ->
  (forall b, 0 <= blc b <= K - 2 * v) ->
  (forall b, 0 <= gb_adjust (S f) M blc (2 * v) b)
  /\ (forall b, b < 1 \/ M < b -> gb_adjust (S f) M blc (2 * v) b = 0)
  /\ wsum (gb_adjust (S f) M blc (2 * v)) 1 (Z.to_nat M)
     = wsum blc 1 (Z.to_nat M).
Proof.
  intros f M K blc v HM HK Hv Hzk HvM Hz Hbnd.
  destruct (adjust_chain (S f) M K blc v HM HK ltac:(lia) Hzk HvM Hz Hbnd)
    as [_ [_ [Hpos [Hfr Hsum]]]].
  split; [exact Hpos|]. split; [|exact Hsum].
  intros b Hb. rewrite (Hfr b Hb). apply Hz. exact Hb.
Qed.

Print Assumptions gb_findbits_spec.
Print Assumptions populated_low_level.
Print Assumptions gba_body_pointwise.
Print Assumptions adjust_chain.
Print Assumptions adjust_exact.
Print Assumptions adjust_facts.
Print Assumptions gba_body_sum.
