(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCHuff BzCRebuildF BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCHuff BzCPermF BzCRebuildF BzCHuffF1. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCHuffF5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma combine_iter_wpres : forall s x, x <= hm_nNodes s -> zget (hm_weight (hm_combine_iter s)) x = zget (hm_weight s) x.
Proof. intros s x Hx. unfold hm_combine_iter. cbn [hm_weight]. apply zget_zset_other. lia. Qed.

Lemma combine_iter_nN : forall s, hm_nNodes (hm_combine_iter s) = hm_nNodes s + 1.
Proof. intros s. reflexivity. Qed.

Section Loop.
  Variables (A T0 TMAX : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HT : T0 + A <= TMAX.
  Hypothesis HTM : TMAX <= 8388607.

  Lemma combine_loop : forall fuel k s, CI A T0 k s -> (Z.to_nat (hm_nHeap s - 1) <= fuel)%nat ->
    let c := hm_combine fuel s in
    CI A T0 (A - 1) c /\ hm_nHeap c = 1 /\ (forall x, x <= hm_nNodes s -> zget (hm_weight c) x = zget (hm_weight s) x).
  Proof.
    induction fuel as [|fuel IH]; intros k s CIs Hf; cbn zeta.
    - cbn [hm_combine]. pose proof (ci_nH _ _ _ _ CIs). pose proof (ci_k _ _ _ _ CIs).
      assert (k = A - 1) by lia. subst k. split; [exact CIs|]. split; [lia|]. intros; reflexivity.
    - cbn [hm_combine]. pose proof (ci_nH _ _ _ _ CIs) as NH. pose proof (ci_k _ _ _ _ CIs) as HK.
      destruct (Z.ltb_spec 1 (hm_nHeap s)) as [GT|LE].
      + pose proof (combine_iter_ok A T0 TMAX HA HT HTM k s CIs GT) as CI'.
        cps_destruct (IH (k + 1) (hm_combine_iter s) CI') as (R1 & R2 & R3).
        { pose proof (ci_nH _ _ _ _ CI'). lia. }
        split; [exact R1|]. split; [exact R2|]. intros x Hx. rewrite R3 by (rewrite combine_iter_nN; lia).
        apply combine_iter_wpres. exact Hx.
      + assert (k = A - 1) by lia. subst k. split; [exact CIs|]. split; [lia|]. intros; reflexivity.
  Qed.
End Loop.

(* [comment removed for export] *)
Definition LW (W : zarr) (A : Z) : Prop := forall i, 1 <= i <= A -> exists t, 1 <= t /\ zget W i = 256 * t.

Lemma LW_tw : forall W A i, LW W A -> 1 <= i <= A -> zget W i = 256 * tw (zget W i) /\ 1 <= tw (zget W i).
Proof.
  intros W A i L Hi. cps_destruct (L i Hi) as (t & Ht & E). rewrite E. unfold tw.
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Definition TS (W : zarr) (A : Z) : Z := sumF (fun i => tw (zget W i)) 1 (Z.to_nat A).

(* [comment removed for export] *)
Section Start.
  Variables (A TMAX : Z) (W heap parent : zarr).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis L : LW W A.
  Hypothesis HT : TS W A + A <= TMAX.
  Hypothesis HTM : TMAX <= 8388607.

  Let W0 := zset W 0 0.
  Let heap0 := zset heap 0 0.
  Let parent0 := zset parent 0 (-2).

  Lemma W0_leaf : forall i, 1 <= i <= A -> zget W0 i = zget W i.
  Proof. intros. subst W0. apply zget_zset_other. lia. Qed.

  Lemma tw_le_TS : forall i, 1 <= i <= A -> tw (zget W i) <= TS W A.
  Proof.
    intros i Hi. unfold TS. apply (sumF_term_le (Z.to_nat A) (fun i => tw (zget W i)) 1 i); [|lia].
    intros b Hb. pose proof (LW_tw W A b L ltac:(lia)). lia.
  Qed.

  Lemma start_CI :
    let r := hm_fill (Z.to_nat A) heap0 W0 parent0 0 1 in
    snd r = A /\ CI A (TS W A) 0 (HMS (fst (fst r)) W0 (snd (fst r)) (snd r) A).
  Proof.
    cbn zeta.
    pose proof (fill_spec W0 A ltac:(lia)) as FS.
    assert (WNN : forall x, 1 <= x <= A -> 0 <= zget W0 x).
    { intros x Hx. rewrite W0_leaf by lia. pose proof (LW_tw W A x L Hx). lia. }
    specialize (FS WNN (Z.to_nat A) heap0 parent0 1 ltac:(lia) ltac:(lia)).
    change (1 - 1) with 0 in FS.
    destruct FS as [R1 R2].
    { split; [|split; [intros z Hz; lia| split; [intros x; rewrite hcnt_0; destruct (Z.leb_spec 1 x), (Z.leb_spec x 0); cbn; lia| intros; lia]]].
      split; subst heap0 W0; apply zget_zset_same. }
    assert (RA : snd (hm_fill (Z.to_nat A) heap0 W0 parent0 0 1) = A) by lia.
    split; [exact RA|].
    cps_destruct R2 as (S1 & O1 & C1 & P1). rewrite RA in *. replace (0 + Z.of_nat (Z.to_nat A)) with A in * by lia.
    pose proof (FI_entries W0 _ _ A ltac:(lia) (conj S1 (conj O1 (conj C1 P1)))) as ENT.
    constructor; cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes]; try lia.
    - exact S1.
    - intros z Hz. split; [apply ENT; exact Hz| apply P1; apply ENT; exact Hz].
    - intros x Hx Px. rewrite C1. destruct (Z.leb_spec 1 x), (Z.leb_spec x A); cbn; lia.
    - exact O1.
    - intros x Hx. rewrite W0_leaf by lia. pose proof (LW_tw W A x L Hx) as [E T]. pose proof (tw_le_TS x Hx).
      split; [|exact T]. unfold W32. rewrite E. lia.
    - unfold RS, TS. rewrite (sumF_ext (Z.to_nat A) _ (fun i => tw (zget W i))); [lia|].
      intros x Hx. rewrite P1 by lia. cbn. rewrite W0_leaf by lia. reflexivity.
    - intros x Hx Px. exfalso. apply Px. apply P1. lia.
    - intros x Hx Px. exfalso. apply Px. apply P1. lia.
    - intros x c r Hx Px Hc Pc. exfalso. rewrite P1 in Pc by lia. lia.
  Qed.
End Start.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fb (d : nat) (a p : Z) : Z := match d with O => a | S d' => fb d' (a + p) a end.

Lemma fb_mono : forall d a p a' p', 0 <= a <= a' -> 0 <= p <= p' -> fb d a p <= fb d a' p'.
Proof. induction d as [|d IH]; intros; cbn; [lia|]. apply IH; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fb_18 : fb 18 1 1 = 6765. Proof. reflexivity. Qed.
Lemma fb_step_mono : forall d a p, 1 <= a -> 1 <= p -> fb d a p <= fb (S d) a p.
Proof.
  intros d. induction d as [|d IH]; intros a p Ha Hp; cbn; [lia|].
  cbn in IH. apply (IH (a + p) a); lia.
Qed.
Lemma fb_mono_d : forall d d' a p, (d <= d')%nat -> 1 <= a -> 1 <= p -> fb d a p <= fb d' a p.
Proof.
  intros d d' a p H Ha Hp. induction H; [lia|]. eapply Z.le_trans; [exact IHle|]. apply fb_step_mono; assumption.
Qed.

Section Depth.
  Variables (A T0 : Z) (c : hms).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis CIc : CI A T0 (A - 1) c.

  Lemma nN_eq : (hm_nNodes c) = 2 * A - 1.
  Proof. pose proof (ci_nN _ _ _ _ CIc). lia. Qed.

  Lemma par_cases : forall k, 1 <= k <= (hm_nNodes c) -> zget (hm_parent c) k = -1 \/ (k < zget (hm_parent c) k <= (hm_nNodes c) /\ A < zget (hm_parent c) k).
  Proof.
    intros k Hk. destruct (Z.eq_dec (zget (hm_parent c) k) (-1)) as [E|NE]; [left; exact E|right].
    exact (ci_par _ _ _ _ CIc k Hk NE).
  Qed.

  Lemma depth_chain : forall fuel k j p,
    1 <= k <= (hm_nNodes c) -> (Z.to_nat ((hm_nNodes c) - k) < fuel)%nat -> 1 <= p ->
    (zget (hm_parent c) k <> -1 -> tw (zget (hm_weight c) k) + p <= tw (zget (hm_weight c) (zget (hm_parent c) k))) ->
    exists (d : nat) (x : Z), hm_depth fuel (hm_parent c) k j = j + Z.of_nat d /\ 1 <= x <= (hm_nNodes c) /\ zget (hm_parent c) x = -1 /\
      fb d (tw (zget (hm_weight c) k)) p <= tw (zget (hm_weight c) x) /\ (d = 0%nat -> x = k).
  Proof.
    induction fuel as [|fuel IH]; intros k j p Hk Hf Hp PB; [lia|].
    cbn [hm_depth]. destruct (par_cases k Hk) as [R|[NR AR]].
    - rewrite R. cbn. exists 0%nat, k. cbn. repeat split; lia.
    - destruct (Z.leb_spec 0 (zget (hm_parent c) k)); [|lia].
      pose proof (ci_w _ _ _ _ CIc k Hk) as [_ TK].
      assert (A1 : 1 <= zget (hm_parent c) k <= (hm_nNodes c)) by lia.
      assert (A2 : (Z.to_nat ((hm_nNodes c) - zget (hm_parent c) k) < fuel)%nat) by lia.
      cps_destruct (IH (zget (hm_parent c) k) (j + 1) (tw (zget (hm_weight c) k)) A1 A2 ltac:(lia)) as (d & x & E & Hx & Rx & FB & _).
      { intros NE. destruct (ci_edge _ _ _ _ CIc (zget (hm_parent c) k) ltac:(lia) NE) as [_ E2]. apply E2; [lia| reflexivity]. }
      exists (S d), x. rewrite E. split; [lia|]. split; [exact Hx|]. split; [exact Rx|]. split; [|intros; lia].
      cbn [fb]. eapply Z.le_trans; [|exact FB]. apply fb_mono; [|lia]. specialize (PB ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma leaf_depth_le17 : forall i, 1 <= i <= A -> T0 + A - 1 < 6765 -> hm_depth 600 (hm_parent c) i 0 <= 17.
  Proof.
    intros i Hi HT.
    pose proof nN_eq as NN. pose proof (ci_w _ _ _ _ CIc i ltac:(lia)) as [_ Ti].
    cps_destruct (depth_chain 600 i 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as (d & x & E & Hx & Rx & FB & _).
    { intros NE. exact (proj1 (ci_edge _ _ _ _ CIc i ltac:(lia) NE)). }
    rewrite E. cbn [Z.add].
    (* [comment removed for export] *)
    assert (TX : tw (zget (hm_weight c) x) <= T0 + (A - 1)).
    { pose proof (ci_rs _ _ _ _ CIc) as RSB. unfold RS in RSB.
      pose proof (sumF_term_le (Z.to_nat (hm_nNodes c)) (fun x0 => if zget (hm_parent c) x0 =? -1 then tw (zget (hm_weight c) x0) else 0) 1 x) as TL.
      cbn beta in TL. rewrite Rx, Z.eqb_refl in TL. cbn beta iota in TL.
      assert (NN0 : forall b, 1 <= b < 1 + Z.of_nat (Z.to_nat (hm_nNodes c)) -> 0 <= (if zget (hm_parent c) b =? -1 then tw (zget (hm_weight c) b) else 0)).
      { intros b Hb. destruct (zget (hm_parent c) b =? -1); [|lia]. pose proof (ci_w _ _ _ _ CIc b ltac:(lia)). lia. }
      specialize (TL NN0 ltac:(lia)). lia. }
    destruct (Nat.le_gt_cases d 17) as [LE|GT]; [lia|]. exfalso.
    pose proof (fb_mono_d 18 d 1 1 ltac:(lia) ltac:(lia) ltac:(lia)) as M1. rewrite fb_18 in M1.
    pose proof (fb_mono d 1 1 (tw (zget (hm_weight c) i)) 1 ltac:(lia) ltac:(lia)) as M2. lia.
  Qed.
End Depth.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hm_lens_false : forall n len par lb maxLen i,
  (forall k, i <= k < i + Z.of_nat n -> hm_depth 600 par k 0 <= maxLen) ->
  snd (hm_lens n len par lb maxLen i false) = false.
Proof.
  assert (G : forall n len par lb maxLen i t,
    (forall k, i <= k < i + Z.of_nat n -> hm_depth 600 par k 0 <= maxLen) ->
    snd (hm_lens n len par lb maxLen i t) = t).
  { induction n as [|n IH]; intros len par lb maxLen i t H; cbn [hm_lens]; [reflexivity|].
    rewrite IH by (intros; apply H; lia).
    replace (maxLen <? hm_depth 600 par i 0) with false by (symmetry; apply Z.ltb_ge; apply H; lia).
    apply Bool.orb_false_r. }
  intros. apply G. assumption.
Qed.

Lemma hm_rescale_spec : forall n W i0,
  (forall i, i0 <= i < i0 + Z.of_nat n -> zget (hm_rescale n W i0) i = Z.shiftl (1 + Z.shiftr (zget W i) 8 / 2) 8) /\
  (forall i, (i < i0 \/ i0 + Z.of_nat n <= i) -> zget (hm_rescale n W i0) i = zget W i).
Proof.
  induction n as [|n IH]; intros W i0; cbn [hm_rescale].
  - split; intros; [lia|reflexivity].
  - destruct (IH (zset W i0 (Z.shiftl (1 + Z.shiftr (zget W i0) 8 / 2) 8)) (i0 + 1)) as [A B]. split.
    + intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
      * rewrite B by lia. apply zget_zset_same.
      * rewrite A by lia. rewrite zget_zset_other by lia. reflexivity.
    + intros i Hi. rewrite B by lia. apply zget_zset_other. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rescale_LW_TS : forall A W Wc, 0 <= A -> LW W A -> (forall i, 1 <= i <= A -> zget Wc i = zget W i) ->
  let W' := hm_rescale (Z.to_nat A) Wc 1 in LW W' A /\ TS W' A <= A + TS W A / 2.
Proof.
  intros A W Wc HA L E. cbn zeta. destruct (hm_rescale_spec (Z.to_nat A) Wc 1) as [R1 R2].
  assert (V : forall i, 1 <= i <= A -> zget (hm_rescale (Z.to_nat A) Wc 1) i = 256 * (1 + tw (zget W i) / 2)).
  { intros i Hi. rewrite R1 by lia. rewrite E by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    change (2 ^ 8) with 256. unfold tw. lia. }
  assert (TWV : forall i, 1 <= i <= A -> tw (zget (hm_rescale (Z.to_nat A) Wc 1) i) = 1 + tw (zget W i) / 2).
  { intros i Hi. rewrite V by exact Hi. unfold tw at 1. rewrite (Z.mul_comm 256). apply Z.div_mul. lia. }
  split.
  - intros i Hi. exists (1 + tw (zget W i) / 2). pose proof (LW_tw W A i L Hi) as [_ T].
    split; [pose proof (Z.div_pos (tw (zget W i)) 2); lia | apply V; exact Hi].
  - unfold TS.
    assert (G : forall n j, (forall i, j <= i < j + Z.of_nat n -> 1 <= i <= A) ->
      2 * sumF (fun i => tw (zget (hm_rescale (Z.to_nat A) Wc 1) i)) j n <= 2 * Z.of_nat n + sumF (fun i => tw (zget W i)) j n).
    { induction n as [|n IH]; intros j Hj; cbn [sumF]; [lia|].
      specialize (IH (j + 1) ltac:(intros; apply Hj; lia)).
      rewrite TWV by (apply Hj; lia).
      pose proof (Z.mul_div_le (tw (zget W j)) 2 ltac:(lia)). lia. }
    specialize (G (Z.to_nat A) 1 ltac:(intros; lia)).
    replace (Z.of_nat (Z.to_nat A)) with A in G by lia.
    set (X := sumF _ 1 (Z.to_nat A)) in *. set (Y := sumF (fun i => tw (zget W i)) 1 (Z.to_nat A)) in *.
    replace (A + Y / 2) with ((A * 2 + Y) / 2) by (rewrite Z.div_add_l by lia; reflexivity).
    apply Z.div_le_lower_bound; lia.
Qed.


Section Rounds.
  Variables (A TMAX lb : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HTM : 774 <= TMAX <= 8388607.

  Lemma round_spec : forall s, LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    let s' := hm_round A 17 lb s in
    (TS (hs_weight s) A + A - 1 < 6765 -> hs_done s' = true) /\
    (hs_done s' = false -> LW (hs_weight s') A /\ TS (hs_weight s') A <= A + TS (hs_weight s) A / 2).
  Proof.
    intros s L HT. cbn zeta. unfold hm_round.
    pose proof (start_CI A TMAX (hs_weight s) (hs_heap s) (hs_parent s) HA L HT ltac:(lia)) as SC. cbn zeta in SC.
    destruct (hm_fill (Z.to_nat A) (zset (hs_heap s) 0 0) (zset (hs_weight s) 0 0) (zset (hs_parent s) 0 (-2)) 0 1) as [[heap parent] nHeap].
    cbn [fst snd] in SC. destruct SC as [-> CI0].
    pose proof (combine_loop A (TS (hs_weight s) A) TMAX HA HT ltac:(lia) (Z.to_nat A) 0 _ CI0 ltac:(cbn [hm_nHeap]; lia)) as CL.
    cbn zeta in CL. cps_destruct CL as (CIf & NH1 & WP). cbn [hm_nNodes hm_weight] in WP.
    set (c := hm_combine (Z.to_nat A) _) in *.
    pose proof (leaf_depth_le17 A (TS (hs_weight s) A) c HA CIf) as LD.
    destruct (hm_lens (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false) as [len tooLong] eqn:HL.
    split.
    - intros HT2. replace tooLong with false; [reflexivity|].
      transitivity (snd (hm_lens (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false)); [|rewrite HL; reflexivity].
      symmetry. apply hm_lens_false. intros k Hk. apply LD; lia.
    - destruct tooLong; cbn [hs_done hs_weight]; [|discriminate]. intros _.
      apply (rescale_LW_TS A (hs_weight s) (hm_weight c) ltac:(lia) L).
      intros i Hi. rewrite WP by lia. apply zget_zset_other. lia.
  Qed.

  Lemma rounds_done_stay : forall f s, hs_done s = true -> hm_rounds f A 17 lb s = s.
  Proof. intros f s H. destruct f; cbn [hm_rounds]; [reflexivity|]. rewrite H. reflexivity. Qed.

  Lemma rounds_done : forall fuel s, (1 <= fuel)%nat -> LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    TS (hs_weight s) A <= 2 * A + 2 ^ (Z.of_nat fuel - 1) ->
    hs_done (hm_rounds fuel A 17 lb s) = true.
  Proof.
    induction fuel as [|fuel IH]; intros s Hf L HT HB; [lia|].
    cbn [hm_rounds]. destruct (hs_done s) eqn:D; [exact D|].
    pose proof (round_spec s L HT) as [R1 R2]. cbn zeta in R1, R2.
    set (s' := hm_round A 17 lb s) in *.
    destruct (hs_done s') eqn:D'.
    - rewrite rounds_done_stay by exact D'. exact D'.
    - destruct (R2 eq_refl) as [L' T'].
      destruct fuel as [|f].
      + exfalso. replace (2 ^ (Z.of_nat 1 - 1)) with 1 in HB by reflexivity. pose proof (R1 ltac:(lia)). congruence.
      + apply IH; [lia| exact L' | |].
        * assert (TS (hs_weight s) A / 2 <= (TMAX - A) / 2) by (apply Z.div_le_mono; lia).
          assert ((TMAX - A) / 2 <= TMAX - 2 * A) by (apply Z.div_le_upper_bound; lia). lia.
        * replace (Z.of_nat (S (S f)) - 1) with (Z.succ (Z.of_nat (S f) - 1)) in HB by lia.
          rewrite Z.pow_succ_r in HB by lia.
          assert (TS (hs_weight s) A / 2 <= A + 2 ^ (Z.of_nat (S f) - 1)).
          { apply Z.div_le_upper_bound; lia. }
          lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hm_winit_spec : forall n weight freq fb i0,
    (forall i, i0 <= i < i0 + Z.of_nat n -> zget (hm_winit n weight freq fb i0) (i + 1) =
        Z.shiftl (if zget freq (fb + i) =? 0 then 1 else zget freq (fb + i)) 8) /\
    (forall j, (j < i0 + 1 \/ i0 + Z.of_nat n + 1 <= j) -> zget (hm_winit n weight freq fb i0) j = zget weight j).
  Proof.
    induction n as [|n IH]; intros weight freq fb i0; cbn [hm_winit].
    - split; intros; [lia|reflexivity].
    - destruct (IH (zset weight (i0 + 1) (Z.shiftl (if zget freq (fb + i0) =? 0 then 1 else zget freq (fb + i0)) 8)) freq fb (i0 + 1)) as [A1 B1].
      split.
      + intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
        * rewrite B1 by lia. apply zget_zset_same.
        * rewrite A1 by lia. reflexivity.
      + intros j Hj. rewrite B1 by lia. apply zget_zset_other. lia.
  Qed.

  Theorem hbMakeCodeLengths_done : forall len freq heap0 weight0 parent0 fb,
    (forall i, 0 <= i < A -> 0 <= zget freq (fb + i)) ->
    sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) + A <= TMAX ->
    hs_done (hbMakeCodeLengths len freq heap0 weight0 parent0 lb fb A 17) = true.
  Proof.
    intros len freq heap0 weight0 parent0 fb FNN FS. unfold hbMakeCodeLengths.
    destruct (hm_winit_spec (Z.to_nat A) weight0 freq fb 0) as [W1 W2].
    set (W := hm_winit (Z.to_nat A) weight0 freq fb 0) in *.
    assert (WV : forall i, 1 <= i <= A -> zget W i = 256 * Z.max (zget freq (fb + (i - 1))) 1).
    { intros i Hi. replace i with (i - 1 + 1) at 1 by lia. rewrite W1 by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      pose proof (FNN (i - 1) ltac:(lia)). destruct (Z.eqb_spec (zget freq (fb + (i - 1))) 0); lia. }
    assert (L : LW W A).
    { intros i Hi. exists (Z.max (zget freq (fb + (i - 1))) 1). split; [lia| apply WV; exact Hi]. }
    assert (T : TS W A = sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A)).
    { unfold TS. apply sumF_ext. intros b Hb. rewrite WV by lia. unfold tw. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    apply (rounds_done 40 (HMST len heap0 W parent0 false) ltac:(lia)); cbn [hs_weight]; [exact L| lia |].
    rewrite T. change (2 ^ (Z.of_nat 40 - 1)) with 549755813888. lia.
  Qed.
End Rounds.
End BzCHuffF5.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.BzCHuffF5.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Module BzCFactsHm2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.BzCHuffF5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Lemma combine_iter_wdef : forall c x, x <= hm_nNodes c -> zdef (hm_weight (hm_combine_iter c)) x = zdef (hm_weight c) x.
Proof. intros c x Hx. rewrite hm_combine_iter_eq. cbn [hm_weight]. unfold cb_w'. rewrite zdef_zset_other by lia. reflexivity. Qed.
Lemma iter_wdef : forall k c x, x <= hm_nNodes c -> zdef (hm_weight (Nat.iter k hm_combine_iter c)) x = zdef (hm_weight c) x.
Proof.
  induction k as [|k IH]; intros c x Hx; [reflexivity|]. rewrite iter_S, combine_iter_wdef by (rewrite iter_nN; lia). apply IH. exact Hx.
Qed.
(* [comment removed for export] *)

Section Intro.
  Variables (len0 freq : zarr) (lb fb A TMAX : Z).
  Hypothesis HA : 3 <= A <= 258.
  Hypothesis HTM : 774 <= TMAX <= 8388607.
  Hypothesis FRQ : forall v, 0 <= v < A -> zdef freq (fb + v) = true /\ 0 <= zget freq (fb + v) < 8388608.
  Hypothesis FS : sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) + A <= TMAX.

  Let rs := hp_rs len0 freq lb fb A.

  Lemma HA2 : 2 <= A <= 258. Proof. lia. Qed.

  (* [comment removed for export] *)
  Lemma W0_props : LW (hp_W0 freq fb A) A /\ TS (hp_W0 freq fb A) A = sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) /\
                   (forall x, 1 <= x <= A -> zdef (hp_W0 freq fb A) x = true).
  Proof.
    unfold hp_W0.
    assert (WV : forall i, 1 <= i <= A -> zget (hm_winit (Z.to_nat A) znew freq fb 0) i = 256 * Z.max (zget freq (fb + (i - 1))) 1).
    { intros i Hi. rewrite hm_winit_get. replace ((0 + 1 <=? i) && (i <=? 0 + Z.of_nat (Z.to_nat A)))%bool with true
        by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.leb_le]; lia).
      unfold fmax1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      pose proof (FRQ (i - 1) ltac:(lia)) as [_ R]. destruct (Z.eqb_spec (zget freq (fb + (i - 1))) 0); lia. }
    split; [|split].
    - intros i Hi. exists (Z.max (zget freq (fb + (i - 1))) 1). split; [lia| apply WV; exact Hi].
    - unfold TS. apply sumF_ext. intros b Hb. rewrite WV by lia. unfold tw. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
    - intros x Hx. rewrite hm_winit_def. replace ((0 + 1 <=? x) && (x <=? 0 + Z.of_nat (Z.to_nat A)))%bool with true
        by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.leb_le]; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma exec_props : forall r, hm_exec len0 freq lb fb A r ->
    LW (hs_weight (rs r)) A /\ TS (hs_weight (rs r)) A + A <= TMAX /\ (forall x, 1 <= x <= A -> zdef (hs_weight (rs r)) x = true).
  Proof.
    induction r as [|r IH]; intros EX.
    - cps_destruct W0_props as (L & T & D). cbn. split; [exact L|]. split; [rewrite T; exact FS| exact D].
    - cps_destruct (IH ltac:(intros r' Hr'; apply EX; lia)) as (L & T & D).
      pose proof (EX (S r) ltac:(lia)) as ND. subst rs. rewrite hp_rs_S in *.
      set (s := hp_rs len0 freq lb fb A r) in *.
      pose proof (round_spec A TMAX lb HA2 HTM s L T) as [_ R2]. cbn zeta in R2. destruct (R2 ND) as [L' T'].
      split; [exact L'|]. split.
      + assert (TS (hs_weight s) A / 2 <= (TMAX - A) / 2) by (apply Z.div_le_mono; lia).
        assert ((TMAX - A) / 2 <= TMAX - 2 * A) by (apply Z.div_le_upper_bound; lia). lia.
      + intros x Hx. rewrite hm_round_eq by lia.
        destruct (hr_lens A lb s) as [len tooLong]. destruct tooLong; cbn [hs_weight].
        * unfold hr_wr. rewrite hm_rescale_def. replace ((1 <=? x) && (x <? 1 + Z.of_nat (Z.to_nat A)))%bool with true
            by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity.
        * unfold hr_cf, hr_cb. rewrite iter_wdef by (cbn [hm_nNodes hr_c0]; lia). cbn [hm_weight hr_c0]. unfold hr_w0.
          rewrite zdef_zset. rewrite D by exact Hx. apply Bool.orb_true_r.
  Qed.

  (* [comment removed for export] *)
  Lemma exec_CI : forall r k, hm_exec len0 freq lb fb A r -> (Z.of_nat k <= A - 1) ->
    CI A (TS (hs_weight (rs r)) A) (Z.of_nat k) (hr_cb A (rs r) k).
  Proof.
    intros r k EX. cps_destruct (exec_props r EX) as (L & T & _). set (s := rs r) in *.
    induction k as [|k IH]; intros Hk.
    - pose proof (start_CI A TMAX (hs_weight s) (hs_heap s) (hs_parent s) HA2 L T ltac:(lia)) as SC. cbn zeta in SC.
      destruct SC as [_ C0]. fold (hr_h0 s) (hr_w0 s) (hr_p0 s) in C0. rewrite hm_fill_eq in C0. cbn [fst snd] in C0.
      replace (0 + Z.of_nat (Z.to_nat A)) with A in C0 by lia. exact C0.
    - rewrite hr_cb_S. replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      apply (combine_iter_ok A (TS (hs_weight s) A) TMAX HA2 T ltac:(lia)); [apply IH; lia|]. rewrite hr_cb_nH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exec_rf_cb : forall r k, hm_exec len0 freq lb fb A r -> (k + 2 <= Z.to_nat A)%nat -> rf_cb (hr_cb A (rs r) k).
  Proof.
    intros r k EX Hk. cps_destruct (exec_props r EX) as (L & T & _).
    pose proof (exec_CI r k EX ltac:(lia)) as CIk. set (c := hr_cb A (rs r) k) in *.
    assert (NH : 1 < hm_nHeap c) by (subst c; rewrite hr_cb_nH; lia).
    pose proof (pop2_facts A (TS (hs_weight (rs r)) A) HA2 (Z.of_nat k) c CIk NH) as PF. cbn zeta in PF.
    cps_destruct PF as (N1R & N1P & N2R & N2P & N12 & _).
    unfold rf_cb. unfold cb_n2, cb_hp1, cb_h1, cb_n1.
    set (n1 := zget (hm_heap c) 1) in *.
    set (n2 := zget (downheap (zset (hm_heap c) 1 (zget (hm_heap c) (hm_nHeap c))) (hm_weight c) (hm_nHeap c - 1) 1) 1) in *.
    destruct CIk as [cnN cnH ck csent cent ccnt cho cw crs cpar cedge cdom].
    pose proof (cw n1 N1R) as [[W1a W1b] T1]. pose proof (cw n2 N2R) as [[W2a W2b] T2].
    rewrite !weightof_eq by (unfold W32; lia).
    (* [comment removed for export] *)
    set (par := hm_parent c) in *. set (wt := hm_weight c) in *. set (nN := hm_nNodes c) in *.
    set (F := fun x => if zget par x =? -1 then tw (zget wt x) else 0).
    assert (Fnn : forall x, 1 <= x < 1 + Z.of_nat (Z.to_nat nN) -> 0 <= F x).
    { intros x Hx. subst F. cbn beta. destruct (zget par x =? -1); [|lia]. pose proof (cw x ltac:(lia)). lia. }
    set (F1 := fun x => if x =? n1 then 0 else F x).
    set (F2 := fun x => if x =? n2 then 0 else F1 x).
    assert (E1 : sumF F1 1 (Z.to_nat nN) = sumF F 1 (Z.to_nat nN) + (- tw (zget wt n1))).
    { apply (sumF_upd (Z.to_nat nN) F F1 1 n1); [lia|].
      intros x. subst F1 F. cbn beta. destruct (Z.eqb_spec x n1) as [->|]; [rewrite N1P; cbn; lia|reflexivity]. }
    assert (E2 : sumF F2 1 (Z.to_nat nN) = sumF F1 1 (Z.to_nat nN) + (- tw (zget wt n2))).
    { apply (sumF_upd (Z.to_nat nN) F1 F2 1 n2); [lia|].
      intros x. subst F2 F1 F. cbn beta. destruct (Z.eqb_spec x n2) as [->|]; [|reflexivity].
      replace (n2 =? n1) with false by (symmetry; apply Z.eqb_neq; congruence). rewrite N2P. cbn. lia. }
    assert (F2nn : 0 <= sumF F2 1 (Z.to_nat nN)).
    { apply sumF_nonneg. intros x Hx. subst F2 F1. cbn beta. destruct (x =? n2); [lia|]. destruct (x =? n1); [lia|]. apply Fnn. exact Hx. }
    unfold RS in crs. fold F in crs. lia.
  Qed.

  Lemma exec_round_facts : forall r, hm_exec len0 freq lb fb A r -> round_facts A (rs r).
  Proof.
    intros r EX. cps_destruct (exec_props r EX) as (L & T & D).
    split; [|split].
    - intros x Hx. split; [apply D; exact Hx|]. pose proof (LW_tw _ _ x L Hx) as [E Tx].
      pose proof (tw_le_TS A (hs_weight (rs r)) HA2 L x Hx). lia.
    - intros k Hk. apply exec_rf_cb; assumption.
    - pose proof (exec_CI r (Z.to_nat (A - 1)) EX ltac:(lia)) as CIf. replace (Z.of_nat (Z.to_nat (A - 1))) with (A - 1) in CIf by lia.
      fold (hr_cf A (rs r)) in CIf.
      pose proof (nN_eq A _ _ CIf) as NN.
      intros x Hx. destruct (par_cases A _ _ CIf x ltac:(lia)) as [E|[R _]]; [left; exact E| right; lia].
  Qed.

  Theorem hm_facts_intro_gen : hm_facts len0 freq lb fb A.
  Proof.
    split.
    - pose proof (hbMakeCodeLengths_done A TMAX lb HA2 HTM len0 freq znew znew znew fb ltac:(intros i Hi; apply FRQ; exact Hi) FS) as DN.
      rewrite (hbMakeCodeLengths_pt len0 freq lb fb A znew znew eq_refl eq_refl) in DN. exact DN.
    - exact exec_round_facts.
  Qed.
End Intro.

Theorem hm_facts_intro : forall (len0 freq : zarr) (lb fb A TMAX : Z),
  3 <= A <= 258 -> 774 <= TMAX <= 8388607 ->
  (forall v, 0 <= v < A -> zdef freq (fb + v) = true /\ 0 <= zget freq (fb + v) < 8388608) ->
  sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) + A <= TMAX ->
  hm_facts len0 freq lb fb A.
Proof. intros. eapply hm_facts_intro_gen; eauto. Qed.
End BzCFactsHm2.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hm_depth_ge : forall f par k j, j <= hm_depth f par k j.
Proof.
  induction f as [|f IH]; intros par k j; cbn [hm_depth]; [lia|].
  destruct (0 <=? zget par k); [|lia]. pose proof (IH par (zget par k) (j + 1)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Depth1.
  Variables (A T0 : Z) (c : hms).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis CIc : CI A T0 (A - 1) c.

  Lemma d1_nH : hm_nHeap c = 1.
  Proof. pose proof (ci_nH _ _ _ _ CIc). lia. Qed.
  Lemma d1_nN : hm_nNodes c = 2 * A - 1.
  Proof. pose proof (ci_nN _ _ _ _ CIc). lia. Qed.

  Lemma root_is_top : forall x, 1 <= x <= hm_nNodes c -> zget (hm_parent c) x = -1 -> zget (hm_heap c) 1 = x.
  Proof.
    intros x Hx Rx. pose proof (ci_cnt _ _ _ _ CIc x Hx Rx) as C1. rewrite d1_nH in C1.
    cps_destruct (hcnt_ex (hm_heap c) 1 x ltac:(lia)) as (z & Hz & E). replace z with 1 in E by lia. exact E.
  Qed.

  Lemma last_is_root : zget (hm_parent c) (hm_nNodes c) = -1.
  Proof.
    pose proof d1_nN as NN.
    destruct (Z.eq_dec (zget (hm_parent c) (hm_nNodes c)) (-1)) as [E|NE]; [exact E|].
    exfalso. destruct (ci_par _ _ _ _ CIc (hm_nNodes c) ltac:(lia) NE) as [P _]. lia.
  Qed.

  Lemma leaf_has_parent : forall i, 1 <= i <= A -> zget (hm_parent c) i <> -1.
  Proof.
    intros i Hi R. pose proof d1_nN as NN.
    pose proof (root_is_top i ltac:(lia) R) as E1.
    pose proof (root_is_top (hm_nNodes c) ltac:(lia) last_is_root) as E2. lia.
  Qed.

  Lemma leaf_depth_ge1 : forall f i, 1 <= i <= A -> 1 <= hm_depth (S f) (hm_parent c) i 0.
  Proof.
    intros f i Hi. pose proof d1_nN as NN. cbn [hm_depth].
    pose proof (leaf_has_parent i Hi) as NR.
    destruct (ci_par _ _ _ _ CIc i ltac:(lia) NR) as [P _].
    destruct (Z.leb_spec 0 (zget (hm_parent c) i)); [|lia].
    pose proof (hm_depth_ge f (hm_parent c) (zget (hm_parent c) i) (0 + 1)). lia.
  Qed.
End Depth1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hm_lens_spec : forall n len par lb maxLen i0 t0,
  let r := hm_lens n len par lb maxLen i0 t0 in
  (forall i, i0 <= i < i0 + Z.of_nat n -> zget (fst r) (lb + i - 1) = (hm_depth 600 par i 0) mod 256) /\
  (forall k, (k < lb + i0 - 1 \/ lb + i0 - 1 + Z.of_nat n <= k) -> zget (fst r) k = zget len k) /\
  (snd r = false -> t0 = false /\ forall i, i0 <= i < i0 + Z.of_nat n -> hm_depth 600 par i 0 <= maxLen).
Proof.
  induction n as [|n IH]; intros len par lb maxLen i0 t0; cbv zeta.
  - cbn [hm_lens fst snd]. split; [intros; lia|]. split; [intros; reflexivity|]. intros E. split; [exact E| intros; lia].
  - cbn [hm_lens].
    specialize (IH (zset len (lb + i0 - 1) (hm_depth 600 par i0 0 mod 256)) par lb maxLen (i0 + 1) (t0 || (maxLen <? hm_depth 600 par i0 0))%bool).
    cbv zeta in IH. cps_destruct IH as (V & F & T).
    split; [| split].
    + intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
      * rewrite F by lia. apply zget_zset_same.
      * apply V. lia.
    + intros k Hk. rewrite F by lia. apply zget_zset_other. lia.
    + intros E. destruct (T E) as [E0 D]. apply Bool.orb_false_iff in E0. destruct E0 as [E1 E2].
      split; [exact E1|]. intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
      * apply Z.ltb_ge in E2. exact E2.
      * apply D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rounds2.
  Variables (A TMAX lb : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HTM : 774 <= TMAX <= 8388607.

  Definition lens_ok (len : zarr) : Prop := forall i, 1 <= i <= A -> 1 <= zget len (lb + i - 1) <= 17.
  Definition lens_frame (len0 len : zarr) : Prop := forall k, (k < lb \/ lb + A <= k) -> zget len k = zget len0 k.

  Lemma round_spec2 : forall s, LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    let s' := hm_round A 17 lb s in
    lens_frame (hs_len s) (hs_len s') /\ (hs_done s' = true -> lens_ok (hs_len s')).
  Proof.
    intros s L HT. cbv zeta. unfold hm_round.
    pose proof (start_CI A TMAX (hs_weight s) (hs_heap s) (hs_parent s) HA L HT ltac:(lia)) as SC. cbv zeta in SC.
    destruct (hm_fill (Z.to_nat A) (zset (hs_heap s) 0 0) (zset (hs_weight s) 0 0) (zset (hs_parent s) 0 (-2)) 0 1) as [[heap parent] nHeap].
    cbn [fst snd] in SC. destruct SC as [-> CI0].
    pose proof (combine_loop A (TS (hs_weight s) A) TMAX HA HT ltac:(lia) (Z.to_nat A) 0 _ CI0 ltac:(cbn [hm_nHeap]; lia)) as CL.
    cbv zeta in CL. cps_destruct CL as (CIf & NH1 & WP).
    set (c := hm_combine (Z.to_nat A) _) in *.
    pose proof (hm_lens_spec (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false) as LS. cbv zeta in LS.
    destruct (hm_lens (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false) as [len tooLong] eqn:HL.
    cbn [fst snd] in LS. cps_destruct LS as (V & F & T).
    assert (FR : lens_frame (hs_len s) len).
    { intros k Hk. apply F. lia. }
    destruct tooLong; cbn [hs_len hs_done].
    - split; [exact FR|]. intros; discriminate.
    - split; [exact FR|]. intros _ i Hi. destruct (T eq_refl) as [_ D].
      rewrite V by lia. pose proof (D i ltac:(lia)) as Di.
      pose proof (leaf_depth_ge1 A (TS (hs_weight s) A) c HA CIf 599 i Hi) as Gi. change (S 599) with 600%nat in Gi.
      rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma rounds_spec2 : forall f s, LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    (hs_done s = true -> lens_ok (hs_len s)) ->
    let s' := hm_rounds f A 17 lb s in
    lens_frame (hs_len s) (hs_len s') /\ (hs_done s' = true -> lens_ok (hs_len s')).
  Proof.
    induction f as [|f IH]; intros s L HT D; cbv zeta.
    - cbn [hm_rounds]. split; [intros k Hk; reflexivity| exact D].
    - cbn [hm_rounds]. destruct (hs_done s) eqn:DS.
      + split; [intros k Hk; reflexivity| intros _; apply D; reflexivity].
      + pose proof (round_spec A TMAX lb HA HTM s L HT) as [R1 R2]. cbv zeta in R1, R2.
        pose proof (round_spec2 s L HT) as [F1 D1]. cbv zeta in F1, D1.
        set (s1 := hm_round A 17 lb s) in *.
        destruct (hs_done s1) eqn:DS1.
        * rewrite (rounds_done_stay A lb f s1 DS1). split; [exact F1| intros _; apply D1; reflexivity].
        * destruct (R2 eq_refl) as [L1 T1].
          assert (HT1 : TS (hs_weight s1) A + A <= TMAX).
          { assert (TS (hs_weight s) A / 2 <= (TMAX - A) / 2) by (apply Z.div_le_mono; lia).
            assert ((TMAX - A) / 2 <= TMAX - 2 * A) by (apply Z.div_le_upper_bound; lia). lia. }
          destruct (IH s1 L1 HT1 ltac:(intros E; rewrite DS1 in E; discriminate)) as [F2 D2].
          split; [| exact D2]. intros k Hk. rewrite F2 by exact Hk. apply F1. exact Hk.
  Qed.

  Theorem hbMakeCodeLengths_lens : forall len freq heap0 weight0 parent0 fb,
    (forall i, 0 <= i < A -> 0 <= zget freq (fb + i)) ->
    sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) + A <= TMAX ->
    let h := hbMakeCodeLengths len freq heap0 weight0 parent0 lb fb A 17 in
    lens_ok (hs_len h) /\ lens_frame len (hs_len h).
  Proof.
    intros len freq heap0 weight0 parent0 fb FNN FS. cbv zeta.
    pose proof (hbMakeCodeLengths_done A TMAX lb HA HTM len freq heap0 weight0 parent0 fb FNN FS) as DN.
    unfold hbMakeCodeLengths in *.
    destruct (hm_winit_spec (Z.to_nat A) weight0 freq fb 0) as [W1 W2].
    set (W := hm_winit (Z.to_nat A) weight0 freq fb 0) in *.
    assert (WV : forall i, 1 <= i <= A -> zget W i = 256 * Z.max (zget freq (fb + (i - 1))) 1).
    { intros i Hi. replace i with (i - 1 + 1) at 1 by lia. rewrite W1 by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      pose proof (FNN (i - 1) ltac:(lia)). destruct (Z.eqb_spec (zget freq (fb + (i - 1))) 0); lia. }
    assert (L : LW W A).
    { intros i Hi. exists (Z.max (zget freq (fb + (i - 1))) 1). split; [lia| apply WV; exact Hi]. }
    assert (T : TS W A = sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A)).
    { unfold TS. apply sumF_ext. intros b Hb. rewrite WV by lia. unfold tw. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    pose proof (rounds_spec2 40 (HMST len heap0 W parent0 false)) as RS. cbn [hs_weight hs_len hs_done] in RS.
    destruct (RS L ltac:(lia) ltac:(intros; discriminate)) as [F D].
    split; [apply D; exact DN| exact F].
  Qed.
End Rounds2.
