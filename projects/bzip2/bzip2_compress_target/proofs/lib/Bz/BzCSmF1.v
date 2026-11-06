(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6 BzCFactsGm.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.BzCHuffF5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sumF_le_mono : forall n g h j, (forall b, j <= b < j + Z.of_nat n -> g b <= h b) -> sumF g j n <= sumF h j n.
Proof.
  induction n as [|n IH]; intros g h j H; cbn; [lia|].
  assert (g j <= h j) by (apply H; lia). assert (sumF g (j + 1) n <= sumF h (j + 1) n) by (apply IH; intros; apply H; lia). lia.
Qed.
Lemma sumF_const : forall n c j, sumF (fun _ => c) j n = c * Z.of_nat n.
Proof. induction n as [|n IH]; intros c j; cbn [sumF]; [lia|]. rewrite IH. lia. Qed.
Lemma sumF_add : forall n g h j, sumF (fun b => g b + h b) j n = sumF g j n + sumF h j n.
Proof. induction n as [|n IH]; intros g h j; cbn [sumF]; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_best_range : forall n cost t bc bt,
  snd (sm_best n cost t bc bt) = bt \/ t <= snd (sm_best n cost t bc bt) < t + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros cost t bc bt; cbn [sm_best]; [left; reflexivity|].
  destruct (zget cost t <? bc).
  - destruct (IH cost (t + 1) (zget cost t) t) as [E|R]; [right; rewrite E; lia| right; lia].
  - destruct (IH cost (t + 1) bc bt) as [E|R]; [left; exact E| right; lia].
Qed.
Lemma sm_best_hit : forall n cost t bc bt, (1 <= n)%nat -> zget cost t < bc ->
  t <= snd (sm_best n cost t bc bt) < t + Z.of_nat n.
Proof.
  intros [|n] cost t bc bt Hn C; [lia|]. cbn [sm_best].
  replace (zget cost t <? bc) with true by (symmetry; apply Z.ltb_lt; exact C).
  destruct (sm_best_range n cost (t + 1) (zget cost t) t) as [E|R]; [rewrite E; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zero6_get : forall c i, 0 <= i < 6 -> zget (zero6 c) i = 0.
Proof.
  intros c i Hi. unfold zero6. rewrite zfill0_get.
  destruct (Z.leb_spec 0 i), (Z.ltb_spec i (0 + Z.of_nat 6)); cbn [andb]; try reflexivity; cbn in *; lia.
Qed.

Lemma cost_slow_t_pos0 : forall n cost len icv t, 1 <= t -> zget (sm_cost_slow_t n cost len icv t) 0 = zget cost 0.
Proof.
  induction n as [|n IH]; intros cost len icv t Ht; cbn [sm_cost_slow_t]; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.
Lemma cost_slow_t_0 : forall n cost len icv, 0 <= zget cost 0 < 65536 ->
  0 <= zget (sm_cost_slow_t n cost len icv 0) 0 < 65536.
Proof.
  intros [|n] cost len icv H; cbn [sm_cost_slow_t]; [exact H|].
  rewrite cost_slow_t_pos0 by lia. rewrite zget_zset_same. apply Z.mod_pos_bound. lia.
Qed.
Lemma cost_slow_0 : forall n cost len arr1 nG i, 0 <= zget cost 0 < 65536 ->
  0 <= zget (sm_cost_slow n cost len arr1 nG i) 0 < 65536.
Proof.
  induction n as [|n IH]; intros cost len arr1 nG i H; cbn [sm_cost_slow]; [exact H|].
  apply IH. apply cost_slow_t_0. exact H.
Qed.

Lemma land_65535 : forall x, 0 <= Z.land x 65535 < 65536.
Proof. intros x. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition COSTC (arr1 len lp : zarr) (nGroups gs ge : Z) (cost0 : zarr) : zarr :=
  let cost := zero6 cost0 in
  if (nGroups =? 6) && (ge - gs + 1 =? 50) then
    let '(c01, c23, c45) := sm_cost_fast 50%nat arr1 lp gs 0 0 0 in
    let cost := zset cost 0 (Z.land c01 65535) in let cost := zset cost 1 (Z.shiftr c01 16) in
    let cost := zset cost 2 (Z.land c23 65535) in let cost := zset cost 3 (Z.shiftr c23 16) in
    let cost := zset cost 4 (Z.land c45 65535) in zset cost 5 (Z.shiftr c45 16)
  else sm_cost_slow (Z.to_nat (ge - gs + 1)) cost len arr1 nGroups gs.

Lemma COSTC_0 : forall arr1 len lp nGroups gs ge cost0, 0 <= zget (COSTC arr1 len lp nGroups gs ge cost0) 0 < 65536.
Proof.
  intros arr1 len lp nGroups gs ge cost0. unfold COSTC.
  destruct ((nGroups =? 6) && (ge - gs + 1 =? 50)).
  - destruct (sm_cost_fast 50 arr1 lp gs 0 0 0) as [[c01 c23] c45].
    rewrite !zget_zset_other by lia. rewrite zget_zset_same. apply land_65535.
  - apply cost_slow_0. rewrite zero6_get by lia. lia.
Qed.

Definition GE (nMTF gs : Z) : Z := let ge := gs + BZ_G_SIZE - 1 in if nMTF <=? ge then nMTF - 1 else ge.

Lemma GE_facts : forall nMTF gs, 0 <= gs < nMTF ->
  gs <= GE nMTF gs < nMTF /\ GE nMTF gs <= gs + 49 /\ GE nMTF gs + 1 = Z.min (gs + 50) nMTF.
Proof.
  intros nMTF gs H. unfold GE, BZ_G_SIZE. destruct (Z.leb_spec nMTF (gs + 50 - 1)); lia.
Qed.

Lemma sm_group_iter_eq : forall arr1 len lp nGroups nMTF s,
  let gs := g_gs s in let ge := GE nMTF gs in
  let cost := COSTC arr1 len lp nGroups gs ge (g_cost s) in
  let r := sm_best (Z.to_nat nGroups) cost 0 999999999 (-1) in
  sm_group_iter arr1 len lp nGroups nMTF s =
  SGS (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) (g_rfreq s) arr1 (snd r) gs) (zset (g_sel s) (g_nSel s) (snd r mod 256))
      cost (zincr (g_fave s) (snd r)) (g_nSel s + 1) (g_totc s + fst r) (ge + 1).
Proof.
  intros arr1 len lp nGroups nMTF s. cbv zeta. unfold sm_group_iter, COSTC, GE.
  destruct (sm_cost_fast 50 arr1 lp (g_gs s) 0 0 0) as [[c01 c23] c45].
  destruct (sm_best _ _ _ _ _) as [bc bt]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rows.
  Variables (A nGroups : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HG : 1 <= nGroups <= 6.

  Definition rowsum (rf : zarr) (t : Z) : Z := sumF (fun i => zget rf (258 * t + (i - 1))) 1 (Z.to_nat A).
  Definition RFI (rf : zarr) (m : Z) : Prop :=
    forall t, 0 <= t < nGroups ->
      (forall v, 0 <= v < A -> zdef rf (258 * t + v) = true /\ 0 <= zget rf (258 * t + v)) /\ rowsum rf t <= m.

  Lemma rfreq_zero_spec : forall n rf t0,
    (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A ->
       zget (sm_rfreq_zero n rf A t0) (258 * t + v) = 0 /\ zdef (sm_rfreq_zero n rf A t0) (258 * t + v) = true) /\
    (forall k, (forall t, t0 <= t < t0 + Z.of_nat n -> ~ (258 * t <= k < 258 * t + A)) ->
       zget (sm_rfreq_zero n rf A t0) k = zget rf k /\ zdef (sm_rfreq_zero n rf A t0) k = zdef rf k).
  Proof.
    induction n as [|n IH]; intros rf t0; cbn [sm_rfreq_zero].
    - split; [intros; lia| intros; split; reflexivity].
    - destruct (IH (zfill0 (Z.to_nat A) rf (258 * t0)) (t0 + 1)) as [V F]. split.
      + intros t v Ht Hv. destruct (Z.eq_dec t t0) as [->|NE].
        * destruct (F (258 * t0 + v)) as [F1 F2]. { intros t' Ht' R. nia. }
          rewrite F1, F2, zfill0_get, zfill0_def.
          replace ((258 * t0 <=? 258 * t0 + v) && (258 * t0 + v <? 258 * t0 + Z.of_nat (Z.to_nat A)))%bool with true
            by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
          split; reflexivity.
        * apply V; lia.
      + intros k Hk. destruct (F k) as [F1 F2]; [intros t Ht; apply Hk; lia|]. rewrite F1, F2, zfill0_get, zfill0_def.
        destruct (Z.leb_spec (258 * t0) k), (Z.ltb_spec k (258 * t0 + Z.of_nat (Z.to_nat A))); cbn [andb orb]; try (split; reflexivity).
        exfalso. apply (Hk t0); lia.
  Qed.

  Lemma RFI_zero : forall rf, RFI (sm_rfreq_zero (Z.to_nat nGroups) rf A 0) 0.
  Proof.
    intros rf t Ht. destruct (rfreq_zero_spec (Z.to_nat nGroups) rf 0) as [V _]. split.
    - intros v Hv. destruct (V t v ltac:(lia) Hv) as [E D]. rewrite E. split; [exact D| lia].
    - unfold rowsum. rewrite (sumF_ext _ _ (fun _ => 0)).
      + rewrite sumF_const. lia.
      + intros b Hb. replace (258 * t + (b - 1)) with (258 * t + (b - 1)) by lia. apply (proj1 (V t (b - 1) ltac:(lia) ltac:(lia))).
  Qed.

  Lemma RFI_mono : forall rf m m', RFI rf m -> m <= m' -> RFI rf m'.
  Proof. intros rf m m' H L t Ht. destruct (H t Ht) as [X Y]. split; [exact X| lia]. Qed.

  Lemma RFI_incr : forall rf m bt v, RFI rf m -> 0 <= bt < nGroups -> 0 <= v < A -> RFI (zincr rf (258 * bt + v)) (m + 1).
  Proof.
    intros rf m bt v H Hbt Hv t Ht. destruct (H t Ht) as [X Y]. split.
    - intros v' Hv'. rewrite zdef_zincr, zget_zincr. destruct (X v' Hv') as [D G].
      destruct (Z.eqb_spec (258 * t + v') (258 * bt + v)) as [E|NE]; cbn [orb]; [|rewrite D; split; [reflexivity| exact G]].
      split; [reflexivity|]. destruct (H bt Hbt) as [Xb _]. pose proof (proj2 (Xb v Hv)). lia.
    - destruct (Z.eq_dec t bt) as [->|NE].
      + unfold rowsum in *. rewrite (sumF_upd (Z.to_nat A) (fun i => zget rf (258 * bt + (i - 1))) _ 1 (v + 1) 1); [lia| lia|].
        intros x. rewrite zget_zincr.
        destruct (Z.eqb_spec (258 * bt + (x - 1)) (258 * bt + v)) as [E1|N1]; destruct (Z.eqb_spec x (v + 1)) as [E2|N2];
          first [ (replace (258 * bt + (x - 1)) with (258 * bt + v) by lia; reflexivity) | reflexivity | lia ].
      + unfold rowsum in *. rewrite (sumF_ext (Z.to_nat A) _ (fun i => zget rf (258 * t + (i - 1)))); [lia|].
        intros b Hb. rewrite zget_zincr. destruct (Z.eqb_spec (258 * t + (b - 1)) (258 * bt + v)); [|reflexivity]. exfalso. nia.
  Qed.

  Lemma RFI_inc : forall arr1 n rf bt i0 m, 0 <= bt < nGroups ->
    (forall i, i0 <= i < i0 + Z.of_nat n -> 0 <= mtfv_at arr1 i < A) ->
    RFI rf m -> RFI (sm_rfreq_inc n rf arr1 bt i0) (m + Z.of_nat n).
  Proof.
    intros arr1 n. induction n as [|n IH]; intros rf bt i0 m Hbt MV H; cbn [sm_rfreq_inc].
    - apply (RFI_mono rf m); [exact H| lia].
    - apply (RFI_mono _ (m + 1 + Z.of_nat n)); [|lia]. apply IH; [exact Hbt| intros; apply MV; lia|].
      apply RFI_incr; [exact H| exact Hbt| apply MV; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma RFI_budget : forall rf m t, RFI rf m -> 0 <= t < nGroups ->
    (forall i, 0 <= i < A -> 0 <= zget rf (258 * t + i)) /\
    sumF (fun i => Z.max (zget rf (258 * t + (i - 1))) 1) 1 (Z.to_nat A) + A <= m + 2 * A.
  Proof.
    intros rf m t H Ht. destruct (H t Ht) as [X Y]. split; [intros i Hi; apply (proj2 (X i Hi))|].
    unfold rowsum in Y.
    assert (sumF (fun i => Z.max (zget rf (258 * t + (i - 1))) 1) 1 (Z.to_nat A) <= sumF (fun i => zget rf (258 * t + (i - 1)) + 1) 1 (Z.to_nat A)).
    { apply sumF_le_mono. intros b Hb. pose proof (proj2 (X (b - 1) ltac:(lia))). lia. }
    rewrite sumF_add, sumF_const in H0. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section G.
    Variables (arr1 len lp : zarr) (nMTF : Z).
    Hypothesis HM : 1 <= nMTF.
    Hypothesis MV : forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A.

    Definition GINV (k : Z) (s : sgs) : Prop :=
      0 <= k /\ g_nSel s = k /\ g_gs s = Z.min (50 * k) nMTF /\ (k = 0 \/ 50 * (k - 1) < nMTF) /\
      (forall i, 0 <= i < k -> 0 <= zget (g_sel s) i < nGroups) /\ RFI (g_rfreq s) (g_gs s).

    Lemma group_iter_GINV : forall k s, GINV k s -> g_gs s < nMTF ->
      GINV (k + 1) (sm_group_iter arr1 len lp nGroups nMTF s).
    Proof.
      (intros k s; cps_intros (K0 & NS & GS & PK & SEL & RF); intros LT).
      rewrite sm_group_iter_eq. cbv zeta.
      set (gs := g_gs s) in *. set (ge := GE nMTF gs).
      set (cost := COSTC arr1 len lp nGroups gs ge (g_cost s)).
      pose proof (COSTC_0 arr1 len lp nGroups gs ge (g_cost s)) as C0. fold cost in C0.
      pose proof (sm_best_hit (Z.to_nat nGroups) cost 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BT.
      set (bt := snd (sm_best (Z.to_nat nGroups) cost 0 999999999 (-1))) in *.
      assert (Hgs : 0 <= gs < nMTF) by lia.
      cps_destruct (GE_facts nMTF gs Hgs) as (G1 & G2 & G3). fold ge in G1, G2, G3.
      unfold GINV; cbn [g_nSel g_gs g_sel g_rfreq].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia|]. split.
      - intros i Hi. rewrite zget_zset. destruct (Z.eqb_spec i (g_nSel s)) as [E|NE].
        + rewrite Z.mod_small by lia. lia.
        + apply SEL. lia.
      - replace (ge + 1) with (gs + Z.of_nat (Z.to_nat (ge - gs + 1))) by lia.
        apply RFI_inc; [lia| intros i Hi; apply MV; lia| exact RF].
    Qed.

    Lemma groups_GINV : forall fuel k s, GINV k s -> nMTF - g_gs s <= Z.of_nat fuel ->
      exists k', GINV k' (sm_groups fuel arr1 len lp nGroups nMTF s) /\ g_gs (sm_groups fuel arr1 len lp nGroups nMTF s) = nMTF.
    Proof.
      induction fuel as [|fuel IH]; intros k s G Hf.
      - cbn [sm_groups]. exists k. split; [exact G|]. cps_destruct G as (K0 & NS & GS & _). lia.
      - cbn [sm_groups]. destruct (Z.leb_spec nMTF (g_gs s)) as [L|L].
        + exists k. split; [exact G|]. cps_destruct G as (K0 & NS & GS & _). lia.
        + pose proof (group_iter_GINV k s G L) as G'.
          cps_destruct (IH (k + 1) _ G') as (k' & G'' & E).
          { cps_destruct G as (K0 & NS & GS & _). cps_destruct G' as (_ & _ & GS' & _). rewrite GS'. lia. }
          exists k'. split; [exact G''| exact E].
    Qed.

    (* [comment removed for export] *)
    Theorem groups_spec : forall rf0 sel cost fave, RFI rf0 0 ->
      let g := sm_groups (Z.to_nat (nMTF + 1)) arr1 len lp nGroups nMTF (SGS rf0 sel cost fave 0 0 0) in
      exists K, 1 <= K /\ g_nSel g = K /\ 50 * (K - 1) < nMTF <= 50 * K /\ g_gs g = nMTF /\
        (forall i, 0 <= i < K -> 0 <= zget (g_sel g) i < nGroups) /\ RFI (g_rfreq g) nMTF.
    Proof.
      intros rf0 sel cost fave R0. cbv zeta.
      assert (G0 : GINV 0 (SGS rf0 sel cost fave 0 0 0)).
      { unfold GINV; cbn [g_nSel g_gs g_sel g_rfreq]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
        split; [intros; lia| exact R0]. }
      cps_destruct (groups_GINV (Z.to_nat (nMTF + 1)) 0 _ G0 ltac:(cbn [g_gs]; lia)) as (K & G & E).
      exists K. cps_destruct G as (K0 & NS & GS & PK & SEL & RF). rewrite E in RF.
      assert (K1 : 1 <= K) by (destruct (Z.eq_dec K 0); [subst; rewrite E in GS; lia| lia]).
      split; [exact K1|]. split; [exact NS|]. split; [| split; [exact E| split; [exact SEL| exact RF]]].
      destruct PK as [PK|PK]; [lia|]. split; [exact PK|]. rewrite E in GS. lia.
    Qed.
  End G.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition row_ok (len : zarr) (t : Z) : Prop := forall v, 0 <= v < A -> 1 <= zget len (258 * t + v) <= 17.

  Lemma mklens_spec : forall nMTF n len rf heap weight parent t0, 1 <= nMTF <= 4194304 -> RFI rf nMTF -> 0 <= t0 -> t0 + Z.of_nat n <= nGroups ->
    let r := sm_mklens n len rf heap weight parent A t0 in
    (forall t, t0 <= t < t0 + Z.of_nat n -> row_ok (fst (fst (fst r))) t) /\
    (forall k, (forall t, t0 <= t < t0 + Z.of_nat n -> ~ (258 * t <= k < 258 * t + A)) -> zget (fst (fst (fst r))) k = zget len k).
  Proof.
    intros nMTF n. induction n as [|n IH]; intros len rf heap weight parent t0 HM RF Ht0 Hn; cbv zeta; cbn [sm_mklens].
    - cbn [fst]. split; [intros; lia| intros; reflexivity].
    - set (h := hbMakeCodeLengths len rf heap weight parent (258 * t0) (258 * t0) A 17).
      destruct (RFI_budget rf nMTF t0 RF ltac:(lia)) as [FNN FS].
      pose proof (hbMakeCodeLengths_lens A 8388607 (258 * t0) HA ltac:(lia) len rf heap weight parent (258 * t0) FNN ltac:(lia)) as HL.
      cbv zeta in HL. fold h in HL. destruct HL as [LO LF].
      destruct (IH (hs_len h) rf (hs_heap h) (hs_weight h) (hs_parent h) (t0 + 1) HM RF ltac:(lia) ltac:(lia)) as [R1 R2].
      split.
      + intros t Ht. destruct (Z.eq_dec t t0) as [->|NE].
        * intros v Hv. rewrite R2. 2:{ intros t' Ht' C. nia. }
          replace (258 * t0 + v) with (258 * t0 + (v + 1) - 1) by lia. apply LO. lia.
        * apply R1. lia.
      + intros k Hk. rewrite R2 by (intros t Ht; apply Hk; lia). apply LF.
        destruct (Z.lt_ge_cases k (258 * t0)); [left; lia| right]. pose proof (Hk t0 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ITF (nMTF : Z) (it : sits) : Prop :=
    exists K, 1 <= K /\ it_nSel it = K /\ 50 * (K - 1) < nMTF <= 50 * K /\
      (forall i, 0 <= i < K -> 0 <= zget (it_sel it) i < nGroups) /\
      (forall t, 0 <= t < nGroups -> row_ok (it_len it) t) /\ RFI (it_rfreq it) nMTF.

  Theorem sm_iter_ITF : forall arr1 nMTF s, 1 <= nMTF <= 4194304 ->
    (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) ->
    ITF nMTF (sm_iter arr1 nGroups A nMTF s).
  Proof.
    intros arr1 nMTF s HM MV. unfold sm_iter.
    set (lp := if nGroups =? 6 then _ else _).
    pose proof (groups_spec arr1 (it_len s) lp nMTF ltac:(lia) MV (sm_rfreq_zero (Z.to_nat nGroups) (it_rfreq s) A 0)
                  (it_sel s) (it_cost s) (zero6 (it_fave s)) (RFI_zero (it_rfreq s))) as GS. cbv zeta in GS.
    set (g := sm_groups _ _ _ _ _ _ _) in *.
    cps_destruct GS as (K & K1 & NS & KB & GG & SEL & RF).
    pose proof (mklens_spec nMTF (Z.to_nat nGroups) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) 0 HM RF ltac:(lia) ltac:(lia)) as ML.
    cbv zeta in ML. destruct ML as [RO _].
    destruct (sm_mklens (Z.to_nat nGroups) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) A 0) as [[[len heap] weight] parent].
    cbn [fst] in RO. exists K. cbn [it_nSel it_sel it_len it_rfreq].
    split; [exact K1|]. split; [exact NS|]. split; [exact KB|]. split; [exact SEL|]. split; [| exact RF].
    intros t Ht. apply RO. lia.
  Qed.

  Theorem sm_iters_ITF : forall n arr1 nMTF s, (1 <= n)%nat -> 1 <= nMTF <= 4194304 ->
    (forall i, 0 <= i < nMTF -> 0 <= mtfv_at arr1 i < A) ->
    ITF nMTF (sm_iters n arr1 nGroups A nMTF s).
  Proof.
    induction n as [|n IH]; intros arr1 nMTF s Hn HM MV; [lia|]. cbn [sm_iters].
    destruct n as [|n]; [cbn [sm_iters]; apply sm_iter_ITF; assumption|].
    apply IH; [lia| exact HM| exact MV].
  Qed.
End Rows.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_search_j : forall f pos ll tmp j, j <= snd (sm_pos_search f pos ll tmp j) <= j + Z.of_nat f.
Proof.
  induction f as [|f IH]; intros pos ll tmp j; cbn [sm_pos_search]; [cbn; lia|].
  destruct (ll =? tmp); [cbn [snd]; lia|]. pose proof (IH (zset pos (j + 1) tmp) ll (zget pos (j + 1)) (j + 1)). lia.
Qed.

Lemma selmtf_spec : forall n pos sel selMtf i0,
  (forall i, i0 <= i < i0 + Z.of_nat n -> 0 <= zget (snd (sm_selmtf n pos sel selMtf i0)) i <= 8) /\
  (forall k, (k < i0 \/ i0 + Z.of_nat n <= k) -> zget (snd (sm_selmtf n pos sel selMtf i0)) k = zget selMtf k).
Proof.
  induction n as [|n IH]; intros pos sel selMtf i0; cbn [sm_selmtf].
  - cbn [snd]. split; [intros; lia| intros; reflexivity].
  - pose proof (pos_search_j 8 pos (zget sel i0) (zget pos 0) 0) as J.
    destruct (sm_pos_search 8 pos (zget sel i0) (zget pos 0) 0) as [[pos' tmp] j]. cbn [snd] in J.
    destruct (IH (zset pos' 0 tmp) sel (zset selMtf i0 j) (i0 + 1)) as [V F]. split.
    + intros i Hi. destruct (Z.eq_dec i i0) as [->|NE].
      * rewrite F by lia. rewrite zget_zset_same. cbn in J. lia.
      * apply V. lia.
    + intros k Hk. rewrite F by lia. apply zget_zset_other. lia.
Qed.
