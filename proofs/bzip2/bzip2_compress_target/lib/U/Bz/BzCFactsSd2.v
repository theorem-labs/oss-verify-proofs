(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState BzCStream BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
  BzCLemmas1 BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCFactsSd CmpCut CmpCutSM CmpLaws.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hm_lens_zdef : forall n len par lb mL i tl k,
  zdef (fst (hm_lens n len par lb mL i tl)) k = (((lb + i - 1 <=? k) && (k <? lb + i - 1 + Z.of_nat n)) || zdef len k)%bool.
Proof.
  induction n as [|n IH]; intros; cbn [hm_lens].
  - change (Z.of_nat 0) with 0. destruct (Z.leb_spec (lb + i - 1) k), (Z.ltb_spec k (lb + i - 1 + 0)); cbn; try reflexivity; lia.
  - rewrite IH, zdef_zset. destruct (Z.leb_spec (lb + (i + 1) - 1) k), (Z.ltb_spec k (lb + (i + 1) - 1 + Z.of_nat n)), (Z.eqb_spec k (lb + i - 1)),
      (Z.leb_spec (lb + i - 1) k), (Z.ltb_spec k (lb + i - 1 + Z.of_nat (S n))); cbn; try reflexivity; lia.
Qed.
Lemma hm_round_zdef : forall A mL lb s k, zdef (hs_len (hm_round A mL lb s)) k = (((lb <=? k) && (k <? lb + Z.of_nat (Z.to_nat A))) || zdef (hs_len s) k)%bool.
Proof.
  intros. unfold hm_round. destruct (hm_fill _ _ _ _ _ _) as [[h p] nH].
  destruct (hm_lens (Z.to_nat A) (hs_len s) _ lb mL 1 false) as [len tl] eqn:E.
  assert (EL : len = fst (hm_lens (Z.to_nat A) (hs_len s) (hm_parent (hm_combine (Z.to_nat A) (HMS h (zset (hs_weight s) 0 0) p nH A))) lb mL 1 false)) by (rewrite E; reflexivity).
  destruct tl; cbn [hs_len]; rewrite EL, hm_lens_zdef; replace (lb + 1 - 1) with lb by lia; reflexivity.
Qed.
Lemma hm_rounds_zdef : forall f A mL lb s k, (1 <= f)%nat -> hs_done s = false ->
  zdef (hs_len (hm_rounds f A mL lb s)) k = (((lb <=? k) && (k <? lb + Z.of_nat (Z.to_nat A))) || zdef (hs_len s) k)%bool.
Proof.
  induction f as [|f IH]; intros A mL lb s k Hf Hd; [lia|]. cbn [hm_rounds]. rewrite Hd.
  destruct f as [|f'].
  - cbn [hm_rounds]. apply hm_round_zdef.
  - destruct (hs_done (hm_round A mL lb s)) eqn:D2.
    + cbn [hm_rounds]. rewrite D2. apply hm_round_zdef.
    + rewrite IH by (lia || exact D2). rewrite hm_round_zdef. destruct (_ && _)%bool; reflexivity.
Qed.
Lemma hbMakeCodeLengths_zdef : forall len freq h w p lb fb A k,
  zdef (hs_len (hbMakeCodeLengths len freq h w p lb fb A 17)) k = (((lb <=? k) && (k <? lb + Z.of_nat (Z.to_nat A))) || zdef len k)%bool.
Proof. intros. unfold hbMakeCodeLengths. apply hm_rounds_zdef; [lia| reflexivity]. Qed.

Lemma sm_mklens_zdef : forall n len rf h w p A t0, 0 <= A ->
  let L' := fst (fst (fst (sm_mklens n len rf h w p A t0))) in
  (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A -> zdef L' (258 * t + v) = true) /\
  (forall k, zdef len k = true -> zdef L' k = true).
Proof.
  induction n as [|n IH]; intros len rf h w p A t0 HA; cbv zeta; cbn [sm_mklens].
  - cbn [fst]. split; [intros; lia| intros k Hk; exact Hk].
  - set (L1 := hs_len (hbMakeCodeLengths len rf h w p (258 * t0) (258 * t0) A 17)).
    destruct (IH L1 rf (hs_heap (hbMakeCodeLengths len rf h w p (258 * t0) (258 * t0) A 17))
                 (hs_weight (hbMakeCodeLengths len rf h w p (258 * t0) (258 * t0) A 17))
                 (hs_parent (hbMakeCodeLengths len rf h w p (258 * t0) (258 * t0) A 17)) A (t0 + 1) HA) as [R M].
    assert (Z1 : forall k, zdef L1 k = (((258 * t0 <=? k) && (k <? 258 * t0 + A)) || zdef len k)%bool).
    { intros k. subst L1. rewrite hbMakeCodeLengths_zdef. rewrite Z2Nat.id by exact HA. reflexivity. }
    split.
    + intros t v Ht Hv. destruct (Z.eq_dec t t0) as [->|NE].
      * apply M. rewrite Z1. destruct (Z.leb_spec (258 * t0) (258 * t0 + v)), (Z.ltb_spec (258 * t0 + v) (258 * t0 + A)); cbn; try reflexivity; lia.
      * apply R; lia.
    + intros k Hk. apply M. rewrite Z1, Hk. apply Bool.orb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_groups_sel_zdef : forall fuel arr1 len lp nG nMTF s,
  0 <= g_nSel s -> (forall i, 0 <= i < g_nSel s -> zdef (g_sel s) i = true) ->
  let g := sm_groups fuel arr1 len lp nG nMTF s in
  0 <= g_nSel g /\ (forall i, 0 <= i < g_nSel g -> zdef (g_sel g) i = true).
Proof.
  induction fuel as [|fuel IH]; intros arr1 len lp nG nMTF s H0 H; cbv zeta; cbn [sm_groups]; [split; assumption|].
  destruct (nMTF <=? g_gs s); [split; assumption|]. apply IH.
  - unfold sm_group_iter. destruct (sm_cost_fast _ _ _ _ _ _ _) as [[c01 c23] c45]. destruct (sm_best _ _ _ _ _) as [bc bt]. cbn [g_nSel]. lia.
  - unfold sm_group_iter. destruct (sm_cost_fast _ _ _ _ _ _ _) as [[c01 c23] c45]. destruct (sm_best _ _ _ _ _) as [bc bt]. cbn [g_nSel g_sel].
    intros i Hi. rewrite zdef_zset. destruct (Z.eqb_spec i (g_nSel s)); [reflexivity|]. cbn. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma sm_iter_zdef : forall arr1 nG A nMTF s, 0 <= A -> 0 <= nG ->
  let it := sm_iter arr1 nG A nMTF s in
  (forall i, 0 <= i < it_nSel it -> zdef (it_sel it) i = true) /\
  (forall t v, 0 <= t < nG -> 0 <= v < A -> zdef (it_len it) (258 * t + v) = true).
Proof.
  intros arr1 nG A nMTF s HA HG. unfold sm_iter.
  set (g := sm_groups _ _ _ _ _ _ _).
  pose proof (sm_mklens_zdef (Z.to_nat nG) (it_len s) (g_rfreq g) (it_heap s) (it_weight s) (it_parent s) A 0 HA) as ML. cbv zeta in ML.
  destruct (sm_mklens _ _ _ _ _ _ _ _) as [[[len heap] weight] parent]. cbn [fst] in ML. destruct ML as [R M].
  cbv zeta. cbn [it_nSel it_sel it_len]. split.
  - subst g. eapply (fun H0 H => proj2 (sm_groups_sel_zdef _ _ _ _ _ _ _ H0 H)); [cbn; lia| cbn; intros; lia].
  - intros t v Ht Hv. apply R; [lia| exact Hv].
Qed.
Lemma sm_iters_zdef : forall n arr1 nG A nMTF s, 0 <= A -> 0 <= nG -> (1 <= n)%nat ->
  let it := sm_iters n arr1 nG A nMTF s in
  (forall i, 0 <= i < it_nSel it -> zdef (it_sel it) i = true) /\
  (forall t v, 0 <= t < nG -> 0 <= v < A -> zdef (it_len it) (258 * t + v) = true).
Proof.
  induction n as [|n IH]; intros arr1 nG A nMTF s HA HG Hn; [lia|]. cbn [sm_iters].
  destruct n as [|n']; [cbn [sm_iters]; apply sm_iter_zdef; assumption| apply IH; [assumption| assumption| lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ha_inner_spec : forall k code len cb lb n i vec,
  0 <= vec ->
  let r := ha_inner k code len cb lb n i vec in
  vec <= snd r <= vec + Z.of_nat k /\
  (forall j, zdef code j = true -> zdef (fst r) j = true) /\
  (forall j, i <= j < i + Z.of_nat k -> zget len (lb + j) = n -> zdef (fst r) (cb + j) = true /\ vec <= zget (fst r) (cb + j) < vec + Z.of_nat k) /\
  (forall j, (forall j', i <= j' < i + Z.of_nat k -> zget len (lb + j') = n -> j <> cb + j') -> zget (fst r) j = zget code j /\ zdef (fst r) j = zdef code j).
Proof.
  induction k as [|k IH]; intros code len cb lb n i vec Hv; cbv zeta; cbn [ha_inner].
  - cbn [fst snd]. split; [lia|]. split; [auto|]. split; [intros; lia| intros; split; reflexivity].
  - destruct (Z.eqb_spec (zget len (lb + i)) n) as [E|NE].
    + cps_destruct (IH (zset code (cb + i) vec) len cb lb n (i + 1) (vec + 1) ltac:(lia)) as (A1 & A2 & A3 & A4).
      split; [lia|]. split; [intros j Hj; apply A2; apply zdef_zset_mono; exact Hj|]. split.
      * intros j Hj Hn. destruct (Z.eq_dec j i) as [->|NJ].
        -- split; [apply A2; apply zdef_zset_same|]. rewrite (proj1 (A4 (cb + i) ltac:(intros j' Hj' _; lia))). rewrite zget_zset_same; lia.
        -- destruct (A3 j ltac:(lia) Hn) as [X Y]. split; [exact X| lia].
      * intros j Hj. destruct (A4 j ltac:(intros j' Hj' Hn'; apply Hj; [lia| exact Hn'])) as [X Y]. rewrite X, Y.
        assert (j <> cb + i) by (apply (Hj i); [lia| exact E]). rewrite zget_zset_other, zdef_zset_other by lia. split; reflexivity.
    + cps_destruct (IH code len cb lb n (i + 1) vec Hv) as (A1 & A2 & A3 & A4).
      split; [lia|]. split; [exact A2|]. split.
      * intros j Hj Hn. destruct (Z.eq_dec j i) as [->|NJ]; [congruence|]. destruct (A3 j ltac:(lia) Hn) as [X Y]. split; [exact X| lia].
      * intros j Hj. apply A4. intros j' Hj' Hn'. apply Hj; [lia| exact Hn'].
Qed.

Lemma ha_outer_spec : forall k code len cb lb A n vec,
  0 <= vec -> 0 <= A ->
  let r := ha_outer k code len cb lb A n vec in
  0 <= snd r <= (vec + 2 * A) * 2 ^ Z.of_nat k /\
  (forall j, zdef code j = true -> zdef (fst r) j = true) /\
  (forall j, 0 <= j < A -> n <= zget len (lb + j) < n + Z.of_nat k -> zdef (fst r) (cb + j) = true /\ 0 <= zget (fst r) (cb + j) < (vec + 2 * A) * 2 ^ Z.of_nat k) /\
  (forall j, (forall j', 0 <= j' < A -> n <= zget len (lb + j') < n + Z.of_nat k -> j <> cb + j') -> zget (fst r) j = zget code j /\ zdef (fst r) j = zdef code j).
Proof.
  induction k as [|k IH]; intros code len cb lb A n vec Hv HA; cbv zeta; cbn [ha_outer].
  - cbn [fst snd Z.of_nat]. rewrite Z.pow_0_r. split; [lia|]. split; [auto|]. split; [intros; lia| intros; split; reflexivity].
  - pose proof (ha_inner_spec (Z.to_nat A) code len cb lb n 0 vec Hv) as IN. cbv zeta in IN.
    destruct (ha_inner _ _ _ _ _ _ _ _) as [code1 vec1]. cbn [fst snd] in IN. cps_destruct IN as (B1 & B2 & B3 & B4).
    rewrite Z2Nat.id in B1, B3, B4 by lia.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    cps_destruct (IH code1 len cb lb A (n + 1) (vec1 * 2) ltac:(lia) HA) as (C1 & C2 & C3 & C4).
    assert (PW : (vec1 * 2 + 2 * A) * 2 ^ Z.of_nat k <= (vec + 2 * A) * 2 ^ Z.of_nat (S k) /\ 2 <= 2 ^ Z.of_nat (S k)).
    { replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). split; nia. }
    destruct PW as [PW P2].
    split; [lia|]. split; [intros j Hj; apply C2, B2, Hj|]. split.
    + intros j Hj Hn. destruct (Z.eq_dec (zget len (lb + j)) n) as [E|NE].
      * destruct (B3 j Hj E) as [D V]. split; [apply C2; exact D|].
        rewrite (proj1 (C4 (cb + j) ltac:(intros j' Hj' Hn' X; assert (j = j') by lia; subst j'; lia))). nia.
      * destruct (C3 j Hj ltac:(lia)) as [D V]. split; [exact D| lia].
    + intros j Hj. destruct (C4 j) as [X Y]. { intros j' Hj' Hn'. apply Hj; [exact Hj'| lia]. }
      rewrite X, Y. apply B4. intros j' Hj' Hn'. apply Hj; [lia| lia].
Qed.

Lemma sm_minmax_spec : forall n len t i mn mx, mn <= 32 -> 0 <= mx ->
  let r := sm_minmax n len t i mn mx in
  fst r <= mn /\ mx <= snd r /\
  (forall j, i <= j < i + Z.of_nat n -> fst r <= zget len (258 * t + j) <= snd r) /\
  ((forall j, i <= j < i + Z.of_nat n -> 1 <= zget len (258 * t + j) <= 17) -> (fst r = mn \/ 1 <= fst r <= 17) /\ (snd r = mx \/ 1 <= snd r <= 17)).
Proof.
  induction n as [|n IH]; intros len t i mn mx Hmn Hmx; cbv zeta; cbn [sm_minmax].
  - cbn [fst snd]. split; [lia|]. split; [lia|]. split; [intros; lia| intros; lia].
  - set (l := zget len (258 * t + i)).
    cps_destruct (IH len t (i + 1) (if l <? mn then l else mn) (if mx <? l then l else mx)) as (A1 & A2 & A3 & A4).
    { destruct (Z.ltb_spec l mn); lia. } { destruct (Z.ltb_spec mx l); lia. }
    split; [destruct (Z.ltb_spec l mn); lia|]. split; [destruct (Z.ltb_spec mx l); lia|]. split.
    + intros j Hj. destruct (Z.eq_dec j i) as [->|NJ]; [| apply A3; lia]. fold l. destruct (Z.ltb_spec l mn), (Z.ltb_spec mx l); lia.
    + intros ROW. destruct (A4 ltac:(intros j Hj; apply ROW; lia)) as [B1 B2]. pose proof (ROW i ltac:(lia)) as Ri. fold l in Ri.
      destruct (Z.ltb_spec l mn), (Z.ltb_spec mx l); split; lia.
Qed.

(* [comment removed for export] *)
Lemma sm_assign_spec : forall n code len A t0, 3 <= A <= 258 -> 0 <= t0 ->
  (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A -> 1 <= zget len (258 * t + v) <= 17) ->
  let c := sm_assign n code len A t0 in
  (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A -> zdef c (258 * t + v) = true /\ 0 <= zget c (258 * t + v) < 4294967296) /\
  (forall j, zdef code j = true -> zdef c j = true) /\
  (forall j, (zdef code j = true -> 0 <= zget code j < 4294967296) -> zdef c j = true -> 0 <= zget c j < 4294967296).
Proof.
  induction n as [|n IH]; intros code len A t0 HA Ht0 ROWS; cbv zeta; cbn [sm_assign].
  - split; [intros; lia|]. split; [auto| auto].
  - pose proof (sm_minmax_spec (Z.to_nat A) len t0 0 32 0 ltac:(lia) ltac:(lia)) as MM. cbv zeta in MM.
    destruct (sm_minmax _ _ _ _ _ _) as [mn mx]. cbn [fst snd] in MM. cps_destruct MM as (M1 & M2 & M3 & M4).
    rewrite Z2Nat.id in M3, M4 by lia.
    destruct (M4 ltac:(intros j Hj; apply ROWS; lia)) as [N1 N2].
    assert (ROW0 : forall v, 0 <= v < A -> mn <= zget len (258 * t0 + v) <= mx) by (intros v Hv; apply M3; lia).
    pose proof (ROWS t0 0 ltac:(lia) ltac:(lia)) as R00. pose proof (ROW0 0 ltac:(lia)) as R01.
    assert (MN : 1 <= mn <= 17) by lia. assert (MX : 1 <= mx <= 17) by lia.
    unfold hbAssignCodes.
    pose proof (ha_outer_spec (Z.to_nat (mx - mn + 1)) code len (258 * t0) (258 * t0) A mn 0 ltac:(lia) ltac:(lia)) as HO. cbv zeta in HO.
    cps_destruct HO as (O1 & O2 & O3 & O4). rewrite Z2Nat.id in O1, O3, O4 by lia.
    set (c1 := fst (ha_outer _ _ _ _ _ _ _ _)) in *.
    assert (PB : (0 + 2 * A) * 2 ^ (mx - mn + 1) < 4294967296).
    { assert (2 ^ (mx - mn + 1) <= 2 ^ 17) by (apply Z.pow_le_mono_r; lia). change (2 ^ 17) with 131072 in H. nia. }
    cps_destruct (IH c1 len A (t0 + 1) HA ltac:(lia) ltac:(intros t v Ht Hv; apply ROWS; lia)) as (I1 & I2 & I3).
    split; [| split].
    + intros t v Ht Hv. destruct (Z.eq_dec t t0) as [->|NT]; [| apply I1; lia].
      destruct (O3 v Hv ltac:(pose proof (ROW0 v Hv); lia)) as [D1 V1].
      split; [apply I2; exact D1|]. apply I3; [intros _; lia| apply I2; exact D1].
    + intros j Hj. apply I2, O2, Hj.
    + intros j Hc Hd. apply I3; [| exact Hd]. intros D.
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases j (258 * t0)) as [L|L]; [| destruct (Z.lt_ge_cases j (258 * t0 + A)) as [L2|L2]].
      * destruct (O4 j ltac:(intros j' Hj' _; lia)) as [X Y]. rewrite X. rewrite Y in D. apply Hc. exact D.
      * destruct (O3 (j - 258 * t0) ltac:(lia) ltac:(pose proof (ROW0 (j - 258 * t0) ltac:(lia)); lia)) as [D2 V2].
        replace (258 * t0 + (j - 258 * t0)) with j in V2 by lia. lia.
      * destruct (O4 j ltac:(intros j' Hj' _; lia)) as [X Y]. rewrite X. rewrite Y in D. apply Hc. exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PP (nG : Z) (pos : zarr) : Prop :=
  (forall j, 0 <= j < nG -> 0 <= zget pos j < nG) /\ (forall v, 0 <= v < nG -> exists j, 0 <= j < nG /\ zget pos j = v).

Lemma pos_search_spec : forall f pos0 pos ll j m nG,
  0 <= j <= m -> m < nG -> (Z.to_nat (m - j) < f)%nat ->
  zget pos0 m = ll -> (forall k, j <= k < m -> zget pos0 k <> ll) ->
  (forall k, 1 <= k <= j -> zget pos k = zget pos0 (k - 1)) -> (forall k, (j < k \/ k = 0) -> zget pos k = zget pos0 k) ->
  let r := sm_pos_search f pos ll (zget pos0 j) j in
  snd r = m /\ snd (fst r) = ll /\
  (forall k, 1 <= k <= m -> zget (fst (fst r)) k = zget pos0 (k - 1)) /\ (forall k, (m < k \/ k = 0) -> zget (fst (fst r)) k = zget pos0 k).
Proof.
  induction f as [|f IH]; intros pos0 pos ll j m nG Hj Hm Hf Em NOT SH REST; [lia|]. cbv zeta. cbn [sm_pos_search].
  destruct (Z.eqb_spec ll (zget pos0 j)) as [E|NE].
  - assert (j = m) by (destruct (Z.eq_dec j m); [assumption|]; exfalso; apply (NOT j); [lia| symmetry; exact E]). subst j.
    cbn [fst snd]. split; [reflexivity|]. split; [symmetry; exact E|]. split; [exact SH| exact REST].
  - assert (j < m) by (destruct (Z.eq_dec j m); [subst; congruence| lia]).
    rewrite (REST (j + 1)) by lia.
    apply (IH pos0 _ ll (j + 1) m nG); [lia| exact Hm| lia| exact Em| intros k Hk; apply NOT; lia| |].
    + intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (j + 1)) as [->|NK]; [f_equal; lia| apply SH; lia].
    + intros k Hk. rewrite zget_zset_other by lia. apply REST. lia.
Qed.

(* [comment removed for export] *)
Lemma first_occ : forall pos v nG, (exists j, 0 <= j < nG /\ zget pos j = v) ->
  exists m, 0 <= m < nG /\ zget pos m = v /\ forall k, 0 <= k < m -> zget pos k <> v.
Proof.
  (intros pos v nG; cps_intros (j & Hj & E)).
  assert (G : forall n, forall j, 0 <= j < nG -> (Z.to_nat j < n)%nat -> zget pos j = v -> exists m, 0 <= m < nG /\ zget pos m = v /\ forall k, 0 <= k < m -> zget pos k <> v).
  { induction n as [|n IH]; intros j0 Hj0 Hn E0; [lia|].
    destruct (Z.eq_dec j0 0) as [->|NZ].
    - exists 0. split; [lia|]. split; [exact E0| intros; lia].
    - destruct (Z.eq_dec (zget pos (j0 - 1)) v) as [E1|N1].
      + apply (IH (j0 - 1)); [lia| lia| exact E1].
      + (* [comment removed for export] *)
        assert (DEC : forall q, 0 <= q -> (exists k, 0 <= k < q /\ zget pos k = v) \/ (forall k, 0 <= k < q -> zget pos k <> v)).
        { intros q Hq. pattern q. apply (Z.right_induction (fun q => (exists k, 0 <= k < q /\ zget pos k = v) \/ (forall k, 0 <= k < q -> zget pos k <> v))) with (z := 0); [intros a b ->; tauto| right; intros; lia| | exact Hq].
          intros q' Hq' [[k [Hk Ek]]|NK]; [left; exists k; split; [lia| exact Ek]|].
          destruct (Z.eq_dec (zget pos q') v) as [Eq|Nq]; [left; exists q'; split; [lia| exact Eq]| right].
          intros k Hk. destruct (Z.eq_dec k q') as [->|]; [exact Nq| apply NK; lia]. }
        destruct (DEC j0 ltac:(lia)) as [[k [Hk Ek]]|NK].
        * apply (IH k); [lia| lia| exact Ek].
        * exists j0. split; [lia|]. split; [exact E0| exact NK]. }
  apply (G (S (Z.to_nat j)) j Hj ltac:(lia) E).
Qed.

Lemma selmtf_full : forall n pos sel selMtf i0 nG,
  nG <= 8 -> 0 <= i0 -> PP nG pos -> (forall i, i0 <= i < i0 + Z.of_nat n -> 0 <= zget sel i < nG) ->
  let r := sm_selmtf n pos sel selMtf i0 in
  PP nG (fst r) /\
  (forall i, i0 <= i < i0 + Z.of_nat n -> zdef (snd r) i = true /\ 0 <= zget (snd r) i < nG) /\
  (forall k, (k < i0 \/ i0 + Z.of_nat n <= k) -> zget (snd r) k = zget selMtf k /\ zdef (snd r) k = zdef selMtf k).
Proof.
  induction n as [|n IH]; intros pos sel selMtf i0 nG HG Hi0 P SEL; cbv zeta; cbn [sm_selmtf].
  - cbn [fst snd]. split; [exact P|]. split; [intros; lia| intros; split; reflexivity].
  - pose proof (SEL i0 ltac:(lia)) as S0. destruct P as [P1 P2].
    cps_destruct (first_occ pos (zget sel i0) nG (P2 _ S0)) as (m & Hm & Em & NOT).
    pose proof (pos_search_spec 8 pos pos (zget sel i0) 0 m nG ltac:(lia) ltac:(lia) ltac:(lia) Em ltac:(intros k Hk; apply NOT; lia)
                  ltac:(intros; lia) ltac:(intros; reflexivity)) as SR. cbv zeta in SR.
    destruct (sm_pos_search 8 pos (zget sel i0) (zget pos 0) 0) as [[pos' tmp] j]. cbn [fst snd] in SR. cps_destruct SR as (Ej & Et & SH & REST). subst j tmp.
    set (pos1 := zset pos' 0 (zget sel i0)).
    assert (P' : PP nG pos1).
    { split.
      - intros k Hk. subst pos1. rewrite zget_zset. destruct (Z.eqb_spec k 0) as [->|NK]; [lia|].
        destruct (Z.le_gt_cases k m) as [L|L]; [rewrite SH by lia; apply P1; lia| rewrite REST by lia; apply P1; lia].
      - intros v Hv. cps_destruct (P2 v Hv) as (k & Hk & Ek). subst pos1.
        destruct (Z.lt_trichotomy k m) as [L|[->|L]].
        + exists (k + 1). split; [lia|]. rewrite zget_zset_other by lia. rewrite SH by lia. replace (k + 1 - 1) with k by lia. exact Ek.
        + exists 0. split; [lia|]. rewrite zget_zset_same. rewrite <- Em. exact Ek || (rewrite Ek in Em; congruence) || (subst; reflexivity).
        + exists k. split; [lia|]. rewrite zget_zset_other by lia. rewrite REST by lia. exact Ek. }
    cps_destruct (IH pos1 sel (zset selMtf i0 m) (i0 + 1) nG HG ltac:(lia) P' ltac:(intros i Hi; apply SEL; lia)) as (Q1 & Q2 & Q3).
    split; [exact Q1|]. split.
    + intros i Hi. destruct (Z.eq_dec i i0) as [->|NI].
      * destruct (Q3 i0 ltac:(lia)) as [X Y]. rewrite X, Y, zget_zset_same, zdef_zset_same. split; [reflexivity| lia].
      * apply Q2. lia.
    + intros k Hk. destruct (Q3 k ltac:(lia)) as [X Y]. rewrite X, Y, zget_zset_other, zdef_zset_other by lia. split; reflexivity.
Qed.

Lemma PP_init : forall n p0 nG, Z.of_nat n = nG -> PP nG (yy_init n p0 0).
Proof.
  intros n p0 nG Hn. split.
  - intros j Hj. rewrite yy_init_get. destruct (Z.leb_spec 0 j), (Z.ltb_spec j (0 + Z.of_nat n)); cbn [andb]; lia.
  - intros v Hv. exists v. split; [lia|]. rewrite yy_init_get. destruct (Z.leb_spec 0 v), (Z.ltb_spec v (0 + Z.of_nat n)); cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma put_data_count : forall K nMTF, 1 <= nMTF -> 50 * (K - 1) < nMTF <= 50 * K ->
  forall fuel b len code arr1 sel c, 0 <= c <= K -> (Z.to_nat (K - c) <= fuel)%nat ->
  snd (sm_put_data fuel b len code arr1 sel nMTF (Z.min (50 * c) nMTF) c) = K.
Proof.
  intros K nMTF HM HK. induction fuel as [|fuel IH]; intros b len code arr1 sel c Hc Hf.
  - cbn [sm_put_data snd]. lia.
  - rewrite put_data_S. destruct (Z.leb_spec nMTF (Z.min (50 * c) nMTF)) as [L|L]; [cbn [snd]; lia|]. cbv zeta.
    set (gs := Z.min (50 * c) nMTF) in *. assert (Egs : gs = 50 * c) by lia.
    change (if nMTF <=? gs + BZ_G_SIZE - 1 then nMTF - 1 else gs + BZ_G_SIZE - 1) with (GE nMTF gs).
    cps_destruct (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    replace (GE nMTF gs + 1) with (Z.min (50 * (c + 1)) nMTF) by lia.
    apply IH; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem sd_facts_intro : forall e0 e c0 f0 p0 h0 w0 q0,
  gm_post e0 e -> 1 <= e_nblock e0 <= NBLOCKMAX + 9 -> zdefr (e_inUse e0) 0 256 -> inuse01 (e_inUse e0) ->
  sd_facts (est_C e c0 f0 p0 h0 w0 q0) (smA_ng e) (smB_nsel e c0 f0 h0 w0 q0).
Proof.
  intros e0 e c0 f0 p0 h0 w0 q0 GP NB DEFR IU.
  cps_destruct GP as (NI & NM & _ & _ & _ & ZA1 & MV & _ & ENB & _ & EIU & _).
  set (A := e_nInUse e + 2). set (nMTF := e_nMTF e).
  pose proof (sm_nGroups_range nMTF) as NG.
  assert (MV' : forall i, 0 <= i < nMTF -> 0 <= mtfv_at (e_arr1 e) i < A) by (intros i Hi; unfold mtfv_at; pose proof (MV i Hi); lia).
  unfold smB_nsel.
  set (it := smB_it e c0 f0 h0 w0 q0).
  assert (IT : ITF A (smA_ng e) nMTF it).
  { subst it. unfold smB_it, sm_alpha, sm_nmtf. fold A. fold nMTF.
    apply (sm_iters_ITF A (smA_ng e) ltac:(lia) ltac:(unfold smA_ng, sm_nmtf; fold nMTF; lia)); [unfold BZ_N_ITERS; lia| unfold nMTF; lia| exact MV']. }
  cps_destruct IT as (K & K1 & NS & KB & SEL & RO & _).
  pose proof (sm_iters_zdef BZ_N_ITERS (e_arr1 e) (smA_ng e) A nMTF
                (SITS (ip_len (smA_ip e)) (e_rfreq e) (e_len_pack e) (e_selector e) c0 f0 0 h0 w0 q0) ltac:(lia) ltac:(unfold smA_ng, sm_nmtf; fold nMTF; lia) ltac:(unfold BZ_N_ITERS; lia)) as ZD.
  cbv zeta in ZD. change (sm_iters BZ_N_ITERS (e_arr1 e) (smA_ng e) A nMTF _) with it in ZD. destruct ZD as [ZS ZL].
  pose proof (sm_assign_spec (Z.to_nat (smA_ng e)) (e_code e) (it_len it) A 0 ltac:(lia) ltac:(lia)) as AS.
  rewrite Z2Nat.id in AS by (unfold smA_ng, sm_nmtf; fold nMTF; lia). cbv zeta in AS.
  cps_destruct AS as (C1 & C2 & C3). { intros t v Ht Hv. apply RO; [lia| exact Hv]. }
  assert (NG' : 2 <= smA_ng e <= 6) by (unfold smA_ng, sm_nmtf; fold nMTF; exact NG).
  assert (PP0 : PP (smA_ng e) (yy_init (Z.to_nat (smA_ng e)) p0 0)) by (apply PP_init; lia).
  pose proof (selmtf_full (Z.to_nat (it_nSel it)) (yy_init (Z.to_nat (smA_ng e)) p0 0) (it_sel it) (e_selectorMtf e) 0 (smA_ng e)
                ltac:(lia) ltac:(lia) PP0) as SM.
  rewrite Z2Nat.id in SM by lia. cbv zeta in SM. cps_destruct SM as (PM1 & PM2 & PM3). { intros i Hi. apply SEL. lia. }
  unfold sd_facts, est_C, smC_code, smC_pm, smC_pos0, sm_alpha, sm_nmtf.
  cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code].
  fold A. fold nMTF. fold it. unfold smB_nsel. fold it.
  rewrite EIU.
  split; [lia|]. split; [exact NG|]. split; [unfold nMTF in *; lia|]. split; [lia|]. split; [unfold nMTF in *; lia|].
  split; [exact ZA1|]. split; [exact MV'|]. split.
  { intros k Hk. split; [apply DEFR; lia|]. destruct (IU k Hk); lia. }
  split; [intros i Hi; apply PM2; lia|]. split.
  { intros i Hi. split; [apply ZS; lia| apply SEL; lia]. }
  split. { intros t v Ht Hv. split; [apply ZL; [exact Ht| exact Hv]| apply RO; [exact Ht| exact Hv]]. }
  split. { intros t v Ht Hv. apply C1; [lia| exact Hv]. }
  intros b. rewrite NS. assert (E0 : Z.min (50 * 0) nMTF = 0) by lia.
  lazymatch goal with |- snd (sm_put_data ?f ?bb ?l ?c ?a ?s ?n 0 0) = _ =>
    replace (sm_put_data f bb l c a s n 0 0) with (sm_put_data f bb l c a s n (Z.min (50 * 0) nMTF) 0) by (rewrite E0; reflexivity) end.
  apply (put_data_count K nMTF ltac:(lia) KB); lia.
Qed.

End ACeilS1.
