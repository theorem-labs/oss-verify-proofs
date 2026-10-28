(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF BzCPermF2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3gtu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3gtu.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section S1.
  Variables (a2 : zarr) (qoff n : Z).
  Hypothesis Hn : 34 <= n.
  Hypothesis Hn9 : n <= 900000.
  Hypothesis OVB : forall i, 0 <= i < 34 -> rd8 a2 (n + i) = rd8 a2 i.
  Hypothesis OVQ : forall i, 0 <= i < 34 -> qrd a2 qoff (n + i) = qrd a2 qoff i.
  Hypothesis QIw : forall p p', 0 <= p < n -> 0 <= p' < n -> rd8 a2 p = rd8 a2 p' ->
    qrd a2 qoff p < qrd a2 qoff p' -> lexle (rot (blk a2 n) (Z.to_nat p)) (rot (blk a2 n) (Z.to_nat p')).
  Variables (d ref : Z).
  Hypothesis Hd : 0 <= d <= 15.

  Local Notation ROT := (rotz a2 n).
  Local Notation EQ := (EQB a2 n).

  (* [comment removed for export] *)
  Definition VAL (v : Z) : Prop := 0 <= v < n /\ EQ v ref d.
  Definition vals (a1 : zarr) (lo hi : Z) : Prop := forall x, lo <= x <= hi -> VAL (rd32 a1 x).
  Definition msorted (a1 : zarr) (lo hi : Z) : Prop :=
    forall i j, lo <= i -> i <= j -> j <= hi -> lexle (ROT (rd32 a1 i)) (ROT (rd32 a1 j)).

  Lemma VAL_w32 : forall v, VAL v -> 0 <= v < 4294967296.
  Proof. intros v [A _]. lia. Qed.

  Lemma EQB_trans : forall x y z k, EQ x y k -> EQ y z k -> EQ x z k.
  Proof. intros x y z k A B j Hj. rewrite (A j Hj). apply B. exact Hj. Qed.

  (* [comment removed for export] *)
  Lemma cmp_sound : forall x y b, VAL x -> VAL y ->
    (fst (mainGtU (x + d) (y + d) a2 qoff n b) = true -> lexle (ROT y) (ROT x)) /\
    (fst (mainGtU (x + d) (y + d) a2 qoff n b) = false -> lexle (ROT x) (ROT y)).
  Proof.
    intros x y b [Rx Ex] [Ry Ey].
    assert (E : EQ x y d) by (eapply EQB_trans; [exact Ex | apply EQB_sym; exact Ey]).
    pose proof (mainGtU_sound a2 qoff n Hn OVB OVQ QIw (x + d) (y + d) b ltac:(lia) ltac:(lia)) as [ST SF].
    split; intros Hb.
    - apply (lexle_shift_back a2 n Hn x y d ltac:(lia) E). apply ST. exact Hb.
    - apply (lexle_shift_back a2 n Hn y x d ltac:(lia) (EQB_sym a2 n x y d E)). apply SF. exact Hb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mss_shift_facts : forall f a1 h lo hi j v b,
    0 < h -> lo + h <= j <= hi -> vals a1 lo hi -> VAL v ->
    let r := mss_shift f a1 a2 qoff n d h lo j v b in
    let a1' := fst (fst r) in let j' := snd (fst r) in
    lo <= j' <= j /\ vals a1' lo hi /\ (forall x, x < lo \/ hi < x -> rd32 a1' x = rd32 a1 x) /\ snd r <= b.
  Proof.
    induction f as [|f IH]; intros a1 h lo hi j v b Hh Hj VS Vv; cbv zeta.
    - cbn [mss_shift fst snd]. split; [lia|]. split; [exact VS|]. split; [intros; reflexivity|lia].
    - rewrite mss_shift_S. pose proof (mainGtU_budget_le (rd32 a1 (j - h) + d) (v + d) a2 qoff n b) as BL.
      destruct (mainGtU _ _ _ _ _ _) as [gt b']. cbn [snd] in BL. destruct gt.
      2:{ cbn [fst snd]. split; [lia|]. split; [exact VS|]. split; [intros; reflexivity|exact BL]. }
      cbv zeta. set (a1w := wr32 a1 j (rd32 a1 (j - h))).
      assert (VSw : vals a1w lo hi).
      { intros x Hx. subst a1w. destruct (Z.eq_dec x j) as [->|N].
        - rewrite rd32_wr32_same; [apply VS; lia|]. apply VAL_w32. apply VS. lia.
        - rewrite rd32_wr32_other by lia. apply VS. lia. }
      assert (FRw : forall x, x < lo \/ hi < x -> rd32 a1w x = rd32 a1 x) by (intros x Hx; subst a1w; apply rd32_wr32_other; lia).
      destruct (Z.leb_spec (j - h) (lo + h - 1)) as [STOP|GO].
      + cbn [fst snd]. split; [lia|]. split; [exact VSw|]. split; [exact FRw|exact BL].
      + specialize (IH a1w h lo hi (j - h) v b' Hh ltac:(lia) VSw Vv). cbv zeta in IH.
        destruct (mss_shift f a1w a2 qoff n d h lo (j - h) v b') as [[a1' j'] b'']. cbn [fst snd] in *.
        cps_destruct IH as (A & B & C & D). split; [lia|]. split; [exact B|]. split; [|lia].
        intros x Hx. rewrite C by lia. apply FRw. lia.
  Qed.

  Lemma mss_ins_facts : forall a1 h lo hi i b,
    0 < h -> lo + h <= i <= hi -> vals a1 lo hi ->
    let r := mss_ins a1 a2 qoff n d h lo i b in
    vals (fst r) lo hi /\ (forall x, x < lo \/ hi < x -> rd32 (fst r) x = rd32 a1 x) /\ snd r <= b.
  Proof.
    intros a1 h lo hi i b Hh Hi VS. cbv zeta. unfold mss_ins.
    pose proof (VS i ltac:(lia)) as Vv.
    pose proof (mss_shift_facts (S (Z.to_nat (i - lo))) a1 h lo hi i (rd32 a1 i) b Hh ltac:(lia) VS Vv) as SH. cbv zeta in SH.
    destruct (mss_shift _ a1 a2 qoff n d h lo i (rd32 a1 i) b) as [[a1' j'] b']. cbn [fst snd] in *.
    cps_destruct SH as (A & B & C & D). split; [|split; [|exact D]].
    - intros x Hx. destruct (Z.eq_dec x j') as [->|N]; [rewrite rd32_wr32_same; [exact Vv|apply VAL_w32; exact Vv]|].
      rewrite rd32_wr32_other by lia. apply B. lia.
    - intros x Hx. rewrite rd32_wr32_other by lia. apply C. lia.
  Qed.

  Lemma mss_hloop_facts : forall f a1 h lo hi i b,
    0 < h -> lo + h <= i -> vals a1 lo hi ->
    let r := mss_hloop f a1 a2 qoff n d h lo hi i b in
    vals (fst (fst r)) lo hi /\ (forall x, x < lo \/ hi < x -> rd32 (fst (fst r)) x = rd32 a1 x) /\
    snd (fst r) <= b /\ (snd r = true -> snd (fst r) < 0).
  Proof.
    induction f as [|f IH]; intros a1 h lo hi i b Hh Hi VS; cbv zeta; cbn [mss_hloop].
    - cbn [fst snd]. split; [exact VS|]. split; [intros; reflexivity|]. split; [lia|intros; discriminate].
    - destruct (Z.ltb_spec hi i) as [L1|L1]. { cbn [fst snd]. split; [exact VS|]. split; [intros; reflexivity|]. split; [lia|intros; discriminate]. }
      pose proof (mss_ins_facts a1 h lo hi i b Hh ltac:(lia) VS) as I1. cbv zeta in I1.
      destruct (mss_ins a1 _ _ _ _ _ _ i b) as [a11 b1]. cbn [fst snd] in I1. cps_destruct I1 as (V1 & F1 & B1).
      destruct (Z.ltb_spec hi (i + 1)) as [L2|L2]. { cbn [fst snd]. split; [exact V1|]. split; [exact F1|]. split; [lia|intros; discriminate]. }
      pose proof (mss_ins_facts a11 h lo hi (i + 1) b1 Hh ltac:(lia) V1) as I2. cbv zeta in I2.
      destruct (mss_ins a11 _ _ _ _ _ _ (i + 1) b1) as [a12 b2]. cbn [fst snd] in I2. cps_destruct I2 as (V2 & F2 & B2).
      destruct (Z.ltb_spec hi (i + 1 + 1)) as [L3|L3].
      { cbn [fst snd]. split; [exact V2|]. split; [intros x Hx; rewrite F2 by lia; apply F1; lia|]. split; [lia|intros; discriminate]. }
      pose proof (mss_ins_facts a12 h lo hi (i + 1 + 1) b2 Hh ltac:(lia) V2) as I3. cbv zeta in I3.
      destruct (mss_ins a12 _ _ _ _ _ _ (i + 1 + 1) b2) as [a13 b3]. cbn [fst snd] in I3. cps_destruct I3 as (V3 & F3 & B3).
      destruct (Z.ltb_spec b3 0) as [L4|L4].
      { cbn [fst snd]. split; [exact V3|]. split; [intros x Hx; rewrite F3, F2 by lia; apply F1; lia|]. split; [lia|intros; lia]. }
      specialize (IH a13 h lo hi (i + 1 + 1 + 1) b3 Hh ltac:(lia) V3). cbv zeta in IH. cps_destruct IH as (V4 & F4 & B4 & E4).
      split; [exact V4|]. split; [intros x Hx; rewrite F4, F3, F2 by lia; apply F1; lia|]. split; [lia|exact E4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mss_shift1_spec : forall f a1 lo hi j v b,
    (Z.to_nat (j - lo) < f)%nat -> lo + 1 <= j <= hi -> vals a1 lo hi -> VAL v ->
    let r := mss_shift f a1 a2 qoff n d 1 lo j v b in
    let a1' := fst (fst r) in let J := snd (fst r) in
    lo <= J <= j /\
    (forall x, J < x <= j -> rd32 a1' x = rd32 a1 (x - 1) /\ lexle (ROT v) (ROT (rd32 a1 (x - 1)))) /\
    (forall x, x <= J \/ j < x -> rd32 a1' x = rd32 a1 x) /\
    (J = lo \/ lexle (ROT (rd32 a1 (J - 1))) (ROT v)).
  Proof.
    induction f as [|f IH]; intros a1 lo hi j v b Hf Hj VS Vv; [lia|]. cbv zeta.
    rewrite mss_shift_S. pose proof (cmp_sound (rd32 a1 (j - 1)) v b (VS (j - 1) ltac:(lia)) Vv) as [CT CF].
    destruct (mainGtU _ _ _ _ _ _) as [gt b']. cbn [fst] in CT, CF. destruct gt.
    2:{ cbn [fst snd]. split; [lia|]. split; [intros; lia|]. split; [intros; reflexivity|]. right. apply CF. reflexivity. }
    cbv zeta. specialize (CT eq_refl). set (a1w := wr32 a1 j (rd32 a1 (j - 1))).
    assert (Ew : forall x, x <> j -> rd32 a1w x = rd32 a1 x) by (intros x Hx; subst a1w; apply rd32_wr32_other; lia).
    assert (Ej : rd32 a1w j = rd32 a1 (j - 1)) by (subst a1w; apply rd32_wr32_same; apply VAL_w32; apply VS; lia).
    replace (lo + 1 - 1) with lo by lia.
    destruct (Z.leb_spec (j - 1) lo) as [STOP|GO].
    - cbn [fst snd]. split; [lia|]. split.
      + intros x Hx. replace x with j by lia. split; [exact Ej|exact CT].
      + split; [intros x Hx; apply Ew; lia|]. left. lia.
    - assert (VSw : vals a1w lo hi).
      { intros x Hx. destruct (Z.eq_dec x j) as [->|N]; [rewrite Ej; apply VS; lia | rewrite Ew by lia; apply VS; lia]. }
      specialize (IH a1w lo hi (j - 1) v b' ltac:(lia) ltac:(lia) VSw Vv). cbv zeta in IH.
      destruct (mss_shift f a1w a2 qoff n d 1 lo (j - 1) v b') as [[a1' J] b'']. cbn [fst snd] in *.
      cps_destruct IH as (A & B & C & D). split; [lia|]. split.
      + intros x Hx. destruct (Z.eq_dec x j) as [->|N].
        * rewrite C by lia. split; [exact Ej|exact CT].
        * destruct (B x ltac:(lia)) as [B1 B2]. rewrite Ew in B1, B2 by lia. split; assumption.
      + split; [intros x Hx; rewrite C by lia; apply Ew; lia|].
        destruct D as [D|D]; [left; exact D|right]. rewrite Ew in D by lia. exact D.
  Qed.

  Lemma mss_ins1_sorted : forall a1 lo hi i b,
    lo + 1 <= i <= hi -> vals a1 lo hi -> msorted a1 lo (i - 1) -> msorted (fst (mss_ins a1 a2 qoff n d 1 lo i b)) lo i.
  Proof.
    intros a1 lo hi i b Hi VS SO. unfold mss_ins. pose proof (VS i ltac:(lia)) as Vv. set (v := rd32 a1 i) in *.
    pose proof (mss_shift1_spec (S (Z.to_nat (i - lo))) a1 lo hi i v b ltac:(lia) ltac:(lia) VS Vv) as SH. cbv zeta in SH.
    destruct (mss_shift _ a1 a2 qoff n d 1 lo i v b) as [[a1' J] b']. cbn [fst snd] in *.
    cps_destruct SH as (HJ & SHIFT & KEEP & STOP).
    set (r := wr32 a1' J v).
    assert (RJ : rd32 r J = v) by (subst r; apply rd32_wr32_same; apply VAL_w32; exact Vv).
    assert (RA : forall x, lo <= x < J -> rd32 r x = rd32 a1 x) by (intros x Hx; subst r; rewrite rd32_wr32_other by lia; apply KEEP; lia).
    assert (RC : forall x, J < x <= i -> rd32 r x = rd32 a1 (x - 1)) by (intros x Hx; subst r; rewrite rd32_wr32_other by lia; apply (proj1 (SHIFT x Hx))).
    intros x y Hx Hxy Hy.
    destruct (Z.lt_trichotomy x J) as [XA|[->|XC]]; destruct (Z.lt_trichotomy y J) as [YA|[->|YC]]; try lia.
    - rewrite !RA by lia. apply SO; lia.
    - rewrite RA, RJ by lia. destruct STOP as [E|LE]; [lia|]. eapply lexle_trans; [|exact LE]. apply SO; lia.
    - rewrite RA, RC by lia. apply SO; lia.
    - rewrite RJ. right; reflexivity.
    - rewrite RJ, RC by lia. apply (proj2 (SHIFT y ltac:(lia))).
    - rewrite !RC by lia. apply SO; lia.
  Qed.

  Lemma mss_hloop1_sorted : forall f a1 lo hi i b,
    hi + 1 - i <= 3 * Z.of_nat f -> lo + 1 <= i -> vals a1 lo hi -> msorted a1 lo (i - 1) ->
    let r := mss_hloop f a1 a2 qoff n d 1 lo hi i b in
    snd r = false -> msorted (fst (fst r)) lo hi.
  Proof.
    induction f as [|f IH]; intros a1 lo hi i b Hf Hi VS SO; cbv zeta; cbn [mss_hloop].
    - cbn [fst snd]. intros _. intros x y Hx Hxy Hy. apply SO; lia.
    - destruct (Z.ltb_spec hi i) as [L1|L1]. { cbn [fst snd]. intros _ x y Hx Hxy Hy. apply SO; lia. }
      pose proof (mss_ins_facts a1 1 lo hi i b ltac:(lia) ltac:(lia) VS) as I1. cbv zeta in I1.
      pose proof (mss_ins1_sorted a1 lo hi i b ltac:(lia) VS SO) as S1.
      destruct (mss_ins a1 _ _ _ _ _ _ i b) as [a11 b1]. cbn [fst snd] in I1, S1. cps_destruct I1 as (V1 & _ & _).
      destruct (Z.ltb_spec hi (i + 1)) as [L2|L2]. { cbn [fst snd]. intros _. replace hi with i by lia. exact S1. }
      pose proof (mss_ins_facts a11 1 lo hi (i + 1) b1 ltac:(lia) ltac:(lia) V1) as I2. cbv zeta in I2.
      pose proof (mss_ins1_sorted a11 lo hi (i + 1) b1 ltac:(lia) V1 ltac:(replace (i + 1 - 1) with i by lia; exact S1)) as S2.
      destruct (mss_ins a11 _ _ _ _ _ _ (i + 1) b1) as [a12 b2]. cbn [fst snd] in I2, S2. cps_destruct I2 as (V2 & _ & _).
      destruct (Z.ltb_spec hi (i + 1 + 1)) as [L3|L3]. { cbn [fst snd]. intros _. replace hi with (i + 1) by lia. exact S2. }
      pose proof (mss_ins_facts a12 1 lo hi (i + 1 + 1) b2 ltac:(lia) ltac:(lia) V2) as I3. cbv zeta in I3.
      pose proof (mss_ins1_sorted a12 lo hi (i + 1 + 1) b2 ltac:(lia) V2 ltac:(replace (i + 1 + 1 - 1) with (i + 1) by lia; exact S2)) as S3.
      destruct (mss_ins a12 _ _ _ _ _ _ (i + 1 + 1) b2) as [a13 b3]. cbn [fst snd] in I3, S3. cps_destruct I3 as (V3 & _ & _).
      destruct (Z.ltb_spec b3 0) as [L4|L4]; [cbn [snd]; intros; discriminate|].
      apply (IH a13 lo hi (i + 1 + 1 + 1) b3 ltac:(lia) ltac:(lia) V3). replace (i + 1 + 1 + 1 - 1) with (i + 1 + 1) by lia. exact S3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma incs_at_0 : incs_at 0 = 1. Proof. reflexivity. Qed.

  Lemma mss_hps_facts : forall k a1 lo hi hp b,
    lo <= hi -> 0 <= hp <= 12 -> hp = Z.of_nat k - 1 -> vals a1 lo hi ->
    let r := mss_hps k a1 a2 qoff n d lo hi hp b in
    vals (fst (fst r)) lo hi /\ (forall x, x < lo \/ hi < x -> rd32 (fst (fst r)) x = rd32 a1 x) /\
    snd (fst r) <= b /\ (snd r = true -> snd (fst r) < 0) /\ (snd r = false -> msorted (fst (fst r)) lo hi).
  Proof.
    induction k as [|k IH]; intros a1 lo hi hp b Hlh Hhp Hk VS; [lia|]. cbv zeta. cbn [mss_hps].
    pose proof (incs_pos hp ltac:(lia)) as HP.
    pose proof (mss_hloop_facts (S (Z.to_nat (hi - lo + 1))) a1 (incs_at hp) lo hi (lo + incs_at hp) b ltac:(lia) ltac:(lia) VS) as HL.
    cbv zeta in HL.
    assert (LAST : hp = 0 -> snd (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff n d (incs_at hp) lo hi (lo + incs_at hp) b) = false ->
                   msorted (fst (fst (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff n d (incs_at hp) lo hi (lo + incs_at hp) b))) lo hi).
    { intros E0. rewrite E0, incs_at_0. apply mss_hloop1_sorted; [lia|lia|exact VS|]. intros x y Hx Hxy Hy. replace y with x by lia. right; reflexivity. }
    destruct (mss_hloop _ _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex]. cbn [fst snd] in HL, LAST. cps_destruct HL as (V1 & F1 & B1 & E1).
    destruct ex.
    { cbn [fst snd]. split; [exact V1|]. split; [exact F1|]. split; [exact B1|]. split; [exact E1|intros; discriminate]. }
    destruct k as [|k'].
    - cbn [mss_hps fst snd]. split; [exact V1|]. split; [exact F1|]. split; [exact B1|]. split; [intros; discriminate|].
      intros _. apply LAST; [lia|reflexivity].
    - specialize (IH a1' lo hi (hp - 1) b' Hlh ltac:(lia) ltac:(lia) V1). cbv zeta in IH.
      destruct (mss_hps (S k') a1' a2 qoff n d lo hi (hp - 1) b') as [[a1'' b''] ex']. cbn [fst snd] in *.
      cps_destruct IH as (V2 & F2 & B2 & E2 & S2).
      split; [exact V2|]. split; [intros x Hx; rewrite F2 by lia; apply F1; lia|]. split; [lia|]. split; [exact E2|exact S2].
  Qed.

  Theorem mainSimpleSort_sorted : forall a1 lo hi b,
    hi - lo + 1 <= 2391484 -> vals a1 lo hi ->
    let r := mainSimpleSort a1 a2 qoff n lo hi d b in
    vals (fst r) lo hi /\ (forall x, x < lo \/ hi < x -> rd32 (fst r) x = rd32 a1 x) /\ snd r <= b /\
    (0 <= snd r -> msorted (fst r) lo hi).
  Proof.
    intros a1 lo hi b Hsz VS. cbv zeta. unfold mainSimpleSort.
    destruct (Z.ltb_spec (hi - lo + 1) 2) as [SM|BIG].
    { cbn [fst snd]. split; [exact VS|]. split; [intros; reflexivity|]. split; [lia|].
      intros _ x y Hx Hxy Hy. replace y with x by lia. right; reflexivity. }
    pose proof (mss_hp_run 15 (hi - lo + 1) 0 ltac:(lia) ltac:(rewrite incs_13; lia) ltac:(cbn; lia)) as HR. cbv zeta in HR.
    cps_destruct HR as (R1 & R2 & R3). set (hp := mss_hp 15 (hi - lo + 1) 0) in *.
    assert (HP1 : 1 <= hp). { destruct (Z.eq_dec hp 0) as [E|NE]; [|lia]. exfalso. rewrite E in R2. cbn in R2. lia. }
    pose proof (mss_hps_facts (Z.to_nat (hp - 1 + 1)) a1 lo hi (hp - 1) b ltac:(lia) ltac:(lia) ltac:(lia) VS) as HS. cbv zeta in HS.
    destruct (mss_hps _ _ _ _ _ _ _ _ _ _) as [[a1' b'] ex]. cbn [fst snd] in *.
    cps_destruct HS as (V & F & B & E & S). split; [exact V|]. split; [exact F|]. split; [exact B|].
    intros Hb. apply S. destruct ex; [|reflexivity]. specialize (E eq_refl). lia.
  Qed.
End S1.
