(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewE. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory BzR3aPre. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3gtu.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory BzR3aPre. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR3cOrd.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3gtu.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Section Ord.
  Variables (a2 : zarr) (nb : Z).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis N34 : 34 <= nb.

  Local Notation KEY := (key a2 nb).
  Local Notation NXT := (BzCPermM.nxt nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation PRV := (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB.prv nb).
  Local Notation BLK := (blk a2 nb).
  Local Notation ROT p := (rot (blk a2 nb) (Z.to_nat p)).

  Let n : nat := Z.to_nat nb.
  Lemma blk_len : length BLK = n. Proof. unfold n. rewrite blk_length. reflexivity. Qed.
  Let Hn0 : (0 < length BLK)%nat. Proof. rewrite blk_len. unfold n. lia. Qed.
  Lemma nbZ : Z.of_nat (length BLK) = nb. Proof. rewrite blk_len. unfold n. lia. Qed.

  (* [comment removed for export] *)
  Lemma ch_blk : forall p k, 0 <= p -> 0 <= k -> ch BLK p k = rd8 a2 ((p + k) mod nb).
  Proof.
    intros p k Hp Hk. unfold ch. rewrite nbZ. apply (blk_nth a2 nb N34). apply Z.mod_pos_bound. lia.
  Qed.

  Lemma nxt_mod : forall i, 0 <= i < nb -> NXT i = (i + 1) mod nb.
  Proof.
    intros i Hi. unfold BzCPermM.nxt. destruct (Z.eqb_spec i (nb - 1)) as [->|N].
    - replace (nb - 1 + 1) with nb by lia. rewrite Z.mod_same by lia. reflexivity.
    - rewrite Z.mod_small; lia.
  Qed.

  Lemma rot_pre : forall p, 0 <= p < nb -> ROT p = pre BLK n p.
  Proof. intros p Hp. symmetry. rewrite <- blk_len. apply pre_n_rot; [exact Hn0|]. rewrite nbZ. exact Hp. Qed.

  (* [comment removed for export] *)
  Lemma pre2_key : forall p, 0 <= p < nb -> pre BLK 2 p = [rd8 a2 p; rd8 a2 (NXT p)].
  Proof.
    intros p Hp. unfold pre. cbn [seq map]. rewrite !ch_blk by lia. rewrite Z.add_0_r, Z.mod_small by lia.
    rewrite nxt_mod by lia. reflexivity.
  Qed.

  Lemma key_lt_rot : forall k k', 0 <= k < nb -> 0 <= k' < nb -> KEY k < KEY k' -> lexlt (ROT k) (ROT k').
  Proof.
    intros k k' Hk Hk' L.
    assert (P2 : lexlt (pre BLK 2 k) (pre BLK 2 k')).
    { rewrite !pre2_key by assumption. unfold key, BzCPermM.key in L.
      pose proof (BB k). pose proof (BB k'). pose proof (BB (NXT k)). pose proof (BB (NXT k')).
      cbn. destruct (Z.lt_ge_cases (rd8 a2 k) (rd8 a2 k')) as [A|A]; [left; exact A|]. right. split; [lia|]. left. lia. }
    rewrite !rot_pre by assumption.
    destruct (Nat.le_gt_cases 2 n) as [Hn2|Hn2].
    - apply (pre_lt_ext BLK Hn0 2); [exact Hn2|exact P2].
    - (* [comment removed for export] *) exfalso. assert (k = k') by (unfold n in Hn2; lia). subst k'. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rot_prv_nxt : forall k, 0 <= k < nb -> ROT k = rotr (ROT (NXT k)).
  Proof.
    intros k Hk. rewrite <- (rot_prv BLK Hn0 (Z.to_nat (NXT k))).
    - f_equal. unfold BzR2Theory.prv. rewrite blk_len. unfold BzCPermM.nxt, n.
      destruct (Z.eqb_spec k (nb - 1)) as [->|N].
      + cbn. lia.
      + destruct (Nat.eqb_spec (Z.to_nat (k + 1)) 0); lia.
    - rewrite blk_len. unfold n. pose proof (nxt_range nb NB k Hk). lia.
  Qed.

  Lemma last_rot_nxt : forall k, 0 <= k < nb -> last (ROT (NXT k)) 0 = rd8 a2 k.
  Proof.
    intros k Hk. pose proof (nxt_range nb NB k Hk) as R1.
    rewrite rot_last by (rewrite blk_len; unfold n; lia).
    replace (BzR2Theory.prv BLK (Z.to_nat (NXT k))) with (Z.to_nat k).
    - apply (blk_nth a2 nb N34). exact Hk.
    - unfold BzR2Theory.prv. rewrite blk_len. unfold BzCPermM.nxt, n.
      destruct (Z.eqb_spec k (nb - 1)) as [->|N]; [cbn; lia|]. destruct (Nat.eqb_spec (Z.to_nat (k + 1)) 0); lia.
  Qed.

  Lemma succ_le_rot : forall k k', 0 <= k < nb -> 0 <= k' < nb -> rd8 a2 k = rd8 a2 k' ->
    lexle (ROT (NXT k)) (ROT (NXT k')) -> lexle (ROT k) (ROT k').
  Proof.
    intros k k' Hk Hk' EB L. pose proof (nxt_range nb NB k Hk) as R1. pose proof (nxt_range nb NB k' Hk') as R2.
    rewrite (rot_prv_nxt k), (rot_prv_nxt k') by assumption.
    assert (LEN : length (ROT (NXT k)) = length (ROT (NXT k'))) by (rewrite !rot_length; rewrite ?blk_len; unfold n; lia).
    assert (LAST : last (ROT (NXT k)) 0 = last (ROT (NXT k')) 0) by (rewrite !last_rot_nxt by assumption; exact EB).
    assert (NN : ROT (NXT k) <> []) by (apply rot_nonnil; rewrite blk_len; unfold n; lia).
    destruct L as [L|E].
    - left. apply (proj1 (lexlt_rotr BLK Hn0 _ _ LEN NN LAST)). exact L.
    - right. rewrite E. reflexivity.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section SideOrd.
    Variable ss : Z.
    Hypothesis SS : 0 <= ss < 256.
    Local Notation SD := (SIDE a2 nb ss).

    Lemma side_spec : forall f u b, 0 <= u < nb -> side a2 nb ss f u = Some b ->
      exists m, (1 <= m <= f)%nat /\ (forall i, (1 <= i < m)%nat -> rd8 a2 ((u + Z.of_nat i) mod nb) = ss) /\
                rd8 a2 ((u + Z.of_nat m) mod nb) <> ss /\ b = (rd8 a2 ((u + Z.of_nat m) mod nb) <? ss).
    Proof.
      induction f as [|f IH]; intros u b Hu H; [discriminate|].
      rewrite side_S in H. rewrite nxt_mod in H by exact Hu.
      destruct (Z.eqb_spec (rd8 a2 ((u + 1) mod nb)) ss) as [E|NE].
      - cps_destruct (IH ((u + 1) mod nb) b ltac:(apply Z.mod_pos_bound; lia) H) as (m & Hm & ALL & LAST & Hb).
        exists (S m). split; [lia|].
        assert (SH : forall i : nat, ((u + 1) mod nb + Z.of_nat i) mod nb = (u + Z.of_nat (S i)) mod nb).
        { intros i. rewrite Zplus_mod_idemp_l. f_equal. lia. }
        split.
        + intros i Hi. destruct i as [|i]; [lia|]. destruct i as [|i'].
          * replace (Z.of_nat 1) with 1 by lia. exact E.
          * rewrite <- SH. apply ALL. lia.
        + rewrite <- !SH. split; [exact LAST|exact Hb].
      - exists 1%nat. replace (Z.of_nat 1) with 1 by lia. split; [lia|]. split; [intros; lia|].
        split; [exact NE|]. injection H as <-. reflexivity.
    Qed.

    Theorem side_lt_rot : forall k k', 0 <= k < nb -> 0 <= k' < nb -> rd8 a2 k = rd8 a2 k' ->
      SD k = Some true -> SD k' = Some false -> lexlt (ROT k) (ROT k').
    Proof.
      intros k k' Hk Hk' EB S1 S2. unfold SIDE in S1, S2.
      cps_destruct (side_spec _ _ _ Hk S1) as (m & Hm & A1 & L1 & B1).
      cps_destruct (side_spec _ _ _ Hk' S2) as (m' & Hm' & A2 & L2 & B2).
      symmetry in B1. apply Z.ltb_lt in B1. symmetry in B2. apply Z.ltb_ge in B2.
      set (e := Nat.min m m').
      assert (He : (1 <= e)%nat /\ (e <= m)%nat /\ (e <= m')%nat) by (subst e; lia).
      (* [comment removed for export] *)
      assert (EQe : pre BLK e k = pre BLK e k').
      { unfold pre. apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite !ch_blk by lia.
        destruct (Nat.eq_dec i 0) as [->|NZ].
        - replace (Z.of_nat 0) with 0 by lia. rewrite !Z.add_0_r, !Z.mod_small by lia. exact EB.
        - rewrite (A1 i), (A2 i) by lia. reflexivity. }
      assert (LT : rd8 a2 ((k + Z.of_nat e) mod nb) < rd8 a2 ((k' + Z.of_nat e) mod nb)).
      { destruct (Nat.lt_trichotomy m m') as [C|[C|C]].
        - assert (e = m) by (subst e; lia). rewrite H. rewrite (A2 m) by lia. exact B1.
        - assert (e = m) by (subst e; lia). rewrite H. rewrite <- C in B2. lia.
        - assert (e = m') by (subst e; lia). rewrite H. rewrite (A1 m') by lia. lia. }
      assert (En : (e < n)%nat).
      { destruct (Nat.lt_ge_cases e n) as [X|X]; [exact X|exfalso].
        (* [comment removed for export] *)
        assert (ALLEQ : forall i : nat, (i < n)%nat -> rd8 a2 ((k + Z.of_nat i) mod nb) = rd8 a2 ((k' + Z.of_nat i) mod nb)).
        { intros i Hi. destruct (Nat.eq_dec i 0) as [->|NZ].
          - replace (Z.of_nat 0) with 0 by lia. rewrite !Z.add_0_r, !Z.mod_small by lia. exact EB.
          - rewrite (A1 i), (A2 i) by lia. reflexivity. }
        (* [comment removed for export] *)
        assert (PER : forall z, 0 <= z -> rd8 a2 ((k + z) mod nb) = rd8 a2 ((k' + z) mod nb)).
        { intros z Hz. rewrite <- (Z.mod_mod (k + z) nb), <- (Z.mod_mod (k' + z) nb) by lia.
          rewrite <- (Zplus_mod_idemp_r z k nb), <- (Zplus_mod_idemp_r z k' nb).
          pose proof (Z.mod_pos_bound z nb ltac:(lia)) as R.
          specialize (ALLEQ (Z.to_nat (z mod nb)) ltac:(unfold n; lia)). rewrite Z2Nat.id in ALLEQ by lia.
          rewrite !Z.mod_mod by lia. exact ALLEQ. }
        pose proof (PER (Z.of_nat e) ltac:(lia)). lia. }
      rewrite (rot_pre k), (rot_pre k') by assumption.
      set (r := (n - e - 1)%nat).
      replace n with (e + S r)%nat by (subst r; lia).
      rewrite (pre_app BLK Hn0 e (S r) k), (pre_app BLK Hn0 e (S r) k').
      apply lexlt_app; [rewrite (pre_length BLK e k), (pre_length BLK e k'); reflexivity|]. right. split; [exact EQe|].
      change (S r) with (1 + r)%nat. rewrite (pre_app BLK Hn0 1 r (k + Z.of_nat e)), (pre_app BLK Hn0 1 r (k' + Z.of_nat e)).
      rewrite (pre_1 BLK (k + Z.of_nat e)), (pre_1 BLK (k' + Z.of_nat e)). cbn [app]. cbn [lexlt]. left.
      rewrite (ch_blk (k + Z.of_nat e) 0), (ch_blk (k' + Z.of_nat e) 0) by lia. rewrite !Z.add_0_r. exact LT.
    Qed.
  End SideOrd.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SB (a : zarr) (v : Z) : Prop :=
    forall p p', CLM v <= p -> p <= p' -> p' < CLM (v + 1) -> lexle (ROT (rd32 a p)) (ROT (rd32 a p')).

  Lemma SB_ext : forall a a' v, SB a v -> (forall p, CLM v <= p < CLM (v + 1) -> rd32 a' p = rd32 a p) -> SB a' v.
  Proof. intros a a' v S E p p' A B C. rewrite !E by lia. apply S; assumption. Qed.

  Lemma SB_small : forall a v, CLM (v + 1) <= CLM v + 1 -> SB a v.
  Proof. intros a v H p p' A B C. assert (p = p') by lia. subst. right; reflexivity. Qed.

  Theorem sorted_of_buckets : forall a, PINV a2 nb a -> (forall v, 0 <= v < 65536 -> SB a v) ->
    forall i j, 0 <= i -> i <= j -> j < nb -> lexle (ROT (rd32 a i)) (ROT (rd32 a j)).
  Proof.
    intros a PV SBS i j Hi Hij Hj.
    cps_destruct (bucket_of a2 nb BB NB i ltac:(lia)) as (v & Hv & Ri). cps_destruct (bucket_of a2 nb BB NB j ltac:(lia)) as (w & Hw & Rj).
    destruct (Z.eq_dec v w) as [->|NE]; [apply (SBS w Hw); lia|].
    destruct (PV v Hv) as [Vv _]. destruct (PV w Hw) as [Vw _].
    destruct (Vv i Ri) as [R1 K1]. destruct (Vw j Rj) as [R2 K2].
    assert (v < w). { destruct (Z.lt_ge_cases v w) as [|G]; [assumption|]. exfalso. pose proof (ClM_mono a2 nb (w + 1) v ltac:(lia)). lia. }
    left. apply key_lt_rot; [exact R1|exact R2|]. rewrite K1, K2. exact H.
  Qed.
End Ord.
End BzR3cOrd.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3gtu OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3cSew.BzR3cOrd.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section Sew.
  Variables (a2 : zarr) (nb ss : Z) (bd P0 : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis N34 : 34 <= nb.
  Hypothesis SS : 0 <= ss < 256.
  Hypothesis BD : zget bd ss = 0.
  Hypothesis P0X : PINV a2 nb P0.
  Hypothesis NA : NALL a2 nb ss.
  Variable a2r : zarr.
  Hypothesis AGR : forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k.
  (* [comment removed for export] *)
  Hypothesis HSB : forall c, 0 <= c < 256 -> c <> ss -> SB a2 nb P0 (256 * ss + c).

  Local Notation KEY := (key a2 nb).
  Local Notation NXT := (BzCPermM.nxt nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation PRV := (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB.prv nb).
  Local Notation SD := (SIDE a2 nb ss).
  Local Notation cs0 := (cs0 a2 nb ss).
  Local Notation ce1 := (ce1 a2 nb ss).
  Local Notation csF := (csF a2 nb ss).
  Local Notation ceB := (ceB a2 nb ss).
  Local Notation B0 := (B0 a2 nb ss).
  Local Notation B1 := (B1 a2 nb ss).
  Local Notation ROT p := (rot (blk a2 nb) (Z.to_nat p)).
  Local Notation LE x y := (lexle (rot (blk a2 nb) (Z.to_nat x)) (rot (blk a2 nb) (Z.to_nat y))).

  (* [comment removed for export] *)
  Lemma key_c_first : forall k c, 0 <= c < 256 -> KEY k = 256 * c + ss -> rd8 a2 k = c.
  Proof. intros k c Hc K. exact (proj1 (proj1 (key_chars a2 nb BB k c ss SS) K)). Qed.

  (* [comment removed for export] *)
  Lemma P0_big_le : forall p p' c c', 0 <= c < 256 -> 0 <= c' < 256 -> c <> ss -> c' <> ss ->
    CLM (256 * ss + c) <= p < CLM (256 * ss + c + 1) -> CLM (256 * ss + c') <= p' < CLM (256 * ss + c' + 1) ->
    p <= p' -> LE (rd32 P0 p) (rd32 P0 p').
  Proof.
    intros p p' c c' Hc Hc' Nc Nc' Rp Rp' LEp.
    destruct (P0X (256 * ss + c) ltac:(nia)) as [V _]. destruct (P0X (256 * ss + c') ltac:(nia)) as [V' _].
    destruct (V p Rp) as [R1 K1]. destruct (V' p' Rp') as [R2 K2].
    destruct (Z.lt_trichotomy c c') as [L|[->|G]].
    - left. apply (key_lt_rot a2 nb BB NB N34); [exact R1|exact R2|lia].
    - apply (HSB c' Hc' Nc'); lia.
    - exfalso. pose proof (ClM_mono a2 nb (256 * ss + c' + 1) (256 * ss + c) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FWO (a1 cs : zarr) : Prop :=
    forall c, 0 <= c < 256 -> zget bd c = 0 ->
    forall q q', cs0 c <= q -> q <= q' -> q' < zget cs c -> LE (rd32 a1 q) (rd32 a1 q').

  (* [comment removed for export] *)
  Lemma fwo_scan_le : forall a1 cs j, FWI a2 nb ss bd P0 a1 cs j -> FWO a1 cs ->
    forall p p', B0 <= p -> p <= p' -> p' < zget cs ss -> LE (rd32 a1 p) (rd32 a1 p').
  Proof.
    intros a1 cs j IV FO p p' Hp Hpp Hp'.
    assert (SEEDv : forall x, B0 <= x < cs0 ss -> rd32 a1 x = rd32 P0 x).
    { intros x Hx. apply (fw3 _ _ _ _ _ _ _ _ IV). intros c Hc Bc R.
      apply (seed_no_reg a2 nb ss BB NB SS c x Hc Hx). exact (fw_reg a2 nb ss bd P0 BB NB SS NA a1 cs j IV c x Hc Bc R). }
    destruct (Z.lt_ge_cases p' (cs0 ss)) as [A|A].
    - (* [comment removed for export] *)
      rewrite !SEEDv by lia.
      cps_destruct (seed_bucket a2 nb ss BB NB p ltac:(lia)) as (c & Hc & R). cps_destruct (seed_bucket a2 nb ss BB NB p' ltac:(lia)) as (c' & Hc' & R').
      apply (P0_big_le p p' c c'); lia || assumption.
    - destruct (Z.lt_ge_cases p (cs0 ss)) as [B|B].
      + (* [comment removed for export] *)
        rewrite (SEEDv p) by lia.
        cps_destruct (seed_val a2 nb ss P0 BB NB SS P0X p ltac:(lia)) as (R1 & E1 & E2 & _).
        cps_destruct (proj1 (fw4 _ _ _ _ _ _ _ _ IV ss p' SS BD ltac:(lia))) as (R2 & K2 & _).
        left. apply (key_lt_rot a2 nb BB NB N34); [exact R1|exact R2|].
        rewrite K2. rewrite (key_split a2 nb), E1. lia.
      + apply (FO ss SS BD); lia.
  Qed.

  Lemma FWO_init : forall cs, (forall c, 0 <= c < 256 -> zget cs c = cs0 c) -> FWO P0 cs.
  Proof. intros cs H c Hc Bc q q' A B C. rewrite H in C by exact Hc. lia. Qed.

  Lemma FWO_step : forall a1 cs j, FWI a2 nb ss bd P0 a1 cs j -> FWO a1 cs -> j < zget cs ss ->
    let k := PRV (rd32 a1 j) in let c1 := rd8 a2 k in
    zget bd c1 = 0 -> FWO (wr32 a1 (zget cs c1) k) (zset cs c1 (zget cs c1 + 1)).
  Proof.
    intros a1 cs j IV FO LT. cbv zeta. intros B1z.
    pose proof (FWI_step a2 nb ss bd P0 BB NB SS BD P0X NA a1 cs j IV LT) as ST. cbv zeta in ST.
    cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & _). destruct (CASE0 B1z) as [RNG _].
    set (k := PRV (rd32 a1 j)) in *. set (c1 := rd8 a2 k) in *.
    intros c Hc Bc q q' Hq Hqq Hq'. rewrite zget_zset in Hq'.
    assert (W : forall x, x <> zget cs c1 -> rd32 (wr32 a1 (zget cs c1) k) x = rd32 a1 x) by (intros; apply rd32_wr32_other; assumption).
    destruct (Z.eqb_spec c c1) as [->|NE].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec q' (zget cs c1)) as [->|NQ'].
      + rewrite rd32_wr32_same by lia.
        destruct (Z.eq_dec q (zget cs c1)) as [->|NQ]; [rewrite rd32_wr32_same by lia; right; reflexivity|].
        rewrite W by lia.
        (* [comment removed for export] *)
        destruct (fw4 _ _ _ _ _ _ _ _ IV c1 q Rc B1z ltac:(lia)) as [(Rq & Kq & _) (p' & Hp' & Ep')].
        apply (succ_le_rot a2 nb NB N34); [exact Rq|exact Rk| |].
        * rewrite (key_c_first _ c1 Rc Kq). symmetry. subst c1. reflexivity.
        * rewrite <- Ep'. subst k. rewrite (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB.nxt_prv nb) by exact Ru.
          pose proof (fw1 _ _ _ _ _ _ _ _ IV). apply (fwo_scan_le a1 cs j IV FO); lia.
      + rewrite !W by lia. apply (FO c1 Rc B1z); lia.
    - replace (c =? c1) with false in Hq' by (symmetry; apply Z.eqb_neq; exact NE).
      assert (D : forall x, cs0 c <= x < zget cs c -> x <> zget cs c1).
      { intros x Hx E. pose proof (fw_reg a2 nb ss bd P0 BB NB SS NA a1 cs j IV c x Hc Bc Hx) as R1.
        apply (reg_disjoint a2 nb ss c c1 x NE R1). rewrite E. exact RNG. }
      rewrite !W by (apply D; lia). apply (FO c Hc Bc); lia.
  Qed.

  Lemma FWO_loop : forall f a1 cs j, FWI a2 nb ss bd P0 a1 cs j -> FWO a1 cs -> nb - j < Z.of_nat f ->
    let r := ms_copy_fwd f a1 cs a2r bd nb ss j in FWO (fst (fst r)) (snd (fst r)).
  Proof.
    induction f as [|f IH]; intros a1 cs j IV FO Hf; cbv zeta.
    - cbn [ms_copy_fwd fst snd]. exact FO.
    - rewrite ms_copy_fwd_S. destruct (Z.ltb_spec j (zget cs ss)) as [LT|GE]; [|cbn [fst snd]; exact FO].
      pose proof (FWI_step a2 nb ss bd P0 BB NB SS BD P0X NA a1 cs j IV LT) as ST. cbv zeta in ST.
      cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
      cbv zeta. rewrite (prv_model' nb NB (rd32 a1 j) Ru). rewrite (AGR (PRV (rd32 a1 j)) Rk).
      destruct (Z.eqb_spec (zget bd (rd8 a2 (PRV (rd32 a1 j)))) 0) as [Bz|Bnz].
      + destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j + 1) IV'); [|lia]. apply (FWO_step a1 cs j IV FO LT Bz).
      + apply (IH a1 cs (j + 1) (CASE1 Bnz) FO). lia.
  Qed.

  Theorem forward_order : forall cs, (forall c, 0 <= c < 256 -> zget cs c = cs0 c) ->
    let r := ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0 in FWO (fst (fst r)) (snd (fst r)).
  Proof.
    intros cs Hcs. apply FWO_loop; [apply (FWI_init a2 nb ss bd P0 SS); exact Hcs | apply FWO_init; exact Hcs |].
    pose proof (B0_ge_0 a2 nb ss NB). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Bw.
    Variables (A0 csA : zarr).
    Hypothesis FW : FWPOST a2 nb ss bd P0 A0 csA.

    Definition BWO (a1 ce : zarr) : Prop :=
      forall c, 0 <= c < 256 -> zget bd c = 0 ->
      forall q q', zget ce c < q -> q <= q' -> q' < ce1 c -> LE (rd32 a1 q) (rd32 a1 q').

    Lemma bwo_scan_le : forall a1 ce j, BWI a2 nb ss bd A0 a1 ce j -> BWO a1 ce ->
      forall p p', zget ce ss < p -> p <= p' -> p' < B1 -> LE (rd32 a1 p) (rd32 a1 p').
    Proof.
      intros a1 ce j IV BO p p' Hp Hpp Hp'.
      pose proof (csF_le_ce1 a2 nb ss BB NB SS NA ss SS) as CF. pose proof (proj2 (proj2 (bw0 _ _ _ _ _ _ _ _ IV ss SS)) BD) as CE.
      assert (TAILv : forall x, ce1 ss <= x < B1 -> rd32 a1 x = rd32 P0 x).
      { intros x Hx. rewrite (bw3 _ _ _ _ _ _ _ _ IV).
        - apply (A0_tail a2 nb ss bd P0 A0 csA BB NB SS NA FW). exact Hx.
        - intros c Hc Bc R. apply (tail_no_reg a2 nb ss BB NB SS c x Hc Hx).
          pose proof (proj1 (bw0 _ _ _ _ _ _ _ _ IV c Hc)). pose proof (cs0_le_ce1 a2 nb ss c).
          pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc). pose proof (proj2 (proj2 (bw0 _ _ _ _ _ _ _ _ IV c Hc)) Bc). lia. }
      destruct (Z.le_gt_cases (ce1 ss) p) as [A|A].
      - (* [comment removed for export] *)
        rewrite !TAILv by lia.
        cps_destruct (tail_bucket a2 nb ss BB NB SS p ltac:(lia)) as (c & Hc & R). cps_destruct (tail_bucket a2 nb ss BB NB SS p' ltac:(lia)) as (c' & Hc' & R').
        apply (P0_big_le p p' c c'); lia || assumption.
      - destruct (Z.le_gt_cases (ce1 ss) p') as [B|B].
        + (* [comment removed for export] *)
          rewrite (TAILv p') by lia.
          cps_destruct (tail_val a2 nb ss P0 BB NB SS P0X p' ltac:(lia)) as (R1 & E1 & E2 & _).
          cps_destruct (proj1 (bw4 _ _ _ _ _ _ _ _ IV ss p SS BD ltac:(lia))) as (R2 & K2 & _).
          left. apply (key_lt_rot a2 nb BB NB N34); [exact R2|exact R1|].
          rewrite K2. rewrite (key_split a2 nb (rd32 P0 p')), E1. lia.
        + apply (BO ss SS BD); lia.
    Qed.

    Lemma BWO_init : forall ce, (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) -> BWO A0 ce.
    Proof. intros ce H c Hc Bc q q' A B C. rewrite H in A by exact Hc. lia. Qed.

    Lemma BWO_step : forall a1 ce j, BWI a2 nb ss bd A0 a1 ce j -> BWO a1 ce -> zget ce ss < j ->
      let k := PRV (rd32 a1 j) in let c1 := rd8 a2 k in
      zget bd c1 = 0 -> BWO (wr32 a1 (zget ce c1) k) (zset ce c1 (zget ce c1 - 1)).
    Proof.
      intros a1 ce j IV BO LT. cbv zeta. intros B1z.
      pose proof (BWI_step a2 nb ss bd P0 A0 csA BB NB SS BD P0X NA FW a1 ce j IV LT) as ST. cbv zeta in ST.
      cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & _). destruct (CASE0 B1z) as [RNG _].
      set (k := PRV (rd32 a1 j)) in *. set (c1 := rd8 a2 k) in *.
      intros c Hc Bc q q' Hq Hqq Hq'. rewrite zget_zset in Hq.
      assert (W : forall x, x <> zget ce c1 -> rd32 (wr32 a1 (zget ce c1) k) x = rd32 a1 x) by (intros; apply rd32_wr32_other; assumption).
      destruct (Z.eqb_spec c c1) as [->|NE].
      - destruct (Z.eq_dec q (zget ce c1)) as [->|NQ].
        + rewrite rd32_wr32_same by lia.
          destruct (Z.eq_dec q' (zget ce c1)) as [->|NQ']; [rewrite rd32_wr32_same by lia; right; reflexivity|].
          rewrite W by lia.
          destruct (bw4 _ _ _ _ _ _ _ _ IV c1 q' Rc B1z ltac:(lia)) as [(Rq & Kq & _) (p' & Hp' & Ep')].
          apply (succ_le_rot a2 nb NB N34); [exact Rk|exact Rq| |].
          * rewrite (key_c_first _ c1 Rc Kq). subst c1. reflexivity.
          * rewrite <- Ep'. subst k. rewrite (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB.nxt_prv nb) by exact Ru.
            apply (bwo_scan_le a1 ce j IV BO); lia.
        + rewrite !W by lia. apply (BO c1 Rc B1z); lia.
      - replace (c =? c1) with false in Hq by (symmetry; apply Z.eqb_neq; exact NE).
        assert (D : forall x, zget ce c < x < ce1 c -> x <> zget ce c1).
        { intros x Hx E. pose proof (proj1 (bw0 _ _ _ _ _ _ _ _ IV c Hc)). pose proof (cs0_le_ce1 a2 nb ss c).
          pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc). pose proof (proj2 (proj2 (bw0 _ _ _ _ _ _ _ _ IV c Hc)) Bc).
          pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c1 Rc).
          apply (reg_disjoint a2 nb ss c c1 x NE ltac:(lia)). rewrite E. lia. }
        rewrite !W by (apply D; lia). apply (BO c Hc Bc); lia.
    Qed.

    Lemma BWO_loop : forall f a1 ce j, BWI a2 nb ss bd A0 a1 ce j -> BWO a1 ce -> j + 1 < Z.of_nat f ->
      let r := ms_copy_bwd f a1 ce a2r bd nb ss j in BWO (fst (fst r)) (snd (fst r)).
    Proof.
      induction f as [|f IH]; intros a1 ce j IV BO Hf; cbv zeta.
      - cbn [ms_copy_bwd fst snd]. exact BO.
      - rewrite ms_copy_bwd_S. destruct (Z.ltb_spec (zget ce ss) j) as [LT|GE]; [|cbn [fst snd]; exact BO].
        pose proof (BWI_step a2 nb ss bd P0 A0 csA BB NB SS BD P0X NA FW a1 ce j IV LT) as ST. cbv zeta in ST.
        cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
        cbv zeta. rewrite (prv_model' nb NB (rd32 a1 j) Ru). rewrite (AGR (PRV (rd32 a1 j)) Rk).
        destruct (Z.eqb_spec (zget bd (rd8 a2 (PRV (rd32 a1 j)))) 0) as [Bz|Bnz].
        + destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j - 1) IV'); [|lia]. apply (BWO_step a1 ce j IV BO LT Bz).
        + apply (IH a1 ce (j - 1) (CASE1 Bnz) BO). lia.
    Qed.

    Theorem backward_order : forall ce, (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) ->
      let r := ms_copy_bwd (S (Z.to_nat nb)) A0 ce a2r bd nb ss (B1 - 1) in BWO (fst (fst r)) (snd (fst r)).
    Proof.
      intros ce Hce. apply BWO_loop; [apply (BWI_init a2 nb ss bd A0 BB NB SS NA); exact Hce | apply BWO_init; exact Hce |].
      pose proof (B1_le_nb a2 nb ss NB). lia.
    Qed.
  End Bw.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem step2_sorted : forall cs ce,
    (forall c, 0 <= c < 256 -> zget cs c = cs0 c) -> (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) ->
    (forall c, 0 <= c < 256 -> zget bd c <> 0 -> SB a2 nb P0 (256 * c + ss)) ->
    let rf := ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0 in
    let rb := ms_copy_bwd (S (Z.to_nat nb)) (fst (fst rf)) ce a2r bd nb ss (B1 - 1) in
    forall c, 0 <= c < 256 -> SB a2 nb (fst (fst rb)) (256 * c + ss).
  Proof.
    intros cs ce Hcs Hce DONE. cbv zeta.
    pose proof (forward_scan a2 nb ss bd P0 BB NB SS BD P0X NA a2r AGR cs Hcs) as FS. cbv zeta in FS. destruct FS as [FW _].
    pose proof (forward_order cs Hcs) as FO. cbv zeta in FO.
    set (A0 := fst (fst (ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0))) in *.
    set (csA := snd (fst (ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0))) in *.
    assert (FWS : forall c, 0 <= c < 256 -> zget bd c = 0 -> forall q q', cs0 c <= q -> q <= q' -> q' < csF c -> LE (rd32 A0 q) (rd32 A0 q')).
    { intros c Hc Bc q q' A B C. apply (FO c Hc Bc); try lia. rewrite (fp_cs _ _ _ _ _ _ _ FW c Hc), Bc. cbn. exact C. }
    pose proof (backward_scan a2 nb ss bd P0 A0 csA BB NB SS BD P0X NA a2r AGR FW ce Hce) as BS. cbv zeta in BS. destruct BS as [BW _].
    pose proof (backward_order A0 csA FW ce Hce) as BO. cbv zeta in BO.
    set (a1 := fst (fst (ms_copy_bwd (S (Z.to_nat nb)) A0 ce a2r bd nb ss (B1 - 1)))) in *.
    set (ceE := snd (fst (ms_copy_bwd (S (Z.to_nat nb)) A0 ce a2r bd nb ss (B1 - 1)))) in *.
    intros c Hc p p' Hp Hpp Hp'.
    change (CLM (256 * c + ss)) with (cs0 c) in Hp. change (CLM (256 * c + ss + 1)) with (ce1 c) in Hp'.
    destruct (Z.eq_dec (zget bd c) 0) as [Bc|Bc].
    - pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc) as CF.
      pose proof (bp_meet _ _ _ _ _ _ _ BW c Hc Bc) as MEET. pose proof (bp_ce _ _ _ _ _ _ _ BW c Hc) as CE. rewrite Bc in CE. cbn in CE.
      assert (FWD : forall x, cs0 c <= x < csF c -> rd32 a1 x = rd32 A0 x).
      { intros x Hx. apply (bp_frame _ _ _ _ _ _ _ BW). intros c' Hc' Bc' R.
        destruct (Z.eq_dec c' c) as [->|NE]; [rewrite MEET in R; lia|].
        pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c' Hc'). pose proof (cs0_le_ce1 a2 nb ss c'). pose proof (bp_meet _ _ _ _ _ _ _ BW c' Hc' Bc').
        apply (reg_disjoint a2 nb ss c c' x ltac:(congruence) ltac:(lia)). lia. }
      destruct (Z.lt_ge_cases p' (csF c)) as [A|A].
      + rewrite !FWD by lia. apply (FWS c Hc Bc); lia.
      + destruct (Z.lt_ge_cases p (csF c)) as [B|B].
        * (* [comment removed for export] *)
          rewrite (FWD p) by lia.
          pose proof (fp_in _ _ _ _ _ _ _ FW c p Hc Bc ltac:(rewrite <- ?MEET; lia)) as INF.
          pose proof (bp_in _ _ _ _ _ _ _ BW c p' Hc Bc ltac:(rewrite MEET; lia)) as INB.
          apply (in_Fset a2 nb ss NB SS) in INF. apply (in_Fset a2 nb ss NB SS) in INB.
          cps_destruct INF as (R1 & K1 & S1). cps_destruct INB as (R2 & K2 & S2).
          left. apply (side_lt_rot a2 nb NB N34 ss); try assumption.
          rewrite (key_c_first _ c Hc K1), (key_c_first _ c Hc K2). reflexivity.
        * apply (BO c Hc Bc); rewrite ?CE, ?MEET; lia.
    - (* [comment removed for export] *)
      assert (UN : forall x, cs0 c <= x < ce1 c -> rd32 a1 x = rd32 P0 x).
      { intros x Hx. rewrite (bp_frame _ _ _ _ _ _ _ BW).
        - apply (fp_frame _ _ _ _ _ _ _ FW). intros c' Hc' Bc' R. pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c' Hc').
          apply (reg_disjoint a2 nb ss c c' x ltac:(congruence) Hx). lia.
        - intros c' Hc' Bc' R. pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c' Hc'). pose proof (bp_meet _ _ _ _ _ _ _ BW c' Hc' Bc').
          pose proof (cs0_le_ce1 a2 nb ss c').
          apply (reg_disjoint a2 nb ss c c' x ltac:(congruence) Hx). lia. }
      rewrite !UN by lia. apply (DONE c Hc Bc); unfold BzCSewC.cs0, BzCSewC.ce1 in *; lia.
  Qed.
End Sew.
