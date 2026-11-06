(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR5cS.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR4m.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Definition MV (a mb : zarr) (k : Z) : Z := zget a (zget mb (k / 16) + k mod 16).
Definition MINV (mb : zarr) : Prop :=
  1 <= zget mb 0 /\ (forall l, 0 <= l < 15 -> zget mb l + 16 <= zget mb (l + 1)) /\ zget mb 15 <= 4080.

Lemma MINV_chain : forall mb, MINV mb -> forall n l0, 0 <= l0 -> l0 + Z.of_nat n <= 15 -> zget mb l0 + 16 * Z.of_nat n <= zget mb (l0 + Z.of_nat n).
Proof.
  (intros mb; cps_intros (A & B & C)). induction n as [|n IH]; intros l0 H0 Hn.
  - replace (l0 + Z.of_nat 0) with l0 by lia. lia.
  - assert (Hn' : l0 + Z.of_nat n <= 14) by lia.
    pose proof (IH l0 H0 ltac:(lia)) as H1. pose proof (B (l0 + Z.of_nat n) ltac:(lia)) as H2.
    replace (l0 + Z.of_nat (S n)) with (l0 + Z.of_nat n + 1) by lia. lia.
Qed.
Lemma MINV_lt : forall mb, MINV mb -> forall l l', 0 <= l -> l < l' < 16 -> zget mb l + 16 <= zget mb l'.
Proof.
  intros mb M l l' Hl Hll.
  pose proof (MINV_chain mb M (Z.to_nat (l' - l)) l Hl ltac:(lia)) as U. rewrite Z2Nat.id in U by lia. replace (l + (l' - l)) with l' in U by lia. lia.
Qed.
Lemma MINV_bounds : forall mb, MINV mb -> forall l, 0 <= l < 16 -> 1 + 16 * l <= zget mb l <= 4080 - 16 * (15 - l).
Proof.
  intros mb M l Hl. cps_pose M as (A & B & C).
  pose proof (MINV_chain mb M (Z.to_nat l) 0 ltac:(lia) ltac:(lia)) as U1. rewrite Z2Nat.id in U1 by lia. rewrite Z.add_0_l in U1.
  pose proof (MINV_chain mb M (Z.to_nat (15 - l)) l ltac:(lia) ltac:(lia)) as U2. rewrite Z2Nat.id in U2 by lia. replace (l + (15 - l)) with 15 in U2 by lia.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mtf_sh4_spec : forall f a pp nn, 0 <= nn -> (Z.to_nat nn <= 4 * f)%nat ->
  let '(a', nn') := mtf_sh4 f a pp nn in
  0 <= nn' <= 3 /\ nn' <= nn /\
  (forall x, pp + nn' < x <= pp + nn -> zget a' x = zget a (x - 1)) /\
  (forall x, (x <= pp + nn' \/ pp + nn < x) -> zget a' x = zget a x).
Proof.
  induction f as [|f IH]; intros a pp nn Hnn Hf; cbn [mtf_sh4].
  - split; [lia|]. split; [lia|]. split; [intros; lia| intros; reflexivity].
  - destruct (Z.ltb_spec 3 nn) as [GT|LE].
    + set (z := pp + nn).
      set (a4 := zset (zset (zset (zset a z (zget a (z - 1))) (z - 1) (zget (zset a z (zget a (z - 1))) (z - 2))) (z - 2)
                   (zget (zset (zset a z (zget a (z - 1))) (z - 1) (zget (zset a z (zget a (z - 1))) (z - 2))) (z - 3))) (z - 3)
                   (zget (zset (zset (zset a z (zget a (z - 1))) (z - 1) (zget (zset a z (zget a (z - 1))) (z - 2))) (z - 2)
                      (zget (zset (zset a z (zget a (z - 1))) (z - 1) (zget (zset a z (zget a (z - 1))) (z - 2))) (z - 3))) (z - 4))).
      assert (A4 : forall x, zget a4 x = if (z - 3 <=? x) && (x <=? z) then zget a (x - 1) else zget a x).
      { intros x. subst a4. rewrite !zget_zset.
        repeat match goal with |- context [?u =? ?v] => destruct (Z.eqb_spec u v); try lia end;
          destruct (Z.leb_spec (z - 3) x), (Z.leb_spec x z); cbn [andb]; try lia; try reflexivity; f_equal; lia. }
      specialize (IH a4 pp (nn - 4) ltac:(lia) ltac:(lia)). fold a4. destruct (mtf_sh4 f a4 pp (nn - 4)) as [a' nn'].
      cps_destruct IH as (R1 & R2 & R3 & R4). split; [lia|]. split; [lia|]. split.
      * intros x Hx. destruct (Z.le_gt_cases x (pp + (nn - 4))) as [LE1|GT1].
        -- rewrite R3 by lia. rewrite A4. destruct (Z.leb_spec (z - 3) (x - 1)), (Z.leb_spec (x - 1) z); cbn [andb]; try reflexivity; subst z; lia.
        -- rewrite R4 by lia. rewrite A4. subst z. destruct (Z.leb_spec (pp + nn - 3) x), (Z.leb_spec x (pp + nn)); cbn [andb]; try reflexivity; lia.
      * intros x Hx. rewrite R4 by lia. rewrite A4. subst z. destruct (Z.leb_spec (pp + nn - 3) x), (Z.leb_spec x (pp + nn)); cbn [andb]; try reflexivity; lia.
    + split; [lia|]. split; [lia|]. split; [intros; lia| intros; reflexivity].
Qed.

Lemma mtf_sh1_spec : forall f a pp nn, 0 <= nn -> (Z.to_nat nn <= f)%nat ->
  (forall x, pp < x <= pp + nn -> zget (mtf_sh1 f a pp nn) x = zget a (x - 1)) /\
  (forall x, (x <= pp \/ pp + nn < x) -> zget (mtf_sh1 f a pp nn) x = zget a x).
Proof.
  induction f as [|f IH]; intros a pp nn Hnn Hf; cbn [mtf_sh1].
  - split; [intros; lia| intros; reflexivity].
  - destruct (Z.ltb_spec 0 nn) as [GT|LE].
    + destruct (IH (zset a (pp + nn) (zget a (pp + nn - 1))) pp (nn - 1) ltac:(lia) ltac:(lia)) as [R1 R2]. split.
      * intros x Hx. destruct (Z.eq_dec x (pp + nn)) as [->|NE].
        -- rewrite R2 by lia. rewrite zget_zset_same. f_equal; lia.
        -- rewrite R1 by lia. rewrite zget_zset_other by lia. reflexivity.
      * intros x Hx. rewrite R2 by lia. apply zget_zset_other. lia.
    + split; [intros; lia| intros; reflexivity].
Qed.

Lemma mtf_shdown_spec : forall f a pp b, b <= pp -> (Z.to_nat (pp - b) <= f)%nat ->
  (forall x, b < x <= pp -> zget (mtf_shdown f a pp b) x = zget a (x - 1)) /\
  (forall x, (x <= b \/ pp < x) -> zget (mtf_shdown f a pp b) x = zget a x).
Proof.
  induction f as [|f IH]; intros a pp b Hb Hf; cbn [mtf_shdown].
  - split; [intros; lia| intros; reflexivity].
  - destruct (Z.ltb_spec b pp) as [LT|GE].
    + destruct (IH (zset a pp (zget a (pp - 1))) (pp - 1) b ltac:(lia) ltac:(lia)) as [R1 R2]. split.
      * intros x Hx. destruct (Z.eq_dec x pp) as [->|NE]; [rewrite R2 by lia; apply zget_zset_same|].
        rewrite R1 by lia. apply zget_zset_other. lia.
      * intros x Hx. rewrite R2 by lia. apply zget_zset_other. lia.
    + split; [intros; lia| intros; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mtf_pull_spec : forall f a mb mb0 lno dl, MINV mb0 -> 0 <= lno <= 15 -> (Z.to_nat lno <= f)%nat -> (dl = 0 \/ dl = 1) ->
  (forall l, 0 <= l < lno -> zget mb l = zget mb0 l) -> (1 <= lno -> zget mb lno = zget mb0 lno + dl) ->
  let '(a', mb') := mtf_pull f a mb lno in
  (forall l, 1 <= l <= lno -> zget mb' l = zget mb0 l - 1 + (if l =? lno then dl else 0)) /\
  (forall l, (l < 1 \/ lno < l) -> zget mb' l = zget mb l) /\
  (forall l, 1 <= l <= lno -> zget a' (zget mb0 l - 1 + (if l =? lno then dl else 0)) = zget a (zget mb0 (l - 1) + 15)) /\
  (forall x, (forall l, 1 <= l <= lno -> x <> zget mb0 l - 1 + (if l =? lno then dl else 0)) -> zget a' x = zget a x).
Proof.
  induction f as [|f IH]; intros a mb mb0 lno dl M Hl Hf Hdl AG TOP; cbn [mtf_pull].
  - assert (lno = 0) by lia. subst lno. split; [intros; lia|]. split; [intros; reflexivity|]. split; [intros; lia| intros; reflexivity].
  - destruct (Z.ltb_spec 0 lno) as [GT|LE].
    + pose proof (MINV_bounds mb0 M) as MB.
      rewrite (TOP ltac:(lia)).
      set (b := zget mb0 lno + dl - 1).
      set (mb1 := zset mb lno b).
      set (a1 := zset a b (zget a (zget mb1 (lno - 1) + 15))).
      assert (E1 : zget mb1 (lno - 1) = zget mb0 (lno - 1)) by (subst mb1; rewrite zget_zset_other by lia; apply AG; lia).
      specialize (IH a1 mb1 mb0 (lno - 1) 0 M ltac:(lia) ltac:(lia) ltac:(lia)).
      destruct (mtf_pull f a1 mb1 (lno - 1)) as [a' mb'].
      cps_destruct IH as (R1 & R2 & R3 & R4).
      { intros l Hl'. subst mb1. rewrite zget_zset_other by lia. apply AG. lia. }
      { intros _. rewrite E1. lia. }
      split; [| split; [| split]].
      * intros l Hl'. destruct (Z.eqb_spec l lno) as [->|NE].
        -- rewrite R2 by lia. subst mb1. rewrite zget_zset_same. subst b. lia.
        -- rewrite R1 by lia. destruct (Z.eqb_spec l (lno - 1)), (Z.eqb_spec l lno); lia.
      * intros l Hl'. rewrite R2 by lia. subst mb1. apply zget_zset_other. lia.
      * intros l Hl'. destruct (Z.eqb_spec l lno) as [->|NE].
        -- rewrite R4.
           ++ subst a1. replace (zget mb0 lno - 1 + dl) with b by (subst b; lia). rewrite zget_zset_same. rewrite E1. reflexivity.
           ++ intros l' Hl2. pose proof (MINV_lt mb0 M l' lno ltac:(lia) ltac:(lia)). destruct (Z.eqb_spec l' (lno - 1)); lia.
        -- replace (if l =? lno then dl else 0) with 0 by (destruct (Z.eqb_spec l lno); lia).
           pose proof (R3 l ltac:(lia)) as X. replace (if l =? lno - 1 then 0 else 0) with 0 in X by (destruct (l =? lno - 1); reflexivity).
           rewrite X. subst a1. rewrite zget_zset_other; [reflexivity|].
           subst b. pose proof (MINV_lt mb0 M (l - 1) (lno - 1) ltac:(lia) ltac:(lia)). pose proof (MINV_lt mb0 M (lno - 1) lno ltac:(lia) ltac:(lia)). lia.
      * intros x Hx. rewrite R4.
        -- subst a1. apply zget_zset_other. pose proof (Hx lno ltac:(lia)) as X. rewrite Z.eqb_refl in X. subst b. lia.
        -- intros l Hl2. pose proof (Hx l ltac:(lia)) as X. destruct (Z.eqb_spec l lno), (Z.eqb_spec l (lno - 1)); lia.
    + assert (lno = 0) by lia. subst lno. split; [intros; lia|]. split; [intros; reflexivity|]. split; [intros; lia| intros; reflexivity].
Qed.

(* [comment removed for export] *)
Definition home (l : Z) : Z := 3840 + 16 * l.

Lemma mtfrb_j_spec : forall n jj ii kk a mb, 0 <= ii -> jj + 1 = Z.of_nat n -> kk = home ii + jj ->
  (forall j, 0 <= j <= jj -> zget mb ii + j <= home ii + j) ->
  let '(a', kk') := mtfrb_j n jj ii kk a mb in
  kk' = home ii - 1 /\
  (forall j, 0 <= j <= jj -> zget a' (home ii + j) = zget a (zget mb ii + j)) /\
  (forall x, (x < home ii \/ home ii + jj < x) -> zget a' x = zget a x).
Proof.
  induction n as [|n IH]; intros jj ii kk a mb Hii Hjj Hkk SRC; cbn [mtfrb_j].
  - split; [lia|]. split; [intros; lia| intros; reflexivity].
  - specialize (IH (jj - 1) ii (kk - 1) (zset a kk (zget a (zget mb ii + jj))) mb Hii ltac:(lia) ltac:(lia) ltac:(intros; apply SRC; lia)).
    destruct (mtfrb_j n (jj - 1) ii (kk - 1) _ mb) as [a' kk']. cps_destruct IH as (K & C & F).
    split; [exact K|]. split.
    + intros j Hj. destruct (Z.eq_dec j jj) as [->|NE].
      * rewrite F by lia. subst kk. rewrite zget_zset_same. reflexivity.
      * rewrite C by lia. rewrite zget_zset_other; [reflexivity|]. pose proof (SRC j ltac:(lia)). subst kk. lia.
    + intros x Hx. rewrite F by lia. apply zget_zset_other. subst kk. lia.
Qed.

Lemma mtfrb_i_spec : forall n ii kk a mb, ii + 1 = Z.of_nat n -> ii <= 15 -> kk = home ii + 15 ->
  (forall l, 0 <= l <= ii -> 16 * l <= zget mb l <= home l) ->
  (forall l, 0 <= l < ii -> zget mb l + 16 <= zget mb (l + 1)) ->
  let '(a', mb') := mtfrb_i n ii kk a mb in
  (forall l j, 0 <= l <= ii -> 0 <= j < 16 -> zget a' (home l + j) = zget a (zget mb l + j)) /\
  (forall l, 0 <= l <= ii -> zget mb' l = home l) /\
  (forall l, (l < 0 \/ ii < l) -> zget mb' l = zget mb l) /\
  (forall x, (x < 0 \/ home ii + 15 < x) -> zget a' x = zget a x).
Proof.
  induction n as [|n IH]; intros ii kk a mb Hn Hii Hkk B1 B2; cbn [mtfrb_i].
  - split; [intros; lia|]. split; [intros; lia|]. split; [intros; reflexivity| intros; reflexivity].
  - pose proof (mtfrb_j_spec 16 15 ii kk a mb ltac:(lia) ltac:(reflexivity) Hkk ltac:(intros; pose proof (B1 ii ltac:(lia)); lia)) as J.
    destruct (mtfrb_j 16 15 ii kk a mb) as [a1 kk1]. cps_destruct J as (K1 & C1 & F1).
    specialize (IH (ii - 1) kk1 a1 (zset mb ii (kk1 + 1)) ltac:(lia) ltac:(lia) ltac:(unfold home in *; lia)).
    destruct (mtfrb_i n (ii - 1) kk1 a1 (zset mb ii (kk1 + 1))) as [a' mb'].
    cps_destruct IH as (C & H1 & H2 & F).
    { intros l Hl. rewrite zget_zset_other by lia. apply B1. lia. }
    { intros l Hl. rewrite !zget_zset_other by lia. apply B2. lia. }
    split; [| split; [| split]].
    + intros l j Hl Hj. destruct (Z.eq_dec l ii) as [->|NE].
      * rewrite F by (unfold home; lia). apply C1. lia.
      * rewrite C by lia. rewrite zget_zset_other by lia. apply F1.
        pose proof (B1 l ltac:(lia)). unfold home in *. lia.
    + intros l Hl. destruct (Z.eq_dec l ii) as [->|NE].
      * rewrite H2 by lia. rewrite zget_zset_same. unfold home in *; lia.
      * apply H1. lia.
    + intros l Hl. rewrite H2 by lia. apply zget_zset_other. lia.
    + intros x Hx. rewrite F by (unfold home in *; lia). apply F1. unfold home in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma divmod16 : forall k, 0 <= k < 256 -> 0 <= k / 16 < 16 /\ 0 <= k mod 16 < 16 /\ k = 16 * (k / 16) + k mod 16.
Proof.
  intros k Hk. pose proof (Z.div_mod k 16 ltac:(lia)). pose proof (Z.mod_pos_bound k 16 ltac:(lia)).
  split; [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem mtf_decode_spec : forall d nn, MINV (d_mtfbase d) -> 0 <= nn < 256 ->
  let '(uc, d') := mtf_decode d nn in
  uc = MV (d_mtfa d) (d_mtfbase d) nn /\ MINV (d_mtfbase d') /\
  (forall k, 0 <= k < 256 -> MV (d_mtfa d') (d_mtfbase d') k = mtf1 (MV (d_mtfa d) (d_mtfbase d)) nn k) /\
  d' = d_set_mtfbase (d_set_mtfa d (d_mtfa d')) (d_mtfbase d').
Proof.
  intros d nn M Hnn. unfold mtf_decode.
  set (a := d_mtfa d) in *. set (mb := d_mtfbase d) in *. pose proof (MINV_bounds mb M) as MB.
  destruct (Z.ltb_spec nn 16) as [F|G].
  - (* [comment removed for export] *)
    set (pp := zget mb 0). pose proof (MB 0 ltac:(lia)) as MB0.
    pose proof (mtf_sh4_spec 4 a pp nn ltac:(lia) ltac:(lia)) as S4. destruct (mtf_sh4 4 a pp nn) as [a1 nn1].
    cps_destruct S4 as (N1 & N2 & A1 & B1).
    pose proof (mtf_sh1_spec 4 a1 pp nn1 ltac:(lia) ltac:(lia)) as [A2 B2].
    set (a2 := mtf_sh1 4 a1 pp nn1) in *.
    cbn [d_mtfa d_mtfbase d_set_mtfa].
    assert (A3 : forall x, zget (zset a2 pp (zget a (pp + nn))) x = (if x =? pp then zget a (pp + nn) else if (pp <? x) && (x <=? pp + nn) then zget a (x - 1) else zget a x)).
    { intros x. rewrite zget_zset. destruct (Z.eqb_spec x pp); [reflexivity|].
      destruct (Z.ltb_spec pp x), (Z.leb_spec x (pp + nn)); cbn [andb].
      - destruct (Z.le_gt_cases x (pp + nn1)); [rewrite A2 by lia; apply B1; lia| rewrite B2 by lia; apply A1; lia].
      - rewrite B2 by lia. apply B1. lia.
      - rewrite B2 by lia. apply B1. lia.
      - rewrite B2 by lia. apply B1. lia. }
    split; [| split; [exact M| split]].
    + unfold MV. rewrite Z.div_small, Z.mod_small by lia. reflexivity.
    + intros k Hk. cps_pose (divmod16 k Hk) as (D1 & D2 & D3). unfold MV, mtf1. fold mb. rewrite A3.
      rewrite (Z.div_small nn 16), (Z.mod_small nn 16) by lia. fold pp.
      destruct (Z.eqb_spec k 0) as [->|K0].
      { rewrite Z.div_0_l, Z.mod_0_l by lia. fold pp. rewrite Z.add_0_r, Z.eqb_refl. reflexivity. }
      destruct (Z.eq_dec (k / 16) 0) as [R0|R0].
      * (* [comment removed for export] *) rewrite R0. fold pp. assert (KM : k mod 16 = k) by lia. rewrite KM.
        replace (pp + k =? pp) with false by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia.
        -- replace ((pp <? pp + k) && (pp + k <=? pp + nn))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.ltb_lt| apply Z.leb_le]; lia).
           rewrite (Z.div_small (k - 1) 16), (Z.mod_small (k - 1) 16) by lia. fold pp. f_equal. lia.
        -- replace ((pp <? pp + k) && (pp + k <=? pp + nn))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia). reflexivity.
      * (* [comment removed for export] *)
        pose proof (MINV_lt mb M 0 (k / 16) ltac:(lia) ltac:(lia)) as LT. fold pp in LT.
        replace (zget mb (k / 16) + k mod 16 =? pp) with false by (symmetry; apply Z.eqb_neq; lia).
        replace ((pp <? zget mb (k / 16) + k mod 16) && (zget mb (k / 16) + k mod 16 <=? pp + nn))%bool with false
          by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try reflexivity; lia.
    + reflexivity.
  - (* [comment removed for export] *)
    set (lno := nn / 16). set (off := nn mod 16).
    pose proof (Z.div_mod nn 16 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 16 ltac:(lia)) as MO. fold lno off in DM, MO.
    assert (Hl : 1 <= lno <= 15).
    { subst lno. assert (nn / 16 < 16) by (apply Z.div_lt_upper_bound; lia). assert (1 <= nn / 16) by (apply Z.div_le_lower_bound; lia). lia. }
    set (pp := zget mb lno + off).
    pose proof (mtf_shdown_spec 16 a pp (zget mb lno) ltac:(lia) ltac:(lia)) as [A1 B1].
    set (a1 := mtf_shdown 16 a pp (zget mb lno)) in *.
    set (mb1 := zset mb lno (zget mb lno + 1)).
    pose proof (mtf_pull_spec 16 a1 mb1 mb lno 1 M ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(intros; subst mb1; apply zget_zset_other; lia) ltac:(intros; subst mb1; apply zget_zset_same)) as PL.
    destruct (mtf_pull 16 a1 mb1 lno) as [a2 mb2]. cps_destruct PL as (P1 & P2 & P3 & P4).
    assert (E0 : zget mb2 0 = zget mb 0) by (rewrite P2 by lia; subst mb1; apply zget_zset_other; lia).
    rewrite E0.
    set (b0 := zget mb 0 - 1). set (mb3 := zset mb2 0 b0). set (a3 := zset a2 b0 (zget a pp)).
    (* [comment removed for export] *)
    assert (MB3 : forall l, 0 <= l < 16 -> zget mb3 l = (if l <? lno then zget mb l - 1 else zget mb l)).
    { intros l Hl0. subst mb3. rewrite zget_zset. destruct (Z.eqb_spec l 0) as [->|NZ].
      - replace (0 <? lno) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      - destruct (Z.ltb_spec l lno).
        + rewrite P1 by lia. replace (l =? lno) with false by (symmetry; apply Z.eqb_neq; lia). lia.
        + destruct (Z.eq_dec l lno) as [->|NE]; [rewrite P1 by lia; rewrite Z.eqb_refl; lia|].
          rewrite P2 by lia. subst mb1. apply zget_zset_other. lia. }
    assert (MV3 : forall k, 0 <= k < 256 -> MV a3 mb3 k = mtf1 (MV a mb) nn k).
    { intros k Hk. cps_pose (divmod16 k Hk) as (D1 & D2 & D3). unfold MV, mtf1. rewrite MB3 by lia.
      fold lno off. set (l := k / 16) in *. set (p := k mod 16) in *.
      pose proof (MB 0 ltac:(lia)) as R0. pose proof (MB l ltac:(lia)) as Rl. pose proof (MB lno ltac:(lia)) as Rlno.
      subst a3. rewrite zget_zset.
      destruct (Z.eqb_spec k 0) as [K0|K0].
      { (* [comment removed for export] *) assert (l = 0 /\ p = 0) as [-> ->] by (subst l p; rewrite K0; cbn; lia).
        replace (0 <? lno) with true by (symmetry; apply Z.ltb_lt; lia). replace (zget mb 0 - 1 + 0 =? b0) with true by (symmetry; apply Z.eqb_eq; lia).
        reflexivity. }
      (* [comment removed for export] *)
      assert (SB : (if l <? lno then zget mb l - 1 else zget mb l) + p <> b0).
      { subst b0. destruct (Z.ltb_spec l lno).
        - destruct (Z.eq_dec l 0) as [->|NZ]; [lia|]. pose proof (MINV_lt mb M 0 l ltac:(lia) ltac:(lia)). lia.
        - pose proof (MINV_lt mb M 0 l ltac:(lia) ltac:(lia)). lia. }
      replace ((if l <? lno then zget mb l - 1 else zget mb l) + p =? b0) with false by (symmetry; apply Z.eqb_neq; exact SB).
      destruct (Z.ltb_spec l lno) as [LL|LL].
      - (* [comment removed for export] *)
        destruct (Z.eq_dec p 0) as [->|PZ].
        + assert (L1 : 1 <= l) by (destruct (Z.eq_dec l 0); lia).
          pose proof (P3 l ltac:(lia)) as X. replace (if l =? lno then 1 else 0) with 0 in X by (destruct (Z.eqb_spec l lno); lia).
          rewrite Z.add_0_r in X |- *. rewrite X. rewrite B1 by (pose proof (MINV_lt mb M (l - 1) lno ltac:(lia) ltac:(lia)); lia).
          destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia.
          replace ((k - 1) / 16) with (l - 1) by (apply (Z.div_unique (k - 1) 16 (l - 1) 15); lia).
          replace ((k - 1) mod 16) with 15 by (apply (Z.mod_unique (k - 1) 16 (l - 1) 15); lia). reflexivity.
        + rewrite P4.
          2:{ intros l' Hl'. destruct (Z.eqb_spec l' lno) as [->|NE].
              - pose proof (MINV_lt mb M l lno ltac:(lia) ltac:(lia)). lia.
              - intros E. destruct (Z.eq_dec l' l) as [->|NL]; [lia|].
                destruct (Z.lt_ge_cases l' l); [pose proof (MINV_lt mb M l' l ltac:(lia) ltac:(lia))| pose proof (MINV_lt mb M l l' ltac:(lia) ltac:(lia))]; lia. }
          rewrite B1 by (pose proof (MINV_lt mb M l lno ltac:(lia) ltac:(lia)); lia).
          destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia.
          replace ((k - 1) / 16) with l by (apply (Z.div_unique (k - 1) 16 l (p - 1)); lia).
          replace ((k - 1) mod 16) with (p - 1) by (apply (Z.mod_unique (k - 1) 16 l (p - 1)); lia). f_equal. lia.
      - destruct (Z.eq_dec l lno) as [->|NE].
        + (* [comment removed for export] *)
          destruct (Z.eq_dec p 0) as [->|PZ].
          * pose proof (P3 lno ltac:(lia)) as X. rewrite Z.eqb_refl in X. replace (zget mb lno - 1 + 1) with (zget mb lno + 0) in X by lia.
            rewrite X. rewrite B1 by (pose proof (MINV_lt mb M (lno - 1) lno ltac:(lia) ltac:(lia)); lia).
            destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia.
            replace ((k - 1) / 16) with (lno - 1) by (apply (Z.div_unique (k - 1) 16 (lno - 1) 15); lia).
            replace ((k - 1) mod 16) with 15 by (apply (Z.mod_unique (k - 1) 16 (lno - 1) 15); lia). reflexivity.
          * rewrite P4.
            2:{ intros l' Hl'. destruct (Z.eqb_spec l' lno) as [->|NE']; [lia|]. pose proof (MINV_lt mb M l' lno ltac:(lia) ltac:(lia)). lia. }
            destruct (Z.le_gt_cases p off) as [PO|PO].
            -- rewrite A1 by lia. destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia.
               replace ((k - 1) / 16) with lno by (apply (Z.div_unique (k - 1) 16 lno (p - 1)); lia).
               replace ((k - 1) mod 16) with (p - 1) by (apply (Z.mod_unique (k - 1) 16 lno (p - 1)); lia). f_equal. lia.
            -- rewrite B1 by lia. destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try lia; reflexivity.
        + (* [comment removed for export] *)
          rewrite P4.
          2:{ intros l' Hl'. destruct (Z.eqb_spec l' lno) as [E'|NE']; pose proof (MINV_lt mb M l' l ltac:(lia) ltac:(lia)); lia. }
          rewrite B1 by (pose proof (MINV_lt mb M lno l ltac:(lia) ltac:(lia)); lia).
          destruct (Z.ltb_spec 0 k), (Z.leb_spec k nn); cbn [andb]; try reflexivity.
          pose proof (MINV_lt mb M lno l ltac:(lia) ltac:(lia)). lia. }
    assert (MINV3 : zget mb 0 <> 1 -> MINV mb3).
    { intros NZ. unfold MINV. rewrite !MB3 by lia. cps_pose M as (MA & MBB & MC).
      replace (0 <? lno) with true by (symmetry; apply Z.ltb_lt; lia).
      split; [lia|]. split.
      - intros l Hl0. rewrite !MB3 by lia. pose proof (MBB l Hl0).
        destruct (Z.ltb_spec l lno), (Z.ltb_spec (l + 1) lno); lia.
      - destruct (Z.ltb_spec 15 lno); lia. }
    cbn [d_mtfa d_mtfbase d_set_mtfa d_set_mtfbase]. fold a mb. fold lno off pp. fold a1.
    destruct (Z.eqb_spec b0 0) as [BZ|BZ].
    + (* [comment removed for export] *)
      pose proof (mtfrb_i_spec 16 15 4095 a3 mb3 ltac:(reflexivity) ltac:(lia) ltac:(reflexivity)) as RB.
      destruct (mtfrb_i 16 15 4095 a3 mb3) as [a4 mb4]. cps_destruct RB as (C & H1 & H2 & F).
      { intros l Hl0. rewrite MB3 by lia. pose proof (MB l ltac:(lia)). unfold home. destruct (Z.ltb_spec l lno); lia. }
      { intros l Hl0. rewrite !MB3 by lia. pose proof (proj1 (proj2 M) l ltac:(lia)). destruct (Z.ltb_spec l lno), (Z.ltb_spec (l + 1) lno); lia. }
      cbn [d_mtfa d_mtfbase d_set_mtfa d_set_mtfbase].
      split; [unfold MV; reflexivity|]. split; [| split; [| reflexivity]].
      * unfold MINV. rewrite !H1 by lia. unfold home. split; [lia|]. split; [| lia]. intros l Hl0. rewrite !H1 by lia. unfold home. lia.
      * intros k Hk. rewrite <- MV3 by lia. cps_pose (divmod16 k Hk) as (D1 & D2 & D3). unfold MV. rewrite H1 by lia. apply C; lia.
    + cbn [d_mtfa d_mtfbase d_set_mtfa d_set_mtfbase].
      split; [unfold MV; reflexivity|]. split; [apply MINV3; lia| split; [exact MV3| reflexivity]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mtfinit_j_spec : forall n jj ii kk a, jj + 1 = Z.of_nat n -> kk = home ii + jj ->
  let '(a', kk') := mtfinit_j n jj ii kk a in
  kk' = home ii - 1 /\
  (forall j, 0 <= j <= jj -> zget a' (home ii + j) = ii * 16 + j) /\
  (forall x, (x < home ii \/ home ii + jj < x) -> zget a' x = zget a x).
Proof.
  induction n as [|n IH]; intros jj ii kk a Hjj Hkk; cbn [mtfinit_j].
  - split; [lia|]. split; [intros; lia| intros; reflexivity].
  - specialize (IH (jj - 1) ii (kk - 1) (zset a kk (ii * 16 + jj)) ltac:(lia) ltac:(lia)).
    destruct (mtfinit_j n (jj - 1) ii (kk - 1) _) as [a' kk']. cps_destruct IH as (K & C & F).
    split; [exact K|]. split.
    + intros j Hj. destruct (Z.eq_dec j jj) as [->|NE].
      * rewrite F by lia. subst kk. rewrite zget_zset_same. reflexivity.
      * rewrite C by lia. reflexivity.
    + intros x Hx. rewrite F by lia. apply zget_zset_other. subst kk. lia.
Qed.

Lemma mtfinit_i_spec : forall n ii kk a mb, ii + 1 = Z.of_nat n -> ii <= 15 -> kk = home ii + 15 ->
  let '(a', mb') := mtfinit_i n ii kk a mb in
  (forall l j, 0 <= l <= ii -> 0 <= j < 16 -> zget a' (home l + j) = l * 16 + j) /\
  (forall l, 0 <= l <= ii -> zget mb' l = home l) /\
  (forall l, (l < 0 \/ ii < l) -> zget mb' l = zget mb l) /\
  (forall x, (x < 0 \/ home ii + 15 < x) -> zget a' x = zget a x).
Proof.
  induction n as [|n IH]; intros ii kk a mb Hn Hii Hkk; cbn [mtfinit_i].
  - split; [intros; lia|]. split; [intros; lia|]. split; [intros; reflexivity| intros; reflexivity].
  - pose proof (mtfinit_j_spec 16 15 ii kk a ltac:(reflexivity) Hkk) as J.
    destruct (mtfinit_j 16 15 ii kk a) as [a1 kk1]. cps_destruct J as (K1 & C1 & F1).
    specialize (IH (ii - 1) kk1 a1 (zset mb ii (kk1 + 1)) ltac:(lia) ltac:(lia) ltac:(unfold home in *; lia)).
    destruct (mtfinit_i n (ii - 1) kk1 a1 (zset mb ii (kk1 + 1))) as [a' mb'].
    cps_destruct IH as (C & H1 & H2 & F).
    split; [| split; [| split]].
    + intros l j Hl Hj. destruct (Z.eq_dec l ii) as [->|NE].
      * rewrite F by (unfold home; lia). apply C1. lia.
      * rewrite C by lia. reflexivity.
    + intros l Hl. destruct (Z.eq_dec l ii) as [->|NE].
      * rewrite H2 by lia. rewrite zget_zset_same. unfold home in *; lia.
      * apply H1. lia.
    + intros l Hl. rewrite H2 by lia. apply zget_zset_other. lia.
    + intros x Hx. rewrite F by (unfold home in *; lia). apply F1. unfold home in *; lia.
Qed.

Theorem mtf_init_spec : forall d,
  let d' := mtf_init d in
  MINV (d_mtfbase d') /\
  (forall k, 0 <= k < 256 -> MV (d_mtfa d') (d_mtfbase d') k = k) /\
  (forall l, 0 <= l < 16 -> zget (d_mtfbase d') l = home l) /\
  d' = d_set_mtfbase (d_set_mtfa d (d_mtfa d')) (d_mtfbase d').
Proof.
  intros d. unfold mtf_init.
  pose proof (mtfinit_i_spec 16 15 4095 (d_mtfa d) (d_mtfbase d) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity)) as SP.
  destruct (mtfinit_i 16 15 4095 (d_mtfa d) (d_mtfbase d)) as [a' mb']. cps_destruct SP as (C & H1 & H2 & F).
  cbv zeta. cbn [d_mtfa d_mtfbase d_set_mtfa d_set_mtfbase].
  split; [| split; [| split; [intros l Hl; apply H1; lia| reflexivity]]].
  - unfold MINV. rewrite !H1 by lia. unfold home. split; [lia|]. split; [| lia]. intros l Hl. rewrite !H1 by lia. unfold home. lia.
  - intros k Hk. cps_pose (divmod16 k Hk) as (D1 & D2 & D3). unfold MV. rewrite H1 by lia. rewrite C by lia. lia.
Qed.
End BzR4m.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MPERM (n : Z) (M : Z -> Z) : Prop :=
  (forall k, 0 <= k < n -> 0 <= M k < n) /\
  (forall k k', 0 <= k < n -> 0 <= k' < n -> M k = M k' -> k = k').

Lemma mtf1_0 : forall M j, mtf1 M j 0 = M j.
Proof. intros. unfold mtf1. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma mtf1_low : forall M j k, 0 < k <= j -> mtf1 M j k = M (k - 1).
Proof.
  intros M j k Hk. unfold mtf1. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((0 <? k) && (k <=? j))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.ltb_lt| apply Z.leb_le]; lia).
  reflexivity.
Qed.
Lemma mtf1_high : forall M j k, j < k -> 0 <= j -> mtf1 M j k = M k.
Proof.
  intros M j k Hk Hj. unfold mtf1. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((0 <? k) && (k <=? j))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
  reflexivity.
Qed.
(* [comment removed for export] *)

Lemma mtf1_MPERM : forall n M j, MPERM n M -> 0 <= j < n -> MPERM n (mtf1 M j).
Proof.
  intros n M j [R I] Hj. split.
  - intros k Hk. destruct (Z.eq_dec k 0) as [->|NE]; [rewrite mtf1_0; apply R; lia|].
    destruct (Z.le_gt_cases k j); [rewrite mtf1_low by lia| rewrite mtf1_high by lia]; apply R; lia.
  - intros k k' Hk Hk' E.
    assert (G : forall x, 0 <= x < n -> exists y, 0 <= y < n /\ mtf1 M j x = M y /\
              (x = 0 -> y = j) /\ (0 < x <= j -> y = x - 1) /\ (j < x -> y = x)).
    { intros x Hx. destruct (Z.eq_dec x 0) as [->|NE].
      - exists j. rewrite mtf1_0. repeat split; try lia.
      - destruct (Z.le_gt_cases x j).
        + exists (x - 1). rewrite mtf1_low by lia. repeat split; try lia.
        + exists x. rewrite mtf1_high by lia. repeat split; try lia. }
    cps_destruct (G k Hk) as (y & Hy & Ey & A1 & A2 & A3). cps_destruct (G k' Hk') as (y' & Hy' & Ey' & B1 & B2 & B3).
    rewrite Ey, Ey' in E. pose proof (I y y' Hy Hy' E). subst y'.
    destruct (Z.eq_dec k 0), (Z.eq_dec k' 0), (Z.le_gt_cases k' j), (Z.le_gt_cases k j); lia.
Qed.

(* [comment removed for export] *)
Fixpoint cntv (m : nat) (M : Z -> Z) (v : Z) : Z :=
  match m with O => 0 | S m' => cntv m' M v + (if M (Z.of_nat m') =? v then 1 else 0) end.
Lemma cntv_nonneg : forall m M v, 0 <= cntv m M v.
Proof. induction m; intros; cbn [cntv]; [lia|]. destruct (M (Z.of_nat m) =? v); pose proof (IHm M v); lia. Qed.
Lemma cntv_pos : forall m M v, 0 < cntv m M v -> exists k, 0 <= k < Z.of_nat m /\ M k = v.
Proof.
  induction m as [|m IH]; intros M v H; cbn [cntv] in H; [lia|].
  destruct (Z.eqb_spec (M (Z.of_nat m)) v).
  - exists (Z.of_nat m). split; [lia| assumption].
  - cps_destruct (IH M v ltac:(lia)) as (k & Hk & E). exists k. split; [lia| exact E].
Qed.
(* [comment removed for export] *)
Lemma cntv_inj_le1 : forall m M v, (forall k k', 0 <= k < Z.of_nat m -> 0 <= k' < Z.of_nat m -> M k = M k' -> k = k') -> cntv m M v <= 1.
Proof.
  induction m as [|m IH]; intros M v I; cbn [cntv]; [lia|].
  destruct (Z.eqb_spec (M (Z.of_nat m)) v) as [E|NE].
  - destruct (Z.le_gt_cases (cntv m M v) 0) as [LE|GT]; [lia|].
    cps_destruct (cntv_pos m M v GT) as (k & Hk & Ek). exfalso.
    pose proof (I k (Z.of_nat m) ltac:(lia) ltac:(lia) ltac:(rewrite Ek, E; reflexivity)). lia.
  - pose proof (IH M v ltac:(intros; apply I; lia)). lia.
Qed.
(* [comment removed for export] *)
Fixpoint sumv (b : nat) (m : nat) (M : Z -> Z) : Z :=
  match b with O => 0 | S b' => sumv b' m M + cntv m M (Z.of_nat b') end.
Fixpoint cntlt (m : nat) (M : Z -> Z) (b : Z) : Z :=
  match m with O => 0 | S m' => cntlt m' M b + (if (0 <=? M (Z.of_nat m')) && (M (Z.of_nat m') <? b) then 1 else 0) end.
Lemma sumv_S_m : forall b m M, sumv b (S m) M = sumv b m M + (if (0 <=? M (Z.of_nat m)) && (M (Z.of_nat m) <? Z.of_nat b) then 1 else 0).
Proof.
  induction b as [|b IH]; intros m M; cbn [sumv].
  - destruct (Z.leb_spec 0 (M (Z.of_nat m))), (Z.ltb_spec (M (Z.of_nat m)) (Z.of_nat 0)); cbn; lia.
  - rewrite IH. cbn [cntv].
    destruct (Z.leb_spec 0 (M (Z.of_nat m))), (Z.ltb_spec (M (Z.of_nat m)) (Z.of_nat b)), (Z.eqb_spec (M (Z.of_nat m)) (Z.of_nat b)),
      (Z.ltb_spec (M (Z.of_nat m)) (Z.of_nat (S b))); cbn [andb]; lia.
Qed.
Lemma sumv_cntlt : forall b m M, sumv b m M = cntlt m M (Z.of_nat b).
Proof.
  intros b m M. induction m as [|m IH].
  - cbn. induction b; cbn [sumv cntv]; lia.
  - rewrite sumv_S_m, IH. reflexivity.
Qed.
Lemma cntlt_all : forall m M b, (forall k, 0 <= k < Z.of_nat m -> 0 <= M k < b) -> cntlt m M b = Z.of_nat m.
Proof.
  induction m as [|m IH]; intros M b R; cbn [cntlt]; [lia|].
  rewrite IH by (intros; apply R; lia). pose proof (R (Z.of_nat m) ltac:(lia)).
  replace ((0 <=? M (Z.of_nat m)) && (M (Z.of_nat m) <? b))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  lia.
Qed.
Lemma sumv_le : forall b m M, (forall v, cntv m M v <= 1) -> sumv b m M <= Z.of_nat b /\
  ((exists v, 0 <= v < Z.of_nat b /\ cntv m M v = 0) -> sumv b m M < Z.of_nat b).
Proof.
  induction b as [|b IH]; intros m M H1; cbn [sumv].
  - split; [lia|]. cps_intros (v & Hv & _). lia.
  - destruct (IH m M H1) as [A B]. pose proof (H1 (Z.of_nat b)). split; [lia|].
    cps_intros (v & Hv & Cv). destruct (Z.eq_dec v (Z.of_nat b)) as [->|NE]; [lia|].
    pose proof (B ltac:(exists v; split; [lia| exact Cv])). lia.
Qed.

Lemma MPERM_onto : forall n M v, MPERM n M -> 0 <= v < n -> exists k, 0 <= k < n /\ M k = v.
Proof.
  intros n M v [R I] Hv.
  destruct (Z.le_gt_cases 1 (cntv (Z.to_nat n) M v)) as [GE|LT].
  - cps_destruct (cntv_pos (Z.to_nat n) M v ltac:(lia)) as (k & Hk & E). exists k. split; [lia| exact E].
  - exfalso. pose proof (cntv_nonneg (Z.to_nat n) M v).
    destruct (sumv_le (Z.to_nat n) (Z.to_nat n) M) as [_ B].
    { intros v'. apply cntv_inj_le1. intros; apply I; lia. }
    specialize (B ltac:(exists v; split; lia)).
    rewrite sumv_cntlt, cntlt_all in B by (intros; pose proof (R k ltac:(lia)); lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mpos (m : nat) (M : Z -> Z) (u : Z) (j : Z) : Z :=
  match m with O => j | S m' => if M j =? u then j else mpos m' M u (j + 1) end.

Lemma mpos_spec : forall m M u j, j <= mpos m M u j <= j + Z.of_nat m /\
  (forall k, j <= k < mpos m M u j -> M k <> u) /\
  (mpos m M u j < j + Z.of_nat m -> M (mpos m M u j) = u) /\
  ((exists k, j <= k < j + Z.of_nat m /\ M k = u) -> mpos m M u j < j + Z.of_nat m).
Proof.
  induction m as [|m IH]; intros M u j; cbn [mpos].
  - split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. cps_intros (k & Hk & _); lia.
  - destruct (Z.eqb_spec (M j) u) as [E|NE].
    + split; [lia|]. split; [intros; lia|]. split; [intros; exact E| intros; lia].
    + cps_destruct (IH M u (j + 1)) as (A & B & C & D). split; [lia|]. split.
      * intros k Hk. destruct (Z.eq_dec k j) as [->|NK]; [exact NE| apply B; lia].
      * split; [intros; apply C; lia|]. cps_intros (k & Hk & Ek). destruct (Z.eq_dec k j) as [->|NK]; [congruence|].
        specialize (D ltac:(exists k; split; [lia| exact Ek])). lia.
Qed.

Lemma mpos_found : forall n M u, MPERM n M -> 0 <= u < n ->
  let j := mpos (Z.to_nat n) M u 0 in 0 <= j < n /\ M j = u /\ (forall k, 0 <= k < j -> M k <> u).
Proof.
  intros n M u P Hu. cps_destruct (mpos_spec (Z.to_nat n) M u 0) as (A & B & C & D).
  cps_destruct (MPERM_onto n M u P Hu) as (k & Hk & Ek).
  specialize (D ltac:(exists k; split; [lia| exact Ek])). cbv zeta.
  split; [lia|]. split; [apply C; lia| exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zdig (f : nat) (z : Z) : list Z :=
  match f with
  | O => []
  | S f' => (if Z.land z 1 =? 0 then 0 else 1) :: (if z <? 2 then [] else zdig f' ((z - 2) / 2))
  end.
Definition zflush (z : Z) : list Z := if 0 <? z then zdig 64 (z - 1) else [].

Lemma land1_even : forall z, 0 <= z -> (Z.land z 1 =? 0) = Z.even z.
Proof.
  intros z Hz. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zeven_mod. reflexivity.
Qed.

Lemma zdig_runs : forall f z, Forall (fun x => x = 0 \/ x = 1) (zdig f z).
Proof.
  induction f as [|f IH]; intros z; cbn [zdig]; [constructor|]. constructor.
  - destruct (Z.land z 1 =? 0); lia.
  - destruct (z <? 2); [constructor| apply IH].
Qed.
Lemma zdig_len : forall f z, 0 <= z -> (forall g, z + 3 <= 2 ^ (Z.of_nat g + 1) -> (length (zdig f z) <= g)%nat).
Proof.
  induction f as [|f IH]; intros z Hz g Hg; cbn [zdig length]; [lia|].
  destruct g as [|g]. { change (2 ^ (Z.of_nat 0 + 1)) with 2 in Hg. lia. }
  destruct (Z.ltb_spec z 2); cbn [length]; [lia|].
  assert ((length (zdig f ((z - 2) / 2)) <= g)%nat); [|lia].
  apply IH. { apply Z.div_pos; lia. }
  replace (Z.of_nat (S g) + 1) with (Z.succ (Z.of_nat g + 1)) in Hg by lia. rewrite Z.pow_succ_r in Hg by lia.
  pose proof (Z.div_mod (z - 2) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (z - 2) 2 ltac:(lia)). lia.
Qed.
Lemma zdig_nonnil : forall f z, (1 <= f)%nat -> zdig f z <> [].
Proof. intros [|f] z Hf; cbn [zdig]; [lia| discriminate]. Qed.
Lemma zflush_runs : forall z, Forall (fun x => x = 0 \/ x = 1) (zflush z).
Proof. intros z. unfold zflush. destruct (0 <? z); [apply zdig_runs| constructor]. Qed.
Lemma zflush_len : forall z, z <= 2 ^ 20 -> (length (zflush z) <= 20)%nat.
Proof.
  intros z Hz. unfold zflush. destruct (Z.ltb_spec 0 z); [| cbn; lia].
  apply zdig_len; [lia|]. change (2 ^ (Z.of_nat 20 + 1)) with (2 * 2 ^ 20). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record gst := GST { g_M : Z -> Z; g_z : Z; g_acc : list Z }.
Definition gstep (n : Z) (st : gst) (u : Z) : gst :=
  let j := mpos (Z.to_nat n) (g_M st) u 0 in
  if j =? 0 then GST (g_M st) (g_z st + 1) (g_acc st)
  else GST (mtf1 (g_M st) j) 0 (g_acc st ++ zflush (g_z st) ++ [j + 1]).
Definition gsteps (n : Z) (st : gst) (us : list Z) : gst := fold_left (gstep n) us st.
Definition gfin (EOB : Z) (st : gst) : list Z := g_acc st ++ zflush (g_z st) ++ [EOB].
Definition genc (n EOB : Z) (M : Z -> Z) (z : Z) (us : list Z) : list Z := gfin EOB (gsteps n (GST M z []) us).

(* [comment removed for export] *)
Lemma gsteps_cons : forall n st u us, gsteps n st (u :: us) = gsteps n (gstep n st u) us. Proof. reflexivity. Qed.
Lemma gsteps_app : forall n st us vs, gsteps n st (us ++ vs) = gsteps n (gsteps n st us) vs.
Proof. intros. unfold gsteps. apply fold_left_app. Qed.

(* [comment removed for export] *)
Lemma gsteps_acc : forall n us M z acc,
  gsteps n (GST M z acc) us = GST (g_M (gsteps n (GST M z []) us)) (g_z (gsteps n (GST M z []) us)) (acc ++ g_acc (gsteps n (GST M z []) us)).
Proof.
  induction us as [|u us IH]; intros M z acc.
  - cbn. rewrite app_nil_r. reflexivity.
  - rewrite !gsteps_cons. unfold gstep. cbn [g_M g_z g_acc].
    destruct (mpos (Z.to_nat n) M u 0 =? 0).
    + rewrite (IH M (z + 1) acc). rewrite (IH M (z + 1) []). reflexivity.
    + rewrite (IH _ 0 (acc ++ _)). rewrite (IH _ 0 ([] ++ _)). cbn [g_M g_z g_acc app]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma genc_cons : forall n EOB M z u us,
  genc n EOB M z (u :: us) =
  (let j := mpos (Z.to_nat n) M u 0 in
   if j =? 0 then genc n EOB M (z + 1) us else zflush z ++ (j + 1) :: genc n EOB (mtf1 M j) 0 us).
Proof.
  intros. unfold genc. rewrite gsteps_cons. unfold gstep at 1. cbn [g_M g_z g_acc].
  destruct (mpos (Z.to_nat n) M u 0 =? 0); [reflexivity|].
  rewrite gsteps_acc. unfold gfin. cbn [g_acc g_z app]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma genc_nil : forall n EOB M z, genc n EOB M z [] = zflush z ++ [EOB]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ast := AST { a_M : Z -> Z; a_out : list Z; a_run : option (Z * Z) }.
Definition isrun (x : Z) : bool := (x =? 0) || (x =? 1).
Definition run_acc (r : option (Z * Z)) : Z * Z := match r with Some p => p | None => (-1, 1) end.
Definition run_out (M : Z -> Z) (r : option (Z * Z)) : list Z :=
  match r with Some (es, _) => repeat (M 0) (Z.to_nat (es + 1)) | None => [] end.
Definition astep (EOB : Z) (st : ast) (x : Z) : ast :=
  if isrun x then
    let '(es, N) := run_acc (a_run st) in AST (a_M st) (a_out st) (Some (es + (x + 1) * N, 2 * N))
  else
    let out := a_out st ++ run_out (a_M st) (a_run st) in
    if x =? EOB then AST (a_M st) out None
    else AST (mtf1 (a_M st) (x - 1)) (out ++ [a_M st (x - 1)]) None.
Definition asteps (EOB : Z) (st : ast) (xs : list Z) : ast := fold_left (astep EOB) xs st.

Lemma asteps_nil : forall EOB st, asteps EOB st [] = st. Proof. reflexivity. Qed.
Lemma asteps_cons : forall EOB st x xs, asteps EOB st (x :: xs) = asteps EOB (astep EOB st x) xs. Proof. reflexivity. Qed.
Lemma asteps_app : forall EOB st xs ys, asteps EOB st (xs ++ ys) = asteps EOB (asteps EOB st xs) ys.
Proof. intros. unfold asteps. apply fold_left_app. Qed.

(* [comment removed for export] *)
Lemma asteps_zdig : forall f EOB M out es N z, 0 <= z /\ z + 2 <= 2 ^ Z.of_nat f -> 0 <= N ->
  exists N', asteps EOB (AST M out (Some (es, N))) (zdig f z) = AST M out (Some (es + (z + 1) * N, N')) /\ 0 <= N'.
Proof.
  induction f as [|f IH]; intros EOB M out es N z Hz HN.
  - change (2 ^ Z.of_nat 0) with 1 in Hz. lia.
  - cbn [zdig]. rewrite asteps_cons. rewrite land1_even by lia.
    assert (P2 : 2 ^ Z.of_nat (S f) = 2 * 2 ^ Z.of_nat f) by (replace (Z.of_nat (S f)) with (Z.succ (Z.of_nat f)) by lia; rewrite Z.pow_succ_r; lia).
    pose proof (Z.div_mod z 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound z 2 ltac:(lia)) as MB.
    destruct (Z.even z) eqn:EV.
    + (* [comment removed for export] *) apply Z.even_spec in EV. destruct EV as [h Hh].
      unfold astep. change (isrun 0) with true. cbn [a_run a_M a_out run_acc].
      destruct (Z.ltb_spec z 2) as [LT|GE].
      * exists (2 * N). rewrite asteps_nil. split; [f_equal; f_equal; f_equal; lia| lia].
      * cps_destruct (IH EOB M out (es + (0 + 1) * N) (2 * N) ((z - 2) / 2)) as (N' & E & HN').
        { replace ((z - 2) / 2) with (h - 1) by (subst z; rewrite <- (Z.div_unique (2 * h - 2) 2 (h - 1) 0); lia). lia. }
        { lia. }
        exists N'. rewrite E. split; [| exact HN']. f_equal. f_equal. f_equal.
        replace ((z - 2) / 2) with (h - 1) by (subst z; rewrite <- (Z.div_unique (2 * h - 2) 2 (h - 1) 0); lia). lia.
    + (* [comment removed for export] *) assert (OD : Z.odd z = true) by (rewrite <- Z.negb_even, EV; reflexivity). apply Z.odd_spec in OD. destruct OD as [h Hh].
      unfold astep. change (isrun 1) with true. cbn [a_run a_M a_out run_acc].
      destruct (Z.ltb_spec z 2) as [LT|GE].
      * exists (2 * N). rewrite asteps_nil. split; [f_equal; f_equal; f_equal; lia| lia].
      * cps_destruct (IH EOB M out (es + (1 + 1) * N) (2 * N) ((z - 2) / 2)) as (N' & E & HN').
        { replace ((z - 2) / 2) with (h - 1) by (subst z; rewrite <- (Z.div_unique (2 * h + 1 - 2) 2 (h - 1) 1); lia). lia. }
        { lia. }
        exists N'. rewrite E. split; [| exact HN']. f_equal. f_equal. f_equal.
        replace ((z - 2) / 2) with (h - 1) by (subst z; rewrite <- (Z.div_unique (2 * h + 1 - 2) 2 (h - 1) 1); lia). lia.
Qed.

Lemma astep_None_run : forall EOB M out x, isrun x = true ->
  astep EOB (AST M out None) x = astep EOB (AST M out (Some (-1, 1))) x.
Proof. intros EOB M out x H. unfold astep. rewrite H. reflexivity. Qed.

Lemma asteps_zflush : forall EOB M out z, 0 <= z < 2 ^ 64 ->
  exists r, asteps EOB (AST M out None) (zflush z) = AST M out r /\ run_out M r = repeat (M 0) (Z.to_nat z).
Proof.
  intros EOB M out z Hz. unfold zflush. destruct (Z.ltb_spec 0 z) as [P|NP].
  - pose proof (zdig_runs 64 (z - 1)) as FR.
    destruct (zdig 64 (z - 1)) as [|x xs] eqn:ZD; [exfalso; apply (zdig_nonnil 64 (z - 1)); [lia| exact ZD]|].
    apply Forall_cons_iff in FR as [Fx _].
    rewrite asteps_cons, astep_None_run, <- asteps_cons by (destruct Fx as [-> | ->]; reflexivity). rewrite <- ZD.
    cps_destruct (asteps_zdig 64 EOB M out (-1) 1 (z - 1) ltac:(change (2 ^ Z.of_nat 64) with (2 ^ 64); lia) ltac:(lia)) as (N' & E & _).
    exists (Some (-1 + (z - 1 + 1) * 1, N')). rewrite E. split; [reflexivity|]. cbn [run_out]. f_equal. f_equal. lia.
  - exists None. rewrite asteps_nil. split; [reflexivity|]. cbn [run_out]. replace (Z.to_nat z) with 0%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem genc_inverse : forall n EOB us M out z,
  1 <= n -> EOB = n + 1 -> MPERM n M -> Forall (fun u => 0 <= u < n) us ->
  0 <= z -> z + Z.of_nat (length us) < 2 ^ 64 ->
  a_out (asteps EOB (AST M out None) (genc n EOB M z us)) = out ++ repeat (M 0) (Z.to_nat z) ++ us.
Proof.
  intros n EOB us. induction us as [|u us IH]; intros M out z Hn HE P F Hz HF.
  - rewrite genc_nil, asteps_app. cbn [length] in HF.
    cps_destruct (asteps_zflush EOB M out z ltac:(lia)) as (r & E & RO). rewrite E.
    cbn [asteps fold_left]. unfold astep. cbn [a_M a_out a_run].
    replace (isrun EOB) with false by (symmetry; unfold isrun; apply Bool.orb_false_iff; split; apply Z.eqb_neq; lia).
    rewrite Z.eqb_refl. cbn [a_out]. rewrite RO, app_nil_r. reflexivity.
  - apply Forall_cons_iff in F as [Fu F]. cbn [length] in HF. rewrite genc_cons. cbv zeta.
    cps_pose (mpos_found n M u P Fu) as (J1 & J2 & J3). set (j := mpos (Z.to_nat n) M u 0) in *.
    destruct (Z.eqb_spec j 0) as [J0|J0].
    + rewrite IH; try assumption; try lia. rewrite <- J2, J0.
      replace (Z.to_nat (z + 1)) with (S (Z.to_nat z)) by lia. cbn [repeat]. rewrite repeat_cons, <- app_assoc. reflexivity.
    + rewrite asteps_app. cps_destruct (asteps_zflush EOB M out z ltac:(lia)) as (r & E & RO). rewrite E.
      rewrite asteps_cons. unfold astep. cbn [a_M a_out a_run].
      replace (isrun (j + 1)) with false by (symmetry; unfold isrun; apply Bool.orb_false_iff; split; apply Z.eqb_neq; lia).
      replace (j + 1 =? EOB) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (j + 1 - 1) with j by lia.
      rewrite IH; try lia.
      * cbn [repeat app]. rewrite RO, J2, <- !app_assoc. reflexivity.
      * apply mtf1_MPERM; [exact P| lia].
      * exact F.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint runs_ok (K : nat) (c : nat) (xs : list Z) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => if isrun x then (S c <= K)%nat /\ runs_ok K (S c) xs' else runs_ok K 0 xs'
  end.
Lemma runs_ok_app : forall K xs ys c, runs_ok K c xs -> Forall (fun x => isrun x = true) xs ->
  runs_ok K (c + length xs) ys -> runs_ok K c (xs ++ ys).
Proof.
  induction xs as [|x xs IH]; intros ys c R F Ry; cbn [app runs_ok length] in *.
  - rewrite Nat.add_0_r in Ry. exact Ry.
  - apply Forall_cons_iff in F as [Fx F]. rewrite Fx in R |- *. destruct R as [R1 R2]. split; [exact R1|].
    apply IH; [exact R2| exact F|]. replace (S c + length xs)%nat with (c + S (length xs))%nat by lia. exact Ry.
Qed.
Lemma runs_ok_runs : forall K xs c, Forall (fun x => isrun x = true) xs -> (c + length xs <= K)%nat -> runs_ok K c xs.
Proof.
  induction xs as [|x xs IH]; intros c F L; cbn [runs_ok length] in *; [exact I|].
  apply Forall_cons_iff in F as [Fx F]. rewrite Fx. split; [lia|]. apply IH; [exact F| lia].
Qed.
(* [comment removed for export] *)
Lemma isrun_runs : forall l, Forall (fun x => x = 0 \/ x = 1) l -> Forall (fun x => isrun x = true) l.
Proof. intros l F. eapply Forall_impl; [| exact F]. intros x [-> | ->]; reflexivity. Qed.

Lemma runs_ok_block : forall K F y rest, Forall (fun x => isrun x = true) F -> (length F <= K)%nat -> isrun y = false ->
  runs_ok K 0 rest -> runs_ok K 0 (F ++ y :: rest).
Proof.
  intros K F y rest HF L Hy R. apply runs_ok_app; [apply runs_ok_runs; [exact HF| lia]| exact HF|].
  cbn [runs_ok]. rewrite Hy. exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Shape.
  Variables (n EOB : Z).
  Hypothesis Hn : 1 <= n.
  Hypothesis HE : EOB = n + 1.

  (* [comment removed for export] *)
  Lemma genc_shape : forall us M z, MPERM n M -> Forall (fun u => 0 <= u < n) us -> 0 <= z ->
    exists body, genc n EOB M z us = body ++ [EOB] /\ Forall (fun x => 0 <= x < EOB) body.
  Proof.
    induction us as [|u us IH]; intros M z P F Hz.
    - exists (zflush z). rewrite genc_nil. split; [reflexivity|].
      eapply Forall_impl; [| apply zflush_runs]. cbv beta. intros x Hx. lia.
    - apply Forall_cons_iff in F as [Fu F]. rewrite genc_cons. cbv zeta.
      cps_pose (mpos_found n M u P Fu) as (J1 & J2 & J3). set (j := mpos (Z.to_nat n) M u 0) in *.
      destruct (Z.eqb_spec j 0) as [J0|J0].
      + apply IH; [exact P| exact F| lia].
      + cps_destruct (IH (mtf1 M j) 0 ltac:(apply mtf1_MPERM; [exact P| lia]) F ltac:(lia)) as (body & E & FB).
        exists (zflush z ++ (j + 1) :: body). rewrite E. split; [rewrite <- app_assoc; reflexivity|].
        apply Forall_app. split; [eapply Forall_impl; [| apply zflush_runs]; cbv beta; intros x Hx; lia|].
        constructor; [lia| exact FB].
  Qed.

  (* [comment removed for export] *)
  Lemma genc_runs_ok : forall us M z, MPERM n M -> Forall (fun u => 0 <= u < n) us -> 0 <= z ->
    z + Z.of_nat (length us) <= 2 ^ 20 -> runs_ok 20 0 (genc n EOB M z us).
  Proof.
    induction us as [|u us IH]; intros M z P F Hz HB.
    - rewrite genc_nil. cbn [length] in HB. apply runs_ok_block; [apply isrun_runs; apply zflush_runs| apply zflush_len; lia| | exact I].
      unfold isrun. apply Bool.orb_false_iff. split; apply Z.eqb_neq; lia.
    - apply Forall_cons_iff in F as [Fu F]. cbn [length] in HB. rewrite genc_cons. cbv zeta.
      cps_pose (mpos_found n M u P Fu) as (J1 & J2 & J3). set (j := mpos (Z.to_nat n) M u 0) in *.
      destruct (Z.eqb_spec j 0) as [J0|J0].
      + apply IH; [exact P| exact F| lia| lia].
      + apply runs_ok_block; [apply isrun_runs; apply zflush_runs| apply zflush_len; lia| |].
        * unfold isrun. apply Bool.orb_false_iff. split; apply Z.eqb_neq; lia.
        * apply IH; [apply mtf1_MPERM; [exact P| lia]| exact F| lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Shape.

(* [comment removed for export] *)
Lemma asteps_out_prefix : forall EOB xs st, exists t, a_out (asteps EOB st xs) = a_out st ++ t.
Proof.
  induction xs as [|x xs IH]; intros st.
  - exists []. rewrite app_nil_r. reflexivity.
  - rewrite asteps_cons. destruct (IH (astep EOB st x)) as [t E]. rewrite E.
    unfold astep. destruct (isrun x).
    + destruct (run_acc (a_run st)) as [es N]. cbn [a_out]. exists t. reflexivity.
    + destruct (x =? EOB); cbn [a_out]; eexists; rewrite <- !app_assoc; reflexivity.
Qed.
Lemma asteps_out_mono : forall EOB xs st, (length (a_out st) <= length (a_out (asteps EOB st xs)))%nat.
Proof. intros. destruct (asteps_out_prefix EOB xs st) as [t E]. rewrite E, length_app. lia. Qed.

(* [comment removed for export] *)
Lemma MPERM_id : forall n, MPERM n (fun k => k).
Proof. intros n. split; [intros; lia| intros; assumption]. Qed.
