(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import List. Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv BzContracts. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecCut DecAux DecAuxM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)

(* [comment removed for export] *)

Definition mb_aft (mb : Z -> Z) (lno l' : Z) : Z := if (0 <=? l') && (l' <? lno) then mb l' - 1 else mb l'.
Definition mb_mid (mb : Z -> Z) (lno l l' : Z) : Z :=
  if (l <? l') && (l' <=? lno) then (if l' =? lno then mb lno else mb l' - 1)
  else (if l' =? lno then mb lno + 1 else mb l').
Definition mb_reb (mb : Z -> Z) (lno ii l' : Z) : Z := if ii <? l' then 3840 + 16 * l' else mb_aft mb lno l'.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mb_mid_top : forall mb lno l', mb_mid mb lno lno l' = (if l' =? lno then mb lno + 1 else mb l').
Proof. intros. unfold mb_mid. destruct (Z.ltb_spec lno l'), (Z.leb_spec l' lno); cbn [andb]; try reflexivity. lia. Qed.
Lemma mb_mid_bot : forall mb lno l', 1 <= lno -> 0 <= l' ->
  mb_mid mb lno 0 l' = (if l' =? 0 then mb 0 else mb_aft mb lno l').
Proof.
  intros mb lno l' Hl Hl'. unfold mb_mid, mb_aft.
  destruct (Z.eqb_spec l' 0), (Z.ltb_spec 0 l'), (Z.leb_spec l' lno), (Z.leb_spec 0 l'), (Z.ltb_spec l' lno), (Z.eqb_spec l' lno); cbn [andb]; subst; try reflexivity; try lia.
Qed.
(* [comment removed for export] *)
Lemma mb_mid_step : forall mb lno l, 1 <= l <= lno ->
  forall l', mb_mid mb lno (l - 1) l' = zfupd (mb_mid mb lno l) l (mb_mid mb lno l l - 1) l'.
Proof.
  intros mb lno l Hl l'. rewrite zfupd_eq. unfold mb_mid. rewrite (Z.ltb_irrefl l). cbn [andb].
  destruct (Z.eqb_spec l' l), (Z.ltb_spec (l - 1) l'), (Z.leb_spec l' lno), (Z.eqb_spec l' lno), (Z.ltb_spec l l'), (Z.eqb_spec l lno); cbn [andb]; subst; try reflexivity; try lia.
Qed.
Lemma mb_mid_val : forall mb lno l, 1 <= l <= lno -> mb_mid mb lno l l = (if l =? lno then mb lno + 1 else mb l).
Proof. intros. unfold mb_mid. rewrite (Z.ltb_irrefl l). cbn [andb]. reflexivity. Qed.
Lemma mb_mid_below : forall mb lno l l', 1 <= l <= lno -> l' < l -> mb_mid mb lno l l' = mb l'.
Proof. intros. unfold mb_mid. destruct (Z.ltb_spec l l'); [lia|]. cbn [andb]. destruct (Z.eqb_spec l' lno); [lia| reflexivity]. Qed.
(* [comment removed for export] *)
Lemma mb_aft_of_mid : forall mb lno, 1 <= lno -> forall l', 0 <= l' -> mb_aft mb lno l' = zfupd (mb_mid mb lno 0) 0 (mb_mid mb lno 0 0 - 1) l'.
Proof.
  intros mb lno Hl l' Hl'. rewrite zfupd_eq. rewrite !mb_mid_bot by lia. cbn [Z.eqb].
  destruct (Z.eqb_spec l' 0); [| reflexivity]. subst. unfold mb_aft. cbn [Z.leb]. destruct (Z.ltb_spec 0 lno); [reflexivity| lia].
Qed.
(* [comment removed for export] *)
Lemma mb_reb_step : forall mb lno ii, 0 <= ii -> forall l', mb_reb mb lno (ii - 1) l' = zfupd (mb_reb mb lno ii) ii (3840 + 16 * ii) l'.
Proof.
  intros mb lno ii Hii l'. rewrite zfupd_eq. unfold mb_reb.
  destruct (Z.eqb_spec l' ii), (Z.ltb_spec (ii - 1) l'), (Z.ltb_spec ii l'); subst; try reflexivity; lia.
Qed.
Lemma mb_reb_top : forall mb lno l', l' <= 15 -> mb_reb mb lno 15 l' = mb_aft mb lno l'.
Proof. intros. unfold mb_reb. destruct (Z.ltb_spec 15 l'); [lia| reflexivity]. Qed.
Lemma mb_reb_home : forall mb lno, mtf_home (mb_reb mb lno (-1)).
Proof. intros mb lno l Hl. unfold mb_reb. destruct (Z.ltb_spec (-1) l); [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Section Bounds.
  Variables (mb : Z -> Z) (lno : Z).
  Hypothesis INV : mtf_inv mb.
  Hypothesis Hl : 1 <= lno <= 15.
  Lemma mbr : forall l, 0 <= l < 16 -> 1 + 16 * l <= mb l <= 4080 - 16 * (15 - l).
  Proof. apply mtf_inv_bounds. exact INV. Qed.
  Lemma mb_aft_range : forall l, 0 <= l < 16 -> 16 * l <= mb_aft mb lno l <= 4080 - 16 * (15 - l).
  Proof. intros l H. unfold mb_aft. pose proof (mbr l H). destruct (Z.leb_spec 0 l), (Z.ltb_spec l lno); cbn [andb]; lia. Qed.
  Lemma mb_mid_range : forall l l', 0 <= l <= lno -> 0 <= l' < 16 -> 16 * l' <= mb_mid mb lno l l' <= 4081 - 16 * (15 - l').
  Proof.
    intros l l' H H'. unfold mb_mid. pose proof (mbr l' H'). pose proof (mbr lno ltac:(lia)).
    destruct (Z.ltb_spec l l'), (Z.leb_spec l' lno), (Z.eqb_spec l' lno); cbn [andb]; subst; lia.
  Qed.
  Lemma mb_reb_range : forall ii l', -1 <= ii <= 15 -> 0 <= l' < 16 -> 16 * l' <= mb_reb mb lno ii l' <= 4080 - 16 * (15 - l').
  Proof. intros ii l' H H'. unfold mb_reb. pose proof (mb_aft_range l' H'). destruct (Z.ltb_spec ii l'); lia. Qed.
  Lemma mb_aft_inv : 1 <= mb_aft mb lno 0 -> mtf_inv (mb_aft mb lno).
  Proof.
    intros H0. cps_destruct INV as (I1 & I2 & I3). unfold mtf_inv, mb_aft in *. split; [exact H0|]. split.
    - intros l H. pose proof (I2 l H).
      destruct (Z.leb_spec 0 l), (Z.ltb_spec l lno), (Z.leb_spec 0 (l + 1)), (Z.ltb_spec (l + 1) lno); cbn [andb]; lia.
    - destruct (Z.leb_spec 0 15), (Z.ltb_spec 15 lno); cbn [andb]; lia.
  Qed.
End Bounds.

End ACeilS1.
