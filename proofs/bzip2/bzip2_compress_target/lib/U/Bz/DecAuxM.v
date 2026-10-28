(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv BzContracts DecCut DecAux.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grp_tab (r : drest) (alpha t mn : Z) : Prop :=
  exists (len lim0 base0 perm0 : Z -> Z) (mx : Z),
    (1 <= mn /\ mn <= mx <= 20)%Z /\
    (forall j, (0 <= j < alpha)%Z -> (mn <= len j <= mx)%Z) /\
    let '(lim, base, perm) := hb_create lim0 base0 perm0 len mn mx alpha in
    (forall i, (0 <= i < 258)%Z -> sv32 (r_lim r) (258 * t + i) = lim i) /\
    (forall i, (0 <= i < 258)%Z -> sv32 (r_base r) (258 * t + i) = base i) /\
    (forall i, (0 <= i < 258)%Z -> sv32 (r_perm r) (258 * t + i) = perm i) /\
    sv32 (r_minl r) t = mn.

Definition tabs_ok (r : drest) (ng alpha : Z) : Prop :=
  forall t, (0 <= t < ng)%Z -> exists mn, grp_tab r alpha t mn.

(* [comment removed for export] *)
Definition mtf_ok (r : drest) (mb : Z -> Z) : Prop := ag32s (r_mtfb r) mb 16 /\ mtf_inv mb.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wnth_app_mid : forall (pre mid post : list word) i, (0 <= i < Z.of_nat (length mid))%Z ->
  wnth (pre ++ mid ++ post) (Z.of_nat (length pre) + i) = wnth mid i.
Proof.
  intros pre mid post i Hi. unfold wnth.
  replace (Z.to_nat (Z.of_nat (length pre) + i)) with (length pre + Z.to_nat i)%nat by lia.
  rewrite app_nth2_plus. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma wnth_app_left : forall (pre rest : list word) i, (0 <= i < Z.of_nat (length pre))%Z ->
  wnth (pre ++ rest) i = wnth pre i.
Proof. intros pre rest i Hi. unfold wnth. rewrite app_nth1 by lia. reflexivity. Qed.

Lemma wnth_app_right : forall (pre rest : list word) i, (Z.of_nat (length pre) <= i)%Z ->
  wnth (pre ++ rest) i = wnth rest (i - Z.of_nat (length pre)).
Proof.
  intros pre rest i Hi. unfold wnth. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma sv32_app_mid : forall pre mid post i, (0 <= i < Z.of_nat (length mid))%Z ->
  sv32 (pre ++ mid ++ post) (Z.of_nat (length pre) + i) = sv32 mid i.
Proof. intros. unfold sv32. rewrite wnth_app_mid by assumption. reflexivity. Qed.

Lemma sv32_app_left : forall pre rest i, (0 <= i < Z.of_nat (length pre))%Z -> sv32 (pre ++ rest) i = sv32 pre i.
Proof. intros. unfold sv32. rewrite wnth_app_left by assumption. reflexivity. Qed.

Lemma sv32_app_right : forall pre rest i, (Z.of_nat (length pre) <= i)%Z ->
  sv32 (pre ++ rest) i = sv32 rest (i - Z.of_nat (length pre)).
Proof. intros. unfold sv32. rewrite wnth_app_right by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sv32_app_other : forall pre mid mid' post i,
  length mid' = length mid -> (0 <= i)%Z ->
  (i < Z.of_nat (length pre) \/ Z.of_nat (length pre) + Z.of_nat (length mid) <= i)%Z ->
  sv32 (pre ++ mid' ++ post) i = sv32 (pre ++ mid ++ post) i.
Proof.
  intros pre mid mid' post i Hl Hi Ho. destruct Ho as [Ho|Ho].
  - rewrite !sv32_app_left by lia. reflexivity.
  - rewrite !(sv32_app_right pre) by lia. rewrite !(sv32_app_right _ post) by (rewrite ?Hl; lia).
    rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uv8_window : forall (bs : list byte) (i k : nat) j, (0 <= j < Z.of_nat k)%Z ->
  uv8 (firstn k (skipn i bs)) j = uv8 bs (Z.of_nat i + j).
Proof.
  intros bs i k j Hj. unfold uv8.
  rewrite nth_firstn. replace (Z.to_nat j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma grp_tab_ext : forall r r' alpha t mn,
  (forall i, (0 <= i < 258)%Z -> sv32 (r_lim r') (258 * t + i) = sv32 (r_lim r) (258 * t + i)) ->
  (forall i, (0 <= i < 258)%Z -> sv32 (r_base r') (258 * t + i) = sv32 (r_base r) (258 * t + i)) ->
  (forall i, (0 <= i < 258)%Z -> sv32 (r_perm r') (258 * t + i) = sv32 (r_perm r) (258 * t + i)) ->
  sv32 (r_minl r') t = sv32 (r_minl r) t ->
  grp_tab r alpha t mn -> grp_tab r' alpha t mn.
Proof.
  (intros r r' alpha t mn EL EB EP EM; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G)).
  exists len, lim0, base0, perm0, mx. split; [exact Hmm|]. split; [exact Hlen|].
  destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm].
  cps_destruct G as (G1 & G2 & G3 & G4).
  repeat split.
  - intros i Hi. rewrite EL by lia. apply G1; lia.
  - intros i Hi. rewrite EB by lia. apply G2; lia.
  - intros i Hi. rewrite EP by lia. apply G3; lia.
  - rewrite EM. exact G4.
Qed.

(* [comment removed for export] *)
Lemma grp_tab_intro : forall r alpha t mn mx (len lim0 base0 perm0 : Z -> Z) (preL lws postL preB bws postB preP pws postP : list word),
  (1 <= mn /\ mn <= mx <= 20)%Z -> (forall j, (0 <= j < alpha)%Z -> (mn <= len j <= mx)%Z) ->
  r_lim r = preL ++ lws ++ postL -> r_base r = preB ++ bws ++ postB -> r_perm r = preP ++ pws ++ postP ->
  Z.of_nat (length preL) = (258 * t)%Z -> Z.of_nat (length preB) = (258 * t)%Z -> Z.of_nat (length preP) = (258 * t)%Z ->
  length lws = 258%nat -> length bws = 258%nat -> length pws = 258%nat ->
  (let '(lim, base, perm) := hb_create lim0 base0 perm0 len mn mx alpha in
   ag32s lws lim 258 /\ ag32s bws base 258 /\ ag32s pws perm 258) ->
  sv32 (r_minl r) t = mn ->
  grp_tab r alpha t mn.
Proof.
  intros r alpha t mn mx len lim0 base0 perm0 preL lws postL preB bws postB preP pws postP
         Hmm Hlen EL EB EP LL LB LP L1 L2 L3 AG EM.
  exists len, lim0, base0, perm0, mx. split; [exact Hmm|]. split; [exact Hlen|].
  destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm]. cps_destruct AG as (A1 & A2 & A3).
  repeat split.
  - intros i Hi. rewrite EL, <- LL, sv32_app_mid by lia. apply A1. lia.
  - intros i Hi. rewrite EB, <- LB, sv32_app_mid by lia. apply A2. lia.
  - intros i Hi. rewrite EP, <- LP, sv32_app_mid by lia. apply A3. lia.
  - exact EM.
Qed.

End ACeilS1.
