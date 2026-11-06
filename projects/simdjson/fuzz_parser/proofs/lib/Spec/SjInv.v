(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record S1OUT (data idxs : list Z) (n : Z) : Prop := {
  s1_n : 1 <= n <= zlength data;
  s1_len : n + 3 <= zlength idxs;
  s1_lt : forall k, 0 <= k < n -> 0 <= znth idxs k < zlength data;
  s1_inc : forall k, 0 <= k < n - 1 -> znth idxs k < znth idxs (k + 1);
  s1_sent : znth idxs n = zlength data /\ znth idxs (n + 1) = zlength data /\ znth idxs (n + 2) = 0;
  s1_str : forall k, 0 <= k < n -> byte_at data (znth idxs k) = 34 ->
           exists j, bpath data (zlength data) (znth idxs k + 1) j /\ j < znth idxs (k + 1)
}.

(* [comment removed for export] *)
Lemma znth_app_l : forall l1 l2 k, 0 <= k < zlength l1 -> znth (l1 ++ l2) k = znth l1 k.
Proof.
  intros l1 l2 k H. unfold znth, zlength in *. destruct (Z.ltb_spec k 0); [lia|]. apply app_nth1. lia.
Qed.
Lemma znth_app_r : forall l1 l2 k, zlength l1 <= k -> znth (l1 ++ l2) k = znth l2 (k - zlength l1).
Proof.
  intros l1 l2 k H. unfold znth, zlength in *. destruct (Z.ltb_spec k 0); [lia|]. destruct (Z.ltb_spec (k - Z.of_nat (length l1)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma zlength_app : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_rev : forall (l : list Z), zlength (rev l) = zlength l.
Proof. intros. unfold zlength. rewrite length_rev. reflexivity. Qed.
Lemma zlength_cons : forall (x : Z) l, zlength (x :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.
Lemma zlength_nonneg : forall (l : list Z), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.
Lemma znth_last : forall l x, znth (l ++ [x]) (zlength l) = x.
Proof. intros l x. rewrite znth_app_r by lia. replace (zlength l - zlength l) with 0 by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sdesc (l : list Z) : Prop :=
  match l with
  | x :: ((y :: _) as r) => y < x /\ sdesc r
  | _ => True
  end.
(* [comment removed for export] *)
Fixpoint strs_okR (data : list Z) (len : Z) (acc : list Z) (b : Z) : Prop :=
  match acc with
  | [] => True
  | x :: r => (byte_at data x = 34 -> exists j, bpath data len (x + 1) j /\ j < b) /\ strs_okR data len r x
  end.

Lemma sdesc_all : forall l x, sdesc (x :: l) -> forall y, In y l -> y < x.
Proof.
  induction l as [|z l IH]; intros x H y Hy; [destruct Hy|]. cbn in H. destruct H as [Hz Hs].
  destruct Hy as [<-|Hy]; [exact Hz|]. specialize (IH z Hs y Hy). lia.
Qed.

Lemma sdesc_length : forall l b, 0 <= b -> sdesc l -> (forall x, In x l -> 0 <= x < b) -> zlength l <= b.
Proof.
  induction l as [|x l IH]; intros b H0 Hs Hb; [unfold zlength; cbn; lia|].
  rewrite zlength_cons. assert (Hx : 0 <= x < b) by (apply Hb; left; reflexivity).
  assert (Hl : zlength l <= x).
  { apply IH; [lia| destruct l; [exact I| exact (proj2 Hs)]|]. intros y Hy. split; [apply Hb; right; exact Hy|]. exact (sdesc_all l x Hs y Hy). }
  lia.
Qed.

Lemma strs_okR_mono : forall data len acc b b', strs_okR data len acc b -> b <= b' -> strs_okR data len acc b'.
Proof.
  intros data len [|x r] b b' H Hb; [exact I|]. cbn in *. destruct H as [H1 H2]. split; [|exact H2].
  intros E. destruct (H1 E) as (j & P & J). exists j. split; [exact P| lia].
Qed.

Lemma strs_okR_len : forall data len acc b, strs_okR data len acc b -> strs_okR data len acc len.
Proof.
  intros data len [|x r] b H; [exact I|]. cbn in *. destruct H as [H1 H2]. split; [|exact H2].
  intros E. destruct (H1 E) as (j & P & J). exists j. split; [exact P|]. apply bpath_bound in P. lia.
Qed.

(* [comment removed for export] *)
Definition sinv (data : list Z) (len i : Z) (acc : list Z) : Prop :=
  0 <= i /\ (forall x, In x acc -> 0 <= x < len /\ x < i) /\ sdesc acc /\ strs_okR data len acc i.

Lemma sinv_push : forall data len i acc i',
  sinv data len i acc -> i < len -> i < i' -> (byte_at data i = 34 -> exists j, bpath data len (i + 1) j /\ j < i') ->
  sinv data len i' (i :: acc).
Proof.
  intros data len i acc i' (H0 & Hx & Hs & Hk) Hl Hi Hq. split; [lia|]. split; [|split].
  - intros x [<-|Hin]; [lia|]. destruct (Hx x Hin). lia.
  - destruct acc as [|y r]; [exact I|]. split; [destruct (Hx y (or_introl eq_refl)); lia| exact Hs].
  - cbn [strs_okR]. split; [exact Hq| exact Hk].
Qed.

Lemma sinv_skip : forall data len i acc i', sinv data len i acc -> i <= i' -> sinv data len i' acc.
Proof.
  intros data len i acc i' (H0 & Hx & Hs & Hk) Hi. split; [lia|]. split; [|split; [exact Hs|]].
  - intros x Hin. destruct (Hx x Hin). lia.
  - eapply strs_okR_mono; eassumption.
Qed.

Lemma scan_from_sinv : forall f data i acc err uncl,
  let len := zlength data in
  sinv data len i acc ->
  match scan_from f data len i acc err uncl with
  | (acc', err', uncl') => uncl' = false ->
      uncl = false /\ (forall x, In x acc' -> 0 <= x < len) /\ sdesc acc' /\ strs_okR data len acc' len
  end.
Proof.
  induction f as [|f IH]; intros data i acc err uncl len HI; cbn [scan_from].
  { intros ->. destruct HI as (H0 & Hx & Hs & Hk). split; [reflexivity|]. split; [intros x Hin; apply Hx; exact Hin|].
    split; [exact Hs| eapply strs_okR_len; exact Hk]. }
  destruct (len <=? i) eqn:EL.
  { intros ->. destruct HI as (H0 & Hx & Hs & Hk). split; [reflexivity|]. split; [intros x Hin; apply Hx; exact Hin|].
    split; [exact Hs| eapply strs_okR_len; exact Hk]. }
  apply Z.leb_gt in EL.
  destruct (is_space (byte_at data i)).
  { apply IH. eapply sinv_skip; [exact HI| lia]. }
  destruct (byte_at data i =? 34) eqn:EQ.
  - destruct (vstring (S (Z.to_nat len)) data len (i + 1) err) as [[j|] e] eqn:EV.
    + pose proof (vstring_some_bound _ _ _ _ _ _ _ EV) as VB.
      pose proof (vstring_bpath (S (Z.to_nat len)) data (i + 1) err j e ltac:(destruct HI; lia) EV) as BP.
      apply IH. apply sinv_push; [exact HI| exact EL| lia|]. intros _. exists j. split; [exact BP| lia].
    + intros; discriminate.
  - apply Z.eqb_neq in EQ.
    destruct (is_op (byte_at data i)).
    + apply IH. apply sinv_push; [exact HI| exact EL| lia|]. intros E; contradiction.
    + pose proof (prim_end_ge (Z.to_nat len) data len i). apply IH. apply sinv_push; [exact HI| exact EL| lia|]. intros E; contradiction.
Qed.

(* [comment removed for export] *)
Lemma sdesc_fwd : forall acc, sdesc acc -> forall k, 0 <= k < zlength acc - 1 -> znth (rev acc) k < znth (rev acc) (k + 1).
Proof.
  induction acc as [|x r IH]; intros Hs k Hk; [unfold zlength in Hk; cbn in Hk; lia|].
  rewrite zlength_cons in Hk. cbn [rev].
  destruct (Z_lt_ge_dec (k + 1) (zlength r)) as [L|G].
  - rewrite !znth_app_l by (rewrite zlength_rev; lia). apply IH; [destruct r; [exact I| exact (proj2 Hs)]| lia].
  - assert (E : k + 1 = zlength r) by lia. rewrite E. rewrite <- (zlength_rev r). rewrite znth_last.
    rewrite znth_app_l by (rewrite zlength_rev; lia).
    destruct r as [|y r']; [unfold zlength in E; cbn in E; lia|].
    assert (Hin : In (znth (rev (y :: r')) k) (y :: r')) by (apply in_rev, znth_range; rewrite zlength_rev; lia).
    exact (sdesc_all (y :: r') x Hs _ Hin).
Qed.

Lemma strs_fwd : forall data len acc b, strs_okR data len acc b ->
  forall k, 0 <= k < zlength acc -> byte_at data (znth (rev acc) k) = 34 ->
  exists j, bpath data len (znth (rev acc) k + 1) j /\ j < znth (rev acc ++ [b]) (k + 1).
Proof.
  induction acc as [|x r IH]; intros b H k Hk Hb; [unfold zlength in Hk; cbn in Hk; lia|].
  rewrite zlength_cons in Hk. cbn [rev] in *. cbn [strs_okR] in H. destruct H as [H1 H2].
  destruct (Z_lt_ge_dec k (zlength r)) as [L|G].
  - rewrite znth_app_l in Hb by (rewrite zlength_rev; lia). rewrite znth_app_l by (rewrite zlength_rev; lia).
    rewrite <- app_assoc. cbn [app].
    destruct (IH x H2 k ltac:(lia) Hb) as (j & P & J). exists j. split; [exact P|].
    destruct (Z_lt_ge_dec (k + 1) (zlength r)) as [L'|G'].
    + rewrite znth_app_l in J |- * by (rewrite zlength_rev; lia). exact J.
    + assert (E : k + 1 = zlength r) by lia. rewrite E in J |- *. rewrite <- zlength_rev in J |- *.
      rewrite znth_last in J. rewrite znth_app_r by lia. replace (zlength (rev r) - zlength (rev r)) with 0 by lia. exact J.
  - assert (E : k = zlength r) by lia. subst k.
    rewrite <- (zlength_rev r) in Hb |- *. rewrite znth_last in Hb |- *.
    destruct (H1 Hb) as (j & P & J). exists j. split; [exact P|].
    rewrite <- app_assoc. cbn [app]. rewrite znth_app_r by lia.
    replace (zlength (rev r) + 1 - zlength (rev r)) with 1 by lia. exact J.
Qed.

(* [comment removed for export] *)
Theorem scan_S1OUT : forall data l, scan data = (true, l) ->
  S1OUT data (l ++ [zlength data; zlength data; 0]) (zlength l).
Proof.
  intros data l H. unfold scan in H.
  pose proof (scan_from_sinv (S (length data)) data 0 [] false false) as SI.
  cbv zeta in SI. change (Z.of_nat (length data)) with (zlength data) in H.
  destruct (scan_from (S (length data)) data (zlength data) 0 [] false false) as [[acc err] uncl] eqn:E.
  inversion H as [[Hok Hl]]. clear H.
  assert (Hu : uncl = false) by (destruct uncl; [rewrite !andb_false_r in Hok; discriminate| reflexivity]).
  assert (Hne : acc <> []) by (intros ->; discriminate Hok).
  destruct (SI ltac:(split; [lia| split; [intros x []| split; exact I]]) Hu) as (_ & Hb & Hs & Hstr). clear SI.
  assert (N1 : 1 <= zlength acc) by (destruct acc; [contradiction| rewrite zlength_cons; pose proof (zlength_nonneg acc); lia]).
  assert (N2 : zlength acc <= zlength data) by (apply sdesc_length; [apply zlength_nonneg| exact Hs| exact Hb]).
  subst l. pose proof (zlength_rev acc) as ZR.
  constructor.
  - lia.
  - rewrite zlength_app. change (zlength [zlength data; zlength data; 0]) with 3. lia.
  - intros k Hk. rewrite znth_app_l by lia. apply Hb. apply in_rev, znth_range. lia.
  - intros k Hk. rewrite !znth_app_l by lia. apply sdesc_fwd; [exact Hs| lia].
  - split; [|split].
    + rewrite znth_app_r by lia. replace (zlength (rev acc) - zlength (rev acc)) with 0 by lia. reflexivity.
    + rewrite znth_app_r by lia. replace (zlength (rev acc) + 1 - zlength (rev acc)) with 1 by lia. reflexivity.
    + rewrite znth_app_r by lia. replace (zlength (rev acc) + 2 - zlength (rev acc)) with 2 by lia. reflexivity.
  - intros k Hk Hq. rewrite znth_app_l in Hq by lia. rewrite znth_app_l by lia.
    destruct (strs_fwd data (zlength data) acc (zlength data) Hstr k ltac:(lia) Hq) as (j & P & J).
    exists j. split; [exact P|].
    destruct (Z_lt_ge_dec (k + 1) (zlength (rev acc))) as [L|G].
    + rewrite znth_app_l in J by lia. rewrite znth_app_l by lia. exact J.
    + assert (Ek : k + 1 = zlength (rev acc)) by lia. rewrite Ek in J |- *. rewrite znth_last in J.
      rewrite znth_app_r by lia. replace (zlength (rev acc) - zlength (rev acc)) with 0 by lia. exact J.
Qed.
