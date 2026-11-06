(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Permutation.
From stdpp Require Import base decidable list.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qu X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
Import ListNotations.

Lemma bp_eqb_refl : forall p : bptr, bptr_eqb p p = true.
Proof.
intros [i o]. unfold bptr_eqb; cbn [fst snd]. rewrite Z.eqb_refl, andb_true_r.
unfold aptr_eqb. destruct i; cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity.
Qed.

Lemma bp_eqb_eq : forall p q : bptr, bptr_eqb p q = true -> p = q.
Proof.
intros [i o] [i' o'] E. unfold bptr_eqb in E; cbn [fst snd] in E. apply andb_prop in E. destruct E as [E1 E2].
apply Z.eqb_eq in E2. unfold aptr_eqb in E1. apply andb_prop in E1. destruct E1 as [E3 E4].
apply N.eqb_eq in E3. apply Z.eqb_eq in E4. destruct i, i'; cbn in *; subst; reflexivity.
Qed.

Lemma bp_eqb_neq : forall p q : bptr, p <> q -> bptr_eqb p q = false.
Proof. intros p q NE. destruct (bptr_eqb p q) eqn:E; [|reflexivity]. exfalso. exact (NE (bp_eqb_eq _ _ E)). Qed.

Lemma lbr_cons : forall p b L, lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then lb_remove p L else b :: lb_remove p L.
Proof.
intros. unfold lb_remove. cbn. destruct (bptr_eqb (blk_id b) p); cbn;
[destruct (decide False) as [X|X]; [destruct X| reflexivity] | destruct (decide True) as [X|X]; [reflexivity| exfalso; exact (X I)]].
Qed.

Lemma lbr_nil : forall p, lb_remove p [] = [].
Proof. reflexivity. Qed.

Lemma lbr_app : forall p l1 l2, lb_remove p (l1 ++ l2) = lb_remove p l1 ++ lb_remove p l2.
Proof. intros. induction l1 as [|b l1 IH]; [reflexivity|]. cbn [app]. rewrite !lbr_cons, IH. destruct (bptr_eqb (blk_id b) p); reflexivity. Qed.

Lemma lbr_hd_same : forall p A n L, lb_remove p ((p, A, n) :: L) = lb_remove p L.
Proof. intros. rewrite lbr_cons. unfold blk_id; cbn [fst]. rewrite bp_eqb_refl. reflexivity. Qed.

Lemma lbr_hd_other : forall p b L, blk_id b <> p -> lb_remove p (b :: L) = b :: lb_remove p L.
Proof. intros p b L NE. rewrite lbr_cons, (bp_eqb_neq _ _ NE). reflexivity. Qed.

Lemma lbr_notin : forall p L, ~ In p (map blk_id L) -> lb_remove p L = L.
Proof.
intros p L NI. induction L as [|b L IH]; [reflexivity|]. rewrite lbr_cons.
destruct (bptr_eqb (blk_id b) p) eqn:E.
- exfalso. apply NI. left. exact (bp_eqb_eq _ _ E).
- f_equal. apply IH. intros H. apply NI. right. exact H.
Qed.

Lemma lbr_other : forall p L, (forall b, In b L -> blk_id b <> p) -> lb_remove p L = L.
Proof.
intros p L H. apply lbr_notin. intros HI. apply in_map_iff in HI. destruct HI as (b & E & Hb). exact (H b Hb E).
Qed.

Lemma lbr_comm : forall p q L, lb_remove p (lb_remove q L) = lb_remove q (lb_remove p L).
Proof.
intros p q L. induction L as [|b L IH]; [reflexivity|]. rewrite !lbr_cons.
destruct (bptr_eqb (blk_id b) q) eqn:Eq, (bptr_eqb (blk_id b) p) eqn:Ep; rewrite ?lbr_cons, ?Eq, ?Ep, IH; reflexivity.
Qed.

Lemma lbr_idem : forall p L, lb_remove p (lb_remove p L) = lb_remove p L.
Proof.
intros p L. induction L as [|b L IH]; [reflexivity|]. rewrite !lbr_cons.
destruct (bptr_eqb (blk_id b) p) eqn:Ep; rewrite ?lbr_cons, ?Ep, IH; reflexivity.
Qed.

Lemma lbr_in : forall p L b, In b (lb_remove p L) <-> In b L /\ blk_id b <> p.
Proof.
intros p L b. induction L as [|x L IH]; [cbn; tauto|]. rewrite lbr_cons.
destruct (bptr_eqb (blk_id x) p) eqn:E.
- rewrite IH. cbn. split; [tauto|]. intros [[->|H] NE]; [| tauto]. exfalso. exact (NE (bp_eqb_eq _ _ E)).
- cbn. rewrite IH. split; [| tauto]. intros [->|H]; [| tauto]. split; [left; reflexivity|].
intros X. rewrite X, bp_eqb_refl in E. discriminate E.
Qed.

Lemma ids_lbr_notin : forall p L, ~ In p (map blk_id (lb_remove p L)).
Proof.
intros p L H. apply in_map_iff in H. destruct H as (b & E & Hb). apply lbr_in in Hb. destruct Hb as [_ NE]. exact (NE E).
Qed.

Lemma nodup_ids_lbr : forall p L, List.NoDup (map blk_id L) -> List.NoDup (map blk_id (lb_remove p L)).
Proof.
intros p L ND. induction L as [|b L IH]; [constructor|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
rewrite lbr_cons. destruct (bptr_eqb (blk_id b) p); [exact (IH ND')|]. cbn. constructor; [| exact (IH ND')].
intros H. apply NI. apply in_map_iff in H. destruct H as (b' & E & Hb'). apply lbr_in in Hb'. destruct Hb' as [Hb' _].
rewrite <- E. apply in_map. exact Hb'.
Qed.

Lemma perm_lbr : forall p (l l' : list block), Permutation l l' -> Permutation (lb_remove p l) (lb_remove p l').
Proof.
intros p l l' P. induction P as [|x l l' P IH| x y l| l l' l'' P1 IH1 P2 IH2].
- apply Permutation_refl.
- rewrite !lbr_cons. destruct (bptr_eqb (blk_id x) p); [exact IH| apply perm_skip; exact IH].
- rewrite !lbr_cons. destruct (bptr_eqb (blk_id y) p), (bptr_eqb (blk_id x) p); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eauto.
Qed.

Lemma nodup_ids_perm' : forall LB L, Permutation LB L -> List.NoDup (map blk_id LB) -> List.NoDup (map blk_id L).
Proof. intros LB L P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma perm_hd_lbr : forall (p : bptr) (A n : Z) (L : list block),
List.NoDup (map blk_id L) -> In (p, A, n) L -> Permutation L ((p, A, n) :: lb_remove p L).
Proof.
intros p A n L ND HIN. apply in_split in HIN. destruct HIN as (l1 & l2 & ->).
rewrite map_app in ND. cbn in ND. pose proof (NoDup_remove _ _ _ ND) as [ND12 NI]. rewrite <- map_app in NI.
rewrite lbr_app, lbr_hd_same.
rewrite (lbr_notin p l1) by (intros H; apply NI; rewrite map_app; apply in_app_iff; left; exact H).
rewrite (lbr_notin p l2) by (intros H; apply NI; rewrite map_app; apply in_app_iff; right; exact H).
apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma lbr_fresh_hd : forall (q : bptr) (A n : Z) (L : list block),
List.NoDup (map blk_id ((q, A, n) :: L)) -> lb_remove q ((q, A, n) :: L) = L.
Proof.
intros q A n L ND. rewrite lbr_hd_same. apply lbr_notin. cbn in ND. inversion ND; subst. assumption.
Qed.

Lemma perm_hd3_lbr : forall (p1 p2 p3 : bptr) (A1 n1 A2 n2 A3 n3 : Z) (L : list block),
List.NoDup (map blk_id L) -> In (p1, A1, n1) L -> In (p2, A2, n2) L -> In (p3, A3, n3) L ->
p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
Permutation L ((p1, A1, n1) :: (p2, A2, n2) :: (p3, A3, n3) :: lb_remove p3 (lb_remove p2 (lb_remove p1 L))).
Proof.
intros p1 p2 p3 A1 n1 A2 n2 A3 n3 L ND H1 H2 H3 N12 N13 N23.
eapply Permutation_trans; [apply (perm_hd_lbr p1 A1 n1 L ND H1)|]. apply perm_skip.
assert (ND1 : List.NoDup (map blk_id (lb_remove p1 L))) by (apply nodup_ids_lbr; exact ND).
assert (H2' : In (p2, A2, n2) (lb_remove p1 L)) by (apply lbr_in; split; [exact H2| cbn; congruence]).
eapply Permutation_trans; [apply (perm_hd_lbr p2 A2 n2 _ ND1 H2')|]. apply perm_skip.
assert (ND2 : List.NoDup (map blk_id (lb_remove p2 (lb_remove p1 L)))) by (apply nodup_ids_lbr; exact ND1).
assert (H3' : In (p3, A3, n3) (lb_remove p2 (lb_remove p1 L))) by (apply lbr_in; split; [apply lbr_in; split; [exact H3| cbn; congruence]| cbn; congruence]).
apply (perm_hd_lbr p3 A3 n3 _ ND2 H3').
Qed.

Lemma lbr_hd_fresh : forall (p : bptr) (A n : Z) (K : list block),
(forall b, In b K -> blk_id b <> p) -> lb_remove p ((p, A, n) :: K) = K.
Proof. intros p A n K FR. rewrite lbr_hd_same. apply lbr_other. exact FR. Qed.

Lemma lbr_hd1_of3 : forall (p1 p2 p3 : bptr) (A1 n1 A2 n2 A3 n3 : Z) (K : list block),
p1 <> p2 -> p1 <> p3 -> (forall b, In b K -> blk_id b <> p1) ->
lb_remove p1 ((p1, A1, n1) :: (p2, A2, n2) :: (p3, A3, n3) :: K) = (p2, A2, n2) :: (p3, A3, n3) :: K.
Proof.
intros p1 p2 p3 A1 n1 A2 n2 A3 n3 K N12 N13 FR.
rewrite lbr_hd_same. rewrite lbr_hd_other by (cbn; congruence). rewrite lbr_hd_other by (cbn; congruence).
rewrite (lbr_other p1 K FR). reflexivity.
Qed.

Lemma lbr_hd3 : forall (p1 p2 p3 : bptr) (A1 n1 A2 n2 A3 n3 : Z) (K : list block),
p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
(forall b, In b K -> blk_id b <> p1) -> (forall b, In b K -> blk_id b <> p2) -> (forall b, In b K -> blk_id b <> p3) ->
lb_remove p3 (lb_remove p2 (lb_remove p1 ((p1, A1, n1) :: (p2, A2, n2) :: (p3, A3, n3) :: K))) = K.
Proof.
intros p1 p2 p3 A1 n1 A2 n2 A3 n3 K N12 N13 N23 F1 F2 F3.
rewrite (lbr_hd1_of3 p1 p2 p3) by assumption.
rewrite lbr_hd_same. rewrite lbr_hd_other by (cbn; congruence). rewrite (lbr_other p2 K F2).
apply lbr_hd_fresh. exact F3.
Qed.
