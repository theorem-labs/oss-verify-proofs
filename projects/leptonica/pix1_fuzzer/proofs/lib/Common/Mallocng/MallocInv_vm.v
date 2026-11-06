(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_app : forall l1 l2 a n,
  region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof.
  intros l1 l2 a n. induction l1 as [|[b sz] l1 IH]; [reflexivity|].
  cbn [region_free app]. rewrite IH. rewrite andb_assoc. reflexivity.
Qed.

Lemma region_free_spec : forall l a n,
  region_free l a n = true <-> (forall b sz, In (b, sz) l -> u a + u n <= u b \/ u b + u sz <= u a).
Proof.
  intros l a n. induction l as [|[b sz] l IH].
  - split; [intros _ b sz [] | reflexivity].
  - split.
    + intros H b' sz' [E | Hin].
      * injection E as <- <-. destruct (region_free_cons b sz l a n H) as [H1 _]. exact H1.
      * destruct (region_free_cons b sz l a n H) as [_ H2]. exact (proj1 IH H2 b' sz' Hin).
    + intros H. cbn [region_free]. apply andb_true_iff. split.
      * apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
        destruct (H b sz ltac:(left; reflexivity)) as [H1 | H1]; [right | left]; apply Z.ltb_ge; llia.
      * apply (proj2 IH). intros b' sz' Hin. apply H. right. exact Hin.
Qed.

Lemma region_free_incl : forall l l' a n, incl l l' -> region_free l' a n = true -> region_free l a n = true.
Proof.
  intros l l' a n Hi H. apply (proj2 (region_free_spec l a n)). intros b sz Hin.
  exact (proj1 (region_free_spec l' a n) H b sz (Hi _ Hin)).
Qed.

(* [comment removed for export] *)
Lemma region_free_sub : forall l a n a' n', region_free l a n = true ->
  u a <= u a' -> u a' + u n' <= u a + u n -> region_free l a' n' = true.
Proof.
  intros l a n a' n' H H1 H2. apply (proj2 (region_free_spec l a' n')). intros b sz Hin.
  destruct (proj1 (region_free_spec l a n) H b sz Hin); llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_contains_mcov : forall l a n, map_contains l a n = true <-> mcov l (u a) (u n).
Proof.
  intros l a n. unfold map_contains, mcov. rewrite existsb_exists. split.
  - intros ([b sz] & Hin & H). cbn in H. apply andb_true_iff in H. destruct H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists b, sz. auto.
  - intros (b & sz & Hin & H1 & H2). exists (b, sz). split; [exact Hin|]. cbn.
    apply andb_true_iff. split; apply Z.leb_le; llia.
Qed.

Lemma map_has_in : forall l a n, map_has l a n = true -> In (a, n) l.
Proof.
  intros l a n H. unfold map_has in H. rewrite existsb_exists in H. destruct H as ([b sz] & Hin & H). cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. exact Hin.
Qed.

Lemma mcov_mono : forall l l' x n, incl l l' -> mcov l x n -> mcov l' x n.
Proof. intros l l' x n Hi (b & sz & Hin & H1 & H2). exists b, sz. split; [exact (Hi _ Hin) | llia]. Qed.

Lemma mcov_sub : forall l x n x' n', mcov l x n -> x <= x' -> x' + n' <= x + n -> mcov l x' n'.
Proof. intros l x n x' n' (b & sz & Hin & H1 & H2) Ha Hb. exists b, sz. split; [exact Hin | llia]. Qed.

Lemma mcov_cons : forall e l x n, mcov l x n -> mcov (e :: l) x n.
Proof. intros e l x n. apply mcov_mono. intros y Hy. right. exact Hy. Qed.

(* [comment removed for export] *)
Lemma mcov_free_disj : forall l x k a n, mcov l x k -> region_free l a n = true ->
  x + k <= u a \/ u a + u n <= x.
Proof.
  intros l x k a n (b & sz & Hin & H1 & H2) Hf.
  destruct (proj1 (region_free_spec l a n) Hf b sz Hin); llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maps_pw_in2 : forall l b1 s1 b2 s2, maps_pw l -> In (b1, s1) l -> In (b2, s2) l ->
  (b1, s1) = (b2, s2) \/ u b1 + u s1 <= u b2 \/ u b2 + u s2 <= u b1.
Proof.
  intros l. induction l as [|[a n] l IH]; intros b1 s1 b2 s2 Hpw H1 H2; [destruct H1|].
  cbn [maps_pw] in Hpw. destruct Hpw as [Hf Hpw].
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - left. rewrite <- E1, <- E2. reflexivity.
  - injection E1 as -> ->. right. destruct (proj1 (region_free_spec l b1 s1) Hf b2 s2 H2); llia.
  - injection E2 as -> ->. right. destruct (proj1 (region_free_spec l b2 s2) Hf b1 s1 H1); llia.
  - exact (IH b1 s1 b2 s2 Hpw H1 H2).
Qed.

Lemma maps_pw_cons_iff : forall a n l, maps_pw ((a, n) :: l) <-> region_free l a n = true /\ maps_pw l.
Proof. intros a n l. reflexivity. Qed.

Lemma maps_pw_filter : forall (f : word * word -> bool) l, maps_pw l -> maps_pw (List.filter f l).
Proof.
  intros f l. induction l as [|[a n] l IH]; intros H; [exact I|].
  cbn [maps_pw] in H. destruct H as [Hf Hpw]. cbn [List.filter].
  destruct (f (a, n)).
  - cbn [maps_pw]. split; [| exact (IH Hpw)]. apply (region_free_incl (List.filter f l) l); [| exact Hf].
    intros e He. apply filter_In in He. tauto.
  - exact (IH Hpw).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_map_remove : forall e l b, In e (map_remove l b) <-> In e l /\ fst e <> b.
Proof.
  intros [a n] l b. unfold map_remove. rewrite filter_In. cbn [fst].
  split; intros [H1 H2]; split; auto.
  - intros ->. rewrite (proj2 (bv_eqb_eq b b) eq_refl) in H2. discriminate H2.
  - destruct (bv_eqb a b) eqn:E; [| reflexivity]. exfalso. apply H2. apply bv_eqb_eq. exact E.
Qed.

Lemma map_remove_incl : forall l b, incl (map_remove l b) l.
Proof. intros l b e He. apply in_map_remove in He. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_in : forall b sz lo hi b' sz',
  u b + u sz <= 2^64 -> In (b', sz') (iv_subtract b sz lo hi) ->
  u b <= u b' /\ u b' + u sz' <= u b + u sz /\ (u b' + u sz' <= lo \/ hi <= u b') /\
  (0 < u sz -> 0 < u sz').
Proof.
  intros b sz lo hi b' sz' Hnw Hin. unfold iv_subtract in Hin.
  pose proof (u64_range b). pose proof (u64_range sz).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (u b <? lo) eqn:E; [| destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Ein | []]. injection Ein as <- <-.
    rewrite u_lit by llia. llia.
  - destruct (hi <? u b + u sz) eqn:E; [| destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Ein | []]. injection Ein as <- <-.
    rewrite !u_lit by llia. llia.
Qed.

Lemma iv_subtract_cover : forall b sz lo hi x k,
  u b + u sz <= 2^64 -> u b <= x -> x + k <= u b + u sz -> 0 < k ->
  (x + k <= lo \/ hi <= x) ->
  exists b' sz', In (b', sz') (iv_subtract b sz lo hi) /\ u b' <= x /\ x + k <= u b' + u sz'.
Proof.
  intros b sz lo hi x k Hnw H1 H2 Hk Hd. unfold iv_subtract.
  pose proof (u64_range b). pose proof (u64_range sz).
  destruct Hd as [Hd | Hd].
  - exists b, (Z_to_bv 64 (Z.min (u sz) (lo - u b))).
    rewrite (proj2 (Z.ltb_lt (u b) (lo))) by llia. split; [apply in_or_app; left; left; reflexivity|].
    rewrite u_lit by llia. llia.
  - exists (Z_to_bv 64 (Z.max (u b) (hi))), (Z_to_bv 64 (u b + u sz - Z.max (u b) (hi))).
    rewrite (proj2 (Z.ltb_lt (hi) (u b + u sz))) by llia. split.
    + apply in_or_app. right. left. reflexivity.
    + rewrite !u_lit by llia. llia.
Qed.

Lemma in_maps_subtract : forall l lo hi b' sz', In (b', sz') (maps_subtract l lo hi) ->
  exists b sz, In (b, sz) l /\ In (b', sz') (iv_subtract b sz lo hi).
Proof.
  intros l lo hi b' sz'. induction l as [|[b sz] l IH]; intros Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - exists b, sz. split; [left; reflexivity | exact Hin].
  - destruct (IH Hin) as (b0 & sz0 & H0 & H1). exists b0, sz0. split; [right; exact H0 | exact H1].
Qed.

Lemma maps_subtract_in_intro : forall l lo hi b sz e, In (b, sz) l -> In e (iv_subtract b sz lo hi) ->
  In e (maps_subtract l lo hi).
Proof.
  intros l lo hi b sz e. induction l as [|[b0 sz0] l IH]; intros Hin He; [destruct Hin|].
  cbn [maps_subtract]. apply in_or_app. destruct Hin as [E | Hin].
  - injection E as -> ->. left. exact He.
  - right. exact (IH Hin He).
Qed.

Definition maps_nw (l : list (word * word)) : Prop := forall b sz, In (b, sz) l -> u b + u sz <= 2^64.

(* [comment removed for export] *)
Lemma maps_subtract_cover : forall l lo hi x k, maps_nw l ->
  mcov l x k -> 0 < k -> (x + k <= lo \/ hi <= x) -> mcov (maps_subtract l lo hi) x k.
Proof.
  intros l lo hi x k Hnw (b & sz & Hin & H1 & H2) Hk Hd.
  destruct (iv_subtract_cover b sz lo hi x k (Hnw b sz Hin) H1 H2 Hk Hd) as (b' & sz' & Hin' & H1' & H2').
  exists b', sz'. split; [| llia]. eapply maps_subtract_in_intro; eauto.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_free : forall l lo hi a n, maps_nw l ->
  region_free l a n = true -> region_free (maps_subtract l lo hi) a n = true.
Proof.
  intros l lo hi a n Hnw Hf. apply (proj2 (region_free_spec _ a n)). intros b' sz' Hin.
  destruct (in_maps_subtract l lo hi b' sz' Hin) as (b & sz & H0 & H1).
  destruct (iv_subtract_in b sz lo hi b' sz' (Hnw b sz H0) H1) as (A1 & A2 & A3 & A4).
  destruct (proj1 (region_free_spec l a n) Hf b sz H0); llia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_free_self : forall l lo hi a n, maps_nw l ->
  lo <= u a -> u a + u n <= hi -> region_free (maps_subtract l lo hi) a n = true.
Proof.
  intros l lo hi a n Hnw H1 H2. apply (proj2 (region_free_spec _ a n)). intros b' sz' Hin.
  destruct (in_maps_subtract l lo hi b' sz' Hin) as (b & sz & H0 & H3).
  destruct (iv_subtract_in b sz lo hi b' sz' (Hnw b sz H0) H3) as (A1 & A2 & A3 & A4). llia.
Qed.

Lemma maps_subtract_nw : forall l lo hi, maps_nw l -> maps_nw (maps_subtract l lo hi).
Proof.
  intros l lo hi Hnw b' sz' Hin.
  destruct (in_maps_subtract l lo hi b' sz' Hin) as (b & sz & H0 & H1).
  destruct (iv_subtract_in b sz lo hi b' sz' (Hnw b sz H0) H1) as (A1 & A2 & A3 & A4). pose proof (Hnw b sz H0). llia.
Qed.

Lemma maps_subtract_pw : forall l lo hi, maps_nw l -> lo <= hi -> maps_pw l -> maps_pw (maps_subtract l lo hi).
Proof.
  intros l lo hi Hnw Hlh. induction l as [|[b sz] l IH]; intros Hpw; [exact I|].
  cbn [maps_pw] in Hpw. destruct Hpw as [Hf Hpw].
  assert (Hnw' : maps_nw l) by (intros b0 sz0 H0; apply Hnw; right; exact H0).
  assert (Hb : u b + u sz <= 2^64) by (apply Hnw; left; reflexivity).
  specialize (IH Hnw' Hpw).
  cbn [maps_subtract].
  (* [comment removed for export] *)
  assert (TL : forall b' sz', In (b', sz') (iv_subtract b sz lo hi) -> region_free (maps_subtract l lo hi) b' sz' = true).
  { intros b' sz' Hin. destruct (iv_subtract_in b sz lo hi b' sz' Hb Hin) as (A1 & A2 & A3 & A4).
    apply (region_free_sub _ b sz); [| llia | llia]. apply maps_subtract_free; assumption. }
  unfold iv_subtract in TL |- *.
  pose proof (u64_range b). pose proof (u64_range sz).
  destruct (u b <? lo) eqn:E1; destruct (hi <? u b + u sz) eqn:E2; cbn [app maps_pw].
  - apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. split; [| split; [| exact IH]].
    + cbn [region_free]. apply andb_true_iff. split.
      * apply negb_true_iff. unfold iv_overlap. rewrite !u_lit by llia. apply andb_false_iff. right. apply Z.ltb_ge. llia.
      * apply TL. apply in_or_app. left. left. reflexivity.
    + apply TL. apply in_or_app. right. left. reflexivity.
  - split; [| exact IH]. apply TL. left. reflexivity.
  - split; [| exact IH]. apply TL. left. reflexivity.
  - exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. intros l1 l2. induction l1 as [|[b sz] l1 IH]; [reflexivity|]. cbn [live_bytes app]. rewrite IH. llia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[b sz] l IH]; cbn [live_bytes]; [llia|]. pose proof (u64_range sz). llia. Qed.

Lemma live_bytes_filter : forall (f : word * word -> bool) l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
  intros f l. induction l as [|[b sz] l IH]; [cbn; llia|]. cbn [List.filter live_bytes].
  pose proof (u64_range sz). destruct (f (b, sz)); cbn [live_bytes]; llia.
Qed.

Lemma live_bytes_remove_entry : forall l b sz, In (b, sz) l -> live_bytes (map_remove l b) + u sz <= live_bytes l.
Proof.
  intros l b sz. induction l as [|[b0 sz0] l IH]; intros Hin; [destruct Hin|].
  unfold map_remove in *. cbn [List.filter live_bytes fst]. pose proof (u64_range sz0).
  destruct Hin as [E | Hin].
  - injection E as -> ->. rewrite (proj2 (bv_eqb_eq b b) eq_refl). cbn [negb].
    pose proof (live_bytes_filter (fun p : word * word => negb (bv_eqb (fst p) b)) l). llia.
  - specialize (IH Hin). destruct (negb (bv_eqb b0 b)); cbn [live_bytes]; llia.
Qed.

Lemma live_bytes_iv_subtract : forall b sz lo hi, u b + u sz <= 2^64 -> lo <= hi ->
  live_bytes (iv_subtract b sz lo hi) <= u sz.
Proof.
  intros b sz lo hi Hnw Hlh. unfold iv_subtract.
  pose proof (u64_range b). pose proof (u64_range sz).
  destruct (u b <? lo) eqn:E1; destruct (hi <? u b + u sz) eqn:E2;
    try apply Z.ltb_lt in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E1; try apply Z.ltb_ge in E2;
    cbn [app live_bytes]; rewrite ?u_lit by llia; llia.
Qed.

Lemma live_bytes_subtract : forall l lo hi, maps_nw l -> lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  intros l lo hi Hnw Hlh. induction l as [|[b sz] l IH]; [cbn; llia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract b sz lo hi ltac:(apply Hnw; left; reflexivity) Hlh).
  specialize (IH ltac:(intros b0 sz0 H0; apply Hnw; right; exact H0)). llia.
Qed.

End WithLayout.
