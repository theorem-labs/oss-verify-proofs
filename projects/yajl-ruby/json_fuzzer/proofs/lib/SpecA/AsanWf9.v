(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WF.
Variable E : aenv.
Variable P : list Z.
Local Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
Definition items_live (s : astate) (l : list Z) : Prop :=
  forall x, In x l -> exists cm i j, as_chunks s !! x = Some cm /\ cm_state cm = CQuarantined i j.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma recycle_items_spec : forall D s0 b l,
  AWf E P D s0 -> In b D -> incl l (b_items b) -> List.NoDup l -> items_live s0 l ->
  hoare (fun s => s = s0) (recycle_items E l)
    (fun s' _ => AWf E P D s' /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0
                 /\ (forall x, ~ In x l -> as_chunks s' !! x = as_chunks s0 !! x)
                 /\ (forall x, In x l -> as_chunks s' !! x = None)).
Proof.
  intros D s0 b l. revert s0. induction l as [|m rest IH]; intros s0 WF HbD INCL ND LIVE.
  - cbn. apply hoare_ret. intros s ->. split; [exact WF|]. split; [reflexivity|]. split; [reflexivity|]. split; [auto|]. intros x [].
  - cbn. inversion ND as [|? ? NI ND']; subst.
    destruct (LIVE m (or_introl eq_refl)) as (cm & i & j & Hcm & ST).
    assert (NIN : forall b', In b' (as_tq s0 ++ as_gq s0) -> ~ In m (b_items b')).
    { intros b' Hb' Hin. destruct WF as (_ & _ & _ & _ & (Q1 & QD & Q2 & Q3) & _).
      assert (A1 : In b' (all_batches D s0)) by (unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb').
      assert (A2 : In b (all_batches D s0)) by (unfold all_batches; apply in_app_iff; right; apply in_app_iff; right; exact HbD).
      pose proof (Q3 b' b m A1 A2 Hin (INCL m (or_introl eq_refl))) as ->.
      unfold all_batches in Q2. rewrite app_assoc, map_app in Q2.
      apply NoDup_app_remove_r in Q2 as ND1 || pose proof Q2 as ND1.
      (* [comment removed for export] *)
      assert (X : In (b_addr b) (map b_addr (as_tq s0 ++ as_gq s0))) by (apply in_map; exact Hb').
      assert (Y : In (b_addr b) (map b_addr D)) by (apply in_map; exact HbD).
      clear -Q2 X Y. induction (as_tq s0 ++ as_gq s0) as [|c k IHk]; [destruct X|].
      cbn in Q2. inversion Q2 as [|? ? NI2 ND2]; subst. destruct X as [EQ|X].
      + apply NI2. rewrite EQ. apply in_app_iff. right. exact Y.
      + exact (IHk ND2 X). }
    eapply hoare_bind; [apply (qcb_recycle_spec E P D s0 m cm i j WF Hcm ST NIN)|].
    intros []. apply hoare_pre. intros s1 (WF1 & HK1 & HT1 & HG1).
    eapply hoare_conseq; [apply (IH s1 WF1 HbD)| auto|].
    + intros x Hx. apply INCL. right; exact Hx.
    + exact ND'.
    + intros x Hx. destruct (LIVE x (or_intror Hx)) as (cm' & i' & j' & H' & ST'). exists cm', i', j'.
      rewrite HK1, lookup_delete_ne by (intros ->; exact (NI Hx)). auto.
    + cbn beta. intros s [] (WF2 & HT2 & HG2 & SAME & GONE). split; [exact WF2|]. split; [congruence|]. split; [congruence|]. split.
      * intros x Hx. rewrite SAME by (intros X; apply Hx; right; exact X). rewrite HK1, lookup_delete_ne by (intros ->; apply Hx; left; reflexivity). reflexivity.
      * intros x [<-|Hx]; [| exact (GONE x Hx)].
        destruct (in_dec Z.eq_dec m rest) as [Hin|Hnin]; [exact (GONE m Hin)|].
        rewrite SAME by exact Hnin. rewrite HK1. apply lookup_delete_eq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AWf_perm_D : forall D D' s, Permutation D D' -> AWf E P D s -> AWf E P D' s.
Proof.
  intros D D' s PD WF.
  assert (PERMA : Permutation (all_batches D' s) (all_batches D s)).
  { unfold all_batches. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact PD. }
  assert (INA : forall b, In b (all_batches D' s) <-> In b (all_batches D s)).
  { intros b; split; intros H; [eapply Permutation_in; [exact PERMA| exact H]| eapply Permutation_in; [apply Permutation_sym; exact PERMA| exact H]]. }
  assert (IB : forall a, is_batch D' s a <-> is_batch D s a).
  { intros a. unfold is_batch. split; intros (b & Hb & X); exists b; split; [apply INA; exact Hb| exact X| apply INA; exact Hb| exact X]. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  split; [exact WE|]. split; [exact WR|]. split; [exact WC|]. split; [|split; [|split; [exact WS| exact WD]]].
  - split; [| exact K2]. intros cb cm H. destruct (K1 _ _ H) as (A & B & C & D0 & E0).
    unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    + destruct (cm_prim cm) as [c|]; [| exact D0]. destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
      repeat (split; [assumption|]). intros X. apply D6. apply IB. exact X.
    + destruct (cm_state cm); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
      destruct E3 as [E3|(b & Hb & X)]; [left; exact E3| right; exists b; split; [apply INA; exact Hb| exact X]].
  - unfold wf_quarantine. split; [|split; [|split]].
    + intros b Hb. exact (Q1 b Hb).
    + intros b Hb. apply QD. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hb].
    + eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERMA| exact Q2].
    + intros b1 b2 x H1 H2. apply INA in H1. apply INA in H2. exact (Q3 b1 b2 x H1 H2).
Qed.

Lemma AWf_drop_dbatch : forall R s b,
  AWf E P (b :: R) s -> (forall x, In x (b_items b) -> as_chunks s !! x = None) ->
  AWf E P R s /\ avail E R s kBatchClass (b_addr b).
Proof.
  intros R s b WF GONE.
  assert (SUB : forall x, In x (all_batches R s) -> In x (all_batches (b :: R) s)).
  { intros x. unfold all_batches. rewrite !in_app_iff. cbn. tauto. }
  assert (IBs : forall a, is_batch R s a -> is_batch (b :: R) s a).
  { intros a (x & Hx & X). exists x. split; [apply SUB; exact Hx| exact X]. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  assert (ND : List.NoDup (map b_addr (all_batches R s)) /\ ~ In (b_addr b) (map b_addr (all_batches R s))).
  { unfold all_batches in *. rewrite app_assoc in Q2 |- *. rewrite map_app in Q2 |- *. cbn in Q2.
    exact (NoDup_remove _ _ _ Q2). }
  destruct ND as [ND NB].
  split.
  - split; [exact WE|]. split; [exact WR|]. split; [exact WC|]. split; [|split; [|split; [exact WS| exact WD]]].
    + split; [| exact K2]. intros cb cm H. destruct (K1 _ _ H) as (A & B & C & D0 & E0).
      unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
      * destruct (cm_prim cm) as [c|]; [| exact D0]. destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
        repeat (split; [assumption|]). intros X. apply D6. apply IBs. exact X.
      * destruct (cm_state cm); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
        destruct E3 as [E3|(x & Hx & X)]; [left; exact E3| right].
        unfold all_batches in Hx. rewrite !in_app_iff in Hx. cbn in Hx.
        destruct Hx as [Hx|[Hx|[<-|Hx]]].
        -- exists x. split; [unfold all_batches; rewrite !in_app_iff; tauto| exact X].
        -- exists x. split; [unfold all_batches; rewrite !in_app_iff; tauto| exact X].
        -- exfalso. rewrite (GONE cb X) in H. discriminate.
        -- exists x. split; [unfold all_batches; rewrite !in_app_iff; tauto| exact X].
    + unfold wf_quarantine. split; [exact Q1|]. split; [intros x Hx; apply QD; right; exact Hx|]. split; [exact ND|].
      intros b1 b2 x H1 H2. apply (Q3 b1 b2 x); apply SUB; assumption.
  - destruct (QD b (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & _).
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    intros (x & Hx & X). apply NB. rewrite <- X. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma do_recycle_spec : forall bs D s0,
  AWf E P (bs ++ D) s0 ->
  (forall b, In b bs -> items_live s0 (b_items b)) ->
  hoare (fun s => s = s0) (do_recycle E bs)
    (fun s' _ => AWf E P D s' /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0 /\ live_same s0 s').
Proof.
  intros bs. induction bs as [|b rest IH]; intros D s0 WF LIVE.
  - cbn. apply hoare_ret. intros s ->. split; [exact WF|]. split; [reflexivity|]. split; [reflexivity| apply live_same_refl].
  - cbn. pose proof WF as X. destruct X as (WE & WR & WC & WCH & (Q1 & QD & Q2 & Q3) & WS & WD).
    pose proof (QD b (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B7).
    eapply hoare_bind; [apply (recycle_items_spec (b :: rest ++ D) s0 b (b_items b) WF (or_introl eq_refl) (incl_refl _) B7 (LIVE b (or_introl eq_refl)))|].
    intros []. apply hoare_pre. intros s1 (WF1 & HT1 & HG1 & SAME & GONE).
    destruct (AWf_drop_dbatch (rest ++ D) s1 b WF1 GONE) as [WF1' AV].
    pose proof WF1' as X. destruct X as (_ & WR1 & _).
    destruct (carved_class_of_addr E s1 kBatchClass (b_addr b) ltac:(unfold kBatchClass, kLargestClassID; lia) WE WR1 (proj1 AV)) as [IP CL].
    rewrite IP, CL.
    eapply hoare_bind; [apply (local_dealloc_spec E P (rest ++ D) s1 kBatchClass (b_addr b) ltac:(unfold kBatchClass, kLargestClassID; lia) WF1' AV)|].
    intros []. apply hoare_pre. intros s2 (WF2 & (HK2 & HT2 & HG2 & _) & _ & _).
    eapply hoare_conseq; [apply (IH D s2 WF2)| auto|].
    + intros b' Hb' x Hx. destruct (LIVE b' (or_intror Hb') x Hx) as (cm & i & j & H & ST). exists cm, i, j. rewrite HK2.
      rewrite SAME; [auto|]. intros Hxb.
      assert (A1 : In b (all_batches (b :: rest ++ D) s0)) by (unfold all_batches; rewrite !in_app_iff; cbn; tauto).
      assert (A2 : In b' (all_batches (b :: rest ++ D) s0)) by (unfold all_batches; rewrite !in_app_iff; cbn; rewrite in_app_iff; tauto).
      pose proof (Q3 b b' x A1 A2 Hxb Hx) as <-.
      (* [comment removed for export] *)
      unfold all_batches in Q2. rewrite !map_app in Q2. cbn in Q2. apply NoDup_app_remove_l in Q2. apply NoDup_app_remove_l in Q2.
      inversion Q2 as [|? ? NI]; subst. apply NI. apply in_app_iff. left. apply in_map. exact Hb'.
    + cbn beta. intros s [] (WF3 & HT3 & HG3 & LS). split; [exact WF3|]. split; [congruence|]. split; [congruence|].
      intros cb cm i Hi. rewrite (LS cb cm i Hi), HK2. split; intros H.
      * destruct (in_dec Z.eq_dec cb (b_items b)) as [Hin|Hnin]; [rewrite (GONE cb Hin) in H; discriminate|]. rewrite <- (SAME cb Hnin). exact H.
      * destruct (in_dec Z.eq_dec cb (b_items b)) as [Hin|Hnin].
        -- exfalso. destruct (LIVE b (or_introl eq_refl) cb Hin) as (cm' & i' & j' & H' & ST'). rewrite H in H'. injection H' as <-. rewrite Hi in ST'. discriminate.
        -- rewrite (SAME cb Hnin). exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pop_prefix_app : forall gq bytes mn, fst (pop_prefix gq bytes mn) ++ snd (pop_prefix gq bytes mn) = gq.
Proof.
  intros gq. induction gq as [|b rest IH]; intros bytes mn; cbn; [reflexivity|].
  destruct (mn <? bytes); cbn; [|reflexivity]. specialize (IH (bytes - b_size b) mn).
  destruct (pop_prefix rest (bytes - b_size b) mn) as [p k]. cbn in *. rewrite IH. reflexivity.
Qed.

Lemma wf_batch_dbatch : forall D s b, wf_batch E D s b -> wf_dbatch E s b.
Proof. intros D s b (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). unfold wf_dbatch. auto. Qed.

Lemma AWf_detach : forall D s popped kept,
  AWf E P D s -> as_gq s = popped ++ kept ->
  AWf E P (popped ++ D) (upd_gq (fun _ => kept) s)
  /\ (forall b, In b popped -> items_live s (b_items b)).
Proof.
  intros D s popped kept WF HGQ. set (s' := upd_gq _ s).
  assert (PERMA : Permutation (all_batches (popped ++ D) s') (all_batches D s)).
  { unfold all_batches. cbn. rewrite HGQ. apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (INA : forall b, In b (all_batches (popped ++ D) s') <-> In b (all_batches D s)).
  { intros b; split; intros H; [eapply Permutation_in; [exact PERMA| exact H]| eapply Permutation_in; [apply Permutation_sym; exact PERMA| exact H]]. }
  assert (IB : forall a, is_batch (popped ++ D) s' a <-> is_batch D s a).
  { intros a. unfold is_batch. split; intros (b & Hb & X); exists b; split; [apply INA; exact Hb| exact X| apply INA; exact Hb| exact X]. }
  assert (LSUB : forall b, In b (as_tq s' ++ as_gq s') -> In b (as_tq s ++ as_gq s)).
  { intros b. cbn. rewrite HGQ, !in_app_iff. tauto. }
  assert (PSUB : forall b, In b popped -> In b (as_tq s ++ as_gq s)).
  { intros b Hb. rewrite HGQ, !in_app_iff. tauto. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  split.
  - split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
    split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
    split; [|split; [|split; [exact WS| exact WD]]].
    + split; [| exact K2]. intros cb cm H. destruct (K1 _ _ H) as (A & B & C & D0 & E0).
      unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
      * destruct (cm_prim cm) as [c|]; [| exact D0]. destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
        repeat (split; [assumption|]). intros X. apply D6. apply IB. exact X.
      * destruct (cm_state cm); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
        destruct E3 as [E3|(b & Hb & X)]; [left; exact E3| right; exists b; split; [apply INA; exact Hb| exact X]].
    + unfold wf_quarantine. split; [|split; [|split]].
      * intros b Hb. exact (Q1 b (LSUB b Hb)).
      * intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [| exact (QD b Hb)]. apply wf_batch_dbatch with (D := D). exact (proj1 (Q1 b (PSUB b Hb))).
      * eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERMA| exact Q2].
      * intros b1 b2 x H1 H2. apply INA in H1. apply INA in H2. exact (Q3 b1 b2 x H1 H2).
  - intros b Hb x Hx. destruct (Q1 b (PSUB b Hb)) as [(_ & _ & _ & _ & _ & _ & _ & B8) _]. exact (B8 x Hx).
Qed.

(* [comment removed for export] *)
Lemma chunk_used_size_nonneg : forall D s x, wf_chunks E P D s -> 0 <= chunk_used_size s x.
Proof.
  intros D s x [K1 _]. unfold chunk_used_size. destruct (as_chunks s !! x) as [cm|] eqn:H; [|lia].
  destruct (K1 _ _ H) as (_ & B & _). lia.
Qed.

Lemma qbytes_ge : forall D s l, AWf E P D s -> incl l (as_tq s ++ as_gq s) -> kBatchSize * zlen l <= qbytes l.
Proof.
  intros D s l WF. induction l as [|b l IH]; intros INCL; [unfold zlen; cbn; lia|].
  unfold zlen in *. cbn [length qbytes fold_right]. fold (qbytes l).
  specialize (IH ltac:(intros x Hx; apply INCL; right; exact Hx)).
  destruct WF as (_ & _ & _ & WCH & (Q1 & _) & _). destruct (Q1 b (INCL b (or_introl eq_refl))) as [(_ & _ & _ & _ & _ & B6 & _) _].
  assert (0 <= fold_right (fun cb acc => chunk_used_size s cb + acc) 0 (b_items b)).
  { clear -WCH. induction (b_items b) as [|y k IHk]; cbn; [lia|]. pose proof (chunk_used_size_nonneg _ s y WCH). lia. }
  rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fold_cus_app : forall s l1 l2,
  fold_right (fun cb acc => chunk_used_size s cb + acc) 0 (l1 ++ l2)
  = fold_right (fun cb acc => chunk_used_size s cb + acc) 0 l1 + fold_right (fun cb acc => chunk_used_size s cb + acc) 0 l2.
Proof. intros s l1 l2. induction l1 as [|x l IH]; cbn; [lia| rewrite IH; lia]. Qed.

Lemma AWf_merge_step : forall D s A cur nx B,
  AWf E P D s -> as_gq s = A ++ cur :: nx :: B -> zlen (b_items cur) + zlen (b_items nx) <= kBatchCap ->
  AWf E P (mkBatch (b_addr nx) [] kBatchSize :: D)
      (upd_gq (fun _ => A ++ mkBatch (b_addr cur) (b_items cur ++ b_items nx) (b_size cur + (b_size nx - kBatchSize)) :: B) s).
Proof.
  intros D s A cur nx B WF HGQ CAP.
  set (cur' := mkBatch (b_addr cur) (b_items cur ++ b_items nx) (b_size cur + (b_size nx - kBatchSize))).
  set (shell := mkBatch (b_addr nx) [] kBatchSize). set (s' := upd_gq _ s).
  set (REST := as_tq s ++ A ++ B ++ D).
  assert (INold : forall b, In b (all_batches D s) <-> b = cur \/ b = nx \/ In b REST).
  { intros b. unfold all_batches, REST. rewrite HGQ. rewrite !in_app_iff. cbn. rewrite ?in_app_iff. intuition (subst; auto). }
  assert (INnew : forall b, In b (all_batches (shell :: D) s') <-> b = cur' \/ b = shell \/ In b REST).
  { intros b. unfold all_batches, REST. cbn [as_tq as_gq s' upd_gq]. rewrite !in_app_iff. cbn. rewrite ?in_app_iff. intuition (subst; auto). }
  assert (Lold : forall b, In b (as_tq s ++ as_gq s) <-> b = cur \/ b = nx \/ In b (as_tq s ++ A ++ B)).
  { intros b. rewrite HGQ. rewrite !in_app_iff. cbn. rewrite ?in_app_iff. intuition (subst; auto). }
  assert (Lnew : forall b, In b (as_tq s' ++ as_gq s') <-> b = cur' \/ In b (as_tq s ++ A ++ B)).
  { intros b. cbn [as_tq as_gq s' upd_gq]. rewrite !in_app_iff. cbn. rewrite ?in_app_iff. intuition (subst; auto). }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  (* [comment removed for export] *)
  set (RA := map b_addr (as_tq s) ++ map b_addr A ++ b_addr cur :: map b_addr B ++ map b_addr D).
  assert (EQold : map b_addr (all_batches D s) = (map b_addr (as_tq s) ++ map b_addr A ++ [b_addr cur]) ++ b_addr nx :: (map b_addr B ++ map b_addr D)).
  { unfold all_batches. rewrite HGQ, !map_app. cbn. rewrite <- !app_assoc. cbn. reflexivity. }
  assert (EQnew : map b_addr (all_batches (shell :: D) s') = (map b_addr (as_tq s) ++ map b_addr A ++ b_addr cur :: map b_addr B) ++ b_addr nx :: map b_addr D).
  { unfold all_batches. cbn [as_tq as_gq s' upd_gq]. rewrite !map_app. cbn. rewrite <- !app_assoc. cbn. rewrite <- ?app_assoc. reflexivity. }
  assert (RA1 : (map b_addr (as_tq s) ++ map b_addr A ++ [b_addr cur]) ++ (map b_addr B ++ map b_addr D) = RA).
  { unfold RA. rewrite <- !app_assoc. cbn. reflexivity. }
  assert (RA2 : (map b_addr (as_tq s) ++ map b_addr A ++ b_addr cur :: map b_addr B) ++ map b_addr D = RA).
  { unfold RA. rewrite <- !app_assoc. cbn. rewrite <- ?app_assoc. reflexivity. }
  assert (PA : Permutation (map b_addr (all_batches D s)) (b_addr nx :: RA)).
  { rewrite EQold, <- RA1. apply Permutation_sym. apply Permutation_middle. }
  assert (PA' : Permutation (map b_addr (all_batches (shell :: D) s')) (b_addr nx :: RA)).
  { rewrite EQnew, <- RA2. apply Permutation_sym. apply Permutation_middle. }
  pose proof (Permutation_NoDup PA Q2) as NDA. inversion NDA as [|? ? NInx NDR]; subst.
  assert (ADDRS : forall b, In b (all_batches D s) -> In (b_addr b) (b_addr nx :: RA)).
  { intros b Hb. eapply Permutation_in; [exact PA|]. apply in_map. exact Hb. }
  (* [comment removed for export] *)
  assert (RAIN : forall b, In b REST -> In (b_addr b) RA).
  { intros b Hb. unfold REST in Hb. unfold RA. rewrite !in_app_iff in Hb. rewrite !in_app_iff. cbn. rewrite in_app_iff.
    destruct Hb as [Hb|[Hb|[Hb|Hb]]]; pose proof (in_map b_addr _ _ Hb) as X; tauto. }
  assert (NXR : ~ In nx REST) by (intros H; apply NInx; exact (RAIN nx H)).
  assert (CURR : ~ In cur REST).
  { intros H. assert (RA3 : RA = (map b_addr (as_tq s) ++ map b_addr A) ++ b_addr cur :: (map b_addr B ++ map b_addr D)).
    { unfold RA. rewrite <- !app_assoc. reflexivity. }
    rewrite RA3 in NDR. apply (NoDup_remove_2 _ _ _ NDR).
    unfold REST in H. rewrite !in_app_iff in H. rewrite !in_app_iff.
    destruct H as [Hb|[Hb|[Hb|Hb]]]; pose proof (in_map b_addr _ _ Hb) as X; tauto. }
  assert (CNX : cur <> nx).
  { intros ->. apply NInx. unfold RA. rewrite !in_app_iff. cbn. tauto. }
  assert (Hcur : In cur (as_tq s ++ as_gq s)) by (apply Lold; auto).
  assert (Hnx : In nx (as_tq s ++ as_gq s)) by (apply Lold; auto).
  destruct (Q1 cur Hcur) as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) CN].
  destruct (Q1 nx Hnx) as [(N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8) NN].
  assert (DISJ : forall x, In x (b_items cur) -> ~ In x (b_items nx)).
  { intros x Hx Hx'. apply CNX. apply (Q3 cur nx x); [apply INold; auto| apply INold; auto| exact Hx| exact Hx']. }
  assert (IB : forall a, is_batch (shell :: D) s' a <-> is_batch D s a).
  { intros a. unfold is_batch. split; intros (b & Hb & X).
    - apply INnew in Hb as [->|[->|Hb]]; [exists cur| exists nx| exists b]; (split; [apply INold; auto| try exact X]).
    - apply INold in Hb as [->|[->|Hb]]; [exists cur'| exists shell| exists b]; (split; [apply INnew; auto| try exact X]). }
  split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
  split; [|split; [|split; [exact WS| exact WD]]].
  - split; [| exact K2]. intros cb cm H. destruct (K1 _ _ H) as (A0 & B0 & C0 & D0 & E0).
    unfold wf_chunk. split; [exact A0|]. split; [exact B0|]. split; [exact C0|]. split.
    + destruct (cm_prim cm) as [c|]; [| exact D0]. destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
      repeat (split; [assumption|]). intros X. apply D6. apply IB. exact X.
    + destruct (cm_state cm); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
      destruct E3 as [E3|(b & Hb & X)]; [left; exact E3| right].
      apply INold in Hb as [->|[->|Hb]].
      * exists cur'. split; [apply INnew; auto| cbn; apply in_app_iff; left; exact X].
      * exists cur'. split; [apply INnew; auto| cbn; apply in_app_iff; right; exact X].
      * exists b. split; [apply INnew; auto| exact X].
  - unfold wf_quarantine. split; [|split; [|split]].
    + intros b Hb. apply Lnew in Hb as [->|Hb].
      * subst cur'. unfold wf_batch. cbn [b_addr b_items b_size]. split; [| unfold zlen in *; rewrite length_app; lia].
        split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
        split; [unfold zlen in *; rewrite length_app, Nat2Z.inj_add; lia|].
        split; [change (chunk_used_size s') with (chunk_used_size s); rewrite fold_cus_app; lia|].
        split; [apply NoDup_app; [exact C7| exact N7| exact DISJ]|].
        intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; [exact (C8 x Hx)| exact (N8 x Hx)].
      * apply Q1. apply Lold. right; right; exact Hb.
    + intros b [<-|Hb]; [| exact (QD b Hb)]. subst shell. unfold wf_dbatch. cbn. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4| constructor].
    + eapply Permutation_NoDup; [apply Permutation_sym; exact PA'|]. exact NDA.
    + intros b1 b2 x H1 H2 X1 X2. apply INnew in H1. apply INnew in H2.
      assert (OWN : forall b, In b REST -> In x (b_items b) -> (In x (b_items cur) \/ In x (b_items nx)) -> False).
      { intros b Hb Xb [Xc|Xn].
        - apply CURR. rewrite <- (Q3 b cur x ltac:(apply INold; auto) ltac:(apply INold; auto) Xb Xc). exact Hb.
        - apply NXR. rewrite <- (Q3 b nx x ltac:(apply INold; auto) ltac:(apply INold; auto) Xb Xn). exact Hb. }
      destruct H1 as [->|[->|H1]]; destruct H2 as [->|[->|H2]]; try reflexivity; try (cbn in X1; destruct X1); try (cbn in X2; destruct X2).
      * exfalso. cbn in X1. apply in_app_iff in X1. exact (OWN b2 H2 X2 X1).
      * exfalso. cbn in X2. apply in_app_iff in X2. exact (OWN b1 H1 X1 X2).
      * apply (Q3 b1 b2 x); [apply INold; auto| apply INold; auto| exact X1| exact X2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd_gq_gq : forall f g s, upd_gq f (upd_gq g s) = upd_gq (fun l => f (g l)) s.
Proof. intros; reflexivity. Qed.

Lemma AWf_gq_ext : forall D s l1 l2, l1 = l2 -> AWf E P D (upd_gq (fun _ => l1) s) -> AWf E P D (upd_gq (fun _ => l2) s).
Proof. intros D s l1 l2 -> H. exact H. Qed.

Lemma merge_aux_ok : forall rest cur acc done D s,
  AWf E P (acc ++ D) s -> as_gq s = done ++ cur :: rest -> (forall b, In b acc -> b_items b = []) ->
  let '(l, o) := merge_batches_aux cur rest acc in
  AWf E P (o ++ D) (upd_gq (fun _ => done ++ l) s) /\ (forall b, In b o -> b_items b = []).
Proof.
  intros rest. induction rest as [|nx rest IH]; intros cur acc done D s WF HGQ ACC; cbn.
  - split; [| exact ACC]. eapply AWf_batches_perm; [..| exact WF]; try reflexivity. cbn. rewrite HGQ. apply Permutation_refl.
  - destruct (zlen (b_items cur) + zlen (b_items nx) <=? kBatchCap) eqn:FIT.
    + apply Z.leb_le in FIT.
      pose proof (AWf_merge_step (acc ++ D) s done cur nx rest WF HGQ FIT) as WF1.
      set (cur' := mkBatch (b_addr cur) (b_items cur ++ b_items nx) (b_size cur + (b_size nx - kBatchSize))) in *.
      set (shell := mkBatch (b_addr nx) [] kBatchSize) in *.
      set (s1 := upd_gq (fun _ => done ++ cur' :: rest) s) in *.
      assert (WF1' : AWf E P ((acc ++ [shell]) ++ D) s1).
      { eapply AWf_perm_D; [| exact WF1]. rewrite <- app_assoc. cbn. apply Permutation_middle. }
      assert (ACC' : forall b, In b (acc ++ [shell]) -> b_items b = []).
      { intros b Hb. apply in_app_iff in Hb as [Hb|[<-|[]]]; [exact (ACC b Hb)| reflexivity]. }
      specialize (IH cur' (acc ++ [shell]) done D s1 WF1' eq_refl ACC').
      destruct (merge_batches_aux cur' rest (acc ++ [shell])) as [l o]. exact IH.
    + specialize (IH nx acc (done ++ [cur]) D s WF ltac:(rewrite HGQ, <- app_assoc; reflexivity) ACC).
      destruct (merge_batches_aux nx rest acc) as [l' o']. destruct IH as [IH1 IH2]. split; [| exact IH2].
      eapply AWf_gq_ext; [| exact IH1]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma merge_ok : forall D s,
  AWf E P D s ->
  let '(gq1, empties) := merge_batches (as_gq s) in
  AWf E P (empties ++ D) (upd_gq (fun _ => gq1) s) /\ (forall b, In b empties -> b_items b = []).
Proof.
  intros D s WF. unfold merge_batches. destruct (as_gq s) as [|b rest] eqn:HGQ.
  - cbn. split; [| intros b []]. eapply AWf_batches_perm; [..| exact WF]; try reflexivity. cbn. rewrite HGQ. apply Permutation_refl.
  - pose proof (merge_aux_ok rest b [] [] D s WF HGQ ltac:(intros x [])) as M. cbn in M.
    destruct (merge_batches_aux b rest []) as [l o]. exact M.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma recycle_spec : forall s0,
  AWf E P [] s0 ->
  hoare (fun s => s = s0) (recycle E)
    (fun s' _ => AWf E P [] s' /\ as_tq s' = as_tq s0 /\ live_same s0 s').
Proof.
  intros s0 WF. unfold recycle. apply hoare_get_bind. intros s ->.
  pose proof (qbytes_ge [] s0 (as_gq s0) WF ltac:(intros x Hx; apply in_app_iff; right; exact Hx)) as GE.
  unfold acheck. replace (kBatchSize * zlen (as_gq s0) <=? qbytes (as_gq s0)) with true by (symmetry; apply Z.leb_le; exact GE).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros []. apply hoare_pre. intros s ->.
  (* [comment removed for export] *)
  match goal with |- hoare _ (let '(_, _) := ?x in _) _ =>
    assert (MG : let '(gq1, empties) := x in AWf E P (empties ++ []) (upd_gq (fun _ => gq1) s0) /\ (forall b, In b empties -> b_items b = []));
    [| destruct x as [gq1 empties]] end.
  { match goal with |- let '(_, _) := (if ?b then _ else _) in _ => destruct b end.
    - apply (merge_ok [] s0 WF).
    - split; [| intros b []]. cbn. eapply AWf_batches_perm; [..| exact WF]; try reflexivity. }
  destruct MG as [WF1 EMP]. rewrite app_nil_r in WF1.
  set (s1 := upd_gq (fun _ => gq1) s0) in *.
  pose proof (pop_prefix_app gq1 (qbytes gq1) kQuarantineMin) as SPLIT.
  destruct (pop_prefix gq1 (qbytes gq1) kQuarantineMin) as [popped kept]. cbn in SPLIT.
  apply hoare_upd_bind. apply hoare_pre. intros s (sx & -> & ->).
  destruct (AWf_detach empties s1 popped kept WF1 ltac:(symmetry; exact SPLIT)) as [WF2 LIVE2].
  change (upd_gq (fun _ => kept) s0) with (upd_gq (fun _ => kept) s1).
  set (s2 := upd_gq (fun _ => kept) s1) in *.
  assert (WF2' : AWf E P ((empties ++ popped) ++ []) s2).
  { rewrite app_nil_r. eapply AWf_perm_D; [apply Permutation_app_comm| exact WF2]. }
  eapply hoare_conseq; [apply (do_recycle_spec (empties ++ popped) [] s2 WF2')| auto|].
  - intros b Hb. apply in_app_iff in Hb as [Hb|Hb].
    + rewrite (EMP b Hb). intros x [].
    + intros x Hx. destruct (LIVE2 b Hb x Hx) as (cm & i & j & H & ST). exists cm, i, j. split; [exact H| exact ST].
  - cbn beta. intros s [] (WF3 & HT3 & HG3 & LS). split; [exact WF3|]. split; [rewrite HT3; reflexivity|].
    intros cb cm i Hi. rewrite (LS cb cm i Hi). reflexivity.
Qed.

Lemma drain_spec : forall s0,
  AWf E P [] s0 ->
  hoare (fun s => s = s0) (drain_if_needed E) (fun s' _ => AWf E P [] s' /\ live_same s0 s').
Proof.
  intros s0 WF. unfold drain_if_needed. apply hoare_get_bind. intros s ->.
  destruct (kThreadQuarantineMax <? tq_bytes s0); [| apply hoare_ret; intros s ->; split; [exact WF| apply live_same_refl]].
  apply hoare_upd_bind. apply hoare_pre. intros s (sx & -> & ->).
  pose proof (AWf_transfer E P [] s0 WF) as WF1. set (s1 := upd_tq _ (upd_gq _ s0)) in *.
  apply hoare_get_bind. intros s ->.
  destruct (kQuarantineMax <? gq_bytes s1); [| apply hoare_ret; intros s ->; split; [exact WF1| apply live_same_eq; reflexivity]].
  eapply hoare_conseq; [apply (recycle_spec s1 WF1)| auto|].
  cbn beta. intros s [] (WF2 & _ & LS). split; [exact WF2|]. intros cb cm i Hi. rewrite (LS cb cm i Hi). reflexivity.
Qed.

End WF.
End RC__1.
