(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5.
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
Local Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition flipped (cm : chunkmeta) (aid fid : Z) : chunkmeta :=
  mkCM (cm_alloc_beg cm) (cm_rz_log cm) (cm_n cm) (cm_prim cm) (CQuarantined aid fid).

Lemma AWf_flip : forall P s cb cm aid fid,
  AWf E P [] s -> as_chunks s !! cb = Some cm -> cm_state cm = CAllocated aid -> 1 <= fid ->
  AWf E (cb :: P) [] (upd_chunks (fun m => <[cb := flipped cm aid fid]> m) s)
  /\ (forall b, In b (as_tq s ++ as_gq s) -> ~ In cb (b_items b)).
Proof.
  intros P s cb cm aid fid WF Hcm ST FID.
  set (cm' := flipped cm aid fid). set (s' := upd_chunks _ s).
  assert (HK : as_chunks s' = <[cb := cm']> (as_chunks s)) by reflexivity.
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  assert (NIN : forall b, In b (as_tq s ++ as_gq s) -> ~ In cb (b_items b)).
  { intros b Hb Hin. destruct (Q1 b Hb) as [(_ & _ & _ & _ & _ & _ & _ & B8) _].
    destruct (B8 cb Hin) as (cm0 & i & j & H0 & S0). rewrite Hcm in H0. injection H0 as <-. rewrite ST in S0. discriminate. }
  split; [|exact NIN].
  (* [comment removed for export] *)
  assert (LK : forall cb0 cm0, as_chunks s' !! cb0 = Some cm0 ->
            (cb0 = cb /\ cm0 = cm') \/ (cb0 <> cb /\ as_chunks s !! cb0 = Some cm0)).
  { intros cb0 cm0 H. rewrite HK in H. destruct (Z.eq_dec cb cb0) as [<-|NE].
    - rewrite lookup_insert_eq in H. injection H as <-. left; auto.
    - rewrite lookup_insert_ne in H by auto. right; auto. }
  assert (AB : forall cb0 cm0, as_chunks s' !! cb0 = Some cm0 -> exists cm1, as_chunks s !! cb0 = Some cm1 /\ cm_alloc_beg cm1 = cm_alloc_beg cm0 /\ cm_n cm1 = cm_n cm0).
  { intros cb0 cm0 H. destruct (LK _ _ H) as [[-> ->]|[NE H0]]; [exists cm; subst cm'; cbn; auto| exists cm0; auto]. }
  assert (ICB : forall a, is_chunk_block s' a <-> is_chunk_block s a).
  { intros a; split; intros (cb0 & cm0 & H & Ha).
    - destruct (AB _ _ H) as (cm1 & H1 & E1 & _). exists cb0, cm1. split; [exact H1| congruence].
    - destruct (Z.eq_dec cb0 cb) as [->|NE].
      + exists cb, cm'. rewrite HK, lookup_insert_eq. rewrite Hcm in H. injection H as ->. split; [reflexivity| exact Ha].
      + exists cb0, cm0. rewrite HK, lookup_insert_ne by auto. auto. }
  assert (CUS : forall x, chunk_used_size s' x = chunk_used_size s x).
  { intros x. unfold chunk_used_size. rewrite HK. destruct (Z.eq_dec cb x) as [<-|NE].
    - rewrite lookup_insert_eq, Hcm. reflexivity.
    - rewrite lookup_insert_ne by auto. reflexivity. }
  split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
  split; [|split; [|split; [exact WS| exact WD]]].
  - split.
    + intros cb0 cm0 H. destruct (LK _ _ H) as [[-> ->]|[NE H0]].
      * destruct (K1 _ _ Hcm) as (A & B & C & D0 & E0). rewrite ST in E0.
        unfold wf_chunk. subst cm'; cbn [flipped cm_alloc_beg cm_rz_log cm_n cm_prim cm_state].
        split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D0|].
        split; [exact E0|]. split; [exact FID|]. left; left; reflexivity.
      * destruct (K1 _ _ H0) as (A & B & C & D0 & E0). unfold wf_chunk.
        split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D0|].
        destruct (cm_state cm0); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
        destruct E3 as [E3|E3]; [left; right; exact E3| right; exact E3].
    + intros cb1 cm1 cb2 cm2 H1 H2 NE. destruct (AB _ _ H1) as (d1 & X1 & A1 & _). destruct (AB _ _ H2) as (d2 & X2 & A2 & _).
      rewrite <- A1, <- A2. exact (K2 _ _ _ _ X1 X2 NE).
  - unfold wf_quarantine. change (as_tq s') with (as_tq s). change (as_gq s') with (as_gq s). change (all_batches [] s') with (all_batches [] s).
    split; [|split; [intros b []| split; [exact Q2| exact Q3]]].
    intros b Hb. destruct (Q1 b Hb) as [(B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) NB]. split; [|exact NB].
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [intros X; apply B4; apply ICB; exact X|].
    split; [exact B5|]. split.
    { rewrite B6. f_equal. clear -CUS. induction (b_items b) as [|i l IH]; [reflexivity|]. cbn. rewrite CUS, IH. reflexivity. }
    split; [exact B7|].
    intros x Hx. destruct (B8 x Hx) as (cm0 & i & j & H0 & S0).
    destruct (Z.eq_dec x cb) as [->|NE]; [exfalso; exact (NIN b Hb Hx)|].
    exists cm0, i, j. rewrite HK, lookup_insert_ne by auto. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pending (s : astate) (cb n : Z) : Prop :=
  (exists cm i j, as_chunks s !! cb = Some cm /\ cm_state cm = CQuarantined i j /\ cm_n cm = n)
  /\ (forall b, In b (as_tq s ++ as_gq s) -> ~ In cb (b_items b)).

Lemma qbytes_app : forall l1 l2, qbytes (l1 ++ l2) = qbytes l1 + qbytes l2.
Proof. intros l1 l2. unfold qbytes. induction l1 as [|b l IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.

(* [comment removed for export] *)
Lemma wf_chunk_push : forall P s s' cb nb cb0 cm0,
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_sec s' = as_sec s ->
  (forall b, In b (all_batches [] s) -> exists b', In b' (all_batches [] s') /\ b_addr b' = b_addr b /\ forall x, In x (b_items b) -> In x (b_items b')) ->
  (forall b', In b' (all_batches [] s') -> (exists b, In b (all_batches [] s) /\ b_addr b = b_addr b') \/ b' = nb) ->
  ~ is_chunk_block s (b_addr nb) -> as_chunks s !! cb0 = Some cm0 ->
  In nb (all_batches [] s') -> In cb (b_items nb) ->
  wf_chunk E (cb :: P) [] s cb0 cm0 -> wf_chunk E P [] s' cb0 cm0.
Proof.
  intros P s s' cb nb cb0 cm0 HR HC HS OLD NEW NCB Hcm0 INB ICB (A & B & C & D0 & E0).
  unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
  - destruct (cm_prim cm0) as [c|].
    + destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
      unfold carved, in_free, in_cache, region_of, get_region, get_cache in *. rewrite HR, HC.
      split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
      intros (b' & Hb' & Hab). destruct (NEW b' Hb') as [(b & Hb & Hba)| ->].
      * apply D6. exists b. split; [exact Hb| congruence].
      * apply NCB. exists cb0, cm0. split; [exact Hcm0| symmetry; exact Hab].
    + rewrite HS. exact D0.
  - destruct (cm_state cm0); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
    destruct E3 as [[<-|E3]|(b & Hb & Hx)].
    + right. exists nb. auto.
    + left; exact E3.
    + right. destruct (OLD b Hb) as (b' & Hb' & _ & SUB). exists b'. split; [exact Hb'| apply SUB; exact Hx].
Qed.

Lemma AWf_push_new : forall P s cb n ba,
  AWf E (cb :: P) [] s -> avail E [] s kBatchClass ba -> pending s cb n ->
  AWf E P [] (upd_tq (fun l => l ++ [mkBatch ba [cb] (kBatchSize + n)]) s).
Proof.
  intros P s cb n ba WF (CV & NF & NC & NCB & NBA) [(cm & i & j & Hcm & ST & Hn) NIN].
  set (nb := mkBatch ba [cb] (kBatchSize + n)). set (s' := upd_tq _ s).
  assert (HT : as_tq s' = as_tq s ++ [nb]) by reflexivity.
  assert (HG : as_gq s' = as_gq s) by reflexivity.
  assert (PERM : Permutation (all_batches [] s') (nb :: all_batches [] s)).
  { unfold all_batches. rewrite HT, HG, !app_nil_r, <- app_assoc. cbn.
    apply Permutation_sym. apply Permutation_middle. }
  assert (INs' : forall b, In b (all_batches [] s') <-> b = nb \/ In b (all_batches [] s)).
  { intros b. split; intros H.
    - apply (Permutation_in _ PERM) in H. destruct H as [<-|H]; auto.
    - apply (Permutation_in _ (Permutation_sym PERM)). destruct H as [<-|H]; [left; reflexivity| right; exact H]. }
  assert (TG : forall b, In b (as_tq s ++ as_gq s) <-> In b (all_batches [] s)) by (intros b; unfold all_batches; rewrite app_nil_r; tauto).
  assert (TG' : forall b, In b (as_tq s' ++ as_gq s') <-> In b (all_batches [] s')) by (intros b; unfold all_batches; rewrite app_nil_r; tauto).
  destruct WF as (WE & WR & WC & WCH & (Q1 & QD & Q2 & Q3) & WS & WD).
  split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
  split; [|split; [|split; [exact WS| exact WD]]].
  - destruct WCH as [K1 K2]. split; [|exact K2]. intros cb0 cm0 H.
    eapply (wf_chunk_push P s s' cb nb); try reflexivity.
    + intros b Hb. exists b. split; [apply INs'; right; exact Hb|]. auto.
    + intros b' Hb'. apply INs' in Hb' as [->|Hb']; [right; reflexivity| left; exists b'; auto].
    + exact NCB.
    + exact H.
    + apply INs'. left; reflexivity.
    + left; reflexivity.
    + exact (K1 _ _ H).
  - unfold wf_quarantine. split; [|split; [intros b []| split]].
    + intros b Hb. apply TG', INs' in Hb. destruct Hb as [->|Hb].
      * subst nb. split; [| unfold zlen; cbn; lia]. unfold wf_batch. cbn [b_addr b_items b_size].
        split; [exact CV|]. split; [exact NF|]. split; [exact NC|]. split; [exact NCB|].
        split; [unfold kBatchCap, zlen; cbn; lia|]. split; [unfold chunk_used_size; cbn; rewrite Hcm, Hn; lia|].
        split; [constructor; [intros []| constructor]|].
        intros x [<-|[]]. exists cm, i, j. auto.
      * apply TG in Hb. exact (Q1 b Hb).
    + eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERM|]. cbn. constructor; [|exact Q2].
      intros Hin. apply in_map_iff in Hin as (b & Hba & Hb). apply NBA. exists b. auto.
    + intros b1 b2 x H1 H2 X1 X2. apply INs' in H1. apply INs' in H2.
      destruct H1 as [->|H1]; destruct H2 as [->|H2].
      * reflexivity.
      * exfalso. destruct X1 as [<-|[]]. apply TG in H2. exact (NIN b2 H2 X2).
      * exfalso. destruct X2 as [<-|[]]. apply TG in H1. exact (NIN b1 H1 X1).
      * exact (Q3 b1 b2 x H1 H2 X1 X2).
Qed.

Lemma AWf_push_last : forall P s cb n l b,
  AWf E (cb :: P) [] s -> pending s cb n -> as_tq s = l ++ [b] -> zlen (b_items b) < kBatchCap ->
  AWf E P [] (upd_tq (fun _ => l ++ [mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)]) s).
Proof.
  intros P s cb n l b WF [(cm & i & j & Hcm & ST & Hn) NIN] HTQ CAP.
  set (nb := mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)). set (s' := upd_tq _ s).
  assert (HT : as_tq s' = l ++ [nb]) by reflexivity.
  assert (HG : as_gq s' = as_gq s) by reflexivity.
  assert (Hb : In b (as_tq s ++ as_gq s)) by (rewrite HTQ; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  destruct WF as (WE & WR & WC & WCH & (Q1 & QD & Q2 & Q3) & WS & WD).
  assert (AB : forall x, In x (all_batches [] s) <-> In x (l ++ as_gq s) \/ x = b).
  { intros x. unfold all_batches. rewrite HTQ, app_nil_r, <- app_assoc. cbn. rewrite !in_app_iff. cbn.
    split; [intros [H|[H|H]] | intros [[H|H]|H]]; subst; auto 6. }
  assert (AB' : forall x, In x (all_batches [] s') <-> In x (l ++ as_gq s) \/ x = nb).
  { intros x. unfold all_batches. rewrite HT, HG, app_nil_r, <- app_assoc. cbn. rewrite !in_app_iff. cbn.
    split; [intros [H|[H|H]] | intros [[H|H]|H]]; subst; auto 6. }
  assert (NDA : List.NoDup (map b_addr (l ++ b :: as_gq s))).
  { unfold all_batches in Q2. rewrite HTQ, app_nil_r, <- app_assoc in Q2. exact Q2. }
  assert (NB : ~ In b (l ++ as_gq s)).
  { intros X. rewrite map_app in NDA. cbn in NDA. apply NoDup_remove_2 in NDA. apply NDA. rewrite <- map_app. apply in_map. exact X. }
  assert (TG : forall x, In x (as_tq s ++ as_gq s) <-> In x (all_batches [] s)) by (intros x; unfold all_batches; rewrite app_nil_r; tauto).
  assert (TG' : forall x, In x (as_tq s' ++ as_gq s') <-> In x (all_batches [] s')) by (intros x; unfold all_batches; rewrite app_nil_r; tauto).
  split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
  destruct (Q1 b Hb) as [(B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) NB1].
  split; [|split; [|split; [exact WS| exact WD]]].
  - destruct WCH as [K1 K2]. split; [|exact K2]. intros cb0 cm0 H.
    eapply (wf_chunk_push P s s' cb nb); try reflexivity.
    + intros x Hx. apply AB in Hx as [Hx| ->].
      * exists x. split; [apply AB'; left; exact Hx|]. auto.
      * exists nb. split; [apply AB'; right; reflexivity|]. split; [reflexivity|]. intros y Hy. cbn. apply in_app_iff. left; exact Hy.
    + intros b' Hb'. apply AB' in Hb' as [Hb'| ->]; [left; exists b'; split; [apply AB; left; exact Hb'| reflexivity]|].
      left. exists b. split; [apply AB; right; reflexivity| reflexivity].
    + exact B4.
    + exact H.
    + apply AB'. right; reflexivity.
    + cbn. apply in_app_iff. right; left; reflexivity.
    + exact (K1 _ _ H).
  - unfold wf_quarantine. split; [|split; [intros x []| split]].
    + intros x Hx. apply TG', AB' in Hx. destruct Hx as [Hx| ->].
      * apply Q1. apply TG, AB. left; exact Hx.
      * subst nb. unfold wf_batch. cbn [b_addr b_items b_size].
        split; [| unfold zlen in *; rewrite length_app; cbn; lia].
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
        split; [unfold zlen in *; rewrite length_app; cbn; unfold kBatchCap in *; lia|].
        split.
        { rewrite B6, fold_right_app. change (fold_right (λ cb1 acc, chunk_used_size s' cb1 + acc) 0 [cb]) with (chunk_used_size s cb + 0).
          unfold chunk_used_size at 3. rewrite Hcm, Hn.
          change (fold_right (λ cb1 acc, chunk_used_size s' cb1 + acc) (n + 0) (b_items b))
            with (fold_right (λ cb1 acc, chunk_used_size s cb1 + acc) (n + 0) (b_items b)).
          generalize (b_items b) as items. clear. intros items. induction items as [|y k IH]; cbn; lia. }
        split; [apply NoDup_app; [exact B7| constructor; [intros []| constructor]| intros y Hy [<-|[]]; exact (NIN b Hb Hy)]|].
        intros y Hy. apply in_app_iff in Hy as [Hy|[<-|[]]]; [exact (B8 y Hy)|]. exists cm, i, j. auto.
    + unfold all_batches. rewrite HT, HG, app_nil_r, <- app_assoc. cbn. rewrite map_app. cbn. rewrite map_app in NDA. cbn in NDA. exact NDA.
    + intros b1 b2 x H1 H2 X1 X2. apply AB' in H1. apply AB' in H2.
      assert (OLDU : forall c1 c2, In c1 (all_batches [] s) -> In c2 (all_batches [] s) -> In x (b_items c1) -> In x (b_items c2) -> c1 = c2) by (intros c1 c2; apply Q3).
      destruct H1 as [H1| ->]; destruct H2 as [H2| ->].
      * apply (OLDU b1 b2); [apply AB; left; assumption| apply AB; left; assumption| assumption| assumption].
      * exfalso. cbn in X2. apply in_app_iff in X2 as [X2|[<-|[]]].
        -- pose proof (OLDU b1 b ltac:(apply AB; left; exact H1) ltac:(apply AB; right; reflexivity) X1 X2) as ->. exact (NB H1).
        -- apply (NIN b1); [apply TG, AB; left; exact H1| exact X1].
      * exfalso. cbn in X1. apply in_app_iff in X1 as [X1|[<-|[]]].
        -- pose proof (OLDU b2 b ltac:(apply AB; left; exact H2) ltac:(apply AB; right; reflexivity) X2 X1) as ->. exact (NB H2).
        -- apply (NIN b2); [apply TG, AB; left; exact H2| exact X2].
      * reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition live_same (s s' : astate) : Prop :=
  forall cb cm i, cm_state cm = CAllocated i -> (as_chunks s' !! cb = Some cm <-> as_chunks s !! cb = Some cm).

Lemma live_same_refl : forall s, live_same s s.
Proof. intros s cb cm i _. tauto. Qed.
Lemma live_same_trans : forall a b c, live_same a b -> live_same b c -> live_same a c.
Proof. intros a b c H1 H2 cb cm i Hi. rewrite (H2 cb cm i Hi). apply (H1 cb cm i Hi). Qed.
Lemma live_same_eq : forall s s', as_chunks s' = as_chunks s -> live_same s s'.
Proof. intros s s' H cb cm i _. rewrite H. tauto. Qed.

Lemma pending_frame : forall s s' cb n, as_chunks s' = as_chunks s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  pending s cb n -> pending s' cb n.
Proof. intros s s' cb n HK HT HG PN. unfold pending in *. rewrite HK, HT, HG. exact PN. Qed.

Lemma batch_alloc_spec : forall P s0,
  AWf E P [] s0 -> room s0 kBatchClass ->
  hoare (fun s => s = s0) (batch_alloc E)
    (fun s' b => AWf E P [] s' /\ pframe s0 s' /\ (forall c a, carved E s0 c a -> carved E s' c a)
                 /\ avail E [] s' kBatchClass b).
Proof.
  intros P s0 WF ROOM. unfold batch_alloc.
  eapply hoare_bind; [apply (cache_pop_spec E P [] s0 kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia) WF ROOM)|].
  intros r. apply hoare_pre. intros s1 (WF1 & PF1 & CV1 & _ & R1). destruct r as [b|]; [|apply hoare_spin].
  destruct (b =? 0); [apply hoare_spin|]. apply hoare_ret. intros s ->.
  destruct R1 as (_ & AV & _). auto.
Qed.

Lemma enqueue_spec : forall P s0 cb n,
  AWf E (cb :: P) [] s0 -> pending s0 cb n -> room s0 kBatchClass ->
  hoare (fun s => s = s0) (enqueue E cb n)
    (fun s' _ => AWf E P [] s' /\ as_chunks s' = as_chunks s0 /\ as_sec s' = as_sec s0 /\ as_ptr_committed s' = as_ptr_committed s0
                 /\ as_gq s' = as_gq s0 /\ as_keys s' = as_keys s0 /\ as_frames s' = as_frames s0).
Proof.
  intros P s0 cb n WF PN ROOM. unfold enqueue. apply hoare_get_bind. intros s ->.
  match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:NN end.
  - eapply hoare_bind; [apply (batch_alloc_spec (cb :: P) s0 WF ROOM)|].
    intros ba. apply hoare_pre. intros s1 (WF1 & (HK & HT & HG & HS & HP & HKy & HF & HN) & CV1 & AV1).
    apply hoare_upd. intros s ->.
    split; [apply AWf_push_new; [exact WF1| exact AV1| eapply pending_frame; [exact HK| exact HT| exact HG| exact PN]]|].
    cbn. repeat split; assumption.
  - destruct (as_tq s0) as [|b0 l0] eqn:HTQ; [discriminate|]. apply Z.eqb_neq in NN.
    set (tq := b0 :: l0) in *.
    assert (TNE : tq <> []) by (subst tq; discriminate).
    pose proof (app_removelast_last (mkBatch 0 [] 0) TNE) as SPLIT. rewrite <- removelast_eq in SPLIT.
    set (b := List.last tq (mkBatch 0 [] 0)) in *.
    apply hoare_upd. intros s ->.
    assert (CAP : zlen (b_items b) < kBatchCap).
    { destruct WF as (_ & _ & _ & _ & (Q1 & _) & _).
      destruct (Q1 b ltac:(rewrite HTQ; fold tq; rewrite SPLIT; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity)) as [(_&_&_&_&B5&_) _].
      lia. }
    split; [| cbn; repeat split; reflexivity].
    match goal with |- AWf _ _ _ (upd_tq ?F s0) =>
      replace (upd_tq F s0) with (upd_tq (fun _ => removelast tq ++ [mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)]) s0)
        by (unfold upd_tq; rewrite HTQ; reflexivity) end.
    eapply AWf_push_last; [exact WF| exact PN| rewrite HTQ; fold tq; exact SPLIT| exact CAP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AWf_batches_perm : forall P D s s',
  as_regions s' = as_regions s -> as_cache s' = as_cache s -> as_cache_inited s' = as_cache_inited s -> as_chunks s' = as_chunks s ->
  as_sec s' = as_sec s -> as_ptr_committed s' = as_ptr_committed s -> as_keys s' = as_keys s -> as_frames s' = as_frames s ->
  as_ndepot_ins s' = as_ndepot_ins s ->
  Permutation (as_tq s' ++ as_gq s') (as_tq s ++ as_gq s) ->
  AWf E P D s -> AWf E P D s'.
Proof.
  intros P D s s' HR HC HI HK HS HP HKy HF HN PERM WF.
  assert (PERMA : Permutation (all_batches D s') (all_batches D s)).
  { unfold all_batches. rewrite !app_assoc. apply Permutation_app_tail. exact PERM. }
  assert (INA : forall b, In b (all_batches D s') <-> In b (all_batches D s)).
  { intros b; split; intros H; [eapply Permutation_in; [exact PERMA| exact H]| eapply Permutation_in; [apply Permutation_sym; exact PERMA| exact H]]. }
  assert (INT : forall b, In b (as_tq s' ++ as_gq s') <-> In b (as_tq s ++ as_gq s)).
  { intros b; split; intros H; [eapply Permutation_in; [exact PERM| exact H]| eapply Permutation_in; [apply Permutation_sym; exact PERM| exact H]]. }
  assert (IB : forall a, is_batch D s' a <-> is_batch D s a).
  { intros a. unfold is_batch. split; intros (b & Hb & X); exists b; split; [apply INA; exact Hb| exact X| apply INA; exact Hb| exact X]. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  split; [exact WE|]. split; [eapply wf_regions_same; [exact HR| exact WR]|].
  split; [eapply wf_cache_same; [exact HR| exact HC| exact HI| exact WC]|].
  split; [|split; [|split]].
  - split; [| rewrite HK; exact K2]. intros cb cm H. rewrite HK in H. destruct (K1 _ _ H) as (A & B & C & D0 & E0).
    unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    + destruct (cm_prim cm) as [c|].
      * destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6). unfold carved, in_free, in_cache, region_of, get_region, get_cache in *.
        rewrite HR, HC. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
        intros X. apply D6. apply IB. exact X.
      * rewrite HS. exact D0.
    + destruct (cm_state cm); [exact E0|]. destruct E0 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|].
      destruct E3 as [E3|(b & Hb & X)]; [left; exact E3| right; exists b; split; [apply INA; exact Hb| exact X]].
  - unfold wf_quarantine. split; [|split; [|split]].
    + intros b Hb. apply INT in Hb. destruct (Q1 b Hb) as [W N]. split; [|exact N].
      unfold wf_batch, carved, in_free, in_cache, is_chunk_block, chunk_used_size, region_of, get_region, get_cache in *.
      rewrite HR, HC, HK. exact W.
    + intros b Hb. pose proof (QD b Hb) as W.
      unfold wf_dbatch, carved, in_free, in_cache, is_chunk_block, region_of, get_region, get_cache in *. rewrite HR, HC, HK. exact W.
    + eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERMA| exact Q2].
    + intros b1 b2 x H1 H2. apply INA in H1. apply INA in H2. exact (Q3 b1 b2 x H1 H2).
  - unfold wf_secondary, n_chunks. rewrite HS, HP. exact WS.
  - unfold wf_depot. rewrite HKy, HF, HN. exact WD.
Qed.

Lemma AWf_transfer : forall P D s,
  AWf E P D s -> AWf E P D (upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq s) s)).
Proof.
  intros P D s WF. eapply AWf_batches_perm; [..| exact WF]; try reflexivity. cbn. apply Permutation_app_comm.
Qed.

End WF.
End RC__1.
