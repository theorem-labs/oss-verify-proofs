(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2.
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
Variable P : list Z.        (* [comment removed for export] *)
Variable D : list batch.    (* [comment removed for export] *)
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carved_range : forall s c a, 1 <= c <= kLargestClassID -> wf_regions E s -> carved E s c a ->
  region_beg SB c <= a /\ a + class_size c <= region_beg SB c + kFreeArrayOffset.
Proof.
  intros s c a Hc [_ WR] (k & Hk & -> & Hb). specialize (WR c Hc). cbn zeta in WR.
  destruct WR as (A1 & A2 & A3 & _). unfold region_of in *.
  pose proof (class_size_mod c Hc) as [_ SZ].
  assert (0 <= k * class_size c) by (apply Z.mul_nonneg_nonneg; lia). nia.
Qed.

Lemma carved_unique : forall s c c' a, 1 <= c <= kLargestClassID -> 1 <= c' <= kLargestClassID -> wf_regions E s ->
  carved E s c a -> carved E s c' a -> c = c'.
Proof.
  intros s c c' a Hc Hc' WR C1 C2.
  pose proof (carved_range s c a Hc WR C1) as [L1 U1]. pose proof (carved_range s c' a Hc' WR C2) as [L2 U2].
  unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID in *.
  pose proof (class_size_mod c Hc) as [_ S1]. pose proof (class_size_mod c' Hc') as [_ S2].
  destruct (Z.lt_trichotomy c c') as [LT|[EQ|GT]]; [| exact EQ |]; exfalso; nia.
Qed.

Lemma carved_coc : forall s c a, 1 <= c <= kLargestClassID -> carved E s c a ->
  chunk_of_compact SB c (compact_of_chunk SB c a) = a.
Proof.
  intros s c a Hc (k & Hk & -> & _). unfold chunk_of_compact, compact_of_chunk.
  replace (region_beg SB c + k * class_size c - region_beg SB c) with (k * class_size c) by lia.
  pose proof (class_size_mod c Hc) as [M _].
  assert (X : exists q, class_size c = 32 * q).
  { exists (class_size c / 32). pose proof (Z.div_mod (class_size c) 32 ltac:(lia)). lia. }
  destruct X as [q Hq]. rewrite Hq. replace (k * (32 * q)) with ((k * q * 2) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma batch_block : forall s b, wf_quarantine E D s -> In b (all_batches D s) ->
  carved E s kBatchClass (b_addr b) /\ ~ in_free E s kBatchClass (b_addr b) /\ ~ in_cache E s kBatchClass (b_addr b)
  /\ ~ is_chunk_block s (b_addr b).
Proof.
  intros s b (Q1 & QD & _) Hb. unfold all_batches in Hb. rewrite app_assoc in Hb. apply in_app_iff in Hb as [Hb|Hb].
  - destruct (Q1 b Hb) as [(B1 & B2 & B3 & B4 & _) _]. auto.
  - destruct (QD b Hb) as (B1 & B2 & B3 & B4 & _). auto.
Qed.

(* [comment removed for export] *)
Definition untracked (s : astate) (a : Z) : Prop := ~ is_chunk_block s a /\ ~ is_batch D s a.

(* [comment removed for export] *)
Lemma free_entry_untracked : forall s c x, AWF s -> 1 <= c <= kLargestClassID ->
  In x (rg_free (get_region s c)) ->
  ~ In x (get_cache s c) /\ untracked s (chunk_of_compact SB c x).
Proof.
  intros s c x WF Hc Hx. destruct WF as (WE & WR & WC & WCH & WQ & WS & WD).
  pose proof WR as WR'. destruct WR as [_ R2]. destruct (R2 c Hc) as (_&_&_&_&_&_&_&_&_& A10 &_).
  destruct (A10 x Hx) as [Cx Mx].
  split; [|split].
  - intros Hin. destruct WC as (_ & _ & C3). destruct (C3 c Hc) as (_ & _ & C). destruct (C x Hin) as (_ & _ & F).
    apply F. exact Hx.
  - intros (cb & cm & Hcm & Ha). destruct WCH as [K1 _]. destruct (K1 cb cm Hcm) as (_ & B & _ & D0 & _).
    destruct (cm_prim cm) as [c'|].
    + destruct D0 as (D1 & D2 & D3 & D4 & _).
      assert (Hc' : 1 <= c' <= kLargestClassID).
      { subst c'. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
      rewrite Ha in D3, D4. pose proof (carved_unique s c c' _ Hc Hc' WR' Cx D3) as <-.
      apply D4. unfold in_free, region_of. rewrite compact_chunk_id. exact Hx.
    + destruct D0 as (_ & sc & Hsc & Hab & _). destruct WS as (_ & _ & S3 & _).
      destruct (S3 sc Hsc) as (_ & _ & _ & P1 & P2 & P3 & _).
      pose proof (carved_range s c _ Hc WR' Cx) as [L U].
      unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID, kSpaceSize, kPageSize in *.
      pose proof (class_size_mod c Hc) as [_ SZ].
      assert (4096 <= sc_map_size sc).
      { pose proof (Z.mod_pos_bound (sc_map_size sc) 4096 ltac:(lia)). 
        destruct (Z.le_gt_cases 4096 (sc_map_size sc)); [assumption|].
        rewrite Z.mod_small in P2 by lia. lia. }
      nia.
  - intros (b & Hb & Ha). destruct (batch_block s b WQ Hb) as (B1 & B2 & _).
    rewrite Ha in B1, B2.
    pose proof (carved_unique s c kBatchClass _ Hc ltac:(unfold kBatchClass, kLargestClassID; lia) WR' Cx B1) as EQ.
    apply B2. rewrite <- EQ. unfold in_free, region_of. rewrite compact_chunk_id. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pframe (s s' : astate) : Prop :=
  as_chunks s' = as_chunks s /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s /\ as_sec s' = as_sec s
  /\ as_ptr_committed s' = as_ptr_committed s /\ as_keys s' = as_keys s /\ as_frames s' = as_frames s /\ as_ndepot_ins s' = as_ndepot_ins s.

Lemma pframe_refl : forall s, pframe s s.
Proof. intros; unfold pframe; repeat split; reflexivity. Qed.
Lemma pframe_trans : forall a b c, pframe a b -> pframe b c -> pframe a c.
Proof. intros a b c (A1&A2&A3&A4&A5&A6&A7&A8) (B1&B2&B3&B4&B5&B6&B7&B8). unfold pframe. repeat split; congruence. Qed.

Lemma AWf_frame_prim : forall s s',
  pframe s s' ->
  (forall c a, carved E s c a -> carved E s' c a) ->
  (forall c a, 1 <= c <= kLargestClassID -> carved E s c a -> in_free E s' c a -> in_free E s c a \/ untracked s a) ->
  (forall c a, 1 <= c <= kLargestClassID -> carved E s c a -> in_cache E s' c a -> in_cache E s c a \/ untracked s a) ->
  wf_regions E s' -> wf_cache E s' -> AWF s -> AWF s'.
Proof.
  intros s s' (HK & HT & HG & HS & HP & HKy & HF & HN) CARV FREE0 CACHE0 WR' WC' H.
  destruct H as (WE & WR & WC & WCH & WQ & WS & WD).
  assert (KB : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  assert (UB : forall a, is_batch D s a -> untracked s a -> False) by (intros a X [_ Y]; exact (Y X)).
  assert (UC : forall a, is_chunk_block s a -> untracked s a -> False) by (intros a X [Y _]; exact (Y X)).
  split; [exact WE|]. split; [exact WR'|]. split; [exact WC'|]. split; [|split; [|split]].
  - (* [comment removed for export] *) destruct WCH as (K1 & K2). unfold wf_chunks. rewrite HK. split; [|exact K2].
    intros cb cm Hcm. destruct (K1 cb cm Hcm) as (A & B & C & D0 & E0). unfold wf_chunk.
    assert (ICB : is_chunk_block s (cm_alloc_beg cm)) by (exists cb, cm; split; [exact Hcm| reflexivity]).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    + destruct (cm_prim cm) as [c|].
      * destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
        assert (Hc : 1 <= c <= kLargestClassID).
        { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
        pose proof (FREE0 c _ Hc D3) as FREE. pose proof (CACHE0 c _ Hc D3) as CACHE.
        split; [exact D1|]. split; [exact D2|]. split; [apply CARV; exact D3|].
        split; [intros X; destruct (FREE X) as [Y|Y]; [exact (D4 Y)| exact (UC _ ICB Y)]|].
        split; [intros X; destruct (CACHE X) as [Y|Y]; [exact (D5 Y)| exact (UC _ ICB Y)]|].
        unfold is_batch, all_batches. rewrite HT, HG. exact D6.
      * rewrite HS. exact D0.
    + unfold all_batches. rewrite ?HT, ?HG. exact E0.
  - (* [comment removed for export] *) destruct WQ as (Q1 & QD & Q2 & Q3). unfold wf_quarantine, all_batches. rewrite HT, HG.
    split; [|split; [|split; [exact Q2| exact Q3]]].
    + intros b Hb. destruct (Q1 b Hb) as [WB NB]. split; [|exact NB].
      assert (IB : is_batch D s (b_addr b)) by (exists b; split; [unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb| reflexivity]).
      destruct WB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). unfold wf_batch.
      pose proof (FREE0 kBatchClass _ KB B1) as FREE. pose proof (CACHE0 kBatchClass _ KB B1) as CACHE.
      split; [apply CARV; exact B1|].
      split; [intros X; destruct (FREE X) as [Y|Y]; [exact (B2 Y)| exact (UB _ IB Y)]|].
      split; [intros X; destruct (CACHE X) as [Y|Y]; [exact (B3 Y)| exact (UB _ IB Y)]|].
      split; [unfold is_chunk_block; rewrite HK; exact B4|].
      split; [exact B5|]. split; [unfold chunk_used_size; rewrite HK; exact B6|]. split; [exact B7|].
      unfold chunk_used_size. rewrite HK. exact B8.
    + intros b Hb. destruct (QD b Hb) as (B1 & B2 & B3 & B4 & B7). unfold wf_dbatch.
      assert (IB : is_batch D s (b_addr b)) by (exists b; split; [unfold all_batches; apply in_app_iff; right; apply in_app_iff; right; exact Hb| reflexivity]).
      pose proof (FREE0 kBatchClass _ KB B1) as FREE. pose proof (CACHE0 kBatchClass _ KB B1) as CACHE.
      split; [apply CARV; exact B1|].
      split; [intros X; destruct (FREE X) as [Y|Y]; [exact (B2 Y)| exact (UB _ IB Y)]|].
      split; [intros X; destruct (CACHE X) as [Y|Y]; [exact (B3 Y)| exact (UB _ IB Y)]|].
      split; [unfold is_chunk_block; rewrite HK; exact B4| exact B7].
  - unfold wf_secondary, n_chunks. rewrite HS, HP. exact WS.
  - unfold wf_depot. rewrite HKy, HF, HN. exact WD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_firstn_In : forall {A} (n : nat) (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left; exact H. Qed.
Lemma In_skipn_In : forall {A} (n : nat) (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. right; exact H. Qed.
Lemma NoDup_firstn : forall {A} (n : nat) (l : list A), List.NoDup l -> List.NoDup (firstn n l).
Proof. intros A n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_r _ _ H). Qed.
Lemma NoDup_skipn : forall {A} (n : nat) (l : list A), List.NoDup l -> List.NoDup (skipn n l).
Proof. intros A n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_l _ _ H). Qed.
Lemma NoDup_firstn_skipn_disj : forall {A} (n : nat) (l : list A) x,
  List.NoDup l -> In x (skipn n l) -> ~ In x (firstn n l).
Proof.
  intros A n l x H Hs Hf. rewrite <- (firstn_skipn n l) in H.
  induction (firstn n l) as [|y f IH]; [destruct Hf|].
  inversion H; subst. destruct Hf as [->|Hf].
  - apply H2. apply in_app_iff. right; exact Hs.
  - exact (IH H3 Hf).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma grows_pframe : forall s s' c fr, grows s s' c fr -> pframe s s' /\ as_cache s' = as_cache s /\ as_cache_inited s' = as_cache_inited s.
Proof. intros s s' c fr (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9n&_). unfold pframe. repeat split; assumption. Qed.

Lemma grows_carved : forall s s' c fr c' a, grows s s' c fr -> carved E s c' a -> carved E s' c' a.
Proof.
  intros s s' c fr c' a (_&_&_&_&_&_&_&_&_&_&OTH&LE&_) H. eapply carved_mono; [|exact H].
  destruct (Z.eq_dec c' c) as [->|NE]; [exact LE|]. rewrite (OTH c' NE). lia.
Qed.

Lemma untracked_pframe : forall s s' a, pframe s s' -> untracked s a -> untracked s' a.
Proof.
  intros s s' a (HK&HT&HG&_) [U1 U2]. split.
  - unfold is_chunk_block. rewrite HK. exact U1.
  - unfold is_batch, all_batches. rewrite HT, HG. exact U2.
Qed.

Definition hi_ok (s' : astate) (c : Z) (hi : list Z) : Prop :=
  zlen hi = hint c /\ List.NoDup hi /\
  forall x, In x hi -> carved E s' c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0
                       /\ ~ In x (rg_free (get_region s' c)) /\ ~ In x (get_cache s' c)
                       /\ untracked s' (chunk_of_compact SB c x).

Lemma get_from_allocator_spec : forall s0 c,
  1 <= c <= kLargestClassID -> AWF s0 -> as_cache_inited s0 = true -> room s0 c ->
  hoare (fun s => s = s0) (get_from_allocator E c (hint c))
    (fun s' r => AWF s' /\ as_cache_inited s' = true /\ pframe s0 s' /\ as_cache s' = as_cache s0
                 /\ (forall c' a, carved E s0 c' a -> carved E s' c' a)
                 /\ match r with None => True | Some hi => hi_ok s' c hi end).
Proof.
  intros s0 c Hc WF HI ROOM. pose proof (hint_range c Hc) as HR.
  unfold get_from_allocator. apply hoare_get_bind. intros s ->.
  set (n := hint c). set (r0 := get_region s0 c).
  eapply hoare_bind with (Q := fun s1 ok => AWF s1 /\ as_cache_inited s1 = true /\ (exists fresh, grows s0 s1 c fresh)
                                          /\ (ok = true -> n <= rg_num_freed (get_region s1 c))).
  { match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:HB end.
    - apply Z.ltb_lt in HB.
      eapply hoare_conseq; [apply (populate_free_array_spec E P D s0 c (n - rg_num_freed r0) Hc ltac:(unfold rg_num_freed in *; lia) WF HI ROOM)| auto |].
      intros s1 ok (A & B & C & DD). split; [exact A|]. split; [exact B|]. split; [exact C|]. intros Hok. specialize (DD Hok). subst r0. lia.
    - apply Z.ltb_ge in HB. apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [exact HI|].
      split; [exists []; apply grows_refl|]. intros _. exact HB. }
  intros ok. apply hoare_pre. intros s1 (WF1 & HI1 & (fresh & GR1) & OK1).
  pose proof (grows_pframe _ _ _ _ GR1) as (PF1 & HC1 & _).
  destruct ok; cbn [negb].
  2:{ apply hoare_ret. intros s2 ->. split; [exact WF1|]. split; [exact HI1|]. split; [exact PF1|]. split; [exact HC1|].
      split; [intros c' a H; eapply grows_carved; [exact GR1| exact H]| exact I]. }
  specialize (OK1 eq_refl).
  apply hoare_get_bind. intros s2 ->.
  unfold acheck. replace (n <=? rg_num_freed (get_region s1 c)) with true by (symmetry; apply Z.leb_le; exact OK1).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s1); intros s2 ->; reflexivity|]. intros [].
  apply hoare_pre. intros s2 ->.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s2 & -> & ->).
  set (r1 := get_region s1 c) in *.
  set (keep := (length (rg_free r1) - Z.to_nat n)%nat).
  set (lo := firstn keep (rg_free r1)). set (hi := skipn keep (rg_free r1)).
  set (rn := mkRegion _ _ _ _ _ _). set (s' := set_region c rn s1).
  pose proof WF1 as WF1c. destruct WF1c as (WE1 & (R11 & R12) & WC1 & WREST1).
  pose proof (R12 c Hc) as RC1. unfold region_of in RC1. fold r1 in RC1.
  destruct RC1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  assert (GC : get_region s' c = rn) by (subst s'; apply get_set_region_eq).
  assert (GO : forall c', c' <> c -> get_region s' c' = get_region s1 c') by (intros c' NE; subst s'; apply get_set_region_ne; auto).
  assert (PF : pframe s1 s') by (subst s'; unfold pframe; repeat split; reflexivity).
  assert (CACHE : forall c', get_cache s' c' = get_cache s1 c') by (intros; subst s'; apply get_cache_set_region).
  assert (ALLOC : forall c', rg_alloc_user (get_region s' c') = rg_alloc_user (get_region s1 c')).
  { intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GC; reflexivity| rewrite GO by auto; reflexivity]. }
  assert (CARV : forall c' a, carved E s1 c' a <-> carved E s' c' a).
  { intros c' a. unfold carved, region_of. rewrite ALLOC. tauto. }
  assert (FREE : forall c' x, In x (rg_free (get_region s' c')) -> In x (rg_free (get_region s1 c'))).
  { intros c' x. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GC; cbn; apply In_firstn_In| rewrite GO by auto; auto]. }
  assert (WR' : wf_regions E s').
  { split.
    - subst s'. rewrite as_regions_set_region. intros c0 r2 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|].
      rewrite lookup_insert_ne in Hl by auto. eapply R11; exact Hl.
    - intros c0 Hc0. cbn zeta. unfold region_of. destruct (Z.eq_dec c0 c) as [->|NE].
      + rewrite GC. subst rn. cbn [rg_alloc_user rg_mapped_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
        assert (P8 : 4 * rg_num_freed {| rg_mapped_user := rg_mapped_user r1; rg_alloc_user := rg_alloc_user r1; rg_free := lo;
                        rg_mapped_fa := rg_mapped_fa r1; rg_n_allocated := rg_n_allocated r1 + n; rg_n_freed := rg_n_freed r1 |} <= rg_mapped_fa r1).
        { unfold rg_num_freed in *. cbn [rg_free]. subst lo. rewrite length_firstn. lia. }
        assert (P9 : List.NoDup lo) by (subst lo; apply NoDup_firstn; exact A9).
        assert (P10 : forall x, In x lo -> carved E s' c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0).
        { intros x Hx. destruct (A10 x (In_firstn_In _ _ _ Hx)) as [Cx Mx]. split; [apply CARV; exact Cx| exact Mx]. }
        assert (P11 : 0 <= rg_n_allocated r1 + n) by lia.
        exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj P8 (conj P9 (conj P10 (conj P11 A12))))))))))).
      + rewrite GO by auto. specialize (R12 c0 Hc0). unfold region_of in R12.
        destruct R12 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
        refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj _ (conj C11 C12))))))))))).
        intros x Hx. destruct (C10 x Hx) as [Cx Mx]. split; [apply CARV; exact Cx| exact Mx]. }
  assert (WC' : wf_cache E s').
  { destruct WC1 as (C1 & C2 & C3). unfold wf_cache.
    replace (as_cache s') with (as_cache s1) by (subst s'; reflexivity).
    replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI1).
    split; [exact C1|]. split; [discriminate|].
    intros c0 Hc0. rewrite CACHE. destruct (C3 c0 Hc0) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
    intros x Hx. destruct (X3 x Hx) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2|].
    intros Z3. apply Y3. unfold region_of in *. apply FREE. exact Z3. }
  assert (WF' : AWF s').
  { eapply AWf_frame_prim; [exact PF| intros c' a H; apply CARV; exact H | | | exact WR' | exact WC' | exact WF1].
    - intros c' a _ _ H. left. unfold in_free, region_of in *. apply FREE. exact H.
    - intros c' a _ _ H. left. unfold in_cache in *. rewrite CACHE in H. exact H. }
  split; [exact WF'|]. split; [subst s'; cbn; exact HI1|]. split; [eapply pframe_trans; [exact PF1| exact PF]|].
  split; [subst s'; cbn; exact HC1|].
  split; [intros c' a H; apply CARV; eapply grows_carved; [exact GR1| exact H]|].
  (* [comment removed for export] *)
  assert (LEN : zlen hi = n).
  { unfold zlen. subst hi. rewrite length_skipn. subst keep. unfold rg_num_freed in OK1. lia. }
  split; [exact LEN|]. split; [subst hi; apply NoDup_skipn; exact A9|].
  intros x Hx. pose proof (In_skipn_In _ _ _ Hx) as Hx1.
  destruct (A10 x Hx1) as [Cx Mx].
  destruct (free_entry_untracked s1 c x WF1 Hc Hx1) as [NC UT].
  split; [apply CARV; exact Cx|]. split; [exact Mx|].
  split; [rewrite GC; cbn; subst lo hi; apply NoDup_firstn_skipn_disj; [exact A9| exact Hx]|].
  split; [rewrite CACHE; exact NC|].
  eapply untracked_pframe; [exact PF| exact UT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cache_entry_untracked : forall s c x, AWF s -> 1 <= c <= kLargestClassID ->
  In x (get_cache s c) -> ~ In x (rg_free (get_region s c)) /\ untracked s (chunk_of_compact SB c x).
Proof.
  intros s c x WF Hc Hx. destruct WF as (WE & WR & WC & WCH & WQ & WS & WD).
  destruct WC as (_ & _ & C3). destruct (C3 c Hc) as (_ & _ & C). destruct (C x Hx) as (Cx & Mx & Fx).
  split; [exact Fx|]. split.
  - intros (cb & cm & Hcm & Ha). destruct WCH as [K1 _]. destruct (K1 cb cm Hcm) as (_ & B & _ & D0 & _).
    destruct (cm_prim cm) as [c'|].
    + destruct D0 as (D1 & D2 & D3 & D4 & D5 & _).
      assert (Hc' : 1 <= c' <= kLargestClassID).
      { subst c'. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
      rewrite Ha in D3, D5. pose proof (carved_unique s c c' _ Hc Hc' WR Cx D3) as <-.
      apply D5. unfold in_cache. rewrite compact_chunk_id. exact Hx.
    + destruct D0 as (_ & sc & Hsc & Hab & _). destruct WS as (_ & _ & S3 & _).
      destruct (S3 sc Hsc) as (_ & _ & _ & P1 & P2 & P3 & _).
      pose proof (carved_range s c _ Hc WR Cx) as [L U].
      unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID, kSpaceSize, kPageSize in *.
      pose proof (class_size_mod c Hc) as [_ SZ].
      assert (4096 <= sc_map_size sc).
      { destruct (Z.le_gt_cases 4096 (sc_map_size sc)); [assumption|]. rewrite Z.mod_small in P2 by lia. lia. }
      nia.
  - intros (b & Hb & Ha). destruct (batch_block s b WQ Hb) as (B1 & B2 & B3 & _).
    rewrite Ha in B1, B3.
    pose proof (carved_unique s c kBatchClass _ Hc ltac:(unfold kBatchClass, kLargestClassID; lia) WR Cx B1) as EQ.
    apply B3. rewrite <- EQ. unfold in_cache. rewrite compact_chunk_id. exact Hx.
Qed.

Lemma init_cache_wf : forall s, AWF s -> AWF (upd_cache_inited true s).
Proof.
  intros s (WE & WR & (C1 & C2 & C3) & WCH & WQ & WS & WD).
  split; [exact WE|]. split; [exact WR|]. split; [| exact (conj WCH (conj WQ (conj WS WD)))].
  split; [exact C1|]. split; [cbn; discriminate| exact C3].
Qed.

Lemma room_same_regions : forall s s' c, as_regions s' = as_regions s -> room s c -> room s' c.
Proof. intros s s' c H R. unfold room, get_region in *. rewrite H. exact R. Qed.

Lemma refill_spec : forall s0 c,
  1 <= c <= kLargestClassID -> AWF s0 -> get_cache s0 c = [] -> room s0 c ->
  hoare (fun s => s = s0) (refill E c)
    (fun s' ok => AWF s' /\ as_cache_inited s' = true /\ pframe s0 s'
                  /\ (forall c' a, carved E s0 c' a -> carved E s' c' a)
                  /\ (forall c', c' <> c -> get_cache s' c' = get_cache s0 c')
                  /\ (ok = true -> get_cache s' c <> [])).
Proof.
  intros s0 c Hc WF EMP ROOM. unfold refill, init_cache.
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->).
  set (s1 := upd_cache_inited true s0).
  assert (WF1 : AWF s1) by (apply init_cache_wf; exact WF).
  assert (R1 : room s1 c) by (eapply room_same_regions; [| exact ROOM]; reflexivity).
  eapply hoare_bind; [apply (get_from_allocator_spec s1 c Hc WF1 eq_refl R1)|].
  intros r. apply hoare_pre. intros s2 (WF2 & HI2 & PF2 & HC2 & CV2 & HR).
  assert (PF02 : pframe s0 s2) by (eapply pframe_trans; [| exact PF2]; unfold pframe; repeat split; reflexivity).
  assert (CV02 : forall c' a, carved E s0 c' a -> carved E s2 c' a) by (intros c' a H; apply CV2; exact H).
  assert (GC2 : forall c', get_cache s2 c' = get_cache s0 c') by (intros c'; unfold get_cache; rewrite HC2; reflexivity).
  destruct r as [hi|].
  2:{ apply hoare_ret. intros s ->. split; [exact WF2|]. split; [exact HI2|]. split; [exact PF02|]. split; [exact CV02|].
      split; [intros c' _; apply GC2| discriminate]. }
  destruct HR as (LEN & ND & HX).
  apply hoare_upd_bind. apply hoare_ret. intros s' (s & -> & ->).
  set (s' := upd_cache_stale _ (set_cache c hi s2)).
  assert (GCe : get_cache s' c = hi) by (subst s'; rewrite get_cache_upd_cache_stale, get_set_cache_eq; reflexivity).
  assert (GCo : forall c', c' <> c -> get_cache s' c' = get_cache s2 c') by (intros c' NE; subst s'; rewrite get_cache_upd_cache_stale, get_set_cache_ne by auto; reflexivity).
  assert (GR : forall c', get_region s' c' = get_region s2 c') by (intros; subst s'; reflexivity).
  assert (PF : pframe s2 s') by (subst s'; unfold pframe; repeat split; reflexivity).
  assert (CARV : forall c' a, carved E s2 c' a <-> carved E s' c' a) by (intros; unfold carved, region_of; rewrite GR; tauto).
  pose proof (hint_range c Hc) as HR.
  assert (WF' : AWF s').
  { pose proof WF2 as X. destruct X as (WE2 & WR2 & (C1 & C2 & C3) & _).
    eapply AWf_frame_prim; [exact PF| intros c' a H; apply CARV; exact H| | | | | exact WF2].
    - intros c' a _ _ H. left. unfold in_free, region_of in *. rewrite GR in H. exact H.
    - intros c' a Hc' Ca H. unfold in_cache in *. destruct (Z.eq_dec c' c) as [->|NE].
      + rewrite GCe in H. right. destruct (HX _ H) as (_ & _ & _ & _ & U). rewrite (carved_coc s2 c a Hc Ca) in U. exact U.
      + left. rewrite GCo in H by auto. exact H.
    - destruct WR2 as [W1 W2]. split; [subst s'; cbn; exact W1|].
      intros c0 Hc0. unfold region_of. rewrite GR. specialize (W2 c0 Hc0). unfold region_of in W2. cbn zeta in W2.
      destruct W2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
      refine (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 (conj D7 (conj D8 (conj D9 (conj _ (conj D11 D12))))))))))).
      intros x Hx. destruct (D10 x Hx) as [Cx Mx]. split; [apply CARV; exact Cx| exact Mx].
    - unfold wf_cache. replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI2).
      split; [| split; [discriminate|]].
      + subst s'. cbn. intros c0 l Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hl by auto. eapply C1; exact Hl.
      + intros c0 Hc0. unfold region_of. rewrite GR. destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite GCe. split; [unfold max_count; lia|]. split; [exact ND|].
          intros x Hx. destruct (HX x Hx) as (Y1 & Y2 & Y3 & _). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3].
        * rewrite GCo by auto. destruct (C3 c0 Hc0) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
          intros x Hx. destruct (X3 x Hx) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3]. }
  split; [exact WF'|]. split; [subst s'; cbn; exact HI2|]. split; [eapply pframe_trans; [exact PF02| exact PF]|].
  split; [intros c' a H; apply CARV; apply CV02; exact H|].
  split; [intros c' NE; rewrite GCo by auto; apply GC2|].
  intros _. rewrite GCe. intros X. rewrite X in LEN. unfold zlen in LEN. cbn in LEN. clear -LEN HR. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition avail (s : astate) (c a : Z) : Prop :=
  carved E s c a /\ ~ in_free E s c a /\ ~ in_cache E s c a /\ untracked s a.

Lemma removelast_eq : forall {A} (l : list A), removelast l = List.removelast l.
Proof.
  intros A l. unfold removelast. symmetry. apply removelast_firstn_len. Qed.

Lemma wf_regions_same : forall s s', as_regions s' = as_regions s -> wf_regions E s -> wf_regions E s'.
Proof.
  intros s s' H W. unfold wf_regions, carved, region_of, get_region in *. rewrite H. exact W.
Qed.

Lemma cache_pop_spec : forall s0 c,
  1 <= c <= kLargestClassID -> AWF s0 -> room s0 c ->
  hoare (fun s => s = s0) (cache_pop E c)
    (fun s' r => AWF s' /\ pframe s0 s'
                 /\ (forall c' a, carved E s0 c' a -> carved E s' c' a)
                 /\ (forall c', c' <> c -> get_cache s' c' = get_cache s0 c')
                 /\ match r with
                    | None => True
                    | Some a => as_cache_inited s' = true /\ avail s' c a
                                /\ exists x, a = chunk_of_compact SB c x /\ (16 * x) mod class_size c = 0
                    end).
Proof.
  intros s0 c Hc WF ROOM. unfold cache_pop. apply hoare_get_bind. intros s ->.
  eapply hoare_bind with (Q := fun s1 ok => AWF s1 /\ pframe s0 s1 /\ (forall c' a, carved E s0 c' a -> carved E s1 c' a)
                                          /\ (forall c', c' <> c -> get_cache s1 c' = get_cache s0 c')
                                          /\ (ok = true -> get_cache s1 c <> [] /\ as_cache_inited s1 = true)).
  { destruct (get_cache s0 c) as [|y l] eqn:HC0.
    - eapply hoare_conseq; [apply (refill_spec s0 c Hc WF HC0 ROOM)| auto|].
      intros s1 ok (A & B & C & DD & F & G). split; [exact A|]. split; [exact C|]. split; [exact DD|]. split; [exact F|].
      intros Hok. split; [exact (G Hok)| exact B].
    - apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [apply pframe_refl|]. split; [auto|]. split; [auto|].
      intros _. rewrite HC0. split; [discriminate|].
      destruct (as_cache_inited s0) eqn:HI; [reflexivity|]. exfalso.
      destruct WF as (_ & _ & (_ & C2 & _) & _). destruct (C2 HI) as [CE _].
      unfold get_cache in HC0. rewrite CE, lookup_empty in HC0. discriminate. }
  intros ok. apply hoare_pre. intros s1 (WF1 & PF1 & CV1 & OC1 & OK1).
  destruct ok; cbn [negb].
  2:{ apply hoare_ret. intros s2 ->. split; [exact WF1|]. split; [exact PF1|]. split; [exact CV1|]. split; [exact OC1| exact I]. }
  destruct (OK1 eq_refl) as [NE1 HI1].
  apply hoare_get_bind. intros s2 ->.
  destruct (get_cache s1 c) as [|y l'] eqn:HC1; [exfalso; exact (NE1 eq_refl)|].
  set (l := y :: l') in *.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s2 & -> & ->).
  set (x := List.last l 0). set (s' := upd_cache_allocated _ (upd_cache_stale _ (set_cache c (removelast l) s1))).
  assert (LNE : l <> []) by (subst l; discriminate).
  pose proof (app_removelast_last 0 LNE) as SPLIT. fold x in SPLIT. rewrite <- removelast_eq in SPLIT.
  assert (INx : In x l) by (rewrite SPLIT; apply in_app_iff; right; left; reflexivity).
  assert (INrl : forall z, In z (removelast l) -> In z l) by (intros z Hz; rewrite SPLIT; apply in_app_iff; left; exact Hz).
  assert (GCe : get_cache s' c = removelast l) by (subst s'; rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_eq; reflexivity).
  assert (GCo : forall c', c' <> c -> get_cache s' c' = get_cache s1 c').
  { intros c' NE; subst s'. rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_ne by auto. reflexivity. }
  assert (RG : as_regions s' = as_regions s1) by (subst s'; reflexivity).
  assert (GR : forall c', get_region s' c' = get_region s1 c') by (intros; unfold get_region; rewrite RG; reflexivity).
  assert (PF : pframe s1 s') by (subst s'; unfold pframe; repeat split; reflexivity).
  assert (CARV : forall c' a, carved E s1 c' a <-> carved E s' c' a) by (intros; unfold carved, region_of; rewrite GR; tauto).
  pose proof WF1 as X. destruct X as (WE1 & WR1 & (C1 & C2 & C3) & _).
  destruct (C3 c Hc) as (X1 & X2 & X3).
  rewrite HC1 in X1, X2, X3.
  assert (NDl : List.NoDup l) by exact X2.
  assert (NIx : ~ In x (removelast l)).
  { rewrite SPLIT in NDl. pose proof (NoDup_remove_2 _ [] _ NDl) as R. rewrite app_nil_r in R. exact R. }
  assert (WF' : AWF s').
  { eapply AWf_frame_prim; [exact PF| intros c' a H; apply CARV; exact H| | | | | exact WF1].
    - intros c' a _ _ H. left. unfold in_free, region_of in *. rewrite GR in H. exact H.
    - intros c' a _ _ H. left. unfold in_cache in *. destruct (Z.eq_dec c' c) as [->|NE].
      + rewrite GCe in H. rewrite HC1. apply INrl. exact H.
      + rewrite GCo in H by auto. exact H.
    - eapply wf_regions_same; [exact RG| exact WR1].
    - unfold wf_cache. replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI1).
      split; [| split; [discriminate|]].
      + subst s'. cbn. intros c0 l0 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hl by auto. eapply C1; exact Hl.
      + intros c0 Hc0. unfold region_of. rewrite GR. destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite GCe. split.
          { unfold zlen in *. rewrite SPLIT in X1. rewrite length_app in X1. replace (length [x]) with 1%nat in X1 by reflexivity. clear -X1. lia. }
          split; [rewrite SPLIT in NDl; exact (NoDup_app_remove_r _ _ NDl)|].
          intros z Hz. destruct (X3 z (INrl z Hz)) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3].
        * rewrite GCo by auto. destruct (C3 c0 Hc0) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
          intros z Hz. destruct (Z3 z Hz) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3]. }
  split; [exact WF'|]. split; [eapply pframe_trans; [exact PF1| exact PF]|].
  split; [intros c' a H; apply CARV; apply CV1; exact H|].
  split; [intros c' NE; rewrite GCo by auto; apply OC1; exact NE|].
  split; [subst s'; cbn; exact HI1|].
  destruct (X3 x INx) as (Cx & Mx & Fx).
  split.
  - split; [apply CARV; exact Cx|]. split.
    + unfold in_free, region_of. rewrite compact_chunk_id, GR. exact Fx.
    + split; [unfold in_cache; rewrite compact_chunk_id, GCe; exact NIx|].
      eapply untracked_pframe; [exact PF|].
      pose proof (cache_entry_untracked s1 c x WF1 Hc ltac:(rewrite HC1; exact INx)) as [_ U]. exact U.
  - exists x. split; [reflexivity| exact Mx].
Qed.

End WF.
End RC__1.
