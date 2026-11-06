(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6.
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
Variable D : list batch.
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AWf_delete_chunk : forall s m f,
  AWF s -> (forall b, In b (as_tq s ++ as_gq s) -> ~ In m (b_items b)) ->
  AWF (upd_dead f (upd_chunks (delete m) s)).
Proof.
  intros s m f WF NIN. set (s' := upd_dead f _).
  assert (HK : as_chunks s' = delete m (as_chunks s)) by reflexivity.
  assert (OLD : forall cb cm, as_chunks s' !! cb = Some cm -> as_chunks s !! cb = Some cm /\ cb <> m).
  { intros cb cm H. rewrite HK in H. destruct (Z.eq_dec cb m) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate|].
    rewrite lookup_delete_ne in H by auto. auto. }
  assert (KEEP : forall cb cm, as_chunks s !! cb = Some cm -> cb <> m -> as_chunks s' !! cb = Some cm).
  { intros cb cm H NE. rewrite HK, lookup_delete_ne by auto. exact H. }
  assert (ICB : forall a, is_chunk_block s' a -> is_chunk_block s a).
  { intros a (cb & cm & H & Ha). exists cb, cm. split; [exact (proj1 (OLD _ _ H))| exact Ha]. }
  destruct WF as (WE & WR & WC & [K1 K2] & (Q1 & QD & Q2 & Q3) & WS & WD).
  split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
  split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
  split; [|split; [|split; [exact WS| exact WD]]].
  - split.
    + intros cb cm H. destruct (OLD _ _ H) as [H0 _]. eapply wf_chunk_frame; [..|exact (K1 _ _ H0)]; reflexivity.
    + intros cb1 cm1 cb2 cm2 H1 H2 NE. exact (K2 _ _ _ _ (proj1 (OLD _ _ H1)) (proj1 (OLD _ _ H2)) NE).
  - unfold wf_quarantine. change (as_tq s') with (as_tq s). change (as_gq s') with (as_gq s). change (all_batches D s') with (all_batches D s).
    split; [|split; [|split; [exact Q2| exact Q3]]].
    + intros b Hb. destruct (Q1 b Hb) as [(B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) NB]. split; [|exact NB].
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [intros X; exact (B4 (ICB _ X))|]. split; [exact B5|].
      split.
      { rewrite B6. f_equal. pose proof (NIN b Hb) as NI. clear -NI HK. induction (b_items b) as [|i l IH]; [reflexivity|]. cbn.
        assert (i <> m) by (intros ->; apply NI; left; reflexivity).
        replace (chunk_used_size s' i) with (chunk_used_size s i) by (unfold chunk_used_size; rewrite HK, lookup_delete_ne by auto; reflexivity).
        rewrite IH; [reflexivity|]. intros X; apply NI; right; exact X. }
      split; [exact B7|].
      intros x Hx. destruct (B8 x Hx) as (cm & i & j & H & Hs). exists cm, i, j. split; [|exact Hs].
      apply KEEP; [exact H|]. intros ->. exact (NIN b Hb Hx).
    + intros b Hb. destruct (QD b Hb) as (B1 & B2 & B3 & B4 & B7).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [intros X; exact (B4 (ICB _ X))| exact B7].
Qed.

(* [comment removed for export] *)
Lemma deleted_block_avail : forall s m cm c f,
  AWF s -> as_chunks s !! m = Some cm -> cm_prim cm = Some c ->
  avail E D (upd_dead f (upd_chunks (delete m) s)) c (cm_alloc_beg cm).
Proof.
  intros s m cm c f WF Hcm PC. destruct WF as (WE & WR & WC & [K1 K2] & WQ & WS & WD).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & E0). rewrite PC in D0. destruct D0 as (D1 & D2 & D3 & D4 & D5 & D6).
  split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [|exact D6].
  intros (cb & cm' & H & Ha). cbn in H. destruct (Z.eq_dec cb m) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate|].
  rewrite lookup_delete_ne in H by auto. exact (K2 _ _ _ _ H Hcm NE Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma prim_chunk_geometry : forall s m cm c,
  AWF s -> as_chunks s !! m = Some cm -> cm_prim cm = Some c ->
  let off := m - SB in
  in_primary SB m = true
  /\ off / kRegionSize = c /\ (off / kRegionSize) mod kNumClasses = c
  /\ region_beg SB c + ((off mod kRegionSize) / class_size c) * class_size c = cm_alloc_beg cm
  /\ ((off mod kRegionSize) / class_size c + 1) * class_size c <= rg_mapped_user (get_region s c)
  /\ 0 < cm_alloc_beg cm.
Proof.
  intros s m cm c WF Hcm PC. pose proof (chunk_beg_loc E P D s m cm WF Hcm) as LOC. rewrite PC in LOC.
  destruct LOC as (Hc & CV & L1 & L2). pose proof WF as X. destruct X as ((_ & HB & RS & _) & WR & _).
  pose proof (carved_range E s c _ Hc WR CV) as [R1 R2]. pose proof (class_size_mod c Hc) as [_ SZ].
  destruct CV as (k & Hk & Hab & Hk1). destruct WR as [_ W2]. destruct (W2 c Hc) as (A1 & _ & A3 & _).
  unfold region_of in *. rewrite kHighMemBeg_val in HB.
  unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID, kNumClasses, kSpaceSize in *. cbn zeta.
  set (size := class_size c) in *. set (d := m - cm_alloc_beg cm).
  assert (Hd : 0 <= d < size) by (subst d; lia).
  assert (OFF : m - SB = c * 2^32 + (k * size + d)) by (subst d; rewrite Hab; lia).
  assert (KS : 0 <= k * size) by (apply Z.mul_nonneg_nonneg; lia).
  assert (LOW : 0 <= k * size + d < 2^32) by nia.
  assert (DIV : (m - SB) / 2^32 = c).
  { rewrite OFF. rewrite (Z.add_comm (c * 2^32)), Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (MOD : (m - SB) mod 2^32 = k * size + d).
  { rewrite OFF. rewrite (Z.add_comm (c * 2^32)), Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (IDX : (k * size + d) / size = k).
  { rewrite (Z.add_comm (k * size)), Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split; [unfold in_primary, kSpaceSize; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; nia|].
  rewrite DIV, MOD, IDX. split; [reflexivity|]. split; [apply Z.mod_small; lia|].
  split; [rewrite Hab; lia|]. split; [lia|]. rewrite Hab. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carved_list_bound : forall s c l, 1 <= c <= kLargestClassID -> wf_regions E s -> List.NoDup l ->
  (forall x, In x l -> carved E s c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0) ->
  zlen l * class_size c <= rg_alloc_user (get_region s c) /\ 4 * zlen l <= kFreeArraySize.
Proof.
  intros s c l Hc WR ND HX0. pose proof (class_size_mod c Hc) as [SZM SZB].
  destruct WR as [_ W2]. destruct (W2 c Hc) as (A1 & A2 & A3 & _). unfold region_of in *.
  set (size := class_size c) in *. set (au := rg_alloc_user (get_region s c)) in *.
  assert (S16 : size = 16 * (size / 16)).
  { pose proof (Z.div_mod size 16 ltac:(lia)).
    assert (size mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in SZM; [|lia]. destruct SZM as [q Hq]. exists (2*q); lia. }
    lia. }
  assert (K0 : 0 <= au / size) by (apply Z.div_pos; lia).
  assert (HX : forall x, In x l -> exists k, 0 <= k < au / size /\ x = k * (size / 16)).
  { intros x Hx. destruct (HX0 x Hx) as [(k & Hk & Ha & Hb) Mx]. exists k.
    unfold chunk_of_compact, region_of in Ha. unfold region_of in Hb. fold au in Hb.
    assert (E16 : 16 * x = k * size) by (subst size; lia).
    split; [| clear -E16 S16; rewrite S16 in E16; lia]. split; [exact Hk|].
    assert (k + 1 <= au / size); [| clear -H; lia].
    apply Z.div_le_lower_bound; clear -Hb SZB; subst size; lia. }
  pose proof (pigeonhole_multiples l (au / size) (size / 16) ltac:(lia) K0 ND HX) as PG.
  pose proof (div_mul_le au size ltac:(lia) ltac:(lia)) as DM.
  assert (B1 : zlen l * size <= au).
  { unfold zlen. eapply Z.le_trans; [| exact DM]. apply Z.mul_le_mono_nonneg_r; [lia| exact PG]. }
  split; [exact B1|].
  assert (zlen l * 32 <= zlen l * size) by (apply Z.mul_le_mono_nonneg_l; unfold zlen; lia).
  unfold kFreeArraySize, kFreeArrayOffset in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition returnable (s : astate) (c : Z) (l : list Z) : Prop :=
  List.NoDup l /\
  forall x, In x l -> carved E s c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0
                      /\ ~ In x (rg_free (get_region s c)) /\ ~ In x (get_cache s c) /\ untracked D s (chunk_of_compact SB c x).

Lemma return_to_allocator_spec : forall s0 c chunks,
  1 <= c <= kLargestClassID -> AWF s0 -> as_cache_inited s0 = true -> returnable s0 c chunks ->
  hoare (fun s => s = s0) (return_to_allocator E c chunks)
    (fun s' _ => AWF s' /\ pframe s0 s' /\ as_cache s' = as_cache s0 /\ as_cache_inited s' = true
                 /\ (forall c' a, carved E s0 c' a -> carved E s' c' a)
                 /\ (forall c' y, In y (rg_free (get_region s' c')) -> In y (rg_free (get_region s0 c')) \/ (c' = c /\ In y chunks))).
Proof.
  intros s0 c chunks Hc WF HI [ND RX]. unfold return_to_allocator. apply hoare_get_bind. intros s ->.
  pose proof WF as X. destruct X as (WE & WR & WC & _).
  pose proof WR as X. destruct X as [_ W2]. destruct (W2 c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). unfold region_of in *.
  set (r0 := get_region s0 c) in *.
  set (new := rg_num_freed r0 + zlen chunks).
  assert (NDA : List.NoDup (rg_free r0 ++ chunks)).
  { apply NoDup_app; [exact A9| exact ND|]. intros x Hx Hc'. destruct (RX x Hc') as (_ & _ & NF & _). exact (NF Hx). }
  assert (CB : forall x, In x (rg_free r0 ++ chunks) -> carved E s0 c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0).
  { intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; [exact (A10 x Hx)|]. destruct (RX x Hx) as (C1 & C2 & _). auto. }
  pose proof (carved_list_bound s0 c _ Hc WR NDA CB) as [_ BND].
  assert (NEWB : 4 * new <= kFreeArraySize) by (subst new; unfold rg_num_freed, zlen in *; rewrite length_app, Nat2Z.inj_add in BND; lia).
  eapply hoare_bind; [apply (ensure_free_array_space_spec E P D s0 c new Hc NEWB WF HI ltac:(subst new r0; unfold zlen; lia))|].
  intros ok. apply hoare_pre. intros s1 (WF1 & HI1 & GR1 & AL1 & MU1 & FA1 & OK1).
  destruct ok; cbn [negb]; [|apply hoare_spin]. specialize (OK1 eq_refl).
  apply hoare_get_bind. intros s ->. apply hoare_upd. intros s ->.
  pose proof (grows_pframe _ _ _ _ GR1) as (PF1 & HC1 & _).
  destruct GR1 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G9n & OTH & LE & FR & _). rewrite app_nil_r in FR.
  set (r1 := get_region s1 c) in *.
  set (rn := mkRegion _ _ _ _ _ _). set (s' := set_region c rn s1).
  assert (GC : get_region s' c = rn) by (subst s'; apply get_set_region_eq).
  assert (GO : forall c', c' <> c -> get_region s' c' = get_region s1 c') by (intros c' NE; subst s'; apply get_set_region_ne; auto).
  assert (CACHE : forall c', get_cache s' c' = get_cache s1 c') by (intros; subst s'; apply get_cache_set_region).
  assert (ALLOC : forall c', rg_alloc_user (get_region s' c') = rg_alloc_user (get_region s1 c')).
  { intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GC; reflexivity| rewrite GO by auto; reflexivity]. }
  assert (CARV : forall c' a, carved E s1 c' a <-> carved E s' c' a) by (intros; unfold carved, region_of; rewrite ALLOC; tauto).
  assert (CARV0 : forall c' a, carved E s0 c' a -> carved E s1 c' a).
  { intros c' a H. eapply carved_mono; [|exact H]. destruct (Z.eq_dec c' c) as [->|NE]; [exact LE| rewrite (OTH c' NE); lia]. }
  assert (FREE : forall c' y, In y (rg_free (get_region s' c')) -> In y (rg_free (get_region s0 c')) \/ (c' = c /\ In y chunks)).
  { intros c' y. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GC. subst rn; cbn. fold r1. rewrite FR. intros H. apply in_app_iff in H as [H|H]; [left; exact H| right; auto].
    - rewrite GO by auto. rewrite (OTH c' NE). left; auto. }
  pose proof WF1 as X. destruct X as (_ & [R11 R12] & (C1 & C2 & C3) & _).
  assert (WR' : wf_regions E s').
  { split.
    - subst s'. rewrite as_regions_set_region. intros c0 r2 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|].
      rewrite lookup_insert_ne in Hl by auto. eapply R11; exact Hl.
    - intros c0 Hc0. cbn zeta. unfold region_of. destruct (Z.eq_dec c0 c) as [->|NE].
      + rewrite GC. subst rn. cbn [rg_alloc_user rg_mapped_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
        specialize (R12 c Hc). unfold region_of in R12. fold r1 in R12.
        destruct R12 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
        assert (P8 : 4 * rg_num_freed {| rg_mapped_user := rg_mapped_user r1; rg_alloc_user := rg_alloc_user r1; rg_free := rg_free r1 ++ chunks;
                       rg_mapped_fa := rg_mapped_fa r1; rg_n_allocated := rg_n_allocated r1; rg_n_freed := rg_n_freed r1 + zlen chunks |} <= rg_mapped_fa r1).
        { unfold rg_num_freed in *. cbn [rg_free]. rewrite length_app, Nat2Z.inj_add. rewrite FR. subst new. unfold zlen in *. subst r0. lia. }
        assert (P9 : List.NoDup (rg_free r1 ++ chunks)) by (rewrite FR; exact NDA).
        assert (P10 : forall x, In x (rg_free r1 ++ chunks) -> carved E s' c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0).
        { intros x Hx. rewrite FR in Hx. destruct (CB x Hx) as [Cx Mx]. split; [apply CARV; apply CARV0; exact Cx| exact Mx]. }
        assert (P12 : 0 <= rg_n_freed r1 + zlen chunks) by (unfold zlen; lia).
        exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj P8 (conj P9 (conj P10 (conj B11 P12))))))))))).
      + rewrite GO by auto. specialize (R12 c0 Hc0). unfold region_of in R12.
        destruct R12 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
        refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj B8 (conj B9 (conj _ (conj B11 B12))))))))))).
        intros x Hx. destruct (B10 x Hx) as [Cx Mx]. split; [apply CARV; exact Cx| exact Mx]. }
  assert (WC' : wf_cache E s').
  { unfold wf_cache. replace (as_cache s') with (as_cache s1) by (subst s'; reflexivity).
    replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI1).
    split; [exact C1|]. split; [discriminate|].
    intros c0 Hc0. rewrite CACHE. destruct (C3 c0 Hc0) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
    intros x Hx. destruct (X3 x Hx) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2|].
    unfold region_of in *. intros Z3. destruct (FREE c0 x Z3) as [Z4|[-> Z4]].
    - destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite <- FR in Z4; exact (Y3 Z4)|]. rewrite <- (OTH c0 NE) in Z4. exact (Y3 Z4).
    - destruct (RX x Z4) as (_ & _ & _ & NC & _). apply NC. unfold get_cache in *. rewrite <- HC1. exact Hx. }
  assert (WF' : AWF s').
  { eapply AWf_frame_prim; [| intros c' a H; apply CARV; exact H | | | exact WR' | exact WC' | exact WF1].
    - subst s'; unfold pframe; repeat split; reflexivity.
    - intros c' a Hc' Ca H. unfold in_free, region_of in *. destruct (FREE c' _ H) as [H0|[-> H0]].
      + destruct (Z.eq_dec c' c) as [->|NE]; [left; rewrite <- FR in H0; exact H0|]. left. rewrite (OTH c' NE). exact H0.
      + right. destruct (RX _ H0) as (_ & _ & _ & _ & U). rewrite (carved_coc E s1 c a Hc Ca) in U.
        eapply untracked_pframe; [exact PF1| exact U].
    - intros c' a _ _ H. left. unfold in_cache in *. rewrite CACHE in H. exact H. }
  split; [exact WF'|]. split; [eapply pframe_trans; [exact PF1| subst s'; unfold pframe; repeat split; reflexivity]|].
  split; [subst s'; cbn; exact HC1|]. split; [subst s'; cbn; exact HI1|].
  split; [intros c' a H; apply CARV; apply CARV0; exact H| exact FREE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carved_compact : forall s c p, 1 <= c <= kLargestClassID -> carved E s c p ->
  (16 * compact_of_chunk SB c p) mod class_size c = 0 /\ chunk_of_compact SB c (compact_of_chunk SB c p) = p.
Proof.
  intros s c p Hc CV. split; [| exact (carved_coc E s c p Hc CV)].
  pose proof (carved_coc E s c p Hc CV) as EQ. unfold chunk_of_compact in EQ.
  destruct CV as (k & Hk & Hp & _).
  replace (16 * compact_of_chunk SB c p) with (k * class_size c) by lia. apply Z_mod_mult.
Qed.

Lemma local_dealloc_spec : forall s0 c p,
  1 <= c <= kLargestClassID -> AWF s0 -> avail E D s0 c p ->
  hoare (fun s => s = s0) (local_dealloc E c p)
    (fun s' _ => AWF s' /\ pframe s0 s' /\ (forall c' a, carved E s0 c' a -> carved E s' c' a) /\ as_cache_inited s' = true).
Proof.
  intros s0 c p Hc WF AV. pose proof (hint_range c Hc) as HR. unfold local_dealloc.
  unfold acheck. replace ((1 <=? c) && (c <? kNumClasses)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kNumClasses, kLargestClassID in *; lia).
  eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros []. apply hoare_pre. intros s ->.
  unfold init_cache. apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->).
  set (s1 := upd_cache_inited true s0).
  assert (WF1 : AWF s1) by (apply init_cache_wf; exact WF).
  assert (AV1 : avail E D s1 c p) by (eapply avail_frame; [..| exact AV]; reflexivity).
  assert (HI1 : as_cache_inited s1 = true) by reflexivity.
  assert (PF01 : pframe s0 s1) by (unfold pframe; repeat split; reflexivity).
  apply hoare_get_bind. intros s ->.
  set (l := get_cache s1 c).
  pose proof WF1 as X. destruct X as (WE1 & WR1 & (C1 & C2 & C3) & _). destruct (C3 c Hc) as (X1 & X2 & X3). fold l in X1, X2, X3.
  destruct AV1 as (CVp & NFp & NCp & Up). unfold in_cache in NCp. fold l in NCp.
  eapply hoare_bind with (Q := fun s3 _ => AWF s3 /\ pframe s1 s3 /\ (forall c' a, carved E s1 c' a -> carved E s3 c' a) /\ as_cache_inited s3 = true
                                         /\ (forall y, In y (get_cache s3 c) -> In y l) /\ zlen (get_cache s3 c) < max_count c
                                         /\ (forall y, In y (rg_free (get_region s3 c)) -> In y (rg_free (get_region s1 c)) \/ In y l)).
  { destruct (zlen l =? max_count c) eqn:FULL.
    - apply Z.eqb_eq in FULL.
      set (keep := (length l - Z.to_nat (hint c))%nat).
      apply hoare_upd_bind. apply hoare_pre. intros s2 (s & -> & ->). set (s2 := set_cache c (firstn keep l) s1).
      assert (GCe : get_cache s2 c = firstn keep l) by (subst s2; apply get_set_cache_eq).
      assert (GCo : forall c', c' <> c -> get_cache s2 c' = get_cache s1 c') by (intros c' NE; subst s2; apply get_set_cache_ne; auto).
      assert (GR : forall c', get_region s2 c' = get_region s1 c') by (intros; reflexivity).
      assert (PF12 : pframe s1 s2) by (unfold pframe; repeat split; reflexivity).
      assert (CARV12 : forall c' a, carved E s1 c' a <-> carved E s2 c' a) by (intros; unfold carved, region_of; rewrite GR; tauto).
      assert (WF2 : AWF s2).
      { eapply AWf_frame_prim; [exact PF12| intros c' a H; apply CARV12; exact H| | | | | exact WF1].
        - intros c' a _ _ H. left. unfold in_free, region_of in *. rewrite GR in H. exact H.
        - intros c' a _ _ H. left. unfold in_cache in *. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite GCe in H; apply (In_firstn_In _ _ _ H)| rewrite GCo in H by auto; exact H].
        - eapply wf_regions_same; [| exact WR1]. reflexivity.
        - unfold wf_cache. replace (as_cache_inited s2) with true by reflexivity. split; [| split; [discriminate|]].
          + subst s2; cbn. intros c0 l0 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hl by auto. eapply C1; exact Hl.
          + intros c0 Hc0. unfold region_of. rewrite GR. destruct (Z.eq_dec c0 c) as [->|NE].
            * rewrite GCe. split; [unfold zlen in *; rewrite length_firstn; lia|]. split; [apply NoDup_firstn; exact X2|].
              intros y Hy. destruct (X3 y (In_firstn_In _ _ _ Hy)) as (Y1 & Y2 & Y3). split; [apply CARV12; exact Y1|]. auto.
            * rewrite GCo by auto. destruct (C3 c0 Hc0) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
              intros y Hy. destruct (Z3 y Hy) as (Y1 & Y2 & Y3). split; [apply CARV12; exact Y1|]. auto. }
      assert (RET : returnable s2 c (skipn keep l)).
      { split; [apply NoDup_skipn; exact X2|]. intros y Hy. pose proof (In_skipn_In _ _ _ Hy) as Hyl.
        destruct (X3 y Hyl) as (Y1 & Y2 & Y3). split; [apply CARV12; exact Y1|]. split; [exact Y2|].
        split; [rewrite GR; unfold region_of in Y3; exact Y3|]. split; [rewrite GCe; apply NoDup_firstn_skipn_disj; [exact X2| exact Hy]|].
        eapply untracked_pframe; [exact PF12|]. exact (proj2 (cache_entry_untracked E P D s1 c y WF1 Hc Hyl)). }
      eapply hoare_conseq; [apply (return_to_allocator_spec s2 c (skipn keep l) Hc WF2 eq_refl RET)| auto|].
      intros s3 [] (WF3 & PF3 & HC3 & HI3 & CV3 & FR3).
      assert (GC3 : get_cache s3 c = firstn keep l) by (unfold get_cache; rewrite HC3; fold (get_cache s2 c); exact GCe).
      split; [exact WF3|]. split; [eapply pframe_trans; [exact PF12| exact PF3]|].
      split; [intros c' a H; apply CV3; apply CARV12; exact H|]. split; [exact HI3|].
      split; [rewrite GC3; intros y Hy; exact (In_firstn_In _ _ _ Hy)|].
      split; [rewrite GC3; unfold zlen in *; rewrite length_firstn; unfold max_count in *; lia|].
      intros y Hy. destruct (FR3 c y Hy) as [H|[_ H]]; [left; rewrite <- GR; exact H| right; exact (In_skipn_In _ _ _ H)].
    - apply Z.eqb_neq in FULL. apply hoare_ret. intros s ->.
      split; [exact WF1|]. split; [apply pframe_refl|]. split; [auto|]. split; [exact HI1|]. split; [auto|]. split; [subst l; clear -FULL X1; lia|]. auto. }
  intros []. apply hoare_pre. intros s3 (WF3 & PF3 & CV3 & HI3 & SUB3 & LT3 & FR3).
  apply hoare_get_bind. intros s ->. apply hoare_upd. intros s ->.
  set (l1 := get_cache s3 c) in *. set (x := compact_of_chunk SB c p).
  set (s' := upd_cache_allocated _ _).
  assert (GCe : get_cache s' c = l1 ++ [x]) by (subst s'; rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_eq; reflexivity).
  assert (GCo : forall c', c' <> c -> get_cache s' c' = get_cache s3 c').
  { intros c' NE; subst s'. rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_ne by auto. reflexivity. }
  assert (GR : forall c', get_region s' c' = get_region s3 c') by (intros; reflexivity).
  assert (PF : pframe s3 s') by (unfold pframe; repeat split; reflexivity).
  assert (CARV : forall c' a, carved E s3 c' a <-> carved E s' c' a) by (intros; unfold carved, region_of; rewrite GR; tauto).
  assert (CVp3 : carved E s3 c p) by (apply CV3; exact CVp).
  pose proof (carved_compact s3 c p Hc CVp3) as [MODx COCx]. fold x in MODx, COCx.
  assert (NFx : ~ In x (rg_free (get_region s3 c))).
  { intros H. destruct (FR3 x H) as [H0|H0]; [| exact (NCp H0)]. apply NFp. unfold in_free, region_of. exact H0. }
  assert (NCx : ~ In x l1) by (intros H; exact (NCp (SUB3 x H))).
  pose proof WF3 as X. destruct X as (WE3 & WR3 & (C31 & C32 & C33) & _).
  assert (WF' : AWF s').
  { eapply AWf_frame_prim; [exact PF| intros c' a H; apply CARV; exact H| | | | | exact WF3].
    - intros c' a _ _ H. left. unfold in_free, region_of in *. rewrite GR in H. exact H.
    - intros c' a Hc' Ca H. unfold in_cache in *. destruct (Z.eq_dec c' c) as [->|NE].
      + rewrite GCe in H. apply in_app_iff in H as [H|[H|[]]]; [left; exact H|]. right.
        rewrite <- (carved_coc E s3 c a Hc Ca), <- H, COCx. eapply untracked_pframe; [eapply pframe_trans; [exact PF01| exact PF3]| exact Up].
      + left. rewrite GCo in H by auto. exact H.
    - eapply wf_regions_same; [| exact WR3]. reflexivity.
    - unfold wf_cache. replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI3). split; [| split; [discriminate|]].
      + subst s'; cbn. intros c0 l0 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hl by auto. eapply C31; exact Hl.
      + intros c0 Hc0. unfold region_of. rewrite GR. destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite GCe. split; [unfold zlen in *; rewrite length_app; cbn; lia|].
          split; [apply NoDup_app; [exact (proj1 (proj2 (C33 c Hc)))| constructor; [intros []| constructor]| intros y Hy [<-|[]]; exact (NCx Hy)]|].
          intros y Hy. apply in_app_iff in Hy as [Hy|[<-|[]]].
          -- destruct (C33 c Hc) as (_ & _ & Z3). destruct (Z3 y Hy) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. auto.
          -- split; [apply CARV; rewrite COCx; exact CVp3|]. split; [exact MODx| exact NFx].
        * rewrite GCo by auto. destruct (C33 c0 Hc0) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
          intros y Hy. destruct (Z3 y Hy) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. auto. }
  split; [exact WF'|]. split; [eapply pframe_trans; [exact PF01| eapply pframe_trans; [exact PF3| exact PF]]|].
  split; [intros c' a H; apply CARV; apply CV3; exact H|].
  subst s'; cbn. exact HI3.
Qed.

End WF.
End RC__1.
