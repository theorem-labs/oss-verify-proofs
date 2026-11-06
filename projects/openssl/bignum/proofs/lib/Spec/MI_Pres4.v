(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition xfresh (X : extras) (f : option aptr) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) f.

Lemma data0_shape r : data_of r = data_of meta0 <-> r = mkMeta (m_prev r) (m_next r) None 0 0 0 0 0 0.
Proof.
  destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.

Lemma data0_mem r : data_of r = data_of meta0 -> m_mem r = None.
Proof. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.

Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Lemma de_fields x :
  m_mem (MR st' x) = m_mem (MR st x) /\ m_avail (MR st' x) = m_avail (MR st x) /\ m_freed (MR st' x) = m_freed (MR st x)
  /\ m_last_idx (MR st' x) = m_last_idx (MR st x) /\ m_freeable (MR st' x) = m_freeable (MR st x)
  /\ m_sizeclass (MR st' x) = m_sizeclass (MR st x) /\ m_maplen (MR st' x) = m_maplen (MR st x).
Proof. apply data_of_eq. apply DE. Qed.
Lemma de_mem x : m_mem (MR st' x) = m_mem (MR st x). Proof. apply de_fields. Qed.
Lemma de_avail x : m_avail (MR st' x) = m_avail (MR st x). Proof. apply de_fields. Qed.
Lemma de_freed x : m_freed (MR st' x) = m_freed (MR st x). Proof. apply de_fields. Qed.
Lemma de_last x : m_last_idx (MR st' x) = m_last_idx (MR st x). Proof. apply de_fields. Qed.
Lemma de_freeable x : m_freeable (MR st' x) = m_freeable (MR st x). Proof. apply de_fields. Qed.
Lemma de_sc x : m_sizeclass (MR st' x) = m_sizeclass (MR st x). Proof. apply de_fields. Qed.
Lemma de_maplen x : m_maplen (MR st' x) = m_maplen (MR st x). Proof. apply de_fields. Qed.
Lemma de_stride x : get_stride (MR st' x) = get_stride (MR st x). Proof. apply get_stride_data. apply DE. Qed.
Lemma de_gbase x : gbase (MR st' x) = gbase (MR st x). Proof. unfold gbase. rewrite de_mem. reflexivity. Qed.
Lemma de_sstart x i : sstart (MR st' x) i = sstart (MR st x) i. Proof. unfold sstart. rewrite de_gbase, de_stride. reflexivity. Qed.
Lemma de_slot_start' x i : slot_start' (MR st' x) i = slot_start' (MR st x) i.
Proof. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
Lemma de_cnt x : cnt_of (MR st' x) = cnt_of (MR st x). Proof. unfold cnt_of. rewrite de_last. reflexivity. Qed.
Lemma de_gend x : gend (MR st' x) = gend (MR st x). Proof. unfold gend. rewrite de_sstart, de_cnt. reflexivity. Qed.
End DEXT.

Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
  cb_secret : c_secret c' = c_secret c;
  cb_init : c_init_done c' = c_init_done c;
  cb_mc : c_mmap_counter c' = c_mmap_counter c;
  cb_am : c_avail_meta c' = c_avail_meta c;
  cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cb_mah : c_meta_area_head c' = c_meta_area_head c;
  cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cb_usage : c_usage c' = c_usage c;
  cb_unmap : c_unmap_seq c' = c_unmap_seq c;
  cb_bounces : c_bounces c' = c_bounces c;
  cb_seq : c_seq c' = c_seq c;
  cb_brk : c_brk c' = c_brk c
}.
Lemma cbh_refl c : ctx_but_heads c c. Proof. constructor; reflexivity. Qed.
Lemma cbh_set_head st h v : ctx_but_heads (s_ctx st) (s_ctx (set_head h v st)).
Proof. destruct h; constructor; reflexivity. Qed.

Lemma inv_L_lists st LS : inv_L st LS -> lists_ok st LS.
Proof. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.

Lemma head_of_app (l : list aptr) g : l <> [] -> head_of (l ++ [g]) = head_of l.
Proof. destruct l; cbn; congruence. Qed.

Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Hypothesis KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None.
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
           (HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
           (HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st).
Hypothesis HC : ctx_but_heads (s_ctx st) (s_ctx st').
Hypothesis XE : x_pend X' = x_pend X /\ x_orph X' = x_orph X /\ x_zomb X' = x_zomb X.
Hypothesis LO' : lists_ok st' LS'.
Hypothesis H_free : forall m, In m (LS' LFree) -> data_of (MR st m) = data_of meta0.
Hypothesis H_active : forall sc m, In m (LS' (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Hypothesis H_keys : forall sc, LS' (LActive sc) <> [] -> 0 <= sc < 48.
Hypothesis H_actkeys : forall sc g, c_active (s_ctx st') !! sc = Some g -> 0 <= sc < 48.
Hypothesis H_idle : forall m, In m (x_idle X') -> s_metas st' !! m = Some meta0 /\ ~ in_list LS' m.
Hypothesis H_zomb : forall z, In z (x_zomb X) -> m_next (MR st' z) = None /\ m_prev (MR st' z) = None /\ ~ in_list LS' z.
Hypothesis H_groups : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
   (x_fresh X' <> Some m -> ai < m_last_idx (MR st m) -> In m (LS' (LActive (m_sizeclass (MR st m)))))
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> ~ in_list LS' m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0)
   /\ (x_fresh X' <> Some m -> forall sc, In m (LS' (LActive sc)) -> Some m <> head_of (LS' (LActive sc)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0)
   /\ (m_sizeclass (MR st m) = 63 -> ~ in_list LS' m)
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < UNIT * size_class (m_sizeclass (MR st m)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0).

Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.

Lemma rl_hosts b m : hosts st' b m <-> hosts st b m. Proof. apply hosts_ext. exact HG. Qed.
Lemma rl_live m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. exact HG. Qed.
Lemma rl_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
Lemma rl_usage sc : usage st' sc = usage st sc.
Proof. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
Lemma rl_gcnt sc : gcnt st' sc = gcnt st sc.
Proof.
  apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.

Theorem INVL_relink : INVL X' st' L BL LS'.
Proof.
  destruct XE as (XP & XO & XZ).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  -   destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
  -   destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
  -   destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
    + intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
    + intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
    + exact H_idle.
    + intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
      split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
  -   destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
    + intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
    + intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
    + intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
  -   destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
      destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
      * apply KEYS. exact g_present.
      * destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
      * intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
    + intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
    + intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
  -   destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
    + intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
    + intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
    + intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
  -   apply (inv_SH_view st st'); auto.
Qed.
End RELINK.

Lemma present_MR st x : s_metas st !! x <> None -> s_metas st !! x = Some (MR st x).
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.

Lemma fupd_in LS h l h' m : In m (fupd LS h l h') <-> (h' = h /\ In m l) \/ (h' <> h /\ In m (LS h')).
Proof.
  unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
  all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.

Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma old_lists : lists_ok st LS. Proof. apply inv_L_lists. exact (proj1 (proj2 (proj2 (proj2 INV)))). Qed.
Lemma old_free m : In m (LS LFree) -> data_of (MR st m) = data_of meta0.
Proof. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
Lemma old_active sc m : In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Proof. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
Lemma old_keys sc : LS (LActive sc) <> [] -> 0 <= sc < 48.
Proof. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
Lemma old_actkeys sc g : c_active (s_ctx st) !! sc = Some g -> 0 <= sc < 48.
Proof. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
Lemma old_idle m : In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list LS m.
Proof. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
Lemma old_zomb z : In z (x_zomb X) -> m_next (MR st z) = None /\ m_prev (MR st z) = None /\ ~ in_list LS z /\
  exists b, m_mem (MR st z) = Some b /\ s_groups st !! b = None.
Proof. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
Lemma old_group m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok X st LS m b ai.
Proof. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
Lemma old_63 m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 -> ~ in_list LS m.
Proof. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.

Lemma listed_next m h : In m (LS h) -> m_next (MR st m) <> None.
Proof. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
Lemma listed_present m h : In m (LS h) -> s_metas st !! m <> None.
Proof. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
Lemma head_listed h a : get_head st h = Some a -> In a (LS h).
Proof. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
Lemma prev_listed h a x : In a (LS h) -> m_prev (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
Lemma next_listed h a x : In a (LS h) -> m_next (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
Lemma idle_unlisted m h : In m (x_idle X) -> ~ In m (LS h).
Proof. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
Lemma zomb_unlisted z h : In z (x_zomb X) -> ~ In z (LS h).
Proof. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
Lemma idle_not_live m : In m (x_idle X) -> ~ live_group st m.
Proof.
  intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
Lemma zomb_not_live z : In z (x_zomb X) -> ~ live_group st z.
Proof.
  intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
Lemma free_not_live m : In m (LS LFree) -> ~ live_group st m.
Proof.
  intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.

Lemma INVL_set_fresh X st L BL LS f :
  INVL X st L BL LS -> x_fresh X = None -> INVL (xfresh X f) st L BL LS.
Proof.
  intros INV HF.
  refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
    split; [| split; [| split; [| split]]].
    + intros _. exact (g_partial _ _ _ _ _ _ GO NF).
    + intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
    + intros _. exact (g_rest _ _ _ _ _ _ GO NF).
    + exact (old_63 _ _ _ _ _ INV m b ai Hb).
    + intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

Lemma INVL_clear_fresh X st L BL LS g :
  INVL X st L BL LS -> x_fresh X = Some g ->
  (forall b ai, s_groups st !! b = Some (mkGhdr (Some g) ai) ->
     (ai < m_last_idx (MR st g) -> In g (LS (LActive (m_sizeclass (MR st g)))))
     /\ (m_sizeclass (MR st g) < 48 -> ~ in_list LS g -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)
     /\ (forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) <> 0)
     /\ (m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < UNIT * size_class (m_sizeclass (MR st g)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)) ->
  INVL (xfresh X None) st L BL LS.
Proof.
  intros INV HF OB.
  refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    destruct (aptr_eq_dec m g) as [->|NE].
    + destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
    + assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      split; [| split; [| split; [| split]]].
      * intros _. exact (g_partial _ _ _ _ _ _ GO NF).
      * intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
      * intros _. exact (g_rest _ _ _ _ _ _ GO NF).
      * exact (old_63 _ _ _ _ _ INV m b ai Hb).
      * intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

Lemma queue_frame h g st : let st' := queue_st h g st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
    repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma queue_metas_other h g st x :
  x <> g -> (forall a, get_head st h = Some a -> x <> a /\ m_prev (MR st a) <> Some x) ->
  s_metas (queue_st h g st) !! x = s_metas st !! x.
Proof.
  intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
  - destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
    destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
  - rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma dequeue_frame h m st : let st' := dequeue h m st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold dequeue.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
  repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma dequeue_metas_other h m st x :
  x <> m -> m_prev (MR st m) <> Some x -> m_next (MR st m) <> Some x ->
  s_metas (dequeue h m st) !! x = s_metas st !! x.
Proof.
  intros NE NP NN. unfold dequeue, MR in *.
  rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.

Lemma get_head_active st sc : get_head st (LActive sc) = c_active (s_ctx st) !! sc.
Proof. reflexivity. Qed.

Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis PRES : s_metas st !! g <> None.
Hypothesis HQ : match h with
  | LActive sc => 0 <= sc < 48 /\ live_group st g /\ m_sizeclass (MR st g) = sc /\ x_fresh X = Some g
  | LFree => data_of (MR st g) = data_of meta0 /\ ~ In g (x_idle X) /\ ~ In g (x_zomb X)
  end.
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).

Lemma q_in m h' : In m (LS' h') <-> In m (LS h') \/ (h' = h /\ m = g).
Proof.
  unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
Lemma q_in_list m : in_list LS' m <-> in_list LS m \/ m = g.
Proof.
  unfold in_list. split.
  - intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
  - intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
Lemma g_not_idle : ~ In g (x_idle X).
Proof.
  destruct h as [sc|]; [| exact (proj1 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hi. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
Qed.
Lemma g_not_zomb : ~ In g (x_zomb X).
Proof.
  destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
Lemma untouched x : (forall h', ~ In x (LS h')) -> x <> g -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
  - intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.

Theorem INVL_queue : INVL X st' L BL LS'.
Proof.
  destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X X st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
  -   intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
    destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
    + exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
  - auto.
  - apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
  - intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
  - intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
  - intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
    + subst h. exact (proj1 HQ).
    + unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
    assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm)).
    split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
    rewrite q_in_list. tauto.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
    rewrite E, q_in_list. repeat split; auto. tauto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
    + intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
      * apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
        -- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
        -- rewrite fupd_ne in Hh by exact NE. exact Hh.
      * exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
    + intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
      destruct h as [sc|].
      * destruct HQ as (A & _ & C & _). lia.
      * pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
        rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
Qed.
End QUEUE.

Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS h = l1 ++ m :: l2.
Hypothesis HX : (exists sc, h = LActive sc /\ x_fresh X = None /\ X' = xfresh X (Some m)) \/ (h = LFree /\ X' = xidle X (m :: x_idle X)).
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).

Lemma m_listed : In m (LS h). Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma d_in x h' : In x (LS' h') -> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
Lemma d_in_rev x h' : In x (LS h') -> x <> m -> In x (LS' h').
Proof.
  intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
  - left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
  - right. auto.
Qed.
Lemma d_in_list x : in_list LS' x -> in_list LS x.
Proof. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
Lemma m_out : ~ in_list LS' m.
Proof.
  intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
  - pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
    destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
  - apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
Lemma untouched_d x : (forall h', ~ In x (LS h')) -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI. apply dequeue_metas_other.
  - intros ->. exact (NI h m_listed).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
  - intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
Lemma nonhead_old x : In x (LS' h) -> Some x <> head_of (LS' h) -> Some x <> head_of (LS h).
Proof.
  intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
  - intros E. inversion E. subst x.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
    apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
  - exact Hh.
Qed.
Lemma MR'_m : MR st' m = data_of (MR st m).
Proof.
  pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
  unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.

Theorem INVL_dequeue : INVL X' st' L BL LS'.
Proof.
  destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
  -   intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
    destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
    + exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
  - destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
  - apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
  - intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
  - intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
  - intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
    destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
    apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
  - intros x Hx.
    assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
    { intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
      - rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
      - intros IL'. exact (NI (d_in_list x IL')). }
    destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
    destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
    split; [| exact m_out].
    rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
    apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
    rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
  - intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
    destruct (aptr_eq_dec x m) as [->|NEm].
    + destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
      * pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
        rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
      * exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
    + assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
      { destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
      split; [| split; [| split; [| split]]].
      5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
      * intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
      * intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
      * intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
        destruct (decide (LActive sc = h)) as [E|NE].
        -- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
        -- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
      * intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
Qed.
End DEQUEUE.

Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS (LActive sc) = a :: rest.
Hypothesis Hn : m_next (MR st a) = Some a'.
Hypothesis OB : x_fresh X <> Some a -> rest <> [] -> m_avail (MR st a) = 0 /\ m_freed (MR st a) <> 0.
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).

Lemma r_in x h' : In x (LS' h') <-> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
  - unfold h. rewrite HL, in_app_iff. cbn. tauto.
  - tauto.
Qed.
Lemma r_in_list x : in_list LS' x <-> in_list LS x.
Proof. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.

Theorem INVL_rotate : INVL X st' L BL LS'.
Proof.
  refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
            _ _ _ _ _ _ _ _).
  - auto.
  - apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
  - intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
  - intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
  - intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
    destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
  - intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
    destruct (decide (LActive sc0 = h)) as [E|NE].
    + apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
    + rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
    unfold st'. rewrite set_head_metas. exact E.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
    + intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
      * unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
        apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
        -- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
           unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
           pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
           apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
        -- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
      * unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
    + intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
Qed.
End ROTATE.
