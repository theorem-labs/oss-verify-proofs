(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocRep MallocTree MallocBlocks MallocKit_B MallocFacts_B MallocModel_B.
Import ListNotations.
Open Scope Z_scope.

Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).

Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
                   m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
                   data_of meta0] in *.

Lemma aptr_eqb_spec' (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.

Ltac case_ptr x y := destruct (aptr_eqb_spec' x y) as [?EQ|?NE]; [subst x|].

Lemma rec_upd st g f x :
  get_meta_rec (upd_meta g f st) x = if aptr_eqb x g then f (get_meta_rec st g) else get_meta_rec st x.
Proof. apply get_meta_rec_upd. Qed.

Lemma rec_put st g mr x :
  get_meta_rec (put_meta g mr st) x = if aptr_eqb x g then mr else get_meta_rec st x.
Proof. apply get_meta_rec_put. Qed.

Lemma data_of_eq r r' :
  data_of r = data_of r' <->
  (m_mem r = m_mem r' /\ m_avail r = m_avail r' /\ m_freed r = m_freed r' /\ m_last_idx r = m_last_idx r'
   /\ m_freeable r = m_freeable r' /\ m_sizeclass r = m_sizeclass r' /\ m_maplen r = m_maplen r').
Proof.
  destruct r, r'; unfold data_of; msimp; split.
  - intros H. inversion H. repeat split; reflexivity.
  - intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.

Lemma get_stride_data r r' : data_of r = data_of r' -> get_stride r = get_stride r'.
Proof. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.
Lemma slot_start'_data r r' i : data_of r = data_of r' -> slot_start' r i = slot_start' r' i.
Proof. intros H. unfold slot_start'. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
Lemma sstart_of_data r r' i : data_of r = data_of r' -> sstart_of r i = sstart_of r' i.
Proof. intros H. unfold sstart_of. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
Lemma slot_free_data r r' i : data_of r = data_of r' -> slot_free r i <-> slot_free r' i.
Proof. intros H. apply data_of_eq in H. unfold slot_free. destruct H as (_ & -> & -> & _). LiaTuning.ctauto. Qed.

Definition kctx (st : mstate) : Prop :=
  0 <= c_seq (ctx st) < 256
  /\ (forall i, 0 <= bounces st i < 256) /\ (forall i, 0 <= unmap_seq st i < 256)
  /\ 0 <= c_secret (ctx st) < 2^64.

Definition usage_ok (st : mstate) (c : Z) : Prop := forall sc, c <= sc -> 0 <= usage st sc < 2^64.

Record KINV (st : mstate) (LB : list block) (c : Z) : Prop := mkKI {
  ki_links : ci_links_t st;
  ki_heads : ci_heads_t st;
  ki_hom : ci_homog st;
  ki_gmetas : ci_gmeta st;
  ki_grps : ci_groups st;
  ki_ginj : ci_group_inj st;
  ki_slts : ci_slots st;
  ki_sltt : ci_slots_total st;
  ki_unk : ci_ghdr_unk st;
  ki_h0 : ci_hdr0 st;
  ki_blks : Forall (blk_ok st) LB;
  ki_nodup : List.NoDup (map blk_slot LB);
  ki_cx : kctx st;
  ki_usage : usage_ok st c;
  ki_bk : ci_brk st;
  ki_ticks : ticks_ok st

}.

Lemma KINV_of_CINV st LB : CINV st LB -> KINV st LB 0.
Proof.
  intros C. pose proof (ci_cx _ _ C) as (S1 & S2 & S3 & S4 & S5).
  constructor; try (destruct C; assumption).
  - unfold kctx. repeat split; try apply S1; try apply S2; try apply S3; try apply S5.
  - intros sc _. apply S4.
Qed.

Lemma KINV_mono st LB c c' : KINV st LB c -> c <= c' -> KINV st LB c'.
Proof. intros K Hc. pose proof (ki_usage _ _ _ K) as U. destruct K; constructor; auto. intros sc Hsc. apply U. lia. Qed.

Section EXT.
Variables st st' : mstate.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis ES : s_shadow st' = s_shadow st.

#[using="EA"] Lemma meta_slot_ext g : meta_slot st g <-> meta_slot st' g.
Proof. unfold meta_slot. rewrite EA. LiaTuning.ctauto. Qed.
#[using="ES"] Lemma get_shadow_ext rid : get_shadow st' rid = get_shadow st rid.
Proof. unfold get_shadow. rewrite ES. reflexivity. Qed.
#[using="ER"] Lemma conc_ext q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

Hypothesis EL : forall x, m_next (get_meta_rec st' x) = m_next (get_meta_rec st x) /\ m_prev (get_meta_rec st' x) = m_prev (get_meta_rec st x).

#[using="EA EL"] Lemma links_ext : ci_links_t st -> ci_links_t st'.
Proof.
  intros [N P NN SF]. constructor.
  - intros m nx H. destruct (EL m) as [E1 _]. rewrite E1 in H. destruct (N m nx H) as [H1 H2].
    destruct (EL nx) as [_ E2]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
  - intros m pv H. destruct (EL m) as [_ E1]. rewrite E1 in H. destruct (P m pv H) as [H1 H2].
    destruct (EL pv) as [E2 _]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
  - intros m. destruct (EL m) as [E1 E2]. rewrite E1, E2. apply NN.
  - intros m H. destruct (EL m) as [E1 _]. rewrite E1 in H. apply meta_slot_ext. apply SF. exact H.
Qed.
End EXT.

Lemma hosts_ext st st' b g : s_groups st' = s_groups st -> hosts st' b g <-> hosts st b g.
Proof. intros E. unfold hosts. rewrite E. LiaTuning.ctauto. Qed.
Lemma is_gm_ext st st' g : s_groups st' = s_groups st -> is_gm st' g <-> is_gm st g.
Proof. intros E. unfold is_gm. split; intros [b H]; exists b; [rewrite <- (hosts_ext st st')|rewrite (hosts_ext st st')]; auto. Qed.

Record LPRE (st : mstate) (LB : list block) (c : Z) (g p : aptr) (i : Z) : Prop := mkLP {
  lp_hosts : hosts st p g;
  lp_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  lp_nonfree : ~ slot_free (get_meta_rec st g) i;
  lp_nogroup : (s_groups st) !! (slot_start' (get_meta_rec st g) i) = None;
  lp_noblock : Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) i) LB;
  lp_class : c <= m_sizeclass (get_meta_rec st g)
}.

Lemma lpre_gmeta st LB c g p i : KINV st LB c -> LPRE st LB c g p i -> gmeta_ok st g p.
Proof. intros K L. apply (ki_gmetas _ _ _ K). apply (lp_hosts _ _ _ _ _ _ L). Qed.

Lemma kinv_next st LB c g nx : KINV st LB c -> m_next (get_meta_rec st g) = Some nx ->
  meta_slot st nx /\ m_prev (get_meta_rec st nx) = Some g /\ m_next (get_meta_rec st nx) <> None
  /\ exists pv, m_prev (get_meta_rec st g) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some g /\ (nx <> g -> pv <> g).
Proof.
  intros K NX. pose proof (ki_links _ _ _ K) as [N P NN SF].
  destruct (N g nx NX) as [P1 S1]. split; [exact S1|]. split; [exact P1|]. split.
  { intros E. apply (proj1 (NN nx)) in E. rewrite E in P1. discriminate. }
  destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN g)) in PV. rewrite PV in NX. discriminate. }
  destruct (P g pv PV) as [N2 S2]. exists pv. repeat split; auto.
  intros NE ->. rewrite N2 in NX. inversion NX. subst. apply NE. reflexivity.
Qed.

Lemma kinv_active st LB c sc a : KINV st LB c -> active st sc = Some a ->
  0 <= sc < 48 /\ meta_slot st a /\ m_next (get_meta_rec st a) <> None /\ is_gm st a /\ m_sizeclass (get_meta_rec st a) = sc
  /\ exists pv, m_prev (get_meta_rec st a) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some a.
Proof.
  intros K HA. pose proof (ki_heads _ _ _ K) as [_ CA]. destruct (CA sc a HA) as (SC & NX & GM & SCa).
  pose proof (ki_links _ _ _ K) as [N P NN SF].
  split; [exact SC|]. split; [apply SF; exact NX|]. split; [exact NX|]. split; [exact GM|]. split; [exact SCa|].
  destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN a)) in PV. exfalso. exact (NX PV). }
  exists pv. destruct (P a pv PV) as [N2 S2]. auto.
Qed.

Lemma kinv_free_head st LB c h : KINV st LB c -> c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ m_next (get_meta_rec st h) <> None /\ ~ is_gm st h
  /\ exists pv, m_prev (get_meta_rec st h) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some h.
Proof.
  intros K HF. pose proof (ki_heads _ _ _ K) as [CF _]. destruct (CF h HF) as (NX & MM).
  pose proof (ki_links _ _ _ K) as [N P NN SF].
  split; [apply SF; exact NX|]. split; [exact NX|]. split.
  { intros [b [ai Hb]]. pose proof (go_mem _ _ _ (ki_gmetas _ _ _ K b h (ex_intro _ ai Hb))) as MEM. congruence. }
  destruct (m_prev (get_meta_rec st h)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN h)) in PV. exfalso. exact (NX PV). }
  exists pv. destruct (P h pv PV) as [N2 S2]. auto.
Qed.

Lemma kinv_fm_facts_raw st LB c g : KINV st LB c -> m_next (get_meta_rec st g) = None ->
  forall h, c_free_meta_head (ctx st) = Some h ->
    h <> g /\ meta_slot st h /\ exists pv, m_prev (get_meta_rec st h) = Some pv /\ pv <> g /\ meta_slot st pv.
Proof.
  intros K GN h HF. destruct (kinv_free_head st LB c h K HF) as (S1 & N1 & _ & pv & P1 & S2 & N2).
  split; [congruence|]. split; [exact S1|]. exists pv. repeat split; auto. congruence.
Qed.

Lemma hosts_is_gm st b g : hosts st b g -> is_gm st g.
Proof. intros H. exists b. exact H. Qed.

Definition LG (st : mstate) (q : aptr) : Prop := m_next (get_meta_rec st q) <> None \/ is_gm st q.

Definition amc (c : mctx) :=
  (c_avail_meta c, c_meta_area_head c, c_meta_area_tail c, c_avail_meta_areas c, c_init_done c,
   c_mmap_counter c, c_avail_meta_count c, c_avail_meta_area_count c, c_meta_alloc_shift c).

Record ntf_frame (st st' : mstate) : Prop := mkNF {
  nf_amc : amc (ctx st') = amc (ctx st);
  nf_regions : s_regions st' = s_regions st;
  nf_shadow : s_shadow st' = s_shadow st;
  nf_areas : s_areas st' = s_areas st;
  nf_reserved : s_reserved st' = s_reserved st;
  nf_tick : s_tick st' = s_tick st;
  nf_brk : c_brk (ctx st') = c_brk (ctx st);
  nf_secret : c_secret (ctx st') = c_secret (ctx st);
  nf_groups : forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh;
  nf_slots : forall s x, (s_slots st') !! s = Some x -> (s_slots st) !! s = Some x;
  nf_linked : forall q, m_next (get_meta_rec st' q) <> None -> LG st q;
  nf_metas : forall q, ~ LG st q -> get_meta_rec st' q = get_meta_rec st q
}.

Lemma frame_refl st : ntf_frame st st.
Proof. constructor; auto. intros q H. left. exact H. Qed.

Lemma LG_frame st stA q : ntf_frame st stA -> LG stA q -> LG st q.
Proof.
  intros FR [H|[b [ai Hb]]]. { apply (nf_linked _ _ FR). exact H. }
  right. exists b, ai. apply (nf_groups _ _ FR). exact Hb.
Qed.

Lemma frame_upd_meta st stA q f : ntf_frame st stA -> LG st q -> ntf_frame st (upd_meta q f stA).
Proof.
  intros FR Hq. destruct FR. constructor; auto.
  - intros q' H. rewrite rec_upd in H. destruct (aptr_eqb_spec' q' q); [subst; exact Hq| auto].
  - intros q' H. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; LiaTuning.ctauto| auto].
Qed.

Lemma frame_put_meta st stA q r : ntf_frame st stA -> LG st q -> ntf_frame st (put_meta q r stA).
Proof. intros. rewrite <- (upd_meta_put stA q (fun _ => r)). apply frame_upd_meta; auto. Qed.

Lemma frame_ctx st stA f : ntf_frame st stA ->
  c_brk (f (s_ctx stA)) = c_brk (s_ctx stA) -> c_secret (f (s_ctx stA)) = c_secret (s_ctx stA) ->
  amc (f (s_ctx stA)) = amc (s_ctx stA) ->
  ntf_frame st (upd_ctx f stA).
Proof.
  intros FR E1 E2 E3. destruct FR. constructor; auto.
  - unfold ctx in *. cbn. congruence.
  - unfold ctx in *. cbn. congruence.
  - unfold ctx in *. cbn. congruence.
Qed.

Lemma frame_set_active st stA sc v : ntf_frame st stA -> ntf_frame st (set_active sc v stA).
Proof. intros FR. unfold set_active. apply frame_ctx; auto; reflexivity. Qed.

Lemma frame_set_head st stA h v : ntf_frame st stA -> ntf_frame st (set_head h v stA).
Proof. intros FR. destruct h; cbn; [apply frame_set_active| apply frame_ctx]; auto; reflexivity. Qed.

Lemma frame_grp_del st stA g p : ntf_frame st stA -> ntf_frame st (grp_del stA g p).
Proof.
  intros FR. destruct FR. unfold grp_del, del_slots, del_group. constructor; cbn; auto.
  - intros b gh Hb. apply nf_groups0. apply lookup_delete_Some in Hb. LiaTuning.ctauto.
  - intros s x Hs. apply nf_slots0.
    revert Hs. generalize (s_slots stA). intros tb.
    match goal with |- context [Z.iter ?n ?F (0, tb)] => set (f := F) end.
    assert (GEN : forall acc, (snd (Z.iter (m_last_idx (get_meta_rec stA g) + 1) f acc)) !! s = Some x -> (snd acc) !! s = Some x).
    { intros acc. unfold Z.iter. destruct (m_last_idx (get_meta_rec stA g) + 1); cbn; auto.
      revert acc. induction p0 using Pos.peano_ind; intros acc.
      - cbn. unfold f at 1. destruct acc as [j t]. cbn. rewrite lookup_delete_Some. LiaTuning.ctauto.
      - rewrite Pos.iter_succ. unfold f at 1. destruct (Pos.iter f acc p0) as [j t] eqn:E. cbn.
        rewrite lookup_delete_Some. intros [_ H]. apply IHp0. rewrite E. exact H. }
    apply (GEN (0, tb)).
Qed.

Lemma frame_aor st stA g i : ntf_frame st stA -> LG st g -> ntf_frame st (aor_st stA g i).
Proof. intros. unfold aor_st. apply frame_upd_meta; auto. Qed.

Lemma frame_act st stA a act : ntf_frame st stA -> LG st a -> ntf_frame st (act_st stA a act).
Proof. intros. unfold act_st. apply frame_upd_meta; auto. Qed.

Lemma frame_dequeue st stA h g : ntf_frame st stA -> ci_links_t stA -> LG st g ->
  ntf_frame st (dequeue h g stA).
Proof.
  intros FR CL Hg. unfold dequeue.
  apply frame_upd_meta; [|exact Hg].
  destruct (negb (optr_eqb (m_next (get_meta_rec stA g)) (Some g))); [|apply frame_set_head; exact FR].
  set (st1 := match m_prev (get_meta_rec stA g) with Some pv => _ | None => stA end).
  assert (F1 : ntf_frame st st1).
  { subst st1. destruct (m_prev (get_meta_rec stA g)) as [pv|] eqn:PV; [|exact FR].
    apply frame_upd_meta; [exact FR|]. apply (LG_frame st stA pv FR). left.
    destruct (cl_prev _ CL g pv PV) as [N _]. rewrite N. discriminate. }
  set (st2 := match m_next (get_meta_rec stA g) with Some nx => _ | None => st1 end).
  assert (F2 : ntf_frame st st2).
  { subst st2. destruct (m_next (get_meta_rec stA g)) as [nx|] eqn:NX; [|exact F1].
    apply frame_upd_meta; [exact F1|]. apply (LG_frame st stA nx FR). left.
    destruct (cl_next _ CL g nx NX) as [P _]. intros E. apply (proj1 (cl_none _ CL nx)) in E. rewrite E in P. discriminate. }
  destruct (optr_eqb (get_head st2 h) (Some g)); [apply frame_set_head|]; exact F2.
Qed.

Lemma frame_queue st stA h g : ntf_frame st stA -> ci_links_t stA ->
  (forall hd, get_head stA h = Some hd -> m_next (get_meta_rec stA hd) <> None) -> LG st g ->
  ntf_frame st (queue_st h g stA).
Proof.
  intros FR CL HH Hg. unfold queue_st, fm_link, fm_single.
  destruct (get_head stA h) as [hd|] eqn:HD.
  - specialize (HH hd eq_refl).
    apply frame_upd_meta.
    + destruct (m_prev (get_meta_rec stA hd)) as [pv|] eqn:PV.
      * apply frame_upd_meta; [apply frame_upd_meta; [exact FR| exact Hg]|].
        apply (LG_frame st stA pv FR). left. destruct (cl_prev _ CL hd pv PV) as [N _]. rewrite N. discriminate.
      * apply frame_upd_meta; [exact FR| exact Hg].
    + apply (LG_frame st stA hd FR). left. exact HH.
  - apply frame_set_head. apply frame_upd_meta; [exact FR| exact Hg].
Qed.

Lemma frame_fm st stA g : ntf_frame st stA -> ci_links_t (put_meta g meta0 stA) ->
  (forall hd, c_free_meta_head (ctx stA) = Some hd -> m_next (get_meta_rec (put_meta g meta0 stA) hd) <> None) -> LG st g ->
  ntf_frame st (fm_st stA g).
Proof.
  intros FR CL HH Hg. unfold fm_st. apply frame_queue; auto. apply frame_put_meta; auto.
Qed.

Lemma frame_seq st stA sc : ntf_frame st stA -> ntf_frame st (record_seq sc (step_seq stA)).
Proof.
  intros FR.
  assert (F1 : ntf_frame st (step_seq stA)).
  { unfold step_seq. destruct (c_seq (ctx stA) =? 255); apply frame_ctx; auto; reflexivity. }
  unfold record_seq. destruct (sc_in_seq_range sc); [apply frame_ctx; auto; reflexivity| exact F1].
Qed.

Lemma frame_fg_usage st stA g : ntf_frame st stA -> ntf_frame st (fg_usage_st stA g).
Proof. intros FR. unfold fg_usage_st. destruct (m_sizeclass _ <? 48); [unfold set_usage; apply frame_ctx|]; auto; reflexivity. Qed.

Record same_but_links (st st' : mstate) : Prop := mkSBL {
  sbl_data : forall q, data_of (get_meta_rec st' q) = data_of (get_meta_rec st q);
  sbl_regions : s_regions st' = s_regions st;
  sbl_shadow : s_shadow st' = s_shadow st;
  sbl_areas : s_areas st' = s_areas st;
  sbl_groups : s_groups st' = s_groups st;
  sbl_slots : s_slots st' = s_slots st;
  sbl_tick : s_tick st' = s_tick st;
  sbl_reserved : s_reserved st' = s_reserved st;
  sbl_brk : c_brk (ctx st') = c_brk (ctx st);
  sbl_secret : c_secret (ctx st') = c_secret (ctx st);
  sbl_seq : c_seq (ctx st') = c_seq (ctx st);
  sbl_usage : forall sc, usage st' sc = usage st sc;
  sbl_bounces : forall j, bounces st' j = bounces st j;
  sbl_unmap : forall j, unmap_seq st' j = unmap_seq st j;
  sbl_fmh_or : True
}.

Lemma sbl_refl st : same_but_links st st.
Proof. constructor; auto. Qed.

Lemma sbl_trans a b c : same_but_links a b -> same_but_links b c -> same_but_links a c.
Proof. intros [] []; constructor; intros; try congruence. Qed.

Lemma data_of_links f r : (forall r, data_of (f r) = data_of r) -> data_of (f r) = data_of r.
Proof. auto. Qed.

Lemma sbl_upd_links st q f : (forall r, data_of (f r) = data_of r) -> same_but_links st (upd_meta q f st).
Proof.
  intros Hf. constructor; try reflexivity.
  intros q'. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; apply Hf| reflexivity].
Qed.

Lemma sbl_set_head st h v : same_but_links st (set_head h v st).
Proof. destruct h; cbn; constructor; try reflexivity. Qed.

Lemma data_set_prev v r : data_of (m_set_prev v r) = data_of r. Proof. reflexivity. Qed.
Lemma data_set_next v r : data_of (m_set_next v r) = data_of r. Proof. reflexivity. Qed.

Lemma sbl_upd_links'' st st0 q f : same_but_links st0 st -> (forall r, data_of (f r) = data_of r) -> same_but_links st0 (upd_meta q f st).
Proof. intros S Hf. eapply sbl_trans; [exact S| apply sbl_upd_links; exact Hf]. Qed.

Lemma sbl_set_head'' st st0 h v : same_but_links st0 st -> same_but_links st0 (set_head h v st).
Proof. intros S. eapply sbl_trans; [exact S| apply sbl_set_head]. Qed.

Lemma sbl_queue st h g : same_but_links st (queue_st h g st).
Proof.
  unfold queue_st, fm_link, fm_single.
  destruct (get_head st h) as [hd|]; [destruct (m_prev (get_meta_rec st hd)) as [pv|]|];
    repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.

Lemma sbl_deq_mid st h g : same_but_links st (deq_mid h g st).
Proof.
  unfold deq_mid.
  destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| apply sbl_set_head].
  destruct (m_prev (get_meta_rec st g)) as [pv|]; destruct (m_next (get_meta_rec st g)) as [nx|];
    match goal with |- same_but_links st (if ?c then _ else _) => destruct c end;
    repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.

Lemma sbl_dequeue st h g : same_but_links st (dequeue h g st).
Proof.
  rewrite dequeue_mid. apply sbl_upd_links''; [apply sbl_deq_mid|]. intros; reflexivity.
Qed.

Lemma data_of_fields st st' q : data_of (get_meta_rec st' q) = data_of (get_meta_rec st q) ->
  m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q) /\ m_avail (get_meta_rec st' q) = m_avail (get_meta_rec st q)
  /\ m_freed (get_meta_rec st' q) = m_freed (get_meta_rec st q) /\ m_last_idx (get_meta_rec st' q) = m_last_idx (get_meta_rec st q)
  /\ m_freeable (get_meta_rec st' q) = m_freeable (get_meta_rec st q) /\ m_sizeclass (get_meta_rec st' q) = m_sizeclass (get_meta_rec st q)
  /\ m_maplen (get_meta_rec st' q) = m_maplen (get_meta_rec st q).
Proof. intros H. apply data_of_eq. exact H. Qed.

Lemma LPRE_sbl st st' LB c g p i : same_but_links st st' -> LPRE st LB c g p i -> LPRE st' LB c g p i.
Proof.
  intros S L. pose proof (sbl_data _ _ S g) as D. destruct L. constructor.
  - unfold hosts in *. rewrite (sbl_groups _ _ S). exact lp_hosts0.
  - rewrite (proj1 (proj2 (proj2 (proj2 (data_of_fields st st' g D))))). exact lp_i0.
  - rewrite (slot_free_data _ _ i D). exact lp_nonfree0.
  - rewrite (sbl_groups _ _ S), (slot_start'_data _ _ i D). exact lp_nogroup0.
  - rewrite (slot_start'_data _ _ i D). exact lp_noblock0.
  - destruct (data_of_fields st st' g D) as (_ & _ & _ & _ & _ & -> & _). exact lp_class0.
Qed.

Lemma meta_slot_sbl st st' q : same_but_links st st' -> meta_slot st q -> meta_slot st' q.
Proof. intros S H. eapply meta_slot_same_areas; [apply (sbl_areas _ _ S)| exact H]. Qed.

Lemma frame_trans st stA stB : ntf_frame st stA -> ntf_frame stA stB -> ntf_frame st stB.
Proof.
  intros F1 F2. pose proof (LG_frame st stA) as LGF.
  destruct F1, F2; constructor; try congruence; auto.
  - intros q H. apply LGF; [constructor; auto|]. apply nf_linked1. exact H.
  - intros q H. rewrite nf_metas1; [apply nf_metas0; exact H|]. intros H'. apply H. apply LGF; [constructor; auto| exact H'].
Qed.

Lemma LPRE_ctx st f LB c g p i : LPRE st LB c g p i -> LPRE (upd_ctx f st) LB c g p i.
Proof. intros L. destruct L; constructor; auto. Qed.

Lemma LPRE_fg_usage st LB c g p i : LPRE st LB c g p i -> LPRE (fg_usage_st st g) LB c g p i.
Proof. intros L. unfold fg_usage_st. destruct (_ <? 48); [apply LPRE_ctx|]; exact L. Qed.

Lemma LPRE_upd_other st q f LB c g p i : q <> g -> LPRE st LB c g p i -> LPRE (upd_meta q f st) LB c g p i.
Proof.
  intros NE L. destruct L; constructor; auto; rewrite ?rec_upd, ?(aptr_eqb_neq g q) by congruence; auto.
Qed.

Lemma LPRE_mono_c st LB c c' g p i : LPRE st LB c g p i -> c' <= c -> LPRE st LB c' g p i.
Proof. intros L Hc. destruct L; constructor; auto. lia. Qed.

Lemma grp_del_groups st g p : s_groups (grp_del st g p) = delete p (s_groups st). Proof. reflexivity. Qed.
Lemma grp_del_rec st g p q : get_meta_rec (grp_del st g p) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma grp_del_regions st g p : s_regions (grp_del st g p) = s_regions st. Proof. reflexivity. Qed.
Lemma grp_del_shadow st g p : s_shadow (grp_del st g p) = s_shadow st. Proof. reflexivity. Qed.
Lemma grp_del_areas st g p : s_areas (grp_del st g p) = s_areas st. Proof. reflexivity. Qed.
Lemma grp_del_ctx st g p : s_ctx (grp_del st g p) = s_ctx st. Proof. reflexivity. Qed.
Lemma conc_grp_del st g p q : conc (grp_del st g p) q = conc st q. Proof. reflexivity. Qed.

Lemma fg_usage_rec st g q : get_meta_rec (fg_usage_st st g) q = get_meta_rec st q.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_groups st g : s_groups (fg_usage_st st g) = s_groups st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_regions st g : s_regions (fg_usage_st st g) = s_regions st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_shadow st g : s_shadow (fg_usage_st st g) = s_shadow st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_areas st g : s_areas (fg_usage_st st g) = s_areas st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_slots st g : s_slots (fg_usage_st st g) = s_slots st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma conc_fg_usage st g q : conc (fg_usage_st st g) q = conc st q.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fmh_fg_usage st g : c_free_meta_head (ctx (fg_usage_st st g)) = c_free_meta_head (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma seq_fg_usage st g : c_seq (ctx (fg_usage_st st g)) = c_seq (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma brk_fg_usage st g : c_brk (ctx (fg_usage_st st g)) = c_brk (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.

Lemma hosts_grp_del st g p b q : hosts (grp_del st g p) b q <-> b <> p /\ hosts st b q.
Proof.
  unfold hosts. rewrite grp_del_groups. split.
  - intros [ai H]. apply lookup_delete_Some in H. destruct H as [NE H]. split; [congruence| exists ai; exact H].
  - intros [NE [ai H]]. exists ai. apply lookup_delete_Some. split; [congruence| exact H].
Qed.

Lemma links_put_meta0 st g : ci_links_t st -> m_next (get_meta_rec st g) = None -> ci_links_t (put_meta g meta0 st).
Proof.
  intros [N P NN SF] GN. pose proof (proj1 (NN g) GN) as GP.
  constructor.
  - intros m nx H. rewrite rec_put in H. rewrite rec_put.
    destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
    destruct (N m nx H) as [H1 H2]. destruct (aptr_eqb_spec' nx g); [subst; rewrite GP in H1; discriminate|].
    split; [exact H1|]. unfold meta_slot in *. exact H2.
  - intros m pv H. rewrite rec_put in H. rewrite rec_put.
    destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
    destruct (P m pv H) as [H1 H2]. destruct (aptr_eqb_spec' pv g); [subst; rewrite GN in H1; discriminate|].
    split; [exact H1|]. exact H2.
  - intros m. rewrite rec_put. destruct (aptr_eqb_spec' m g); [subst; cbn; LiaTuning.ctauto| apply NN].
  - intros m H. rewrite rec_put in H. destruct (aptr_eqb_spec' m g); [subst; cbn in H; congruence|]. apply SF. exact H.
Qed.

Lemma seq_shape X sc : let st' := record_seq sc (step_seq X) in
  s_regions st' = s_regions X /\ s_shadow st' = s_shadow X /\ s_groups st' = s_groups X /\ s_slots st' = s_slots X
  /\ s_areas st' = s_areas X /\ s_metas st' = s_metas X /\ c_brk (ctx st') = c_brk (ctx X) /\ c_free_meta_head (ctx st') = c_free_meta_head (ctx X).
Proof.
  unfold record_seq, step_seq. destruct (c_seq (ctx X) =? 255); destruct (sc_in_seq_range sc); cbn; repeat split; reflexivity.
Qed.

Lemma fm_shape X g : let st' := fm_st X g in
  s_regions st' = s_regions X /\ s_shadow st' = s_shadow X /\ s_groups st' = s_groups X /\ s_slots st' = s_slots X
  /\ s_areas st' = s_areas X /\ c_brk (ctx st') = c_brk (ctx X).
Proof.
  pose proof (sbl_queue (put_meta g meta0 X) LFree g) as S. unfold fm_st. cbn zeta.
  rewrite (sbl_regions _ _ S), (sbl_shadow _ _ S), (sbl_groups _ _ S), (sbl_slots _ _ S), (sbl_areas _ _ S), (sbl_brk _ _ S).
  repeat split; reflexivity.
Qed.

Lemma deq_mid_shape st h g : same_but_links st (deq_mid h g st).
Proof. apply sbl_deq_mid. Qed.

Lemma conc_sbl st st' q : same_but_links st st' -> conc st' q = conc st q.
Proof. intros S. unfold conc, get_region. rewrite (sbl_regions _ _ S). reflexivity. Qed.

Lemma pd_st_cases an st1 sc :
  pd_st an st1 sc = st1 \/ exists a, an = true /\ active st1 sc = Some a /\ pd_st an st1 sc = act_st st1 a (act_of st1 a).
Proof.
  unfold pd_st. destruct an; [|left; reflexivity]. destruct (active st1 sc) as [a|]; [right; exists a; auto| left; reflexivity].
Qed.

Lemma act_st_rec_other st a act q : q <> a -> get_meta_rec (act_st st a act) q = get_meta_rec st q.
Proof. intros NE. unfold act_st. rewrite rec_upd, (aptr_eqb_neq q a NE). reflexivity. Qed.
Lemma act_st_groups st a act : s_groups (act_st st a act) = s_groups st. Proof. reflexivity. Qed.
Lemma act_st_regions st a act : s_regions (act_st st a act) = s_regions st. Proof. reflexivity. Qed.
Lemma act_st_shadow st a act : s_shadow (act_st st a act) = s_shadow st. Proof. reflexivity. Qed.
Lemma act_st_areas st a act : s_areas (act_st st a act) = s_areas st. Proof. reflexivity. Qed.
Lemma act_st_ctx st a act : s_ctx (act_st st a act) = s_ctx st. Proof. reflexivity. Qed.

Lemma act_of_nonneg st a : 0 <= act_of st a.
Proof.
  unfold act_of. destruct (m_mem (get_meta_rec st a)) as [b|]; [|lia]. cbn [default id].
  unfold mask_upto.
  assert (H : 0 <= group_active_idx st b).
  { unfold group_active_idx. destruct (get_group st b); [apply Z.land_nonneg; right; lia| lia]. }
  assert (0 < 2 ^ (group_active_idx st b + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma slot_start'_eq r i : slot_start' r i = (fst (default (0%N, 0) (m_mem r)), sstart_of r i).
Proof. unfold slot_start', sstart_of, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.

Lemma bits_lt_pow2 n a m : 0 <= a < 2^n -> n <= m -> Z.testbit a m = false.
Proof.
  intros Ha Hm. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  apply (proj1 (Z.bounded_iff_bits_nonneg n a Hn ltac:(lia))); lia.
Qed.
Lemma lt_pow2_bits n a : 0 <= n -> 0 <= a -> (forall m, n <= m -> Z.testbit a m = false) -> a < 2^n.
Proof. intros Hn Ha H. apply (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha)). exact H. Qed.
Lemma lor_range n a b : 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  split; [apply Z.lor_nonneg; lia|].
  apply lt_pow2_bits; [lia| apply Z.lor_nonneg; lia|]. intros m Hm. rewrite Z.lor_spec, (bits_lt_pow2 n a m), (bits_lt_pow2 n b m) by lia. reflexivity.
Qed.
Lemma land_range n a b : 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
  intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  split; [apply Z.land_nonneg; lia|].
  apply lt_pow2_bits; [lia| apply Z.land_nonneg; lia|]. intros m Hm. rewrite Z.land_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
Lemma ldiff_range n a b : 0 <= a < 2^n -> 0 <= Z.ldiff a b < 2^n.
Proof.
  intros Ha. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  assert (H0 : 0 <= Z.ldiff a b) by (apply (proj2 (Z.ldiff_nonneg a b)); lia).
  split; [exact H0|].
  apply lt_pow2_bits; [lia| exact H0|]. intros m Hm. rewrite Z.ldiff_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
Lemma bit_range i : 0 <= i <= 31 -> 0 <= bit i < 2^32.
Proof. intros Hi. unfold bit. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]. Qed.
Lemma testbit_bit i j : 0 <= i -> Z.testbit (bit i) j = (i =? j).
Proof. intros. unfold bit. apply Z.pow2_bits_eqb. lia. Qed.
Lemma testbit_mask_upto li j : 0 <= li -> 0 <= j -> Z.testbit (mask_upto li) j = (j <=? li).
Proof.
  intros. unfold mask_upto. replace (2 ^ (li + 1) - 1) with (Z.ones (li + 1)).
  2:{ unfold Z.ones. rewrite Z.shiftl_1_l. lia. }
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec j (li + 1)); destruct (Z.leb_spec j li); try reflexivity; lia.
Qed.

Lemma all_free_of_mask : forall freed avail i li,
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= i <= li -> li <= 31 ->
  Z.testbit freed i = false -> Z.testbit avail i = false ->
  Z.lor freed avail + bit i = mask_upto li ->
  forall j, 0 <= j <= li -> j <> i -> Z.testbit freed j = true \/ Z.testbit avail j = true.
Proof.
  intros freed avail i li HF HA Hi Hli Fi Ai HM j Hj NE.
  assert (L0 : Z.land (Z.lor freed avail) (bit i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.testbit_0_l by lia.
    destruct (Z.eqb_spec i n); [subst; rewrite Fi, Ai; reflexivity| apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor _ _ L0), (Z.lxor_lor _ _ L0) in HM.
  assert (T : Z.testbit (Z.lor (Z.lor freed avail) (bit i)) j = true).
  { rewrite HM, testbit_mask_upto by lia. apply Z.leb_le. lia. }
  rewrite !Z.lor_spec, testbit_bit in T by lia.
  destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in T.
  destruct (Z.testbit freed j); [left; reflexivity|]. destruct (Z.testbit avail j); [right; reflexivity|]. discriminate.
Qed.

Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n y, 0 <= n -> P n y -> P (n + 1) (f y)) ->
  forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

Lemma del_slots_lookup p stride cnt st s x : 0 <= cnt ->
  (s_slots (del_slots p stride cnt st)) !! s = Some x <->
  (s_slots st) !! s = Some x /\ forall i, 0 <= i < cnt -> s <> aadd p (UNIT + stride * i).
Proof.
  intros Hc. unfold del_slots. cbn [s_slots].
  match goal with |- context [Z.iter cnt ?f ?x0] =>
    enough (IND : fst (Z.iter cnt f x0) = cnt /\ forall s' x', snd (Z.iter cnt f x0) !! s' = Some x' <->
             ((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < cnt -> s' <> aadd p (UNIT + stride * i)))
      by (apply (proj2 IND));
    apply (Z_iter_ind f (fun n acc => fst acc = n /\ forall s' x', snd acc !! s' = Some x' <->
             ((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < n -> s' <> aadd p (UNIT + stride * i)))); [| | exact Hc]
  end.
  - split; [reflexivity|]. intros s' x'. cbn [snd]. split; [intros H; split; [exact H| intros; lia]| intros [H _]; exact H].
  - intros n [i tb] Hn [Hi IH]. cbn [fst snd] in Hi, IH |- *. subst i. split; [reflexivity|].
    intros s' x'. rewrite lookup_delete_Some, IH. split.
    + intros [NE [H1 H2]]. split; [exact H1|]. intros j Hj.
      destruct (Z.eq_dec j n) as [->|]; [congruence| apply H2; lia].
    + intros [H1 H2]. split; [| split; [exact H1| intros j Hj; apply H2; lia]].
      intros E. apply (H2 n); [lia| congruence].
Qed.

Lemma del_slots_lookup_None p stride cnt st s : 0 <= cnt ->
  (s_slots st) !! s = None -> (s_slots (del_slots p stride cnt st)) !! s = None.
Proof.
  intros Hc H. destruct (s_slots (del_slots p stride cnt st) !! s) as [x|] eqn:E; [|reflexivity].
  apply (del_slots_lookup p stride cnt st s x Hc) in E. destruct E as [E _]. congruence.
Qed.

Lemma slot_start'_mem r p j : m_mem r = Some p -> slot_start' r j = aadd p (UNIT + get_stride r * j).
Proof. intros H. unfold slot_start'. rewrite H. reflexivity. Qed.

Definition geom_eq (r r' : meta) : Prop :=
  m_mem r' = m_mem r /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.

Lemma geom_eq_refl r : geom_eq r r. Proof. repeat split; reflexivity. Qed.
Lemma geom_of_data r r' : data_of r' = data_of r -> geom_eq r r'.
Proof. intros H. apply data_of_eq in H. destruct H as (A1 & _ & _ & A4 & A5 & A6 & A7). repeat split; auto. Qed.
Lemma get_stride_geom r r' : geom_eq r r' -> get_stride r' = get_stride r.
Proof. intros (A1 & A2 & A3 & A4 & A5). unfold get_stride. rewrite A2, A4, A5. reflexivity. Qed.
Lemma slot_start'_geom r r' i : geom_eq r r' -> slot_start' r' i = slot_start' r i.
Proof. intros G. unfold slot_start'. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.
Lemma sstart_of_geom r r' i : geom_eq r r' -> sstart_of r' i = sstart_of r i.
Proof. intros G. unfold sstart_of. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.

Section XFER.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis ET : s_tick st' = s_tick st.
Hypothesis EB : c_brk (ctx st') = c_brk (ctx st).
Hypothesis GEO : forall q, is_gm st q -> geom_eq (get_meta_rec st q) (get_meta_rec st' q).
Hypothesis MASK : forall q b, hosts st b q ->
  0 <= m_avail (get_meta_rec st' q) < 2^32 /\ 0 <= m_freed (get_meta_rec st' q) < 2^32
  /\ forall i, 0 <= i ->
       (Z.testbit (m_avail (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q))
       /\ (Z.testbit (m_freed (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q)).
Hypothesis NF : forall q b j, hosts st b q -> 0 <= j <= m_last_idx (get_meta_rec st q) ->
  ~ slot_free (get_meta_rec st q) j -> slot_free (get_meta_rec st' q) j ->
  (s_groups st) !! (slot_start' (get_meta_rec st q) j) = None
  /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st q) j) LB.

#[using="EG"] Lemma hosts_x b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. LiaTuning.ctauto. Qed.
#[using="EG"] Lemma is_gm_x q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_x; exact H. Qed.
#[using="EA"] Lemma meta_slot_x q : meta_slot st' q <-> meta_slot st q.
Proof. unfold meta_slot. rewrite EA. LiaTuning.ctauto. Qed.
#[using="ES"] Lemma get_shadow_x rid : get_shadow st' rid = get_shadow st rid.
Proof. unfold get_shadow. rewrite ES. reflexivity. Qed.
#[using="ER"] Lemma conc_x q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.
#[using="ES"] Lemma hdr_known_x p b1 i1 : hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof. unfold hdr_known. rewrite !get_shadow_x. exact (fun H => H). Qed.

#[using="LB ER ES EA EG ESL GEO MASK NF"] Lemma gmeta_x b g : ci_slots st -> ci_gmeta st -> hosts st b g -> gmeta_ok st' g b.
Proof.
  intros CS CG HB. pose proof (CG b g HB) as GO. pose proof (GEO g (ex_intro _ b HB)) as Gg.
  pose proof Gg as (M1 & M2 & M3 & M4 & M5).
  destruct (MASK g b HB) as (RA & RF & BITS).
  constructor.
  - apply meta_slot_x. exact (go_slot _ _ _ GO).
  - exact RA.
  - exact RF.
  - rewrite M2. exact (go_li _ _ _ GO).
  - rewrite M3. exact (go_freeable _ _ _ GO).
  - rewrite M4, M2, M5. exact (go_sc _ _ _ GO).
  - rewrite M5. exact (go_maplen _ _ _ GO).
  - intros i Hi. rewrite M2. exact (BITS i Hi).
  - rewrite M1. exact (go_mem _ _ _ GO).
  - destruct (go_region _ _ _ GO) as (r & Hr & Kr & S0 & S16 & SP & TOP). exists r.
    rewrite ER, (sstart_of_geom _ _ _ Gg), M2, M5. repeat split; auto; apply TOP; auto.
  - rewrite (get_stride_geom _ _ Gg). exact (go_stride _ _ _ GO).
  - intros ML. rewrite M5 in ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
    pose proof (GEO g1 (ex_intro _ b1 HB1)) as G1. pose proof G1 as (N1 & N2 & N3 & N4 & N5).
    exists g1, i1, b1. rewrite ESL, (slot_start'_geom _ _ _ G1), N2, N4, M4.
    split; [exact SL|]. split; [apply hosts_x; exact HB1|]. split; [exact FB|]. split; [exact EQB|]. split; [exact I1|].
    split.
    { intros FR'. destruct (NF g1 b1 i1 HB1 I1 NF1 FR') as [NG _]. rewrite <- EQB in NG.
      destruct HB as [ai Hai]. rewrite Hai in NG. discriminate. }
    split; [exact LT|]. apply hdr_known_x. exact HK.
Qed.

#[using="ER ES EG ESL GEO NF"] Lemma blks_x : ci_slots st -> Forall (blk_ok st) LB -> Forall (blk_ok st') LB.
Proof.
  intros CS H. apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) H blk Hin) as BK.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  pose proof (GEO g (ex_intro _ b HB)) as Gg. pose proof Gg as (M1 & M2 & M3 & M4 & M5).
  constructor.
  - exists g, i, b. rewrite ESL, M2, (get_stride_geom _ _ Gg), get_shadow_x, conc_x.
    split; [exact SL|]. split; [apply hosts_x; exact HB|]. split; [exact FB|]. split; [exact I|]. split.
    + intros FR'. destruct (NF g b i HB I NFR FR') as [_ NB].
      pose proof (proj1 (Forall_forall _ _) NB blk Hin) as NE. apply NE.
      destruct (CS _ _ _ SL) as (_ & E & _). exact E.
    + exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split; [exact OK|]. apply hdr_known_x. exact HK.
  - rewrite EG. exact NG.
  - exact SZ.
Qed.

#[using="ER ES EA EG ESL ET EB GEO MASK NF"] Lemma KINV_xfer c c' : KINV st LB c -> ci_links_t st' -> ci_heads_t st' -> ci_homog st' -> kctx st' -> usage_ok st' c' -> KINV st' LB c'.
Proof.
  intros K L H HO KC US.
  pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_gmetas _ _ _ K) as CG.
  constructor; auto.
  - intros b g HB. apply gmeta_x; auto. apply hosts_x. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. split; [exact Hg|].
    assert (HB : hosts st b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    destruct (GEO g (ex_intro _ b HB)) as (_ & -> & _). exact Hai.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_x; auto.
  - intros s g i Hs. rewrite ESL in Hs. destruct (CS s g i Hs) as (GM & E & I).
    pose proof (GEO g GM) as Gg. rewrite (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & -> & _).
    split; [apply is_gm_x; exact GM| auto].
  - intros b g i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
    rewrite ESL, (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite get_shadow_x. exact (ki_unk _ _ _ K b gh o Hb Ho).
  - intros g b i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
    rewrite get_shadow_x, (sstart_of_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_h0 _ _ _ K g b i HB Hi).
  - apply blks_x; auto. exact (ki_blks _ _ _ K).
  - exact (ki_nodup _ _ _ K).
  - intros rid off Hb. rewrite EB in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - pose proof (ki_ticks _ _ _ K) as [T1 T2]. split; intros until 0; rewrite ES, ET; [apply T1| apply T2].
Qed.
End XFER.

Section LINKX.
Variables (st st' : mstate).
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis EL : forall q, m_next (get_meta_rec st' q) = m_next (get_meta_rec st q) /\ m_prev (get_meta_rec st' q) = m_prev (get_meta_rec st q).
Hypothesis EH : forall sc, active st' sc = active st sc.
Hypothesis EF : c_free_meta_head (ctx st') = c_free_meta_head (ctx st).
Hypothesis ED : forall q, m_next (get_meta_rec st q) <> None ->
  m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q) /\ m_sizeclass (get_meta_rec st' q) = m_sizeclass (get_meta_rec st q).

#[using="EG EL EH EF ED"] Lemma heads_lx : ci_heads_t st -> ci_heads_t st'.
Proof.
  intros [CF CA]. constructor.
  - intros h Hh. rewrite EF in Hh. destruct (CF h Hh) as [N M]. destruct (EL h) as [E1 _]. rewrite E1.
    destruct (ED h N) as [-> _]. auto.
  - intros sc a Ha. rewrite EH in Ha. destruct (CA sc a Ha) as (SC & N & GM & SCa). destruct (EL a) as [E1 _]. rewrite E1.
    destruct (ED a N) as [_ ->]. pose proof (proj2 (is_gm_ext st st' a EG) GM). auto.
Qed.

#[using="EG EL ED"] Lemma homog_lx : ci_links_t st -> ci_homog st -> ci_homog st'.
Proof.
  intros [LN LP LNN LS] HO m nx Hn. destruct (EL m) as [E1 _]. rewrite E1 in Hn. destruct (HO m nx Hn) as [H1 H2].
  assert (Nm : m_next (get_meta_rec st m) <> None) by congruence.
  assert (Nx : m_next (get_meta_rec st nx) <> None).
  { intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. congruence. }
  destruct (ED m Nm) as [_ ->]. destruct (ED nx Nx) as [_ ->].
  pose proof (is_gm_ext st st' m EG). pose proof (is_gm_ext st st' nx EG). LiaTuning.ctauto.
Qed.
End LINKX.

Lemma KINV_xfer_recs st st' LB c c' :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_tick st' = s_tick st -> s_reserved st' = s_reserved st ->
  c_brk (ctx st') = c_brk (ctx st) -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  (forall sc, active st' sc = active st sc) -> c_free_meta_head (ctx st') = c_free_meta_head (ctx st) ->
  KINV st LB c -> kctx st' -> usage_ok st' c' -> KINV st' LB c'.
Proof.
  intros ER ES EA EG ESL ET ERS EB EM EH EF K KC US.
  eapply (KINV_xfer st st' LB ER ES EA EG ESL ET EB); try exact K; try exact KC; try exact US.
  - intros q _. rewrite EM. apply geom_eq_refl.
  - intros q b HB. rewrite EM. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
    split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
  - intros q b j _ _ NFR FR. rewrite EM in FR. LiaTuning.ctauto.
  - apply (links_ext st st' EA); [| exact (ki_links _ _ _ K)]. intros q. rewrite EM. auto.
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto | exact EH | exact EF | intros q _; rewrite EM; auto | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto | intros q _; rewrite EM; auto | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
Qed.

Lemma KINV_xfer_sbl st st' LB c : same_but_links st st' -> KINV st LB c ->
  ci_links_t st' -> ci_heads_t st' -> ci_homog st' -> KINV st' LB c.
Proof.
  intros S K L H HO.
  eapply (KINV_xfer st st' LB (sbl_regions _ _ S) (sbl_shadow _ _ S) (sbl_areas _ _ S) (sbl_groups _ _ S) (sbl_slots _ _ S)
            (sbl_tick _ _ S) (sbl_brk _ _ S)); try exact K; try exact L; try exact H; try exact HO.
  - intros q _. apply geom_of_data. apply (sbl_data _ _ S).
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
    destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (_ & -> & -> & _).
    split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
  - intros q b j _ _ NFR FR. exfalso. apply NFR. apply (proj1 (slot_free_data _ _ j (sbl_data _ _ S q))). exact FR.
  - pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4). unfold kctx.
    rewrite (sbl_seq _ _ S), (sbl_secret _ _ S). split; [exact X1|]. split; [intros i; rewrite (sbl_bounces _ _ S); apply X2|].
    split; [intros i; rewrite (sbl_unmap _ _ S); apply X3| exact X4].
  - intros sc Hsc. rewrite (sbl_usage _ _ S). exact (ki_usage _ _ _ K sc Hsc).
Qed.

Lemma rec_set_head st h v q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.
Lemma active_set_active_eq st sc v : active (set_active sc v st) sc = v.
Proof.
  unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
  destruct v as [p|]; [apply lookup_insert_eq| apply lookup_delete_eq].
Qed.
Lemma active_set_active_ne st sc sc' v : sc' <> sc -> active (set_active sc v st) sc' = active st sc'.
Proof.
  intros NE. unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
  destruct v as [p|]; [rewrite lookup_insert_ne by lia| rewrite lookup_delete_ne by lia]; reflexivity.
Qed.
Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h as [sc|]; cbn [get_head set_head]; [apply active_set_active_eq| reflexivity]. Qed.

Ltac crush_ptr :=
  repeat (match goal with |- context [aptr_eqb ?x ?y] => destruct (aptr_eqb_spec' x y); try subst end);
  cbn [m_next m_prev m_set_prev m_set_next]; try reflexivity; try congruence.

Lemma fm_single_next st h g q :
  m_next (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
Lemma fm_single_prev st h g q :
  m_prev (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
Lemma fm_link_next st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
  m_next (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.
Lemma fm_link_prev st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
  m_prev (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.

Lemma queue_ctx_some st h g hd : get_head st h = Some hd -> ctx (queue_st h g st) = ctx st.
Proof. intros H. unfold queue_st. rewrite H. unfold fm_link. destruct (m_prev (get_meta_rec st hd)); reflexivity. Qed.
Lemma queue_head_none st h g : get_head st h = None -> get_head (queue_st h g st) h = Some g.
Proof. intros H. unfold queue_st. rewrite H. unfold fm_single. apply get_head_set_head. Qed.
Lemma queue_active_none st h g sc : get_head st h = None -> h <> LActive sc -> active (queue_st h g st) sc = active st sc.
Proof.
  intros H NE. unfold queue_st. rewrite H. unfold fm_single. destruct h as [sc0|]; cbn [set_head].
  - rewrite active_set_active_ne by congruence. reflexivity.
  - reflexivity.
Qed.
Lemma queue_fmh_none st sc g : get_head st (LActive sc) = None ->
  c_free_meta_head (ctx (queue_st (LActive sc) g st)) = c_free_meta_head (ctx st).
Proof. intros H. unfold queue_st. rewrite H. reflexivity. Qed.

Lemma dequeue_next_self st h g q : m_next (get_meta_rec st g) = Some g ->
  m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_next (get_meta_rec st q).
Proof.
  intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
  rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
Lemma dequeue_prev_self st h g q : m_next (get_meta_rec st g) = Some g ->
  m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q).
Proof.
  intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
  rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
Lemma dequeue_next st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
  m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q).
Proof.
  intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
  rewrite rec_upd.
  match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.
Lemma dequeue_prev st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
  m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q).
Proof.
  intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
  rewrite rec_upd.
  match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.

Lemma dequeue_active st sc g nx pv sc' : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  active (dequeue (LActive sc) g st) sc' =
    if sc' =? sc then (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
    else active st sc'.
Proof.
  intros NX PV. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb].
  change (active (upd_meta g ?f ?s) sc') with (active s sc').
  destruct (aptr_eqb_spec' nx g).
  - cbn [negb set_head]. destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| apply active_set_active_ne; exact NE].
  - cbn [negb get_head set_head].
    change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc) with (active st sc).
    destruct (active st sc) as [a|] eqn:HA; cbn [optr_eqb].
    + destruct (aptr_eqb_spec' a g).
      * destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| rewrite active_set_active_ne by exact NE; reflexivity].
      * change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
    + change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
Qed.

Lemma dequeue_fmh st sc g : c_free_meta_head (ctx (dequeue (LActive sc) g st)) = c_free_meta_head (ctx st).
Proof.
  unfold dequeue. lazy zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| reflexivity].
  destruct (m_prev (get_meta_rec st g)); destruct (m_next (get_meta_rec st g));
    match goal with |- context [if ?c then set_head _ _ _ else _] => destruct c end; reflexivity.
Qed.

Lemma dequeue_shape : forall st g sc nx pv,
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  let st' := dequeue (LActive sc) g st in
  (forall x, data_of (get_meta_rec st' x) = data_of (get_meta_rec st x))
  /\ m_next (get_meta_rec st' g) = None /\ m_prev (get_meta_rec st' g) = None
  /\ s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_areas st' = s_areas st
  /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_reserved st' = s_reserved st
  /\ active st' sc = (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
  /\ (forall sc', sc' <> sc -> active st' sc' = active st sc')
  /\ c_free_meta_head (ctx st') = c_free_meta_head (ctx st)
  /\ (forall sc', usage st' sc' = usage st sc') /\ (forall j, bounces st' j = bounces st j) /\ (forall j, unmap_seq st' j = unmap_seq st j)
  /\ c_seq (ctx st') = c_seq (ctx st) /\ c_brk (ctx st') = c_brk (ctx st) /\ c_secret (ctx st') = c_secret (ctx st).
Proof.
  intros st g sc nx pv NX PV. pose proof (sbl_dequeue st (LActive sc) g) as S. cbn zeta.
  split; [exact (sbl_data _ _ S)|].
  split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
  split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
  split; [exact (sbl_regions _ _ S)|]. split; [exact (sbl_shadow _ _ S)|]. split; [exact (sbl_areas _ _ S)|].
  split; [exact (sbl_groups _ _ S)|]. split; [exact (sbl_slots _ _ S)|]. split; [exact (sbl_tick _ _ S)|]. split; [exact (sbl_reserved _ _ S)|].
  split. { rewrite (dequeue_active st sc g nx pv sc NX PV), Z.eqb_refl. reflexivity. }
  split. { intros sc' NE. rewrite (dequeue_active st sc g nx pv sc' NX PV). destruct (Z.eqb_spec sc' sc); [lia| reflexivity]. }
  split; [apply dequeue_fmh|].
  split; [exact (sbl_usage _ _ S)|]. split; [exact (sbl_bounces _ _ S)|]. split; [exact (sbl_unmap _ _ S)|].
  split; [exact (sbl_seq _ _ S)|]. split; [exact (sbl_brk _ _ S)| exact (sbl_secret _ _ S)].
Qed.

Lemma KINV_set_usage : forall st LB c sc v,
  KINV st LB c -> c <= sc -> KINV (set_usage sc v st) LB (sc + 1).
Proof.
  intros st LB c sc v K Hc.
  apply (KINV_xfer_recs st (set_usage sc v st) LB c); try reflexivity; try exact K.
  - exact (ki_cx _ _ _ K).
  - intros sc' Hsc'. unfold usage, set_usage, upd_ctx, ctx. cbn [s_ctx c_usage set_usage_map].
    rewrite lookup_insert_ne by lia. exact (ki_usage _ _ _ K sc' ltac:(lia)).
Qed.

Lemma KINV_seq : forall st LB c sc, KINV st LB c -> KINV (record_seq sc (step_seq st)) LB c.
Proof.
  intros st LB c sc K. pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4).
  apply (KINV_xfer_recs st _ LB c); try exact K;
    try (unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity).
  - unfold kctx, bounces, unmap_seq in *. unfold record_seq, step_seq, upd_ctx, ctx in *.
    destruct (Z.eqb_spec (c_seq (s_ctx st)) 255) as [E|NE]; destruct (sc_in_seq_range sc);
      cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map]; unfold ctx; cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map].
    all: split; [lia|]; split; [exact X2|]; split; [| exact X4].
    all: intros i.
    + destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; rewrite lookup_empty; cbn; lia].
    + rewrite lookup_empty; cbn; lia.
    + destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; apply X3].
    + apply X3.
  - intros sc0 Hsc0. unfold usage. replace (c_usage (ctx (record_seq sc (step_seq st)))) with (c_usage (ctx st)).
    + exact (ki_usage _ _ _ K sc0 Hsc0).
    + unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity.
Qed.

Lemma KINV_fg_usage st LB c g p i : KINV st LB c -> LPRE st LB c g p i -> KINV (fg_usage_st st g) LB (m_sizeclass (get_meta_rec st g) + 1).
Proof.
  intros K L. unfold fg_usage_st. destruct (_ <? 48).
  - apply (KINV_set_usage st LB c); [exact K| exact (lp_class _ _ _ _ _ _ L)].
  - eapply KINV_mono; [exact K|]. pose proof (lp_class _ _ _ _ _ _ L). lia.
Qed.

Lemma KINV_aor : forall st LB c g p i,
  KINV st LB c -> LPRE st LB c g p i -> KINV (aor_st st g i) LB c.
Proof.
  intros st LB c g p i K L. pose proof (lpre_gmeta _ _ _ _ _ _ K L) as GO.
  pose proof (lp_i _ _ _ _ _ _ L) as Hi. pose proof (go_li _ _ _ GO) as LI.
  assert (RQ : forall q, get_meta_rec (aor_st st g i) q =
            if aptr_eqb q g then m_set_freed (Z.lor (m_freed (get_meta_rec st g)) (bit i)) (get_meta_rec st g) else get_meta_rec st q).
  { intros q. unfold aor_st. rewrite rec_upd. reflexivity. }
  apply (KINV_xfer st (aor_st st g i) LB) with (c := c); try reflexivity.
  - intros q _. rewrite RQ. case_ptr q g; [| apply geom_eq_refl]. repeat split; reflexivity.
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ. case_ptr q g.
    + cbn [m_avail m_freed m_set_freed].
      split; [exact (go_avail _ _ _ GQ)|].
      split; [apply (lor_range 32); [exact (go_freed _ _ _ GQ)| apply bit_range; lia]|].
      intros k Hk. split; [intros T; exact (proj1 (go_bits _ _ _ GQ k Hk) T)|].
      rewrite Z.lor_spec, testbit_bit by lia. intros T. apply orb_true_iff in T.
      destruct T as [T|T]; [exact (proj2 (go_bits _ _ _ GQ k Hk) T)| apply Z.eqb_eq in T; lia].
    + exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b j HB Hj NFR FR. rewrite RQ in FR. case_ptr q g; [| LiaTuning.ctauto].
    assert (b = p) as -> by (exact (ki_ginj _ _ _ K b p g HB (lp_hosts _ _ _ _ _ _ L))).
    unfold slot_free in NFR, FR. cbn [m_freed m_avail m_set_freed] in FR. rewrite Z.lor_spec, testbit_bit in FR by lia.
    assert (j = i) as ->.
    { destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in FR. LiaTuning.ctauto. }
    split; [exact (lp_nogroup _ _ _ _ _ _ L)| exact (lp_noblock _ _ _ _ _ _ L)].
  - exact K.
  - apply (links_ext st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K)].
  - apply (heads_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

Lemma KINV_act : forall st LB c a act,
  KINV st LB c -> is_gm st a -> m_avail (get_meta_rec st a) = 0 -> 0 <= act ->
  KINV (act_st st a act) LB c.
Proof.
  intros st LB c a act K GM AV Hact. destruct GM as [b HB]. pose proof (ki_gmetas _ _ _ K b a HB) as GO.
  assert (RQ : forall q, get_meta_rec (act_st st a act) q =
            if aptr_eqb q a then m_set_avail (Z.land (m_freed (get_meta_rec st a)) act) (m_set_freed (Z.ldiff (m_freed (get_meta_rec st a)) act) (get_meta_rec st a)) else get_meta_rec st q).
  { intros q. unfold act_st. rewrite rec_upd. reflexivity. }
  apply (KINV_xfer st (act_st st a act) LB) with (c := c); try reflexivity.
  - intros q _. rewrite RQ. case_ptr q a; [| apply geom_eq_refl]. repeat split; reflexivity.
  - intros q b' HB'. pose proof (ki_gmetas _ _ _ K b' q HB') as GQ. rewrite RQ. case_ptr q a.
    + cbn [m_avail m_freed m_set_freed m_set_avail].
      split; [apply (land_range 32); [exact (go_freed _ _ _ GQ)| exact Hact]|].
      split; [apply (ldiff_range 32); exact (go_freed _ _ _ GQ)|].
      intros k Hk. rewrite Z.land_spec, Z.ldiff_spec.
      split; intros T; apply andb_true_iff in T; destruct T as [T _]; exact (proj2 (go_bits _ _ _ GQ k Hk) T).
    + exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b' j HB' Hj NFR FR. exfalso. apply NFR. rewrite RQ in FR. case_ptr q a; [| exact FR].
    unfold slot_free in FR |- *. cbn [m_avail m_freed m_set_freed m_set_avail] in FR. rewrite Z.land_spec, Z.ldiff_spec in FR.
    left. destruct FR as [T|T]; apply andb_true_iff in T; LiaTuning.ctauto.
  - exact K.
  - apply (links_ext st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K)].
  - apply (heads_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

Definition hkind (st : mstate) (h : lhead) (x : aptr) : Prop :=
  match h with
  | LActive sc => is_gm st x /\ m_sizeclass (get_meta_rec st x) = sc
  | LFree => ~ is_gm st x
  end.

Lemma free_head_not_gm st LB c h : KINV st LB c -> c_free_meta_head (ctx st) = Some h -> ~ is_gm st h.
Proof. intros K H. exact (proj1 (proj2 (proj2 (kinv_free_head st LB c h K H)))). Qed.

Lemma KINV_queue_gen st LB c g h :
  KINV st LB c -> meta_slot st g ->
  m_next (get_meta_rec st g) = None -> m_prev (get_meta_rec st g) = None ->
  match h with
  | LActive sc => is_gm st g /\ m_sizeclass (get_meta_rec st g) = sc /\ 0 <= sc < 48
  | LFree => ~ is_gm st g /\ m_mem (get_meta_rec st g) = None
  end ->
  KINV (queue_st h g st) LB c.
Proof.
  intros K MSg N0 P0 HH.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (sbl_queue st h g) as S. set (st' := queue_st h g st) in *.
  assert (GK : hkind st h g) by (destruct h; cbn; LiaTuning.ctauto).
  assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
  assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
  assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
  assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).

  assert (HD : forall hd, get_head st h = Some hd ->
             m_next (get_meta_rec st hd) <> None /\ hd <> g /\ hkind st h hd /\
             exists pv, m_prev (get_meta_rec st hd) = Some pv /\ pv <> g /\ m_next (get_meta_rec st pv) = Some hd /\ hkind st h pv).
  { intros hd Hhd.
    assert (N : m_next (get_meta_rec st hd) <> None /\ hkind st h hd).
    { destruct h as [sc|]; cbn in Hhd |- *.
      - destruct (CA _ _ Hhd) as (_ & N & GM & SC). auto.
      - split; [exact (proj1 (CF _ Hhd))| exact (free_head_not_gm st LB c hd K Hhd)]. }
    destruct N as [N HK]. split; [exact N|]. split; [congruence|]. split; [exact HK|].
    destruct (m_prev (get_meta_rec st hd)) as [pv|] eqn:PV; [| exfalso; apply N; apply (proj2 (LNN hd)); exact PV].
    exists pv. destruct (LP hd pv PV) as [NP _]. split; [reflexivity|]. split; [congruence|]. split; [exact NP|].
    destruct (HO pv hd NP) as [G1 G2]. destruct h as [sc|]; cbn in HK |- *.
    - destruct HK as [GMh SCh]. assert (GMp : is_gm st pv) by LiaTuning.ctauto. split; [exact GMp|]. rewrite <- (G2 GMp). exact SCh.
    - LiaTuning.ctauto. }
  apply (KINV_xfer_sbl st st' LB c S K).
  -
    destruct (get_head st h) as [hd|] eqn:Hhd.
    + destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
      assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_next. exact PV. }
      assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_prev. exact PV. }
      constructor.
      * intros m nx Hn. rewrite FN in Hn. rewrite FP.
        destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
        -- assert (nx = g) as -> by congruence. rewrite (aptr_eqb_neq g hd) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- assert (nx = hd) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; exact Nhd].
        -- destruct (LN m nx Hn) as [P1 S1].
           destruct (aptr_eqb_spec' nx hd); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; LiaTuning.ctauto|].
           destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|].
           split; [exact P1| apply MSx; exact S1].
      * intros m pv0 Hp. rewrite FP in Hp. rewrite FN.
        destruct (aptr_eqb_spec' m hd) as [->|NEmh]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
        -- assert (pv0 = g) as -> by congruence. rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- assert (pv0 = pv) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; congruence].
        -- destruct (LP m pv0 Hp) as [N1 S1].
           destruct (aptr_eqb_spec' pv0 pv); [subst; exfalso; rewrite Npv in N1; assert (m = hd) by congruence; LiaTuning.ctauto|].
           destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|].
           split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP.
        destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m g); [subst|]].
        -- destruct (aptr_eqb_spec' pv hd); [split; discriminate|]. rewrite (aptr_eqb_neq pv g) by congruence.
           assert (m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
           split; [discriminate| intros E; exfalso; exact (H E)].
        -- rewrite (aptr_eqb_neq g hd) by congruence. split; discriminate.
        -- destruct (aptr_eqb_spec' m hd); [subst; split; [intros E; exfalso; exact (Nhd E)| discriminate]| apply LNN].
      * intros m Hn. rewrite FN in Hn. apply MSx.
        destruct (aptr_eqb_spec' m pv); [subst; apply LS; congruence|]. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
    + assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_next. }
      assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_prev. }
      constructor.
      * intros m nx Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [->|NEmg].
        -- assert (nx = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- destruct (LN m nx Hn) as [P1 S1]. destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|]. split; [exact P1| apply MSx; exact S1].
      * intros m pv0 Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [->|NEmg].
        -- assert (pv0 = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- destruct (LP m pv0 Hp) as [N1 S1]. destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|]. split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [split; discriminate| apply LNN].
      * intros m Hn. rewrite FN in Hn. apply MSx. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
  -
    assert (NXT : forall x, m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
    { intros x Hx. unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
      - destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & _). rewrite (fm_link_next st g hd pv x PV).
        destruct (aptr_eqb x pv); [discriminate|]. destruct (aptr_eqb x g); [discriminate| exact Hx].
      - rewrite fm_single_next. destruct (aptr_eqb x g); [discriminate| exact Hx]. }
    assert (NXg : m_next (get_meta_rec st' g) <> None).
    { unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
      - destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & NEpv & _). rewrite (fm_link_next st g hd pv g PV).
        rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. discriminate.
      - rewrite fm_single_next, aptr_eqb_refl. discriminate. }
    constructor.
    + intros h0 Hh0.
      destruct (get_head st h) as [hd|] eqn:Hhd.
      * unfold st' in Hh0. rewrite (queue_ctx_some st h g hd Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
      * destruct h as [sc|].
        -- unfold st' in Hh0. rewrite (queue_fmh_none st sc g Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
        -- pose proof (queue_head_none st LFree g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Hh0. assert (h0 = g) as -> by congruence.
           rewrite EMM. split; [exact NXg| exact (proj2 HH)].
    + intros sc a Ha.
      assert (OLD : active st sc = Some a -> 0 <= sc < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st' a) = sc).
      { intros Ho. destruct (CA sc a Ho) as (R & N & GM & SC). rewrite ESC. split; [exact R|]. split; [apply NXT; exact N|]. split; [apply EGM; exact GM| exact SC]. }
      destruct (get_head st h) as [hd|] eqn:Hhd.
      * apply OLD. unfold st' in Ha. unfold active in Ha |- *. rewrite (queue_ctx_some st h g hd Hhd) in Ha. exact Ha.
      * destruct h as [sc0|].
        -- destruct (Z.eq_dec sc sc0) as [->|NE].
           ++ pose proof (queue_head_none st (LActive sc0) g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Ha. assert (a = g) as -> by congruence.
              destruct HH as (GM & SC & R). rewrite ESC. split; [exact R|]. split; [exact NXg|]. split; [apply EGM; exact GM| exact SC].
           ++ apply OLD. unfold st' in Ha. rewrite (queue_active_none st (LActive sc0) g sc Hhd) in Ha by congruence. exact Ha.
        -- apply OLD. unfold st' in Ha. rewrite (queue_active_none st LFree g sc Hhd) in Ha by congruence. exact Ha.
  -
    assert (HKx : forall x y, hkind st h x -> hkind st h y -> (is_gm st x <-> is_gm st y) /\ (is_gm st x -> m_sizeclass (get_meta_rec st y) = m_sizeclass (get_meta_rec st x))).
    { intros x y Hx Hy. destruct h as [sc|]; cbn in Hx, Hy; [| LiaTuning.ctauto]. destruct Hx as [Gx Sx], Hy as [Gy Sy]. split; [LiaTuning.ctauto| intros _; congruence]. }
    intros m nx Hn. rewrite !EGM, !ESC.
    destruct (get_head st h) as [hd|] eqn:Hhd.
    + destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
      unfold st', queue_st in Hn. rewrite Hhd, (fm_link_next st g hd pv m PV) in Hn.
      destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [assert (nx = g) as -> by congruence; apply HKx; auto|].
      destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = hd) as -> by congruence; apply HKx; auto|].
      exact (HO m nx Hn).
    + unfold st', queue_st in Hn. rewrite Hhd, fm_single_next in Hn.
      destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = g) as -> by congruence; split; [LiaTuning.ctauto| reflexivity]|].
      exact (HO m nx Hn).
Qed.

Lemma KINV_queue : forall st LB c g p sc,
  KINV st LB c -> hosts st p g -> sc = m_sizeclass (get_meta_rec st g) -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = None -> m_prev (get_meta_rec st g) = None ->
  active st sc <> Some g ->
  KINV (queue_st (LActive sc) g st) LB c.
Proof.
  intros st LB c g p sc K HB SC R N0 P0 _.
  apply (KINV_queue_gen st LB c g (LActive sc) K (go_slot _ _ _ (ki_gmetas _ _ _ K p g HB)) N0 P0).
  split; [exists p; exact HB|]. split; [symmetry; exact SC| exact R].
Qed.

Lemma KINV_dequeue : forall st LB c g p sc nx,
  KINV st LB c -> hosts st p g -> sc = m_sizeclass (get_meta_rec st g) ->
  m_next (get_meta_rec st g) = Some nx ->
  KINV (dequeue (LActive sc) g st) LB c.
Proof.
  intros st LB c g p sc nx K HB SC NX.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (ki_gmetas _ _ _ K p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM.
  assert (GMg : is_gm st g) by (exists p; exact HB).
  pose proof (sbl_dequeue st (LActive sc) g) as S. set (st' := dequeue (LActive sc) g st) in *.
  assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
  assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
  assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
  assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).
  destruct (LN g nx NX) as [Pnx Snx].
  destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV; [| apply (proj2 (LNN g)) in PV; congruence].
  destruct (LP g pv PV) as [Npv Spv].
  pose proof (dequeue_fmh st sc g) as EF. fold st' in EF.
  pose proof (fun sc' => dequeue_active st sc g nx pv sc' NX PV) as EH. fold st' in EH.

  assert (NEfree : forall h0, c_free_meta_head (ctx st) = Some h0 -> h0 <> g).
  { intros h0 Hh0 ->. destruct (CF g Hh0) as [_ M]. congruence. }
  destruct (aptr_eqb_spec' nx g) as [Enx|NEnx].
  -
    subst nx. assert (pv = g) as -> by congruence.
    assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else m_next (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_next_self. exact NX. }
    assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_prev_self. exact NX. }
    assert (NXo : forall m x, m_next (get_meta_rec st m) = Some x -> m <> g -> x <> g).
    { intros m x Hm NE ->. destruct (LN m g Hm) as [P1 _]. congruence. }
    assert (PVo : forall m x, m_prev (get_meta_rec st m) = Some x -> m <> g -> x <> g).
    { intros m x Hm NE ->. destruct (LP m g Hm) as [P1 _]. congruence. }
    apply (KINV_xfer_sbl st st' LB c S K).
    + constructor.
      * intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        rewrite (aptr_eqb_neq x g) by (exact (NXo m x Hn NEmg)). destruct (LN m x Hn) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
      * intros m x Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        rewrite (aptr_eqb_neq x g) by (exact (PVo m x Hp NEmg)). destruct (LP m x Hp) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [LiaTuning.ctauto| apply LNN].
      * intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx. apply LS. exact Hn.
    + constructor.
      * intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite FN, EMM, (aptr_eqb_neq h0 g) by (exact (NEfree h0 Hh0)). auto.
      * intros sc' a Ha. rewrite EH in Ha. rewrite ?aptr_eqb_refl in Ha.
        destruct (Z.eqb_spec sc' sc); [discriminate|].
        destruct (CA sc' a Ha) as (R & N & GM & SCa).
        assert (NEa : a <> g) by (intros ->; apply n; rewrite SC; symmetry; exact SCa).
        rewrite FN, ESC, (aptr_eqb_neq a g NEa). split; [exact R|]. split; [exact N|]. split; [apply EGM; exact GM| exact SCa].
    + intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [discriminate|]. exact (HO m x Hn).
  -
    assert (NEpv : pv <> g) by (intros ->; rewrite Npv in NX; apply NEnx; congruence).
    assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_next; assumption. }
    assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_prev; assumption. }
    assert (Nnx : m_next (get_meta_rec st nx) <> None) by (intros E; apply (proj1 (LNN nx)) in E; congruence).
    assert (Ppv : m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
    assert (NXT : forall x, x <> g -> m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
    { intros x NE Hx. rewrite FN, (aptr_eqb_neq x g NE). destruct (aptr_eqb x pv); [discriminate| exact Hx]. }
    apply (KINV_xfer_sbl st st' LB c S K).
    + constructor.
      * intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        destruct (aptr_eqb_spec' m pv) as [->|NEmp].
        -- assert (x = nx) as -> by congruence. rewrite (aptr_eqb_neq nx g NEnx), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Snx].
        -- destruct (LN m x Hn) as [P1 S1].
           destruct (aptr_eqb_spec' x g); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; LiaTuning.ctauto|].
           destruct (aptr_eqb_spec' x nx); [subst; exfalso; rewrite Pnx in P1; assert (m = g) by congruence; LiaTuning.ctauto|].
           split; [exact P1| apply MSx; exact S1].
      * intros m y Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        destruct (aptr_eqb_spec' m nx) as [->|NEmn].
        -- assert (y = pv) as -> by congruence. rewrite (aptr_eqb_neq pv g NEpv), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Spv].
        -- destruct (LP m y Hp) as [N1 S1].
           destruct (aptr_eqb_spec' y g); [subst; exfalso; rewrite NX in N1; assert (m = nx) by congruence; LiaTuning.ctauto|].
           destruct (aptr_eqb_spec' y pv); [subst; exfalso; rewrite Npv in N1; assert (m = g) by congruence; LiaTuning.ctauto|].
           split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [LiaTuning.ctauto|].
        destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m nx); [subst|]].
        -- destruct (aptr_eqb_spec' pv nx); [split; discriminate|]. split; [discriminate| intros E; exfalso; exact (Ppv E)].
        -- split; [intros E; exfalso; exact (Nnx E)| discriminate].
        -- apply LNN.
      * intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx.
        destruct (aptr_eqb_spec' m pv); [subst; exact Spv| apply LS; exact Hn].
    + constructor.
      * intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; [exact (NEfree h0 Hh0)| exact N]| exact M].
      * intros sc' a Ha. rewrite EH, ?(aptr_eqb_neq nx g NEnx) in Ha. rewrite ESC.
        assert (OLD : active st sc' = Some a -> a <> g -> 0 <= sc' < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st a) = sc').
        { intros Ho NE. destruct (CA sc' a Ho) as (R & N & GM & SCa). split; [exact R|]. split; [apply NXT; auto|]. split; [apply EGM; exact GM| exact SCa]. }
        destruct (Z.eqb_spec sc' sc).
        -- subst sc'. destruct (active st sc) as [a0|] eqn:A0; cbn [optr_eqb] in Ha; [|discriminate].
           destruct (aptr_eqb_spec' a0 g).
           ++ assert (a = nx) as -> by congruence. destruct (CA _ _ A0) as (R & _ & _ & _). destruct (HO g nx NX) as [G1 G2].
              split; [exact R|]. split; [apply NXT; [exact NEnx| exact Nnx]|]. split; [apply EGM; LiaTuning.ctauto| rewrite (G2 GMg); symmetry; exact SC].
           ++ apply OLD; [exact Ha| congruence].
        -- apply OLD; [exact Ha|]. intros ->. destruct (CA sc' g Ha) as (_ & _ & _ & SCg). apply n. rewrite SC. symmetry. exact SCg.
    + intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
      destruct (aptr_eqb_spec' m pv) as [->|NEmp].
      * assert (x = nx) as -> by congruence. destruct (HO pv g Npv) as [A1 A2]. destruct (HO g nx NX) as [B1 B2].
        split; [LiaTuning.ctauto|]. intros Gp. rewrite (B2 GMg). exact (A2 Gp).
      * exact (HO m x Hn).
Qed.

Lemma KINV_grp_del : forall st LB c g p,
  KINV st LB c -> hosts st p g -> m_next (get_meta_rec st g) = None ->
  (forall j, 0 <= j <= m_last_idx (get_meta_rec st g) ->
     (s_groups st) !! (slot_start' (get_meta_rec st g) j) = None
     /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) j) LB) ->
  KINV (grp_del st g p) LB c
  /\ ~ is_gm (grp_del st g p) g
  /\ (forall s j, (s_slots (grp_del st g p)) !! s <> Some (g, j)).
Proof.
  intros st LB c g p K HB GN CLR.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM. pose proof (go_li _ _ _ GO) as LI.
  pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_sltt _ _ _ K) as CT. pose proof (ki_ginj _ _ _ K) as GI.
  set (st' := grp_del st g p).
  assert (CNT : 0 <= m_last_idx (get_meta_rec st g) + 1) by lia.

  assert (SL : forall s x, (s_slots st') !! s = Some x <->
            (s_slots st) !! s = Some x /\ forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
  { intros s x. unfold st', grp_del. rewrite (del_slots_lookup p _ _ (del_group p st) s x CNT). cbn [s_slots del_group set_groups].
    split; intros [H1 H2]; split; auto; intros j Hj; rewrite ?(slot_start'_mem _ p j MEM); [apply H2; lia|].
    rewrite <- (slot_start'_mem _ p j MEM). apply H2. lia. }

  assert (GR : forall b gh, (s_groups st') !! b = Some gh <-> b <> p /\ (s_groups st) !! b = Some gh).
  { intros b gh. unfold st'. rewrite grp_del_groups, lookup_delete_Some. split; intros [A B]; split; auto; congruence. }
  assert (HX : forall b q, hosts st' b q <-> b <> p /\ hosts st b q) by (intros; apply hosts_grp_del).
  assert (Hg : forall b, hosts st b g -> b = p) by (intros b Hb; exact (GI b p g Hb HB)).
  assert (Hp : forall q, hosts st p q -> q = g).
  { intros q [ai Hq]. destruct HB as [ai' Hb']. rewrite Hb' in Hq. congruence. }
  assert (GMX : forall q, q <> g -> (is_gm st' q <-> is_gm st q)).
  { intros q NE. split; intros [b Hb]; exists b; [apply HX in Hb; LiaTuning.ctauto|]. apply HX. split; [| exact Hb]. intros ->. apply NE. apply Hp. exact Hb. }
  assert (NGM : ~ is_gm st' g).
  { intros [b Hb]. apply HX in Hb. destruct Hb as [NE Hb]. apply NE. apply Hg. exact Hb. }

  assert (KEEP : forall s, (exists gh, (s_groups st) !! s = Some gh) \/ (exists blk, blk ∈ LB /\ blk_slot blk = s) ->
            forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
  { intros s Hs j Hj ->. destruct (CLR j Hj) as [C1 C2]. destruct Hs as [[gh Hgh]|[blk [Hin Hbs]]]; [rewrite C1 in Hgh; discriminate|].
    exact (proj1 (Forall_forall _ _) C2 blk Hin Hbs). }
  assert (LINKED_NE : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
  split; [| split; [exact NGM|]].
  2:{ intros s j Hs. apply SL in Hs. destruct Hs as [H1 H2]. destruct (CS _ _ _ H1) as (_ & E & J). exact (H2 j J E). }
  constructor.
  - apply (links_ext st st'); [reflexivity| intros; split; reflexivity| exact L].
  - constructor.
    + intros h Hh. exact (CF h Hh).
    + intros sc a Ha. destruct (CA sc a Ha) as (R & N & GM & SC). split; [exact R|]. split; [exact N|]. split; [apply GMX; [apply LINKED_NE; exact N| exact GM]| exact SC].
  - intros m nx Hn. change (get_meta_rec st' m) with (get_meta_rec st m) in Hn.
    change (m_sizeclass (get_meta_rec st' nx)) with (m_sizeclass (get_meta_rec st nx)).
    change (m_sizeclass (get_meta_rec st' m)) with (m_sizeclass (get_meta_rec st m)).
    destruct (HO m nx Hn) as [A B].
    assert (NEm : m <> g) by (apply LINKED_NE; rewrite Hn; discriminate).
    assert (NEn : nx <> g).
    { apply LINKED_NE. intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. rewrite E in P. discriminate. }
    pose proof (GMX m NEm). pose proof (GMX nx NEn). LiaTuning.ctauto.
  - intros b q HBq. apply HX in HBq. destruct HBq as [NEb HBq].
    assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
    pose proof (CG b q HBq) as GQ.
    constructor; try (change (get_meta_rec st' ?x) with (get_meta_rec st x)); try exact (go_avail _ _ _ GQ); try exact (go_freed _ _ _ GQ);
      try exact (go_li _ _ _ GQ); try exact (go_freeable _ _ _ GQ); try exact (go_sc _ _ _ GQ); try exact (go_maplen _ _ _ GQ);
      try exact (go_bits _ _ _ GQ); try exact (go_mem _ _ _ GQ); try exact (go_region _ _ _ GQ); try exact (go_stride _ _ _ GQ).
    + exact (go_slot _ _ _ GQ).
    + intros ML. destruct (go_nest _ _ _ GQ ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      exists g1, i1, b1. change (get_meta_rec st' ?x) with (get_meta_rec st x).
      split. { apply SL. split; [exact S1|]. apply KEEP. left. destruct HBq as [ai Hai]. eexists; exact Hai. }
      split. { apply HX. split; [| exact HB1]. intros ->. pose proof (Hp g1 HB1) as ->.
               destruct (CLR i1 I1) as [C1 _]. rewrite <- EQB in C1. destruct HBq as [ai Hai]. rewrite C1 in Hai. discriminate. }
      change (get_meta_rec st' g1) with (get_meta_rec st g1). change (get_meta_rec st' q) with (get_meta_rec st q).
      split; [exact FB|]. split; [exact EQB|]. split; [exact I1|]. split; [exact NF1|]. split; [exact LT|]. exact HK.
  - intros b gh Hb. apply GR in Hb. destruct Hb as [_ Hb]. exact (ki_grps _ _ _ K b gh Hb).
  - intros b1 b2 q H1 H2. apply HX in H1. apply HX in H2. exact (GI b1 b2 q (proj2 H1) (proj2 H2)).
  - intros s q i Hs. apply SL in Hs. destruct Hs as [Hs NK]. destruct (CS s q i Hs) as (GM & E & I).
    change (get_meta_rec st' q) with (get_meta_rec st q).
    assert (NEq : q <> g) by (intros ->; exact (NK i I E)).
    split; [apply GMX; auto| auto].
  - intros b q i HBq Hi. change (get_meta_rec st' q) with (get_meta_rec st q) in Hi |- *.
    apply HX in HBq. destruct HBq as [NEb HBq].
    assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
    apply SL. split; [exact (CT b q i HBq Hi)|].
    intros j Hj E. pose proof (CT p g j HB Hj) as Tg. rewrite <- E, (CT b q i HBq Hi) in Tg. exfalso. apply NEq. congruence.
  - intros b gh o Hb Ho. apply GR in Hb. exact (ki_unk _ _ _ K b gh o (proj2 Hb) Ho).
  - intros q b i HBq Hi. apply HX in HBq. exact (ki_h0 _ _ _ K q b i (proj2 HBq) Hi).
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & REST) NG SZ].
    constructor; [| unfold st'; rewrite grp_del_groups, lookup_delete_None; right; exact NG | exact SZ].
    exists q, i, b. change (get_meta_rec st' ?x) with (get_meta_rec st x). change (conc st' ?x) with (conc st x). change (get_shadow st' ?x) with (get_shadow st x).
    split. { apply SL. split; [exact S1|]. apply KEEP. right. exists blk. auto. }
    split. { apply HX. split; [| exact HBq]. intros ->. pose proof (Hp q HBq) as ->.
             destruct (CS _ _ _ S1) as (_ & E & _). exact (KEEP (blk_slot blk) (or_intror (ex_intro _ blk (conj Hin eq_refl))) i I E). }
    split; [exact FB|]. split; [exact I|]. split; [exact NFR|]. exact REST.
  - exact (ki_nodup _ _ _ K).
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
  - exact (ki_bk _ _ _ K).
  - exact (ki_ticks _ _ _ K).
Qed.

Lemma KINV_put_meta0 st LB c g :
  KINV st LB c -> ~ is_gm st g -> m_next (get_meta_rec st g) = None ->
  (forall s j, (s_slots st) !! s <> Some (g, j)) ->
  KINV (put_meta g meta0 st) LB c.
Proof.
  intros K NGM GN NS.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS]. pose proof (proj1 (LNN g) GN) as GP.
  assert (RQ : forall q, get_meta_rec (put_meta g meta0 st) q = if aptr_eqb q g then meta0 else get_meta_rec st q) by (intros q; apply rec_put).
  assert (GMne : forall q, is_gm st q -> q <> g) by (intros q Hq ->; exact (NGM Hq)).
  assert (LKne : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
  apply (KINV_xfer st (put_meta g meta0 st) LB) with (c := c); try reflexivity.
  - intros q Hq. rewrite RQ, (aptr_eqb_neq q g (GMne q Hq)). apply geom_eq_refl.
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))).
    exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b j HB _ NFR FR. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))) in FR. LiaTuning.ctauto.
  - exact K.
  - apply links_put_meta0; [exact L| exact GN].
  - apply (heads_lx st (put_meta g meta0 st)); [reflexivity | | intros sc; reflexivity | reflexivity | | exact (ki_heads _ _ _ K)].
    + intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
    + intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
  - apply (homog_lx st (put_meta g meta0 st)); [reflexivity | | | exact L | exact (ki_hom _ _ _ K)].
    + intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
    + intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

Lemma KINV_fm : forall st LB c g,
  KINV st LB c -> meta_slot st g -> ~ is_gm st g ->
  m_next (get_meta_rec st g) = None ->
  (forall s j, (s_slots st) !! s <> Some (g, j)) ->
  KINV (fm_st st g) LB c.
Proof.
  intros st LB c g K MSg NGM GN NS. unfold fm_st.
  apply (KINV_queue_gen (put_meta g meta0 st) LB c g LFree).
  - apply KINV_put_meta0; assumption.
  - exact MSg.
  - rewrite rec_put, aptr_eqb_refl. reflexivity.
  - rewrite rec_put, aptr_eqb_refl. reflexivity.
  - cbn. split; [| rewrite rec_put, aptr_eqb_refl; reflexivity]. intros [b [ai Hb]]. apply NGM. exists b, ai. exact Hb.
Qed.

Lemma snd_slot_start' st g p j : gmeta_ok st g p -> 0 <= j -> snd p + 16 <= snd (slot_start' (get_meta_rec st g) j).
Proof.
  intros GO Hj. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). cbn [aadd snd].
  pose proof (go_stride _ _ _ GO) as [S16 _]. unfold UNIT in *.
  assert (0 <= get_stride (get_meta_rec st g) * j) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

Lemma fst_slot_start' st g p j : gmeta_ok st g p -> fst (slot_start' (get_meta_rec st g) j) = fst p.
Proof. intros GO. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). reflexivity. Qed.

Lemma free_slot_clear : forall st LB c g p j,
  KINV st LB c -> hosts st p g -> 0 <= j <= m_last_idx (get_meta_rec st g) ->
  slot_free (get_meta_rec st g) j ->
  (s_groups st) !! (slot_start' (get_meta_rec st g) j) = None
  /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) j) LB.
Proof.
  intros st LB c g p j K HB Hj FR.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (ki_sltt _ _ _ K p g j HB Hj) as Tj.
  set (s := slot_start' (get_meta_rec st g) j) in *.
  split.
  - destruct (s_groups st !! s) as [gh|] eqn:Hs; [| reflexivity]. exfalso.
    destruct (ki_grps _ _ _ K s gh Hs) as (g' & Hg' & _).
    assert (HB' : hosts st s g') by (exists (g_active_idx gh); rewrite Hs; destruct gh; cbn in Hg' |- *; subst; reflexivity).
    pose proof (CG s g' HB') as GO'.
    destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML|ML].
    + destruct (go_nest _ _ _ GO' ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
      rewrite Tj in S1. assert (g1 = g) as -> by congruence. assert (i1 = j) as -> by congruence. exact (NF1 FR).
    + destruct (go_region _ _ _ GO') as (r & _ & _ & _ & _ & _ & TOP). destruct (TOP ML) as [S0 _].
      destruct (go_region _ _ _ GO) as (r0 & _ & _ & P0 & _).
      pose proof (snd_slot_start' st g p j GO ltac:(lia)) as LE. fold s in LE. lia.
  - apply Forall_forall. intros blk Hin E.
    pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & _) _ _].
    rewrite E, Tj in S1. assert (q = g) as -> by congruence. assert (i = j) as -> by congruence. exact (NFR FR).
Qed.

Lemma top_region_clear : forall st LB c g p i,
  KINV st LB c -> LPRE st LB c g p i -> m_maplen (get_meta_rec st g) <> 0 ->
  (forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> j <> i -> slot_free (get_meta_rec st g) j) ->
  forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> b = p.
Proof.
  intros st LB c g p i K L ML ALLF.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (lp_hosts _ _ _ _ _ _ L) as HB. pose proof (CG p g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & _ & _ & _ & _ & TOP). destruct (TOP ML) as [P0 _].
  assert (REC : forall n, forall b gh, 0 <= snd b < Z.of_nat n -> (s_groups st) !! b = Some gh -> fst b = fst p -> b = p).
  { induction n as [|n IH]; intros b gh Hn Hb Hf; [lia|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
    assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
    pose proof (CG b g' HB') as GO'.
    destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML'|ML'].
    - destruct (go_nest _ _ _ GO' ML') as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
      pose proof (CG b1 g1 HB1) as GO1.
      destruct (go_region _ _ _ GO1) as (r1 & _ & _ & B10 & _).
      pose proof (snd_slot_start' st g1 b1 i1 GO1 ltac:(lia)) as LE. rewrite <- EQB in LE.
      assert (E1 : b1 = p).
      { destruct HB1 as [ai1 Hb1]. apply (IH b1 _ ltac:(lia) Hb1). rewrite FB. exact Hf. }
      subst b1. assert (g1 = g) as ->.
      { destruct HB1 as [ai1 Hb1]. destruct HB as [ai Hb0]. rewrite Hb0 in Hb1. congruence. }
      exfalso. destruct (Z.eq_dec i1 i) as [->|NE].
      + pose proof (lp_nogroup _ _ _ _ _ _ L) as NG. rewrite <- EQB in NG. rewrite NG in Hb. discriminate.
      + exact (NF1 (ALLF i1 I1 NE)).
    - destruct (go_region _ _ _ GO') as (r' & _ & _ & _ & _ & _ & TOP'). destruct (TOP' ML') as [B0 _].
      apply injective_projections; [exact Hf| rewrite B0, P0; reflexivity]. }
  intros b gh Hb Hf.
  destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
  assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
  destruct (go_region _ _ _ (CG b g' HB')) as (rb & _ & _ & B0 & _).
  apply (REC (S (Z.to_nat (snd b))) b gh); [| exact Hb| exact Hf]. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

Definition ZINV (st : mstate) (Zs : list aptr) : Prop :=
  forall q b, m_mem (get_meta_rec st q) = Some b -> hosts st b q \/ In q Zs.

Lemma ZINV_of_CINV st LB : CINV st LB -> ZINV st [].
Proof. intros C q b H. left. exact (ci_memh _ _ C q b H). Qed.

Lemma ZINV_ext st st' Zs : (forall q, m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q)) ->
  s_groups st' = s_groups st -> ZINV st Zs -> ZINV st' Zs.
Proof.
  intros EM EG Z q b H. rewrite EM in H. destruct (Z q b H) as [HB|HI]; [left| right; exact HI].
  unfold hosts in *. rewrite EG. exact HB.
Qed.

Lemma ZINV_sbl st st' Zs : same_but_links st st' -> ZINV st Zs -> ZINV st' Zs.
Proof.
  intros S. apply ZINV_ext; [| exact (sbl_groups _ _ S)].
  intros q. destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (E & _). exact E.
Qed.

Lemma ZINV_aor st g i Zs : ZINV st Zs -> ZINV (aor_st st g i) Zs.
Proof. apply ZINV_ext; [| reflexivity]. intros q. unfold aor_st. rewrite rec_upd. destruct (aptr_eqb_spec' q g); [subst; reflexivity| reflexivity]. Qed.

Lemma ZINV_act st a act Zs : ZINV st Zs -> ZINV (act_st st a act) Zs.
Proof. apply ZINV_ext; [| reflexivity]. intros q. unfold act_st. rewrite rec_upd. destruct (aptr_eqb_spec' q a); [subst; reflexivity| reflexivity]. Qed.

Lemma ZINV_pd an st sc Zs : ZINV st Zs -> ZINV (pd_st an st sc) Zs.
Proof. intros Z. destruct (pd_st_cases an st sc) as [-> | (a & _ & _ & ->)]; [exact Z| apply ZINV_act; exact Z]. Qed.

Lemma ZINV_ctx st f Zs : ZINV st Zs -> ZINV (upd_ctx f st) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

Lemma ZINV_fg_usage st g Zs : ZINV st Zs -> ZINV (fg_usage_st st g) Zs.
Proof. intros Z. unfold fg_usage_st. destruct (_ <? 48); [apply ZINV_ctx|]; exact Z. Qed.

Lemma ZINV_seq st sc Zs : ZINV st Zs -> ZINV (record_seq sc (step_seq st)) Zs.
Proof.
  intros Z. unfold record_seq, step_seq.
  destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); repeat apply ZINV_ctx; exact Z.
Qed.

Lemma ZINV_dequeue st h g Zs : ZINV st Zs -> ZINV (dequeue h g st) Zs.
Proof. apply ZINV_sbl. apply sbl_dequeue. Qed.

Lemma ZINV_queue st h g Zs : ZINV st Zs -> ZINV (queue_st h g st) Zs.
Proof. apply ZINV_sbl. apply sbl_queue. Qed.

Lemma ZINV_grp_del st g p Zs : ZINV st Zs -> hosts st p g -> ZINV (grp_del st g p) (g :: Zs).
Proof.
  intros Z HB q b H. change (get_meta_rec (grp_del st g p) q) with (get_meta_rec st q) in H.
  destruct (Z q b H) as [Hq|HI]; [| right; right; exact HI].
  destruct (aptr_eqb_spec' b p).
  - subst. right. left. destruct Hq as [ai Hq]. destruct HB as [ai' HB]. rewrite HB in Hq. congruence.
  - left. apply hosts_grp_del. split; [exact n| exact Hq].
Qed.

Lemma ZINV_fm st g Zs : ZINV st (g :: Zs) -> ZINV (fm_st st g) Zs.
Proof.
  intros Z. unfold fm_st. apply ZINV_queue.
  intros q b H. rewrite rec_put in H. destruct (aptr_eqb_spec' q g); [subst; cbn in H; discriminate|].
  destruct (Z q b H) as [Hq|[E|HI]]; [left; exact Hq| exfalso; exact (n (eq_sym E))| right; exact HI].
Qed.

Lemma ZINV_mono st Zs Zs' : ZINV st Zs -> incl Zs Zs' -> ZINV st Zs'.
Proof. intros Z HI q b H. destruct (Z q b H) as [Hq|Hin]; [left; exact Hq| right; exact (HI _ Hin)]. Qed.