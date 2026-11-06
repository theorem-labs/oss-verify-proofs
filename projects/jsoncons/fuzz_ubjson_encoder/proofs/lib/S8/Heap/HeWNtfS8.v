(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 MI_Pres4S8 MI_WFree2S8 MI_WNtf2S8 KStepS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMWNTF.
Context {RUNp : RunP}.

Lemma lists_ok_links st st' LS : lists_ok st LS -> (forall h, get_head st' h = get_head st h) ->
  (forall x, m_next (MR st' x) = m_next (MR st x) /\ m_prev (MR st' x) = m_prev (MR st x)) -> lists_ok st' LS.
Proof.
  intros LO HH HL. destruct LO as [L1 L2 L3 L4 L5]. constructor.
  - intros h. rewrite HH. apply L1.
  - intros h. specialize (L2 h). destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in L2 |- *.
    eapply linked_ext; [| | exact L2]; intros x _; apply HL.
  - exact L3.
  - exact L4.
  - intros m. destruct (HL m) as [E1 E2]. rewrite E1, E2. apply L5.
Qed.

Lemma nmeta_upd_present st m f : s_metas st !! m <> None -> nmeta (upd_meta m f st) = nmeta st.
Proof.
  intros H. unfold nmeta. rewrite s_metas_upd_meta. rewrite map_size_insert_Some; [reflexivity|].
  destruct (s_metas st !! m) as [r|] eqn:E; [eexists; reflexivity| congruence].
Qed.

Lemma nmeta_put_present st m r : s_metas st !! m <> None -> nmeta (put_meta m r st) = nmeta st.
Proof.
  intros H. unfold nmeta. rewrite s_metas_put_meta. rewrite map_size_insert_Some; [reflexivity|].
  destruct (s_metas st !! m) as [r'|] eqn:E; [eexists; reflexivity| congruence].
Qed.

Lemma present_of_next st m : m_next (MR st m) <> None -> s_metas st !! m <> None.
Proof. intros H E. apply H. unfold MR, get_meta_rec. rewrite E. reflexivity. Qed.

Lemma ngrp_del st b h : s_groups st !! b = Some h -> ngrp (del_group b st) = ngrp st - 1.
Proof.
  intros H. unfold ngrp. rewrite s_groups_del_group. rewrite map_size_delete_Some by (eexists; exact H).
  assert (0 < size (s_groups st))%nat.
  { destruct (size (s_groups st)) eqn:E; [|lia]. apply map_size_empty_iff in E. rewrite E in H. rewrite lookup_empty in H. discriminate. }
  lia.
Qed.

Lemma nmeta_queue st LS h g : lists_ok st LS -> s_metas st !! g <> None -> nmeta (queue_st h g st) = nmeta st.
Proof.
  intros LO Pg. unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|] eqn:Ha.
  - assert (Ain : In a (LS h)) by (pose proof (lo_head _ _ LO h) as E; rewrite Ha in E; destruct (LS h) as [|a' l]; [discriminate| injection E as ->; left; reflexivity]).
    assert (Pa : s_metas st !! a <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h a Ain)).
    set (st1 := upd_meta g _ st).
    assert (P1 : forall x, s_metas st !! x <> None -> s_metas st1 !! x <> None).
    { intros x Hx. unfold st1. rewrite lookup_metas_upd. destruct (aptr_eqb x g); [discriminate| exact Hx]. }
    assert (N1 : nmeta st1 = nmeta st) by (apply nmeta_upd_present; exact Pg).
    destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Hpv.
    + destruct (lists_prev_in _ _ LO h a Ain) as (y & Hy & Ey & _). unfold MR in Ey. rewrite Hpv in Ey. injection Ey as <-.
      assert (Ppv : s_metas st !! pv <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h pv Hy)).
      rewrite nmeta_upd_present; [rewrite nmeta_upd_present; [exact N1| apply P1; exact Ppv]|].
      rewrite lookup_metas_upd. destruct (aptr_eqb a pv); [discriminate| apply P1; exact Pa].
    + rewrite nmeta_upd_present; [exact N1| apply P1; exact Pa].
  - assert (E : forall s, nmeta (set_head h (Some g) s) = nmeta s) by (intros s; destruct h; reflexivity).
    rewrite E. apply nmeta_upd_present. exact Pg.
Qed.

Lemma nmeta_dequeue st LS h m : lists_ok st LS -> In m (LS h) -> nmeta (dequeue h m st) = nmeta st.
Proof.
  intros LO Hm. assert (Pm : s_metas st !! m <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h m Hm)).
  destruct (lists_next_in _ _ LO h m Hm) as (nx & Hnx & Enx & _). destruct (lists_prev_in _ _ LO h m Hm) as (pv & Hpv & Epv & _).
  assert (Pn : s_metas st !! nx <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h nx Hnx)).
  assert (Pp : s_metas st !! pv <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h pv Hpv)).
  assert (KEEP : forall s x f, s_metas s !! x <> None -> forall y, s_metas s !! y <> None -> s_metas (upd_meta x f s) !! y <> None).
  { intros s0 x f _ y Hy. rewrite lookup_metas_upd. destruct (aptr_eqb y x); [discriminate| exact Hy]. }
  assert (SH : forall s hh v, nmeta (set_head hh v s) = nmeta s /\ s_metas (set_head hh v s) = s_metas s) by (intros; destruct hh; split; reflexivity).
  unfold dequeue. fold (MR st m). rewrite Enx, Epv.
  destruct (negb (optr_eqb (Some nx) (Some m))).
  - set (s1 := upd_meta pv _ st). set (s2 := upd_meta nx _ s1).
    assert (N2 : nmeta s2 = nmeta st) by (unfold s2, s1; rewrite nmeta_upd_present by (apply KEEP; assumption); apply nmeta_upd_present; exact Pp).
    assert (P2 : s_metas s2 !! m <> None) by (unfold s2, s1; apply KEEP; [apply KEEP; assumption|]; apply KEEP; assumption).
    destruct (optr_eqb (get_head s2 h) (Some m)).
    + rewrite nmeta_upd_present by (rewrite (proj2 (SH _ _ _)); exact P2). rewrite (proj1 (SH _ _ _)). exact N2.
    + rewrite nmeta_upd_present by exact P2. exact N2.
  - rewrite nmeta_upd_present by (rewrite (proj2 (SH _ _ _)); exact Pm). rewrite (proj1 (SH _ _ _)). reflexivity.
Qed.

Lemma queue_keys_iff st LS h g : lists_ok st LS -> s_metas st !! g <> None ->
  forall x, s_metas (queue_st h g st) !! x <> None <-> s_metas st !! x <> None.
Proof.
  intros LO Pg x.
  assert (LIN : forall h' y, In y (LS h') -> s_metas st !! y <> None) by (intros h' y Hy; apply present_of_next; exact (lists_in_next_some _ _ LO h' y Hy)).
  split; [| intros H; apply queue_keys_mono; exact H].
  intros H. destruct (queue_keys h g st x H) as [H'|[->|[H'|(a & Ha & Hp)]]].
  - exact H'.
  - exact Pg.
  - rewrite (lo_head _ _ LO) in H'. destruct (LS h) as [|y r] eqn:EL; [discriminate|]. cbn in H'. injection H' as ->.
    apply (LIN h x). rewrite EL. left. reflexivity.
  - rewrite (lo_head _ _ LO) in Ha. destruct (LS h) as [|y r] eqn:EL; [discriminate|]. cbn in Ha. injection Ha as ->.
    destruct (lists_head_prev _ _ LO h a r EL) as [Hpa _]. rewrite Hp in Hpa. injection Hpa as ->.
    apply (LIN h (List.last r a)). rewrite EL. apply last_In.
Qed.

Lemma dequeue_keys_iff st LS h m : lists_ok st LS -> In m (LS h) ->
  forall x, s_metas (dequeue h m st) !! x <> None <-> s_metas st !! x <> None.
Proof.
  intros LO Hm x.
  assert (Pm : s_metas st !! m <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO h m Hm)).
  split; [| intros H; apply dequeue_keys_mono; exact H].
  intros H. destruct (dequeue_keys h m st x H) as [H'|[->|[H'|H']]]; [exact H'| exact Pm| |].
  - destruct (lists_prev_in _ _ LO h m Hm) as (y & Hy & Ey & _). fold (MR st m) in H'. rewrite H' in Ey. injection Ey as <-.
    apply present_of_next. exact (lists_in_next_some _ _ LO h x Hy).
  - destruct (lists_next_in _ _ LO h m Hm) as (y & Hy & Ey & _). fold (MR st m) in H'. rewrite H' in Ey. injection Ey as <-.
    apply present_of_next. exact (lists_in_next_some _ _ LO h x Hy).
Qed.

Record CTXM (a b : mstate) : Prop := mkCTXM {
  cm_amc : c_avail_meta_count (s_ctx b) = c_avail_meta_count (s_ctx a);
  cm_amac : c_avail_meta_area_count (s_ctx b) = c_avail_meta_area_count (s_ctx a);
  cm_shift : c_meta_alloc_shift (s_ctx b) = c_meta_alloc_shift (s_ctx a);
  cm_brk : c_brk (s_ctx b) = c_brk (s_ctx a);
  cm_areas : s_areas b = s_areas a
}.
Lemma ctxm_refl a : CTXM a a. Proof. constructor; reflexivity. Qed.
Lemma ctxm_trans a b c : CTXM a b -> CTXM b c -> CTXM a c.
Proof. intros [] []; constructor; congruence. Qed.
Lemma ctxm_cbh a b : ctx_but_heads (s_ctx a) (s_ctx b) -> s_areas b = s_areas a -> CTXM a b.
Proof. intros C E. constructor; try apply C; exact E. Qed.

Section CASCADE.
Variables (st0 : mstate) (L0 : mled) (BL0 : list blk) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVC x0 st0 L0 BL0 LS0.

Record ABOVE (st : mstate) (LS : lhead -> list aptr) (sc : Z) : Prop := mkAB {
  ab_hosts : forall b m, hosts st0 b m -> sc <= m_sizeclass (MR st0 m) -> hosts st b m /\ MR st m = MR st0 m;
  ab_active : forall sc', sc <= sc' -> active st sc' = active st0 sc' /\ LS (LActive sc') = LS0 (LActive sc');
  ab_usage : forall sc', sc <= sc' -> usage st sc' = usage st0 sc';
  ab_bounces : c_bounces (s_ctx st) = c_bounces (s_ctx st0);
  ab_slots : forall s p j, s_slots st0 !! s = Some (p, j) -> sc <= m_sizeclass (MR st0 p) -> s_slots st !! s = Some (p, j)
}.

Record CASC (st : mstate) (LS : lhead -> list aptr) (ZB : list aptr) (sc : Z) : Prop := mkCA {
  ca_lists : lists_ok st LS;
  ca_free : LS LFree = LS0 LFree;
  ca_above : ABOVE st LS sc;
  ca_hosts : forall b m, hosts st b m -> hosts st0 b m /\ GEOM (MR st m) = GEOM (MR st0 m) /\ fmask (MR st m) = fmask (MR st0 m);
  ca_regions : s_regions st = s_regions st0;
  ca_nmeta : nmeta st = nmeta st0;
  ca_ngrp : ngrp st + Z.of_nat (length ZB) = ngrp st0;
  ca_zomb : forall z, In z ZB -> s_metas st !! z <> None /\ (forall h, ~ In z (LS h)) /\ ~ live_group st z;
  ca_znd : NoDup ZB;
  ca_ctx : CTXM st0 st;
  ca_slots : forall s p j, s_slots st !! s = Some (p, j) -> s_slots st0 !! s = Some (p, j);
  ca_actok : forall sc' m, In m (LS (LActive sc')) -> live_group st m /\ m_sizeclass (MR st m) = sc';
  ca_freeok : forall m, In m (LS LFree) -> ~ live_group st m;
  ca_keys : forall m, s_metas st !! m <> None <-> s_metas st0 !! m <> None;
  ca_back : forall b m, hosts st0 b m -> hosts st b m \/ In m ZB
}.

Record NPOST (ZB : list aptr) (st' : mstate) (mi : mapinfo) : Prop := mkNP {
  np_lists : exists LS', lists_ok st' LS'
      /\ Z.of_nat (length (LS' LFree)) + ngrp st' + Z.of_nat (length ZB) = Z.of_nat (length (LS0 LFree)) + ngrp st0
      /\ (forall z, In z ZB -> forall h, ~ In z (LS' h))
      /\ (forall m, In m (LS0 LFree) -> In m (LS' LFree))
      /\ (forall b m, hosts st0 b m -> hosts st' b m \/ In m (LS' LFree) \/ In m ZB);
  np_keys : forall m, s_metas st' !! m <> None <-> s_metas st0 !! m <> None;
  np_zomb : forall z, In z ZB -> s_metas st' !! z <> None /\ ~ live_group st' z;
  np_znd : NoDup ZB;
  np_hosts : forall b m, hosts st' b m -> hosts st0 b m /\ GEOM (MR st' m) = GEOM (MR st0 m);
  np_empty : exists so : option aptr, forall b m, hosts st' b m -> gempty st' m ->
      gempty st0 m \/ (so = Some m /\ m_next (MR st0 m) = Some m /\ m_maplen (MR st0 m) <> 0 /\ 7 <= m_sizeclass (MR st0 m) <= 38);
  np_regions : s_regions st' = s_regions st0;
  np_mi : match mi with
          | Some (base, len) => snd base = 0 /\ exists r, s_regions st0 !! fst base = Some r /\ r_kind r = RKGroup /\ len = mmap_len (r_len r) /\ 0 < len
          | None => True
          end;
  np_nmeta : nmeta st' = nmeta st0;
  np_ctx : CTXM st0 st';
  np_slots : forall s p j, s_slots st' !! s = Some (p, j) -> s_slots st0 !! s = Some (p, j)
}.

Lemma NPOST_fm ZB g st3 mi : NPOST (g :: ZB) st3 mi -> NPOST ZB (fm_st st3 g) mi.
Proof.
  intros [(LS3 & LO3 & CNT3 & ZU3 & FL3 & BK3) KY3 Z3 ND3 H3 E3 R3 MI3 N3 C3 S3].
  destruct (Z3 g (or_introl eq_refl)) as [Pg NLg].
  pose proof (ZU3 g (or_introl eq_refl)) as Ug.
  apply NoDup_cons in ND3 as [Ng ND3']. assert (Ng' : ~ In g ZB) by (intros X; apply Ng; apply list_elem_of_In; exact X).
  set (sp := put_meta g meta0 st3).
  assert (LOp : lists_ok sp LS3).
  { apply (lists_ok_links st3 sp LS3 LO3); [intros h; destruct h; reflexivity|].
    intros x. unfold sp, MR. rewrite get_meta_rec_put. destruct (aptr_eqb_spec x g) as [->|NE]; [|split; reflexivity].
    pose proof (lo_link _ _ LO3 g) as [Lk1 Lk2].
    assert (Hn : m_next (get_meta_rec st3 g) = None).
    { destruct (m_next (get_meta_rec st3 g)) eqn:E; [|reflexivity]. exfalso.
      assert (IN : exists h, In g (LS3 h)) by (apply Lk1; unfold MR; rewrite E; discriminate). destruct IN as [h Hh]. exact (Ug h Hh). }
    split; [exact (eq_sym Hn)| symmetry; apply Lk2; exact Hn]. }
  pose proof (lists_queue sp LS3 LOp LFree g ltac:(unfold MR, sp; rewrite get_meta_rec_put_same; reflexivity)) as LO4.
  assert (FR : forall s, s_groups (fm_st s g) = s_groups s /\ s_slots (fm_st s g) = s_slots s /\ s_regions (fm_st s g) = s_regions s
                         /\ ctx_but_heads (s_ctx s) (s_ctx (fm_st s g)) /\ s_areas (fm_st s g) = s_areas s).
  { intros s. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s)) as (Q1 & _ & _ & Q4 & Q5 & Q6 & _ & _ & _ & Q10).
    change (s_ctx (put_meta g meta0 s)) with (s_ctx s) in Q10.
    split; [rewrite Q5; reflexivity|]. split; [rewrite Q6; reflexivity|]. split; [rewrite Q1; reflexivity|].
    split; [exact Q10| rewrite Q4; reflexivity]. }
  destruct (FR st3) as (FG & FS & FRg & FC & FA).
  assert (DATA : forall x, x <> g -> data_of (MR (fm_st st3 g) x) = data_of (MR st3 x)).
  { intros x NE. unfold fm_st. rewrite (queue_data LFree g sp x). unfold sp, MR. rewrite get_meta_rec_put_other by exact NE. reflexivity. }
  assert (HOSTS : forall b m, hosts (fm_st st3 g) b m <-> hosts st3 b m) by (intros; apply hosts_ext; exact FG).
  assert (NE_live : forall b m, hosts st3 b m -> m <> g) by (intros b m H ->; apply NLg; exists b; exact H).
  constructor.
  - exists (fupd LS3 LFree (LS3 LFree ++ [g])). split; [exact LO4|]. split; [| split; [| split]].
    + rewrite fupd_eq, length_app. cbn [length]. unfold ngrp in *. rewrite FG. cbn [length] in CNT3. lia.
    + intros z Hz h Hzh. destruct (decide (h = LFree)) as [->|NEh].
      * rewrite fupd_eq in Hzh. apply in_app_iff in Hzh as [Hzh|[<-|[]]]; [exact (ZU3 z (or_intror Hz) LFree Hzh)| exact (Ng' Hz)].
      * rewrite fupd_ne in Hzh by exact NEh. exact (ZU3 z (or_intror Hz) h Hzh).
    + intros m Hm. rewrite fupd_eq. apply in_app_iff. left. exact (FL3 m Hm).
    + intros b m Hb. rewrite fupd_eq. destruct (BK3 b m Hb) as [H|[H|[<-|H]]].
      * left. apply HOSTS. exact H.
      * right. left. apply in_app_iff. left. exact H.
      * right. left. apply in_app_iff. right. left. reflexivity.
      * right. right. exact H.
  - intros m. rewrite <- (KY3 m). unfold fm_st. fold sp. rewrite (queue_keys_iff sp LS3 LFree g LOp ltac:(unfold sp; rewrite s_metas_put_meta, lookup_insert_eq; discriminate) m).
    unfold sp. rewrite s_metas_put_meta. destruct (decide (m = g)) as [->|NE]; [rewrite lookup_insert_eq; split; [intros _; exact Pg| discriminate]|].
    rewrite lookup_insert_ne by congruence. tauto.
  - intros z Hz. destruct (Z3 z (or_intror Hz)) as [Pz NLz]. split.
    + unfold fm_st. apply (queue_keys_mono LFree g sp z). unfold sp. rewrite s_metas_put_meta. rewrite lookup_insert_ne; [exact Pz|].
      intros ->. exact (Ng' Hz).
    + intros [b Hb]. apply NLz. exists b. apply HOSTS. exact Hb.
  - exact ND3'.
  - intros b m Hb. apply HOSTS in Hb. destruct (H3 b m Hb) as [H0 G0]. split; [exact H0|].
    rewrite (GEOM_data _ _ (DATA m (NE_live b m Hb))). exact G0.
  - destruct E3 as [so E3]. exists so. intros b m Hb He. apply HOSTS in Hb.
    apply (E3 b m Hb). apply (proj1 (gempty_data st3 (fm_st st3 g) m (DATA m (NE_live b m Hb)))) in He. exact He.
  - rewrite FRg. exact R3.
  - exact MI3.
  - unfold fm_st. rewrite <- N3. fold sp. rewrite (nmeta_queue sp LS3 LFree g LOp).
    + unfold sp. apply nmeta_put_present. exact Pg.
    + unfold sp. rewrite s_metas_put_meta, lookup_insert_eq. discriminate.
  - apply (ctxm_trans _ st3); [exact C3| apply ctxm_cbh; [exact FC| exact FA]].
  - intros s p j Hs. rewrite FS in Hs. exact (S3 s p j Hs).
Qed.

Definition NTFW (T : Type) (w : ev -> Z) (f : nat) : Prop :=
  forall st LS ZB g bg i (k : mstate -> mapinfo -> M T) bail c n Q,
  CASC st LS ZB (m_sizeclass (MR st0 g)) ->
  hosts st0 bg g -> MR st g = MR st0 g -> hosts st bg g ->
  0 <= i <= m_last_idx (MR st0 g) -> Z.testbit (fmask (MR st0 g)) i = false ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st0 g) <= Z.of_nat f ->
  (forall st' mi, NPOST ZB st' mi -> apw w (k st' mi) c n Q) ->
  apw w (nontrivial_free dec_slots f st g i k bail) c n Q.

Lemma g0_facts bg g : hosts st0 bg g ->
  exists ai, s_groups st0 !! bg = Some (mkGhdr (Some g) ai) /\ group_ok x0 st0 LS0 g bg ai.
Proof.
  destruct INV0 as (IR & IA & IM & IL & IG & IS). intros [ai H]. exists ai. split; [exact H| exact (ig_ok _ _ _ IG _ _ _ H)].
Qed.

Lemma npost_keep st LS ZB g bg i (stq : mstate) (LSq : lhead -> list aptr) :
  CASC st LS ZB (m_sizeclass (MR st0 g)) -> hosts st0 bg g -> MR st g = MR st0 g -> hosts st bg g ->
  0 <= i <= m_last_idx (MR st0 g) -> Z.testbit (fmask (MR st0 g)) i = false ->
  (Z.lor (fmask (MR st0 g)) (bit i) = mask_upto (m_last_idx (MR st0 g)) -> okay_to_free st g = false) ->
  lists_ok stq LSq -> LSq LFree = LS LFree -> (forall z, In z ZB -> forall h, ~ In z (LSq h)) ->
  s_groups stq = s_groups st -> s_slots stq = s_slots st -> s_regions stq = s_regions st ->
  (forall x, data_of (MR stq x) = data_of (MR st x)) -> nmeta stq = nmeta st -> CTXM st stq ->
  (forall x, s_metas stq !! x <> None <-> s_metas st !! x <> None) ->
  NPOST ZB (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) None.
Proof.
  intros CA H0 EG Hs Hi Hbit OK LOq FRq ZUq Gq Sq Rq Dq Nq Cq Pq'.
  assert (Pq : forall x, s_metas st !! x <> None -> s_metas stq !! x <> None) by (intros x; apply (proj2 (Pq' x))).
  destruct CA as [LO FR AB HO RG NM NG ZO ZN CT SL AO FO KY BK].
  set (st' := upd_meta g _ stq).
  assert (G' : s_groups st' = s_groups st) by (unfold st'; rewrite s_groups_upd_meta; exact Gq).
  assert (HOST : forall b m, hosts st' b m <-> hosts st b m) by (intros; apply hosts_ext; exact G').
  assert (Hm0 : m_mem (MR st0 g) = Some bg) by (destruct INV0 as (_ & _ & IM & _ & _ & _); eapply hosts_mem; [exact IM| exact H0]).
  assert (Pg : s_metas stq !! g <> None).
  { apply Pq. intros E. assert (Hm' : m_mem (MR st g) = Some bg) by (rewrite EG; exact Hm0).
    unfold MR, get_meta_rec in Hm'. rewrite E in Hm'. discriminate. }
  assert (D' : forall x, x <> g -> data_of (MR st' x) = data_of (MR st x)).
  { intros x NE. unfold st', MR. rewrite get_meta_rec_upd_other by exact NE. apply Dq. }
  assert (Rg : MR st' g = m_set_freed (Z.lor (m_freed (MR stq g)) (bit i)) (MR stq g)) by (unfold st', MR; rewrite get_meta_rec_upd_same; reflexivity).
  assert (Dg : data_of (MR stq g) = data_of (MR st0 g)) by (rewrite Dq, EG; reflexivity).
  constructor.
  - exists LSq. split.
    + apply (lists_ok_links stq st' LSq LOq); [intros h; unfold st'; apply get_head_upd_meta|].
      intros x. unfold st', MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x g) as [->|NE]; split; reflexivity.
    + split; [| split; [exact ZUq| split; [intros m Hm; rewrite FRq, FR; exact Hm|]]].
      * rewrite FRq, FR. unfold ngrp. rewrite G'. unfold ngrp in NG. lia.
      * intros b m Hb. destruct (BK b m Hb) as [H|H]; [left; apply HOST; exact H| right; right; exact H].
  - intros m. unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE].
    + split; [intros _; apply (proj1 (KY g)); exact (proj1 (Pq' g) Pg)| intros _; discriminate].
    + rewrite (Pq' m). exact (KY m).
  - intros z Hz. destruct (ZO z Hz) as (Pz & _ & NLz). split.
    + unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb z g); [discriminate| apply Pq; exact Pz].
    + intros [b Hb]. apply NLz. exists b. apply HOST. exact Hb.
  - exact ZN.
  - intros b m Hb. apply HOST in Hb. destruct (HO b m Hb) as (H0m & Gm & _). split; [exact H0m|].
    destruct (aptr_eqb_spec m g) as [->|NE].
    + rewrite Rg, GEOM_set_freed, (GEOM_data _ _ Dg). reflexivity.
    + rewrite (GEOM_data _ _ (D' m NE)). exact Gm.
  - exists (Some g). intros b m Hb He. apply HOST in Hb. destruct (HO b m Hb) as (H0m & Gm & Fm).
    destruct (aptr_eqb_spec m g) as [->|NE].
    + right. unfold gempty in He. rewrite Rg, fmask_set_freed_or in He.
      assert (Lq : m_last_idx (m_set_freed (Z.lor (m_freed (MR stq g)) (bit i)) (MR stq g)) = m_last_idx (MR st0 g))
        by (cbn; apply data_of_eq in Dg; tauto).
      rewrite Lq, (fmask_data _ _ Dg) in He.
      assert (OKf : okay_to_free st g = false) by (apply OK; exact He).
      destruct (g0_facts bg g H0) as (ai & _ & GO). pose proof (g_freeable _ _ _ _ _ _ GO) as Fr.
      rewrite <- EG in Fr. destruct (otf_false st g Fr OKf) as (_ & A2 & A3 & A4). rewrite EG in A2, A3, A4. auto.
    + left. unfold gempty in He |- *. rewrite (fmask_data _ _ (D' m NE)) in He.
      apply GEOM_eq in Gm as (_ & Lm & _). pose proof (D' m NE) as Dm. apply data_of_eq in Dm as (_ & _ & _ & Lm' & _).
      rewrite Lm' in He. rewrite Fm, Lm in He. exact He.
  - unfold st'. rewrite s_regions_upd_meta, Rq. exact RG.
  - exact I.
  - unfold st'. rewrite nmeta_upd_present by exact Pg. rewrite Nq. exact NM.
  - apply (ctxm_trans _ st); [exact CT|]. apply (ctxm_trans _ stq); [exact Cq|]. constructor; reflexivity.
  - intros s0 p j Hs0. unfold st' in Hs0. rewrite s_slots_upd_meta, Sq in Hs0. exact (SL s0 p j Hs0).
Qed.

Record FGPRE (stx : mstate) (LSx : lhead -> list aptr) (ZB : list aptr) (g bg : aptr) : Prop := mkFGP {
  fp_lists : lists_ok stx LSx;
  fp_free : LSx LFree = LS0 LFree;
  fp_gun : forall h, ~ In g (LSx h);
  fp_above : ABOVE stx LSx (m_sizeclass (MR st0 g) + 1);
  fp_hosts : forall b m, hosts stx b m -> hosts st0 b m /\ GEOM (MR stx m) = GEOM (MR st0 m) /\ fmask (MR stx m) = fmask (MR st0 m);
  fp_g : hosts stx bg g /\ hosts st0 bg g /\ data_of (MR stx g) = data_of (MR st0 g);
  fp_regions : s_regions stx = s_regions st0;
  fp_nmeta : nmeta stx = nmeta st0;
  fp_ngrp : ngrp stx + Z.of_nat (length ZB) = ngrp st0;
  fp_zomb : forall z, In z ZB -> s_metas stx !! z <> None /\ (forall h, ~ In z (LSx h)) /\ ~ live_group stx z;
  fp_znd : NoDup ZB;
  fp_ctx : CTXM st0 stx;
  fp_slots : forall s p j, s_slots stx !! s = Some (p, j) -> s_slots st0 !! s = Some (p, j);
  fp_actok : forall sc' m, In m (LSx (LActive sc')) -> live_group stx m /\ m_sizeclass (MR stx m) = sc';
  fp_freeok : forall m, In m (LSx LFree) -> ~ live_group stx m;
  fp_keys : forall m, s_metas stx !! m <> None <-> s_metas st0 !! m <> None;
  fp_back : forall b m, hosts st0 b m -> hosts stx b m \/ In m ZB
}.

Lemma slot_key_false p stride cnt : 0 < stride ->
  ((fst p =? fst p)%N && (0 <=? snd p - snd p - UNIT) && ((snd p - snd p - UNIT) mod stride =? 0) && ((snd p - snd p - UNIT) / stride <? cnt)) = false.
Proof. intros _. replace (snd p - snd p - UNIT) with (-16) by (unfold UNIT; lia). rewrite N.eqb_refl. reflexivity. Qed.

Lemma above_weaken st LS sc sc' : ABOVE st LS sc -> sc <= sc' -> ABOVE st LS sc'.
Proof.
  intros [A1 A2 A3 A4 A5] Hle. constructor; auto.
  - intros b m Hb Hc. apply A1; [exact Hb| lia].
  - intros s0 Hc. apply A2. lia.
  - intros s0 Hc. apply A3. lia.
  - intros s0 p j H Hc. apply (A5 s0 p j H). lia.
Qed.

Lemma fgpre_unlisted st LS ZB g bg : CASC st LS ZB (m_sizeclass (MR st0 g)) -> hosts st0 bg g -> MR st g = MR st0 g -> hosts st bg g ->
  (forall h, ~ In g (LS h)) -> FGPRE st LS ZB g bg.
Proof.
  intros [LO FR AB HO RG NM NG ZO ZN CT SL AO FO KY BK] H0 EG Hs GU. constructor; auto.
  - apply (above_weaken _ _ _ _ AB). lia.
  - split; [exact Hs|]. split; [exact H0|]. rewrite EG. reflexivity.
Qed.

Lemma fgpre_dequeue st LS ZB g bg l1 l2 : CASC st LS ZB (m_sizeclass (MR st0 g)) -> hosts st0 bg g -> MR st g = MR st0 g -> hosts st bg g ->
  LS (LActive (m_sizeclass (MR st0 g))) = l1 ++ g :: l2 ->
  FGPRE (dequeue (LActive (m_sizeclass (MR st0 g))) g st) (fupd LS (LActive (m_sizeclass (MR st0 g))) (l1 ++ l2)) ZB g bg.
Proof.
  intros [LO FR AB HO RG NM NG ZO ZN CT SL AO FO KY BK] H0 EG Hs E.
  set (sc := m_sizeclass (MR st0 g)) in *.
  set (std := dequeue (LActive sc) g st).
  pose proof (lists_dequeue st LS LO (LActive sc) g l1 l2 E) as LOd.
  destruct (dequeue_frame (LActive sc) g st) as (D1 & _ & _ & D4 & D5 & D6 & _ & _ & _ & D10). fold std in D1, D4, D5, D6, D10.
  assert (Gin : In g (LS (LActive sc))) by (rewrite E; apply in_app_iff; right; left; reflexivity).
  pose proof (lo_nodup _ _ LO (LActive sc)) as ND. rewrite E in ND. destruct (NoDup_In_split _ _ _ ND) as [N1 N2].
  assert (HOd : forall b m, hosts std b m <-> hosts st b m) by (intros; apply hosts_ext; exact D5).
  assert (Dd : forall x, data_of (MR std x) = data_of (MR st x)) by (intros x; apply dequeue_data).

  assert (NB : forall x, sc < m_sizeclass (MR st0 x) -> (exists b, hosts st0 b x) -> MR std x = MR st x).
  { intros x Hx [b Hb]. unfold MR, get_meta_rec. f_equal. apply dequeue_metas_other.
    - intros ->. lia.
    - intros Ep. destruct (lists_prev_in st LS LO _ g Gin) as (y & Hy & Ey & _). fold (MR st g) in Ep. rewrite Ep in Ey. injection Ey as <-.
      destruct (AO _ x Hy) as [_ Ec]. destruct (ab_hosts _ _ _ AB b x Hb ltac:(lia)) as [_ Em]. rewrite Em in Ec. lia.
    - intros En. destruct (lists_next_in st LS LO _ g Gin) as (y & Hy & Ey & _). fold (MR st g) in En. rewrite En in Ey. injection Ey as <-.
      destruct (AO _ x Hy) as [_ Ec]. destruct (ab_hosts _ _ _ AB b x Hb ltac:(lia)) as [_ Em]. rewrite Em in Ec. lia. }
  constructor.
  - exact LOd.
  - rewrite fupd_ne by discriminate. exact FR.
  - intros h Hh. destruct (decide (h = LActive sc)) as [->|NEh].
    + rewrite fupd_eq in Hh. apply in_app_iff in Hh as [Hh|Hh]; [exact (N1 Hh)| exact (N2 Hh)].
    + rewrite fupd_ne in Hh by exact NEh. exact (NEh (lo_disj _ _ LO h (LActive sc) g Hh Gin)).
  - destruct AB as [A1 A2 A3 A4 A5]. constructor.
    + intros b m Hb Hc. destruct (A1 b m Hb ltac:(lia)) as [Hbs Em]. split; [apply HOd; exact Hbs|].
      rewrite (NB m ltac:(lia) (ex_intro _ b Hb)). exact Em.
    + intros sc' Hc. destruct (A2 sc' ltac:(lia)) as [Ea El]. split.
      * change (active std sc') with (get_head std (LActive sc')). rewrite dequeue_head.
        destruct (decide (LActive sc' = LActive sc)) as [Eq|NEq]; [injection Eq; lia| exact Ea].
      * rewrite fupd_ne by (intros Eq; injection Eq; lia). exact El.
    + intros sc' Hc. unfold usage. rewrite (cb_usage _ _ D10). apply A3. lia.
    + rewrite (cb_bounces _ _ D10). exact A4.
    + intros s0 p j H Hc. rewrite D6. exact (A5 s0 p j H ltac:(lia)).
  - intros b m Hb. apply HOd in Hb. destruct (HO b m Hb) as (H0' & G' & F'). split; [exact H0'|].
    rewrite (GEOM_data _ _ (Dd m)), (fmask_data _ _ (Dd m)). split; assumption.
  - split; [apply HOd; exact Hs|]. split; [exact H0|]. rewrite Dd, EG. reflexivity.
  - rewrite D1. exact RG.
  - rewrite (nmeta_dequeue st LS (LActive sc) g LO Gin). exact NM.
  - unfold ngrp. rewrite D5. exact NG.
  - intros z Hz. destruct (ZO z Hz) as (P & U & N). split; [apply dequeue_keys_mono; exact P|]. split.
    + intros h Hh. destruct (decide (h = LActive sc)) as [->|NEh].
      * rewrite fupd_eq in Hh. apply (U (LActive sc)). rewrite E. apply in_app_iff in Hh as [Hh|Hh]; apply in_app_iff; [left; exact Hh| right; right; exact Hh].
      * rewrite fupd_ne in Hh by exact NEh. exact (U h Hh).
    + intros [b Hb]. apply N. exists b. apply HOd. exact Hb.
  - exact ZN.
  - apply (ctxm_trans _ st); [exact CT| apply ctxm_cbh; [exact D10| exact D4]].
  - intros s0 p j H. rewrite D6 in H. exact (SL s0 p j H).
  - intros sc' m Hm. assert (Hm' : In m (LS (LActive sc'))).
    { destruct (decide (LActive sc' = LActive sc)) as [Eq|NEq].
      - rewrite Eq in Hm |- *. rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm as [Hm|Hm]; apply in_app_iff; [left; exact Hm| right; right; exact Hm].
      - rewrite fupd_ne in Hm by exact NEq. exact Hm. }
    destruct (AO sc' m Hm') as ([b Hb] & Ec). split; [exists b; apply HOd; exact Hb|].
    pose proof (Dd m) as Dm. apply data_of_eq in Dm as (_ & _ & _ & _ & _ & Es & _). rewrite Es. exact Ec.
  - intros m Hm [b Hb]. rewrite fupd_ne in Hm by discriminate. apply (FO m Hm). exists b. apply HOd. exact Hb.
  - intros m. rewrite <- (KY m). unfold std. apply (dequeue_keys_iff st LS _ g LO Gin).
  - intros b m Hb. destruct (BK b m Hb) as [H|H]; [left; apply HOd; exact H| right; exact H].
Qed.

Lemma fgpre_activate stx LSx ZB g bg a act : FGPRE stx LSx ZB g bg ->
  In a (LSx (LActive (m_sizeclass (MR st0 g)))) -> m_avail (MR stx a) = 0 ->
  FGPRE (upd_meta a (fun r => m_set_avail (Z.land (m_freed (MR stx a)) act) (m_set_freed (Z.ldiff (m_freed (MR stx a)) act) r)) stx) LSx ZB g bg.
Proof.
  intros [LO FR GU AB HO (Hgx & Hg0 & Dg) RG NM NG ZO ZN CT SL AO FO KY BK] Ha HA0.
  set (sc := m_sizeclass (MR st0 g)) in *.
  set (sta := upd_meta a _ stx).
  assert (MRa : MR sta a = m_set_avail (Z.land (m_freed (MR stx a)) act) (m_set_freed (Z.ldiff (m_freed (MR stx a)) act) (MR stx a)))
    by (unfold sta, MR; rewrite get_meta_rec_upd_same; reflexivity).
  assert (MRo : forall x, x <> a -> MR sta x = MR stx x) by (intros x NE; unfold sta, MR; rewrite get_meta_rec_upd_other by exact NE; reflexivity).
  assert (Ga : s_groups sta = s_groups stx) by reflexivity.
  assert (HOa : forall b m, hosts sta b m <-> hosts stx b m) by (intros; apply hosts_ext; exact Ga).
  assert (Gna : g <> a) by (intros ->; exact (GU _ Ha)).
  destruct (AO sc a Ha) as (_ & Eca).
  assert (Pa : s_metas stx !! a <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO _ a Ha)).
  constructor.
  - apply (lists_ok_links stx sta LSx LO); [intros h; unfold sta; apply get_head_upd_meta|].
    intros x. destruct (aptr_eqb_spec x a) as [->|NE]; [rewrite MRa; split; reflexivity| rewrite (MRo x NE); split; reflexivity].
  - exact FR.
  - exact GU.
  - destruct AB as [A1 A2 A3 A4 A5]. constructor; auto.
    intros b m Hb Hc. destruct (A1 b m Hb Hc) as [Hbs Em]. split; [apply HOa; exact Hbs|].
    rewrite MRo; [exact Em|]. intros ->. rewrite Em in Eca. lia.
  - intros b m Hb. apply HOa in Hb. destruct (HO b m Hb) as (H0' & G' & F'). split; [exact H0'|].
    destruct (aptr_eqb_spec m a) as [->|NE].
    + rewrite MRa, GEOM_set_avail, GEOM_set_freed, fmask_activate by exact HA0. split; assumption.
    + rewrite (MRo m NE). split; assumption.
  - split; [apply HOa; exact Hgx|]. split; [exact Hg0|]. rewrite (MRo g Gna). exact Dg.
  - exact RG.
  - unfold sta. rewrite nmeta_upd_present by exact Pa. exact NM.
  - exact NG.
  - intros z Hz. destruct (ZO z Hz) as (P & U & N). split; [unfold sta; rewrite lookup_metas_upd; destruct (aptr_eqb z a); [discriminate| exact P]|].
    split; [exact U|]. intros [b Hb]. apply N. exists b. apply HOa. exact Hb.
  - exact ZN.
  - apply (ctxm_trans _ stx); [exact CT| constructor; reflexivity].
  - exact SL.
  - intros sc' m Hm. destruct (AO sc' m Hm) as ([b Hb] & Ec). split; [exists b; apply HOa; exact Hb|].
    destruct (aptr_eqb_spec m a) as [->|NE]; [rewrite MRa; exact Ec| rewrite (MRo m NE); exact Ec].
  - intros m Hm [b Hb]. apply (FO m Hm). exists b. apply HOa. exact Hb.
  - intros m. unfold sta. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m a) as [->|NE]; [| exact (KY m)].
    split; [intros _; apply (proj1 (KY a)); exact Pa| intros _; discriminate].
  - intros b m Hb. destruct (BK b m Hb) as [H|H]; [left; apply HOa; exact H| right; exact H].
Qed.

Lemma fg_walk T w f' : NTFW T w f' ->
  forall stx LSx ZB g bg (k : mstate -> mapinfo -> M T) bail c n Q,
  FGPRE stx LSx ZB g bg -> 48 - m_sizeclass (MR st0 g) <= Z.of_nat f' ->
  (forall st' mi, NPOST ZB st' mi -> apw w (k st' mi) c n Q) ->
  apw w (free_group T dec_slots (nontrivial_free dec_slots f') stx g k bail) c n Q.
Proof.
  intros IH stx LSx ZB g bg k bail c n Q FP Hf2 CONT.
  pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  destruct FP as [LO FR GU AB HO (Hgx & Hg0 & Dg) RG NM NG ZO ZN CT SL AO FO KY BK].
  destruct (g0_facts bg g Hg0) as (ai & Hg0' & GO).
  pose proof (proj1 (data_of_eq (MR stx g) (MR st0 g)) Dg) as (Emem & Eav & Efr & Eli & Efa & Esc & Eml).
  pose proof (hosts_mem x0 st0 LS0 IM bg g Hg0) as Hmem.
  assert (STR : get_stride (MR stx g) = get_stride (MR st0 g)) by (apply get_stride_data; exact Dg).
  assert (SPOS : 0 < get_stride (MR st0 g)).
  { assert (H := stride_ge x0 st0 LS0 IG bg g Hg0). unfold UNIT in H. lia. }
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold free_group. fold (MR stx g). rewrite Emem, Hmem.
  set (sc := m_sizeclass (MR stx g)).
  set (cnt := m_last_idx (MR stx g) + 1).
  set (st1 := if sc <? 48 then set_usage sc (usage stx sc - cnt) stx else stx).
  assert (F1 : s_metas st1 = s_metas stx /\ s_groups st1 = s_groups stx /\ s_slots st1 = s_slots stx /\ s_regions st1 = s_regions stx
               /\ (forall h, get_head st1 h = get_head stx h) /\ CTXM stx st1 /\ c_bounces (s_ctx st1) = c_bounces (s_ctx stx)
               /\ (forall sc', sc' <> sc -> usage st1 sc' = usage stx sc')).
  { unfold st1. destruct (sc <? 48).
    - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros h; destruct h; reflexivity|]. split; [constructor; reflexivity|]. split; [reflexivity|].
      intros sc' NE. unfold usage, set_usage, upd_ctx. cbn. rewrite lookup_insert_ne by congruence. reflexivity.
    - repeat split; try reflexivity; try (constructor; reflexivity). }
  destruct F1 as (M1 & G1 & SL1 & R1 & H1 & C1 & B1 & U1).
  set (stk := del_slots bg (get_stride (MR stx g)) cnt (del_group bg st1)).
  assert (Mk : s_metas stk = s_metas stx) by (unfold stk; rewrite s_metas_del_slots, s_metas_del_group; exact M1).
  assert (MRk : forall x, MR stk x = MR stx x) by (intros x; unfold MR, get_meta_rec; rewrite Mk; reflexivity).
  assert (Gk : s_groups stk = delete bg (s_groups stx)) by (unfold stk; rewrite s_groups_del_slots, s_groups_del_group, G1; reflexivity).
  assert (HOk : forall b m, hosts stk b m <-> hosts stx b m /\ b <> bg).
  { intros b m. unfold hosts. rewrite Gk. split.
    - intros [a Ha]. destruct (aptr_eqb_spec b bg) as [->|NE]; [rewrite lookup_delete_eq in Ha; discriminate|].
      rewrite lookup_delete_ne in Ha by congruence. split; [exists a; exact Ha| exact NE].
    - intros ([a Ha] & NE). exists a. rewrite lookup_delete_ne by congruence. exact Ha. }
  assert (HDk : forall h, get_head stk h = get_head stx h) by (intros h; rewrite <- H1; destruct h; reflexivity).
  assert (Rk : s_regions stk = s_regions stx) by (unfold stk; cbn; exact R1).
  assert (SLk : forall s0, s_slots stk !! s0 = if (fst s0 =? fst bg)%N && (0 <=? snd s0 - snd bg - UNIT) && ((snd s0 - snd bg - UNIT) mod get_stride (MR stx g) =? 0)
                                               && ((snd s0 - snd bg - UNIT) / get_stride (MR stx g) <? cnt) then None else s_slots stx !! s0).
  { intros s0. unfold stk. rewrite lookup_del_slots by (unfold cnt; lia). rewrite s_slots_del_group, SL1. reflexivity. }
  assert (SLk' : forall s0 v, s_slots stk !! s0 = Some v -> s_slots stx !! s0 = Some v).
  { intros s0 v H. rewrite SLk in H. destruct (_ && _); [discriminate| exact H]. }
  assert (NGk : ngrp stk = ngrp stx - 1).
  { destruct Hgx as [a Ha]. rewrite <- (ngrp_del stx bg (mkGhdr (Some g) a) Ha). unfold ngrp. rewrite Gk. reflexivity. }
  assert (CTk : CTXM stx stk) by (apply (ctxm_trans _ st1); [exact C1| constructor; reflexivity]).
  assert (LOk : lists_ok stk LSx) by (apply (lists_ok_links stx stk LSx LO HDk); intros x; rewrite MRk; split; reflexivity).
  assert (Pg : s_metas stx !! g <> None) by (intros E; unfold MR, get_meta_rec in Emem; rewrite E in Emem; cbn in Emem; rewrite Hmem in Emem; discriminate).
  assert (NLk : ~ live_group stk g).
  { intros [b Hb]. apply HOk in Hb as [Hb NE]. apply NE. destruct (HO b g Hb) as (Hb0 & _).
    exact (hosts_inj x0 st0 LS0 IM b bg g Hb0 Hg0). }
  assert (GnZ : ~ In g ZB) by (intros Hz; destruct (ZO g Hz) as (_ & _ & NL); apply NL; exists bg; exact Hgx).
  destruct (Z.eqb_spec (m_maplen (MR stx g)) 0) as [ML0|ML0]; cbn [negb].
  -
    rewrite Eml in ML0. destruct (g_nest _ _ _ _ _ _ GO ML0) as (pm & ip & Hsl0 & Hreg & Hgend & Hcls & Hstr).
    fold (MR st0 pm) in *.
    destruct (is_valid _ _ _ IS _ _ _ Hsl0) as (LV & Hip & Ebg). destruct LV as [bpm Hpm0].
    assert (CLS : m_sizeclass (MR st0 g) + 1 <= m_sizeclass (MR st0 pm)) by lia.
    assert (Hslx : s_slots stx !! bg = Some (pm, ip)) by (apply (ab_slots _ _ _ AB _ _ _ Hsl0); lia).
    assert (Hslk : s_slots stk !! bg = Some (pm, ip)) by (rewrite SLk, slot_key_false by (rewrite STR; exact SPOS); exact Hslx).
    unfold dec_slots. rewrite Hslk.
    destruct (ab_hosts _ _ _ AB bpm pm Hpm0 ltac:(lia)) as [Hpmx MRpm].
    assert (Hpmk : hosts stk bpm pm).
    { apply HOk. split; [exact Hpmx|]. intros Eb. rewrite Eb in Hpm0. pose proof (hosts_fun st0 bg g pm Hg0 Hpm0) as E. subst pm. lia. }
    apply (IH stk LSx (g :: ZB) pm bpm ip).
    + constructor.
      * exact LOk.
      * exact FR.
      * destruct AB as [A1 A2 A3 A4 A5]. constructor.
        -- intros b m Hb Hc. destruct (A1 b m Hb ltac:(lia)) as [Hbx Em]. split; [| rewrite MRk; exact Em].
           apply HOk. split; [exact Hbx|]. intros ->. pose proof (hosts_fun st0 bg g m Hg0 Hb) as E. subst m. lia.
        -- intros sc' Hc. assert (Ak : active stk sc' = active stx sc') by exact (HDk (LActive sc')). rewrite Ak. apply (A2 sc'). lia.
        -- intros sc' Hc. unfold stk. change (usage (del_slots bg (get_stride (MR stx g)) cnt (del_group bg st1)) sc') with (usage st1 sc').
           rewrite U1 by (unfold sc; rewrite Esc; lia). apply A3. lia.
        -- unfold stk. cbn. rewrite B1. exact A4.
        -- intros s0 p0 j H0 Hc. rewrite SLk. rewrite (A5 s0 p0 j H0 ltac:(lia)).
           destruct (_ && _) eqn:KEY; [|reflexivity]. exfalso.
           apply (slot_key_test bg (get_stride (MR stx g)) cnt s0 ltac:(rewrite STR; exact SPOS)) in KEY as (j' & Hj' & Es0).
           pose proof (is_total _ _ _ IS bg g j' Hg0 ltac:(unfold cnt in Hj'; lia)) as T0.
           rewrite (slot_start'_eq x0 st0 LS0 IM g bg j' Hg0) in T0. unfold sstart in T0.
           rewrite (hosts_gbase x0 st0 LS0 IM bg g Hg0) in T0. rewrite STR in Es0.
           assert (Es0' : s0 = (fst bg, snd bg + UNIT + get_stride (MR st0 g) * j')) by (rewrite Es0; unfold aadd; f_equal; lia).
           rewrite <- Es0' in T0. rewrite H0 in T0. injection T0 as -> _. lia.
      * intros b m Hb. apply HOk in Hb as [Hb _]. rewrite MRk. exact (HO b m Hb).
      * rewrite Rk. exact RG.
      * unfold nmeta. rewrite Mk. exact NM.
      * cbn [length]. lia.
      * intros z [<-|Hz].
        -- split; [rewrite Mk; exact Pg|]. split; [exact GU| exact NLk].
        -- destruct (ZO z Hz) as (P & U & N). split; [rewrite Mk; exact P|]. split; [exact U|].
           intros [b Hb]. apply N. exists b. apply HOk in Hb. tauto.
      * constructor; [intros X; apply GnZ; apply list_elem_of_In; exact X| exact ZN].
      * apply (ctxm_trans _ stx); [exact CT| exact CTk].
      * intros s0 p0 j H0. exact (SL s0 p0 j (SLk' s0 _ H0)).
      * intros sc' m Hm. destruct (AO sc' m Hm) as ([b Hb] & Ec). rewrite MRk. split; [|exact Ec].
        exists b. apply HOk. split; [exact Hb|]. intros ->. pose proof (hosts_fun stx bg m g Hb Hgx) as E. subst m. exact (GU _ Hm).
      * intros m Hm [b Hb]. apply (FO m Hm). exists b. apply HOk in Hb. tauto.
      * intros m. rewrite Mk. exact (KY m).
      * intros b m Hb. destruct (BK b m Hb) as [H|H]; [| right; right; exact H].
        destruct (aptr_eqb_spec b bg) as [->|NE]; [right; left; exact (hosts_fun stx bg g m Hgx H)|].
        left. apply HOk. split; [exact H| exact NE].
    + exact Hpm0.
    + rewrite MRk. exact MRpm.
    + exact Hpmk.
    + exact Hip.
    +
      pose proof Hpm0 as [aip Hpmg].
      pose proof (is_part _ _ _ IS bpm pm aip ip Hpmg Hip) as PART. cbn zeta in PART. rewrite <- Ebg in PART.
      unfold one5 in PART. destruct PART as (_ & _ & _ & NAD & _ & _ & NBD & _).
      assert (D : s_groups st0 !! bg <> None) by (rewrite Hg0'; discriminate).
      unfold fmask. rewrite Z.lor_spec. unfold tbit in NAD, NBD.
      destruct (Z.testbit (m_avail (MR st0 pm)) ip) eqn:A; [exfalso; apply NAD; split; [reflexivity| exact D]|].
      destruct (Z.testbit (m_freed (MR st0 pm)) ip) eqn:B; [exfalso; apply NBD; split; [reflexivity| exact D]| reflexivity].
    + lia.
    + lia.
    + intros st3 mi NP3. rewrite free_meta_eq. apply CONT. apply NPOST_fm. exact NP3.
  -
    rewrite free_meta_eq. apply CONT. apply NPOST_fm.
    set (st2 := record_seq sc (step_seq stk)).
    assert (E2 : s_metas st2 = s_metas stk /\ s_groups st2 = s_groups stk /\ s_slots st2 = s_slots stk /\ s_regions st2 = s_regions stk
                 /\ (forall h, get_head st2 h = get_head stk h) /\ CTXM stk st2).
    { unfold st2, record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx stk) =? 255);
        (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]);
        (split; [intros h; destruct h; reflexivity| constructor; reflexivity]). }
    destruct E2 as (M2 & G2 & S2 & R2 & H2 & C2).
    assert (MR2 : forall x, MR st2 x = MR stx x) by (intros x; unfold MR, get_meta_rec; rewrite M2, Mk; reflexivity).
    assert (HO2 : forall b m, hosts st2 b m <-> hosts stk b m) by (intros; apply hosts_ext; exact G2).
    rewrite Eml in ML0. destruct (g_top _ _ _ _ _ _ GO ML0) as (B0 & r & Hr & Hk & Hlen & _).
    pose proof (g_maplen _ _ _ _ _ _ GO) as MLpos.
    constructor.
    + exists LSx. split; [apply (lists_ok_links stk st2 LSx LOk H2); intros x; rewrite MR2, MRk; split; reflexivity|]. split; [| split; [| split]].
      * rewrite FR. unfold ngrp in *. rewrite G2. cbn [length]. lia.
      * intros z [<-|Hz]; [exact GU| exact (proj1 (proj2 (ZO z Hz)))].
      * intros m Hm. rewrite FR. exact Hm.
      * intros b m Hb. destruct (BK b m Hb) as [H|H]; [| right; right; right; exact H].
        destruct (aptr_eqb_spec b bg) as [->|NE]; [right; right; left; exact (hosts_fun stx bg g m Hgx H)|].
        left. apply HO2, HOk. split; [exact H| exact NE].
    + intros m. rewrite <- (KY m). unfold MR. rewrite M2, Mk. tauto.
    + intros z [<-|Hz].
      * split; [rewrite M2, Mk; exact Pg|]. intros [b Hb]. apply NLk. exists b. apply HO2. exact Hb.
      * destruct (ZO z Hz) as (P & _ & N). split; [rewrite M2, Mk; exact P|]. intros [b Hb]. apply N. exists b. apply HO2, HOk in Hb. tauto.
    + constructor; [intros X; apply GnZ; apply list_elem_of_In; exact X| exact ZN].
    + intros b m Hb. apply HO2, HOk in Hb as [Hb _]. rewrite MR2. destruct (HO b m Hb) as (H0' & G0' & _). split; assumption.
    + exists None. intros b m Hb He. left. apply HO2, HOk in Hb as [Hb _]. destruct (HO b m Hb) as (_ & G0' & F0').
      unfold gempty in He |- *. rewrite MR2 in He. rewrite F0' in He. apply GEOM_eq in G0' as (_ & L0' & _). rewrite L0' in He. exact He.
    + rewrite R2, Rk. exact RG.
    + cbn [fst snd]. split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split.
      * rewrite Eml, Hlen, round_up_pg_eq. reflexivity.
      * rewrite Eml. lia.
    + unfold nmeta. rewrite M2, Mk. exact NM.
    + apply (ctxm_trans _ stx); [exact CT|]. apply (ctxm_trans _ stk); [exact CTk| exact C2].
    + intros s0 p0 j H0. rewrite S2 in H0. exact (SL s0 p0 j (SLk' s0 _ H0)).
Qed.

Theorem ntf_walk T w : forall f, NTFW T w f.
Proof.
  induction f as [|f IHf]; intros st LS ZB g bg i k bail c n Q CA H0 EG Hs Hi Hbit F1 F2 CONT; [lia|].
  pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  destruct (g0_facts bg g H0) as (ai & Hg0' & GO).
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  pose proof (g_masks _ _ _ _ _ _ GO) as (Mav & Mfr & _).
  pose proof (hosts_mem x0 st0 LS0 IM bg g H0) as Hmem.
  rewrite ntf_unfold. rewrite EG.
  set (sc := m_sizeclass (MR st0 g)) in *.
  set (mask := Z.lor (m_freed (MR st0 g)) (m_avail (MR st0 g))).
  assert (MF : mask = fmask (MR st0 g)) by (unfold mask, fmask; apply Z.lor_comm).
  assert (MN : 0 <= mask) by (unfold mask; apply Z.lor_nonneg; auto).
  assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; [exact MN| lia| rewrite MF; exact Hbit]).
  assert (OTF : okay_to_free st g = okay_to_free st0 g).
  { unfold okay_to_free. fold (MR st g) (MR st0 g). rewrite EG.
    destruct CA as [_ _ AB _ _ _ _ _ _ _ _ _ _ _ _]. rewrite (ab_usage _ _ _ AB sc ltac:(lia)).
    unfold is_bouncing, bounces. rewrite (ab_bounces _ _ _ AB). reflexivity. }
  destruct CA as [LO FR AB HO RG NM NG ZO ZN CT SL AO FO KY BK].

  assert (GNF : ~ In g (LS LFree)) by (intros Hf; apply (FO g Hf); exists bg; exact Hs).
  assert (GCL : forall sc', In g (LS (LActive sc')) -> sc' = sc).
  { intros sc' Hin. destruct (AO sc' g Hin) as [_ E]. rewrite EG in E. symmetry. exact E. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st0 g))) && okay_to_free st g) eqn:C1.
  -
    apply Bool.andb_true_iff in C1 as [CM COK].
    assert (CA : CASC st LS ZB sc) by (constructor; assumption).
    assert (FUEL : 48 - m_sizeclass (MR st0 g) <= Z.of_nat f) by lia.
    destruct (m_next (MR st0 g)) as [nx|] eqn:NX.
    + apply apw_guard. intros Hsc. apply Z.ltb_lt in Hsc.
      assert (IN : exists h, In g (LS h)) by (apply (proj1 (lo_link _ _ LO g)); rewrite EG, NX; discriminate).
      destruct IN as [h Hh]. destruct h as [sc'|]; [| exfalso; exact (GNF Hh)].
      pose proof (GCL sc' Hh) as ->. apply in_split in Hh as (l1 & l2 & Esp).
      pose proof (fgpre_dequeue st LS ZB g bg l1 l2 CA H0 EG Hs Esp) as FPd. fold sc in FPd.
      set (std := dequeue (LActive sc) g st) in *.
      destruct (optr_eqb (active st sc) (Some g)); [| apply (fg_walk T w f IHf std _ ZB g bg k bail c n Q FPd FUEL CONT)].
      destruct (active std sc) as [a|] eqn:AD; [| apply (fg_walk T w f IHf std _ ZB g bg k bail c n Q FPd FUEL CONT)].
      unfold activate_group. apply apw_guard. intros HA0. apply Z.eqb_eq in HA0.
      assert (Ain : In a (fupd LS (LActive sc) (l1 ++ l2) (LActive sc))).
      { pose proof (lo_head _ _ (fp_lists _ _ _ _ _ FPd) (LActive sc)) as Eh. change (get_head std (LActive sc)) with (active std sc) in Eh.
        rewrite AD in Eh. destruct (fupd LS (LActive sc) (l1 ++ l2) (LActive sc)) as [|a' r]; [discriminate| injection Eh as ->; left; reflexivity]. }
      apply (fg_walk T w f IHf _ _ ZB g bg k bail c n Q (fgpre_activate std _ ZB g bg a _ FPd Ain HA0) FUEL CONT).
    + assert (GUN : forall h, ~ In g (LS h)) by (apply (lists_notin st LS LO); rewrite EG; exact NX).
      apply (fg_walk T w f IHf st LS ZB g bg k bail c n Q (fgpre_unlisted st LS ZB g bg CA H0 EG Hs GUN) FUEL CONT).
  -
    assert (KEEP : Z.lor (fmask (MR st0 g)) (bit i) = mask_upto (m_last_idx (MR st0 g)) -> okay_to_free st g = false).
    { intros He. rewrite <- MF, <- MADD in He. rewrite He, Z.eqb_refl in C1. exact C1. }
    assert (CA : CASC st LS ZB sc) by (constructor; assumption).
    assert (Pq : forall x, s_metas st !! x <> None <-> s_metas st !! x <> None) by tauto.
    destruct (mask =? 0) eqn:M0.
    + apply apw_guard. intros Hsc. apply Z.ltb_lt in Hsc.
      destruct (negb (optr_eqb (active st sc) (Some g))) eqn:AH.
      *
        assert (UNL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [|reflexivity]. exfalso.
          assert (IN : exists h, In g (LS h)) by (apply (proj1 (lo_link _ _ LO g)); rewrite NX; discriminate).
          destruct IN as [h Hh]. destruct h as [sc'|]; [| exact (GNF Hh)].
          pose proof (GCL sc' Hh) as ->. destruct (ab_active _ _ _ AB sc ltac:(lia)) as [Eact ELS].
          rewrite ELS in Hh.
          destruct (optr_eqb_spec (active st sc) (Some g)) as [E|NE]; [cbn in AH; discriminate|].
          assert (NH : Some g <> head_of (LS0 (LActive sc))).
          { intros E. apply NE. rewrite Eact. change (active st0 sc) with (get_head st0 (LActive sc)). rewrite (il_head _ _ IL (LActive sc)). exact (eq_sym E). }
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hh NH) as [A0 F0].
          apply Z.eqb_eq in M0. unfold mask in M0. rewrite A0, Z.lor_0_r in M0. exact (F0 M0). }
        assert (UNLp : m_prev (MR st g) = None) by (apply (proj2 (lo_link _ _ LO g)); exact UNL).
        rewrite (queue_eq (LActive sc) g st _ bail UNL UNLp).
        apply CONT.
        assert (GUN : forall h, ~ In g (LS h)) by (apply (lists_notin st LS LO); exact UNL).
        apply (npost_keep st LS ZB g bg i (queue_st (LActive sc) g st) (fupd LS (LActive sc) (LS (LActive sc) ++ [g])) CA H0 EG Hs Hi Hbit KEEP).
        -- apply lists_queue; [exact LO| exact UNL].
        -- rewrite fupd_ne by discriminate. reflexivity.
        -- intros z Hz h Hzh. destruct (ZO z Hz) as (_ & U & NLz). destruct (decide (h = LActive sc)) as [->|NEh].
           ++ rewrite fupd_eq in Hzh. apply in_app_iff in Hzh as [Hzh|[<-|[]]]; [exact (U _ Hzh)| apply NLz; exists bg; exact Hs].
           ++ rewrite fupd_ne in Hzh by exact NEh. exact (U _ Hzh).
        -- destruct (queue_frame (LActive sc) g st) as (_ & _ & _ & _ & Q5 & _). exact Q5.
        -- destruct (queue_frame (LActive sc) g st) as (_ & _ & _ & _ & _ & Q6 & _). exact Q6.
        -- destruct (queue_frame (LActive sc) g st) as (Q1 & _). exact Q1.
        -- intros x. apply queue_data.
        -- apply (nmeta_queue st LS (LActive sc) g LO). intros E. assert (Hm' : m_mem (MR st g) = Some bg) by (rewrite EG; exact Hmem). unfold MR, get_meta_rec in Hm'. rewrite E in Hm'. discriminate.
        -- destruct (queue_frame (LActive sc) g st) as (_ & _ & _ & Q4 & _ & _ & _ & _ & _ & Q10). apply ctxm_cbh; [exact Q10| exact Q4].
        -- apply (queue_keys_iff st LS (LActive sc) g LO). intros E. assert (Hm' : m_mem (MR st g) = Some bg) by (rewrite EG; exact Hmem). unfold MR, get_meta_rec in Hm'. rewrite E in Hm'. discriminate.
      * apply CONT. apply (npost_keep st LS ZB g bg i st LS CA H0 EG Hs Hi Hbit KEEP LO); try reflexivity; auto.
        -- intros z Hz. exact (proj1 (proj2 (ZO z Hz))).
        -- apply ctxm_refl.
    + apply CONT. apply (npost_keep st LS ZB g bg i st LS CA H0 EG Hs Hi Hbit KEEP LO); try reflexivity; auto.
      * intros z Hz. exact (proj1 (proj2 (ZO z Hz))).
      * apply ctxm_refl.
Qed.

End CASCADE.

End HMWNTF.
