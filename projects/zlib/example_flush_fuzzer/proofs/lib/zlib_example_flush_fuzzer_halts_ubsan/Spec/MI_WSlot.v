(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.


Definition GP (st st' : mstate) : Prop :=
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
  /\ s_secret st' = s_secret st.
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.


Definition hdrsh (t : N) : shadow := mkShadow ∅ (<[0 := [(12, t)]]> ∅) ∅.
Definition gnone (st : mstate) (rid : N) : Prop := forall b h, s_groups st !! b = Some h -> fst b <> rid.
Definition gonly0 (st : mstate) (rid : N) : Prop :=
  s_groups st !! (rid, 0) <> None /\ forall b h, s_groups st !! b = Some h -> fst b = rid -> b = (rid, 0).
Definition GMONO (st st' : mstate) : Prop := forall b, s_groups st' !! b = None -> s_groups st !! b = None.
Definition SHK (st st' : mstate) : Prop := forall rid, gonly0 st rid -> gonly0 st' rid -> get_shadow st' rid = get_shadow st rid.
Definition TOPNEW (st st' : mstate) : Prop := forall rid, gnone st rid -> gonly0 st' rid -> exists t, get_shadow st' rid = hdrsh t.
Definition GPX (st st' : mstate) : Prop := GP st st' /\ GMONO st st' /\ SHK st st' /\ TOPNEW st st'.

Lemma GPX_GP st st' : GPX st st' -> GP st st'. Proof. intros [H _]. exact H. Qed.
Lemma gnone_gonly0 st rid : gnone st rid -> gonly0 st rid -> False.
Proof. intros N [S _]. destruct (s_groups st !! (rid, 0)) as [h|] eqn:E; [exact (N _ _ E eq_refl)| exact (S eq_refl)]. Qed.
Lemma gonly0_mono st st' rid : GMONO st st' -> (forall b h, s_groups st !! b = Some h -> s_groups st' !! b <> None) ->
  s_groups st !! (rid, 0) <> None -> gonly0 st' rid -> gonly0 st rid.
Proof.
  intros _ FW S0 [_ O']. split; [exact S0|]. intros b h Hb E. destruct (s_groups st' !! b) as [h'|] eqn:E'; [exact (O' _ _ E' E)|].
  exfalso. exact (FW _ _ Hb E').
Qed.
Lemma GMONO_fw st st' : GMONO st st' -> forall b h, s_groups st !! b = Some h -> s_groups st' !! b <> None.
Proof. intros M b h Hb E'. rewrite (M _ E') in Hb. discriminate. Qed.

Lemma gnone_back st0 st1 rid : GMONO st0 st1 -> gnone st1 rid -> gnone st0 rid.
Proof.
  intros M N b h Hb E. destruct (s_groups st1 !! b) as [h1|] eqn:E1; [exact (N _ _ E1 E)|]. rewrite (M _ E1) in Hb. discriminate.
Qed.
Lemma gonly0_top st st' rid h : s_groups st' = <[(rid, 0) := h]> (s_groups st) -> gnone st rid -> gonly0 st' rid.
Proof.
  intros GR N. split; [rewrite GR, lookup_insert_eq; discriminate|].
  intros b hb Hb E. rewrite GR in Hb. destruct (decide (b = (rid, 0))) as [->|NE]; [reflexivity|].
  rewrite lookup_insert_ne in Hb by congruence. exfalso. exact (N _ _ Hb E).
Qed.
Lemma gonly0_same st st' rid : s_groups st' = s_groups st -> gonly0 st rid -> gonly0 st' rid.
Proof. intros E [A B]. split; [rewrite E; exact A| intros b h Hb; rewrite E in Hb; exact (B b h Hb)]. Qed.

Lemma GPX_refl st : GPX st st.
Proof. split; [apply GP_refl|]. split; [intros b H; exact H|]. split; [intros rid _ _; reflexivity|]. intros rid N O. exfalso. exact (gnone_gonly0 _ _ N O). Qed.

Lemma GPX_trans a b c : GPX a b -> GPX b c -> GPX a c.
Proof.
  intros (G1 & M1 & S1 & T1) (G2 & M2 & S2 & T2). split; [exact (GP_trans _ _ _ G1 G2)|].
  split; [intros k H; exact (M1 _ (M2 _ H))|].
  assert (MID : forall rid, s_groups a !! (rid, 0) <> None -> gonly0 c rid -> gonly0 b rid).
  { intros rid A0 Oc. apply (gonly0_mono b c rid M2 (GMONO_fw _ _ M2)); [| exact Oc]. intros E. exact (A0 (M1 _ E)). }
  split.
  - intros rid Oa Oc. pose proof (MID rid (proj1 Oa) Oc) as Ob. rewrite (S2 rid Ob Oc). exact (S1 rid Oa Ob).
  - intros rid Na Oc. destruct (s_groups b !! (rid, 0)) as [h|] eqn:Eb.
    + assert (Ob : gonly0 b rid) by (apply (gonly0_mono b c rid M2 (GMONO_fw _ _ M2)); [rewrite Eb; discriminate| exact Oc]).
      destruct (T1 rid Na Ob) as [t Ht]. exists t. rewrite (S2 rid Ob Oc). exact Ht.
    + apply (T2 rid); [| exact Oc]. intros k h Hk E. destruct (proj2 Oc k h ltac:(destruct (s_groups c !! k) as [h'|] eqn:E'; [|exfalso; exact (GMONO_fw _ _ M2 _ _ Hk E')];
        pose proof (proj2 Oc k h' E' E) as ->; rewrite Eb in Hk; discriminate) E).
      rewrite Eb in Hk. discriminate.
Qed.

Lemma GPX_keep st st' : GP st st' -> (forall b, s_groups st' !! b = None <-> s_groups st !! b = None) -> s_shadow st' = s_shadow st -> GPX st st'.
Proof.
  intros G D SH. split; [exact G|]. split; [intros b H; exact (proj1 (D b) H)|].
  assert (GS : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite SH; reflexivity).
  split; [intros rid _ _; apply GS|].
  intros rid N [O1 O2]. apply False_ind.
  destruct (s_groups st !! (rid, 0)) as [h0|] eqn:E0; [exact (N _ _ E0 eq_refl)|]. exact (O1 (proj2 (D (rid, 0)) E0)).
Qed.
Lemma GPX_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> GPX st st'.
Proof. intros R S G SH. apply GPX_keep; [apply GP_eq; assumption| intros b; rewrite G; tauto| exact SH]. Qed.
Lemma GPX_amf st st' : AM_frame st st' -> GPX st st'.
Proof. intros AF. apply GPX_keep; [exact (GP_amf _ _ AF)| intros b; rewrite (amf_groups _ _ AF); tauto| exact (amf_shadow _ _ AF)]. Qed.
Lemma GPX_taf st st' sc : TA_frame st st' sc -> GPX st st'.
Proof. intros TF. apply GPX_keep; [exact (GP_taf _ _ _ TF)| exact (taf_gdom _ _ _ TF)| exact (taf_shadow _ _ _ TF)]. Qed.

Lemma get_shadow_wr8_other p v st q : q <> fst p -> get_shadow (wr8 p v st) q = get_shadow st q.
Proof. intros NE. unfold wr8. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec q (fst p)); [congruence| reflexivity]. Qed.
Lemma get_shadow_wr16_other p v st q : q <> fst p -> get_shadow (wr16 p v st) q = get_shadow st q.
Proof. intros NE. unfold wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity. Qed.
Lemma get_shadow_wr32_other p v st q : q <> fst p -> get_shadow (wr32 p v st) q = get_shadow st q.
Proof. intros NE. unfold wr32. rewrite !get_shadow_wr8_other by exact NE. reflexivity. Qed.
Lemma get_shadow_set_size_other p e n b3 st q : q <> fst p -> fst e = fst p -> get_shadow (set_size p e n b3 st) q = get_shadow st q.
Proof.
  intros NE E. unfold set_size.
  set (st1 := if negb (snd e - snd p - n =? 0) then wr8 (aadd e (- (snd e - snd p - n))) 0 st else st).
  assert (S1 : get_shadow st1 q = get_shadow st q) by (unfold st1; destruct (negb _); [apply get_shadow_wr8_other; cbn; congruence| reflexivity]).
  destruct (5 <=? snd e - snd p - n); rewrite get_shadow_wr8_other by exact NE; [| exact S1].
  rewrite get_shadow_wr8_other by (cbn; congruence). rewrite get_shadow_wr32_other by (cbn; congruence). exact S1.
Qed.
Lemma get_shadow_zero_hdrs_other p size c : forall i st q, q <> fst p -> get_shadow (zero_hdrs p size i c st) q = get_shadow st q.
Proof. induction c as [|c IH]; intros i st q NE; cbn; [reflexivity|]. rewrite IH by exact NE. apply get_shadow_wr8_other. exact NE. Qed.
Lemma enframe_at_region st g idx n off : fst (snd (enframe_at st g idx n off)) = fst (gbase (MR st g)).
Proof. unfold enframe_at, gbase, MR. destruct (negb (off =? 0)); reflexivity. Qed.
Lemma get_shadow_enframe_at_other st g idx n off q : q <> fst (gbase (MR st g)) -> get_shadow (fst (enframe_at st g idx n off)) q = get_shadow st q.
Proof.
  intros NE. unfold enframe_at, gbase, MR in *. cbn zeta.
  destruct (negb (off =? 0)); cbn [fst snd];
    (rewrite get_shadow_set_size_other by (cbn; congruence)); rewrite get_shadow_wr8_other by exact NE; rewrite get_shadow_wr16_other by exact NE; [| reflexivity].
  rewrite get_shadow_wr8_other by exact NE. rewrite get_shadow_wr8_other by exact NE. rewrite get_shadow_wr16_other by exact NE. reflexivity.
Qed.
Lemma get_shadow_nest_layout_other st g idx j size cnt q : q <> fst (gbase (MR st g)) -> get_shadow (nest_layout st g idx j size cnt) q = get_shadow st q.
Proof.
  intros NE. unfold nest_layout. destruct (enframe_at st g idx (UNIT * size_class j - IB) 0) as [st1 p] eqn:E.
  pose proof (enframe_at_region st g idx (UNIT * size_class j - IB) 0) as R. rewrite E in R. cbn [snd] in R.
  rewrite get_shadow_zero_hdrs_other by congruence. rewrite get_shadow_wr8_other by (cbn; congruence).
  pose proof (get_shadow_enframe_at_other st g idx (UNIT * size_class j - IB) 0 q NE) as H. rewrite E in H. exact H.
Qed.
Lemma nest_layout_other_region X st L BL LS g bg idx j size cnt : INVL X st L BL LS -> hosts st bg g ->
  forall q, q <> fst bg -> get_shadow (nest_layout st g idx j size cnt) q = get_shadow st q.
Proof. intros INV Hh q NE. apply get_shadow_nest_layout_other. rewrite (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hh). exact NE. Qed.
Lemma sstart_ne0 X st L BL LS g bg idx : INVL X st L BL LS -> hosts st bg g -> 0 <= idx -> sstart (MR st g) idx <> 0.
Proof.
  intros INV Hh Hi. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (hosts_ok X st LS IG _ _ Hh) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _].
  pose proof (stride_ge X st LS IG _ _ Hh) as [SG _]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hh).
  assert (0 <= get_stride (MR st g) * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in SG; lia). unfold UNIT in *. lia.
Qed.

Lemma GPX_top st st' rid h t :
  GP st st' -> s_groups st' = <[(rid, 0) := h]> (s_groups st) -> (forall q, q <> rid -> get_shadow st' q = get_shadow st q) ->
  get_shadow st' rid = hdrsh t -> gnone st rid -> GPX st st'.
Proof.
  intros G GR SHo SHr GN.
  assert (KEEP : forall q, q <> rid -> forall off, s_groups st' !! (q, off) = s_groups st !! (q, off)).
  { intros q NE off. rewrite GR, lookup_insert_ne by congruence. reflexivity. }
  split; [exact G|]. split.
  { intros k H. rewrite GR in H. destruct (decide (k = (rid, 0))) as [->|NE]; [rewrite lookup_insert_eq in H; discriminate| rewrite lookup_insert_ne in H by congruence; exact H]. }
  split.
  - intros q Oq Oq'. destruct (N.eq_dec q rid) as [->|NE]; [exfalso; exact (gnone_gonly0 _ _ GN Oq)| exact (SHo q NE)].
  - intros q Nq Oq'. destruct (N.eq_dec q rid) as [->|NE]; [exists t; exact SHr|].
    exfalso. destruct Oq' as [O1 O2]. rewrite (KEEP q NE 0) in O1. destruct (s_groups st !! (q, 0)) as [h0|] eqn:E; [exact (Nq _ _ E eq_refl)| exact (O1 eq_refl)].
Qed.
Lemma hdr_havoc_fresh_shadow st st0 rid : s_shadow st = s_shadow st0 -> s_shadow st0 !! rid = None ->
  get_shadow (hdr_havoc (rid, 0) st) rid = hdrsh (s_tick st).
Proof.
  intros ES NS. change rid with (fst (rid, 0%Z)) at 1. rewrite (hdr_havoc_shadow (rid, 0) st). unfold get_shadow. rewrite ES, NS. cbn.
  unfold hdrsh. rewrite lookup_empty. reflexivity.
Qed.
Lemma GPX_agt_top st st1 sc m rid cnt ai :
  GP st (agt st1 sc m (rid, 0) cnt ai) -> s_groups st1 = s_groups st -> s_shadow st1 = s_shadow st ->
  s_shadow st !! rid = None -> gnone st rid ->
  GPX st (agt st1 sc m (rid, 0) cnt ai).
Proof.
  intros G EG ES NS GN. apply (GPX_top _ _ rid (mkGhdr (Some m) (Z.land ai 31)) (s_tick st1) G).
  - rewrite agt_groups, EG. reflexivity.
  - intros q NE. unfold get_shadow at 1. rewrite agt_shadow. fold (get_shadow (hdr_havoc (rid, 0) st1) q).
    rewrite (hdr_havoc_other_region (rid, 0) st1 q NE). unfold get_shadow. rewrite ES. reflexivity.
  - unfold get_shadow at 1. rewrite agt_shadow. fold (get_shadow (hdr_havoc (rid, 0) st1) rid). exact (hdr_havoc_fresh_shadow st1 st rid ES NS).
  - exact GN.
Qed.

Lemma GPX_agt_nest st st1 sc m r off cnt ai :
  GP st (agt st1 sc m (r, off) cnt ai) -> s_groups st1 = s_groups st -> (forall q, q <> r -> get_shadow st1 q = get_shadow st q) -> off <> 0 ->
  GPX st (agt st1 sc m (r, off) cnt ai).
Proof.
  intros G EG ES NZ. set (st' := agt st1 sc m (r, off) cnt ai).
  assert (GR : s_groups st' = <[(r, off) := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st)) by (unfold st'; rewrite agt_groups, EG; reflexivity).
  assert (SHo : forall q, q <> r -> get_shadow st' q = get_shadow st q).
  { intros q NE. unfold st'. unfold get_shadow at 1. rewrite agt_shadow. fold (get_shadow (hdr_havoc (r, off) st1) q).
    rewrite (hdr_havoc_other_region (r, off) st1 q NE). exact (ES q NE). }
  assert (NO : ~ gonly0 st' r).
  { intros [_ O2]. pose proof (O2 (r, off) (mkGhdr (Some m) (Z.land ai 31)) ltac:(rewrite GR, lookup_insert_eq; reflexivity) eq_refl) as E. inversion E. exact (NZ H0). }
  assert (KEEP : forall q, q <> r -> forall o, s_groups st' !! (q, o) = s_groups st !! (q, o)).
  { intros q NE o. rewrite GR, lookup_insert_ne by congruence. reflexivity. }
  split; [exact G|]. split.
  { intros k H. rewrite GR in H. destruct (decide (k = (r, off))) as [->|NE]; [rewrite lookup_insert_eq in H; discriminate| rewrite lookup_insert_ne in H by congruence; exact H]. }
  split.
  - intros q Oq Oq'. destruct (N.eq_dec q r) as [->|NE]; [exfalso; exact (NO Oq')| exact (SHo q NE)].
  - intros q Nq Oq'. destruct (N.eq_dec q r) as [->|NE]; [exfalso; exact (NO Oq')|].
    exfalso. destruct Oq' as [O1 O2]. rewrite (KEEP q NE 0) in O1. destruct (s_groups st !! (q, 0)) as [h|] eqn:E; [exact (Nq _ _ E eq_refl)| exact (O1 eq_refl)].
Qed.


Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : geo_of r' = geo_of r ->
  (forall i, sstart r' i = sstart r i) /\ cnt_of r' = cnt_of r /\ m_maplen r' = m_maplen r /\ get_stride r' = get_stride r.
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma same_geo_of_geo r1 r0 : geo_of r1 = geo_of r0 -> same_geo r1 r0.
Proof. unfold geo_of. intros H. injection H. intros. repeat split; assumption. Qed.

Lemma geom_kept_geo st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall x, geo_of (MR st' x) = geo_of (MR st x)) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.


Lemma INVL_idle_sub X idle' st L BL LS :
  (forall x, In x idle' -> In x (x_idle X)) -> INVL X st L BL LS -> INVL (xidle X idle') st L BL LS.
Proof.
  intros SUB (IR & IA & IM & IL & IG & IS & ISH).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.


Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.


Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : hosts st2 b m. Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2
    /\ same_geo (MR st4 m) (MR st2 m) .
Proof.
  exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  {
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity|]. split; [rewrite F8; reflexivity|].
  apply same_geo_of_geo. rewrite (fin_geo m), Em. reflexivity.
Qed.
End FINISH.
