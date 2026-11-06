(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_WAMeta.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Record AM_frame (st st1 : mstate) : Prop := mkAMF {
  amf_groups : s_groups st1 = s_groups st;
  amf_slots : s_slots st1 = s_slots st;
  amf_shadow : s_shadow st1 = s_shadow st;
  amf_tick : s_tick st1 = s_tick st;
  amf_active : forall sc, active st1 sc = active st sc;
  amf_usage : forall sc, usage st1 sc = usage st sc;
  amf_bounces : c_bounces (s_ctx st1) = c_bounces (s_ctx st);
  amf_seq : c_seq (s_ctx st1) = c_seq (s_ctx st);
  amf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  amf_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st1 !! rid = Some r;
  amf_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amf_ssec : s_secret st1 = s_secret st
}.
#[using="Type"] Lemma amf_refl st : AM_frame st st.
Proof. constructor; auto; first [reflexivity| lia]. Qed.
#[using="Type"] Lemma amf_trans a b c : AM_frame a b -> AM_frame b c -> AM_frame a c.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11]; constructor; try congruence.
  - intros rid r H K. apply B10; [| exact K]. apply A10; assumption.
  - clear -A11 B11. eapply N.le_trans; eassumption.
Qed.

Record L_frame (L L1 : mled) : Prop := mkLF {
  lf_groups : ld_groups L1 = ld_groups L;
  lf_live : ld_live L1 = ld_live L;
  lf_resv : ld_resv L1 = ld_resv L
}.
#[using="Type"] Lemma lf_refl L : L_frame L L. Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma lf_trans a b c : L_frame a b -> L_frame b c -> L_frame a c.
Proof. intros [] []; constructor; congruence. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inv_SH_view' st st' BL :
  s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r) ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_metas st' = s_metas st ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros SH TK HR HG HS HM I.
  pose proof (inv_SH_view st (set_regions (s_regions st) st') BL SH TK eq_refl HG HS) as V.
  assert (ME : forall x, MR (set_regions (s_regions st) st') x = MR st x) by (intros; apply MR_ext; exact HM).
  specialize (V ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) I).
  destruct V as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
  intros rid sh H. destruct (D1 rid sh H) as (r & Hr & K). exists r. split; [apply HR; assumption| exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma mslot_succ a k : aadd (mslot a k) META_SIZE = mslot a (k + 1).
Proof. unfold mslot, aadd, META_SIZE. cbn. f_equal. lia. Qed.

Section TAKE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HC : 0 < c_avail_meta_count (s_ctx st).

#[using="INV HC"] Lemma am_take_ok {T} (k : mstate -> optr -> M T) bail :
  exists m st2, am_take st k bail = k st2 (Some m) /\ INVL (xidle X (m :: x_idle X)) st2 L BL LS /\ AM_frame st st2 /\ ~ In m (x_idle X).
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (ia_avail _ IA) as [A1 A2]. destruct (A2 HC) as (a & Ht & Eam & FREE).
  set (k0 := NSLOTS - c_avail_meta_count (s_ctx st)) in *.
  exists (mslot a k0).
  unfold am_take, ctx. rewrite Eam.
  set (st1 := upd_ctx _ st). set (st2 := upd_meta (mslot a k0) _ st1).
  exists st2. split; [reflexivity|].
  assert (ABS : s_metas st !! mslot a k0 = None) by (apply FREE; lia).
  assert (MRm : MR st (mslot a k0) = meta0) by (unfold MR, get_meta_rec; rewrite ABS; reflexivity).
  assert (M2 : s_metas st2 = <[mslot a k0 := meta0]> (s_metas st)).
  { unfold st2, st1. rewrite s_metas_upd_meta. cbn. f_equal. rewrite get_meta_rec_upd_ctx. fold (MR st (mslot a k0)). rewrite MRm. reflexivity. }
  assert (MR2 : forall x, MR st2 x = MR st x).
  { intros x. unfold MR, get_meta_rec. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
    - rewrite lookup_insert_eq, ABS. reflexivity.
    - rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (DE : forall x, data_of (MR st2 x) = data_of (MR st x)) by (intros x; rewrite MR2; reflexivity).
  assert (KEYS : forall x, s_metas st2 !! x <> None <-> s_metas st !! x <> None \/ x = mslot a k0).
  { intros x. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
    - rewrite lookup_insert_eq. split; [auto| discriminate].
    - rewrite lookup_insert_ne by congruence. tauto. }
  assert (Ha : s_areas st !! a <> None) by (apply (ia_tail _ IA); exact Ht).
  assert (NLm : forall h, ~ In (mslot a k0) (LS h)).
  { intros h Hin. apply (listed_present _ _ _ _ _ (conj IR (conj IA (conj IM (conj IL (conj IG (conj IS ISH)))))) _ _ Hin). exact ABS. }
  split.
  - (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
      assert (CT2 : c_meta_area_tail (s_ctx st2) = c_meta_area_tail (ctx st)) by reflexivity.
      assert (CC2 : c_avail_meta_count (s_ctx st2) = c_avail_meta_count (s_ctx st) - 1) by reflexivity.
      assert (CA2 : c_avail_meta (s_ctx st2) = Some (mslot a (k0 + 1))) by (rewrite <- mslot_succ; reflexivity).
      destruct IA; constructor.
      * exact ia_ctx.
      * exact ia_secret.
      * exact ia_areas.
      * exact ia_head.
      * exact ia_tail.
      * cbn. intros Hn. exfalso. unfold ctx in Ht. rewrite Ht in Hn. discriminate.
      * intros m mr Hm. rewrite M2 in Hm. destruct (aptr_eq_dec m (mslot a k0)) as [->|NE].
        -- exists a, ar, k0. split; [exact Ea|]. split; [unfold k0; lia| reflexivity].
        -- rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
      * rewrite CT2, CA2, CC2. split; [lia|]. intros Hc. exists a. split; [exact Ht|]. split; [unfold k0; f_equal; f_equal; lia|].
        intros k1 Hk1. rewrite M2, lookup_insert_ne; [apply FREE; lia|]. unfold mslot, aadd. intros E. inversion E. unfold META_SIZE in *. lia.
      * rewrite CA2. intros q Hq. inversion Hq. subst q. unfold mslot, aadd. cbn [fst].
        destruct (ia_areas _ _ Ea) as ((r & Hr & K & _) & _). exists r. auto.
      * intros sc Hsc. unfold usage, ctx. cbn. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry.
        apply (gcnt_ext_groups st st2 eq_refl). intros b h m _ _. rewrite MR2. auto.
      * exact ia_usage_keys.
      * exact ia_active_keys.
    + destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn [x_idle x_zomb x_pend x_orph x_fresh xidle].
      * intros m Hm. rewrite !MR2 in *. exact (Q1 m Hm).
      * intros m b Hm. rewrite MR2 in Hm. exact (Q2 m b Hm).
      * intros b h Hb. destruct (Q3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !MR2. auto.
      * intros m [<-|Hm].
        -- split; [rewrite M2, lookup_insert_eq; reflexivity|]. intros [h Hin]. exact (NLm h Hin).
        -- destruct (Q4 m Hm) as [E NI]. split; [| exact NI]. rewrite M2, lookup_insert_ne; [exact E|]. intros Emm. congruence.
      * intros z Hz. rewrite !MR2. exact (Q5 z Hz).
    + destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
      all: try (intros h; destruct h; cbn; apply L1).
      * intros h. pose proof (L2 h) as D. destruct (LS h) as [|x l]; [exact I|]. cbn [dll] in D |- *. eapply linked_ext; [| | exact D]; intros; rewrite MR2; reflexivity.
      * intros m. rewrite !MR2. apply L5.
      * intros m Hm. rewrite !MR2. apply L6. exact Hm.
      * intros sc m Hm. rewrite MR2. exact (L7 sc m Hm).
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      * intros m b ai Hb. pose proof (G1 m b ai Hb) as GO. destruct GO; constructor; rewrite ?MR2; try assumption.
        -- apply KEYS. left. exact g_present.
        -- intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !MR2. auto 10.
      * intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MR2. eapply G3; eassumption.
      * intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite MR2. auto.
    + destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
      * intros s m i Hs. rewrite !MR2. exact (S1 s m i Hs).
      * intros b m i Hb Hi. rewrite MR2 in Hi |- *. exact (S2 b m i Hb Hi).
      * intros b m ai i Hb Hi. rewrite MR2 in Hi. rewrite !MR2. exact (S3 b m ai i Hb Hi).
      * intros kk Hk. destruct (S6 kk Hk) as (m & i & ? & ?). exists m, i. rewrite MR2. auto.
    + apply (inv_SH_view st st2); try reflexivity; try (intros; rewrite MR2; reflexivity). exact ISH.
  - split; [constructor; cbn; auto; first [reflexivity| lia]|].
    intros Hin. pose proof (proj1 (im_idle _ _ _ IM _ Hin)) as E. rewrite ABS in E. discriminate.
Qed.
End TAKE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition adv (st : mstate) (p : aptr) : mstate :=
  upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st.

Definition carve_rest (s : mstate) (p : aptr) : mstate :=
  let st2 := match c_meta_area_tail (ctx s) with
             | Some tl => set_areas (<[tl := match (s_areas s) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas s)) s
             | None => upd_ctx (set_meta_area_head (Some p)) s
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
  upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4.

#[using="Type"] Lemma am_carve_eq {T} st p (k : mstate -> optr -> M T) bail : am_carve st p k bail = am_take (carve_rest (adv st p) p) k bail.
Proof. reflexivity. Qed.

Section CARVE.
Variables (X : extras) (s : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (p : aptr).
Hypothesis INV : INVL X s L BL LS.
Hypothesis HP : c_avail_meta_areas (s_ctx s) = Some (aadd p 4096).
Hypothesis NA : s_areas s !! p = None.
Hypothesis NM : forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None.
Hypothesis PG : PGSZ <= snd p.
Hypothesis PM : snd p mod PGSZ = 0.
Hypothesis INIT : c_init_done (s_ctx s) = 1.
Let s' := carve_rest s p.

(* [comment removed for export] *)
Definition cr_areas : gmap aptr area :=
  match c_meta_area_tail (ctx s) with
  | Some tl => <[p := mkArea (c_secret (ctx s)) None NSLOTS]>
                 (<[tl := match (s_areas s) !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
  | None => <[p := mkArea (c_secret (ctx s)) None NSLOTS]> (s_areas s)
  end.
Definition cr_head : optr := match c_meta_area_tail (ctx s) with Some _ => c_meta_area_head (ctx s) | None => Some p end.

#[using="CE X L BL LS INV NA"] Lemma tail_not_p tl : c_meta_area_tail (ctx s) = Some tl -> tl <> p.
Proof. intros Ht ->. apply (ia_tail _ (proj1 (proj2 INV)) p Ht). exact NA. Qed.

#[using="CE X L BL LS INV NA"] Lemma cr_shape :
  s_areas s' = cr_areas /\ c_meta_area_head (s_ctx s') = cr_head /\ c_meta_area_tail (s_ctx s') = Some p
  /\ c_avail_meta (s_ctx s') = Some (aadd p AREA_HDR) /\ c_avail_meta_count (s_ctx s') = NSLOTS
  /\ s_regions s' = s_regions s /\ s_metas s' = s_metas s /\ s_groups s' = s_groups s /\ s_slots s' = s_slots s
  /\ s_shadow s' = s_shadow s /\ s_tick s' = s_tick s /\ s_next_rid s' = s_next_rid s /\ s_secret s' = s_secret s /\ s_reserved s' = s_reserved s
  /\ c_avail_meta_areas (s_ctx s') = c_avail_meta_areas (s_ctx s) /\ c_avail_meta_area_count (s_ctx s') = c_avail_meta_area_count (s_ctx s)
  /\ c_secret (s_ctx s') = c_secret (s_ctx s) /\ c_init_done (s_ctx s') = c_init_done (s_ctx s)
  /\ c_active (s_ctx s') = c_active (s_ctx s) /\ c_usage (s_ctx s') = c_usage (s_ctx s) /\ c_free_meta_head (s_ctx s') = c_free_meta_head (s_ctx s)
  /\ c_meta_alloc_shift (s_ctx s') = c_meta_alloc_shift (s_ctx s) /\ c_brk (s_ctx s') = c_brk (s_ctx s)
  /\ c_mmap_counter (s_ctx s') = c_mmap_counter (s_ctx s) /\ c_seq (s_ctx s') = c_seq (s_ctx s)
  /\ c_bounces (s_ctx s') = c_bounces (s_ctx s) /\ c_unmap_seq (s_ctx s') = c_unmap_seq (s_ctx s).
Proof.
  unfold s', carve_rest, cr_areas, cr_head, ctx. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET; cbn -[lookup insert NSLOTS AREA_HDR].
  - rewrite lookup_insert_ne by (intros E; exact (tail_not_p tl ET (eq_sym E)) || exact (tail_not_p tl ET E)). rewrite NA. cbn. repeat split; reflexivity.
  - rewrite NA. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma cr_areas_lookup a : cr_areas !! a =
  if aptr_eqb a p then Some (mkArea (c_secret (ctx s)) None NSLOTS)
  else match c_meta_area_tail (ctx s) with
       | Some tl => if aptr_eqb a tl then Some (match (s_areas s) !! tl with Some ar => mkArea (a_check ar) (Some p) (a_nslots ar) | None => mkArea 0 (Some p) 0 end)
                    else s_areas s !! a
       | None => s_areas s !! a
       end.
Proof.
  unfold cr_areas. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ET.
  - destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence.
    destruct (aptr_eqb_spec a tl) as [->|NE2]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
  - destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma mslot0 : aadd p AREA_HDR = mslot p (NSLOTS - NSLOTS).
Proof. unfold mslot, aadd. f_equal. Qed.

#[using="INV HP NA NM PG PM INIT"] Theorem INVL_carve : INVL X s' L BL LS /\ AM_frame s s' /\ 0 < c_avail_meta_count (s_ctx s').
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct cr_shape as (EA & EH & ET & EAM & EAC & ER & EM & EG & ESL & ESH & ETK & EN & ESE & ERS & ECA & ECC & EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7 & EC8 & EC9 & EC10 & EC11).
  assert (FR : forall rid r, frontier s' rid r = frontier s rid r) by (intros; unfold frontier; rewrite ECA; reflexivity).
  assert (MRE : forall x, MR s' x = MR s x) by (intros; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  destruct (ir_cursor _ _ _ IR) as (CU1 & CU2 & CU3). destruct (CU3 _ _ HP) as (rp & Hrp & Kp & _ & _ & Ep & _). cbn in Hrp, Ep.
  assert (HE : forall h, get_head s' h = get_head s h) by (intros [sc|]; cbn [get_head]; unfold active, ctx; rewrite ?EC3, ?EC5; reflexivity).
  split; [| split].
  - split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; rewrite ?ER, ?EN, ?ERS, ?EG, ?ECA, ?ECC, ?EC6, ?EC7; try assumption.
      * eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
      * intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
      * intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
    + destruct IA; constructor; rewrite ?ER, ?EA, ?EH, ?ET, ?EAM, ?EAC, ?EM, ?ESE, ?EC1, ?EC2, ?EC3, ?EC4, ?EC8, ?EC9, ?EC10, ?EC11; try assumption.
      * destruct ia_secret as [S0 [[I0 _]|S1]]; [exfalso; rewrite INIT in I0; discriminate|]. split; [exact S0| right; exact S1].
      * intros a ar. rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp].
        -- intros E. inversion E. subst ar. cbn. split; [| split; [reflexivity| split; [reflexivity| intros a' H; discriminate]]].
           exists rp. rewrite FR. unfold frontier. rewrite HP. cbn. rewrite N.eqb_refl. split; [exact Hrp|]. split; [exact Kp|]. split; [exact PM|]. split; [exact PG|]. unfold PGSZ. lia.
        -- assert (OLD : forall ar0, s_areas s !! a = Some ar0 -> (exists r, s_regions s !! fst a = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a /\ snd a + PGSZ <= frontier s' (fst a) r)
                          /\ a_check ar0 = c_secret (s_ctx s) /\ a_nslots ar0 = NSLOTS /\ (forall a', a_next ar0 = Some a' -> cr_areas !! a' <> None)).
           { intros ar0 H0. destruct (ia_areas a ar0 H0) as ((r & Hr & K & M & P & F) & C & NS & NX). split; [exists r; rewrite FR; auto 10|]. split; [exact C|]. split; [exact NS|].
             intros a' Ha'. rewrite cr_areas_lookup. destruct (aptr_eqb a' p); [discriminate|].
             destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a' tl); [discriminate|]|]; exact (NX a' Ha'). }
           destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
           ++ destruct (aptr_eqb_spec a tl) as [->|NEt].
              ** destruct (s_areas s !! tl) as [ar0|] eqn:E0; [| exfalso; exact (ia_tail tl ETL E0)].
                 intros E. inversion E. subst ar. cbn. destruct (OLD ar0 E0) as (R1 & C & NS & _). split; [exact R1|]. split; [exact C|]. split; [exact NS|].
                 intros a' Ha'. inversion Ha'. subst a'. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
              ** intros H0. exact (OLD ar H0).
           ++ intros H0. exact (OLD ar H0).
      * intros h Hh. rewrite cr_areas_lookup. destruct (aptr_eqb_spec h p) as [->|NEhp]; [discriminate|].
        unfold cr_head in Hh. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
        -- destruct (aptr_eqb h tl); [discriminate|]. exact (ia_head h Hh).
        -- inversion Hh. congruence.
      * intros t Ht. inversion Ht. subst t. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
      * intros H. discriminate.
      * intros m mr Hm. destruct (ia_metas m mr Hm) as (a & ar & k & Ha & Hk & Em). exists a.
        rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp]; [rewrite NA in Ha; discriminate|].
        destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a tl); [eexists _, k; eauto| exists ar, k; auto]| exists ar, k; auto].
      * split; [unfold NSLOTS; lia|]. intros _. exists p. split; [reflexivity|]. split; [rewrite mslot0; reflexivity|].
        intros k Hk. apply NM. unfold NSLOTS in *. lia.
      * intros q Hq. inversion Hq. subst q. cbn. exists rp. auto.
      * intros sc Hsc. unfold usage, ctx. rewrite EC4. fold (ctx s). fold (usage s sc). rewrite (ia_usage sc Hsc). symmetry.
        apply (gcnt_ext s s'); [exact EG| exact EM].
    + apply (inv_M_ext X s s'); [exact EM| exact EG| exact IM].
    + apply (inv_L_ext s s'); [exact EM| exact EG| exact HE| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; rewrite ?EG, ?ER.
      * intros m b ai Hb. apply (group_ok_ext X s s'); [exact EM| exact ESL| intros; rewrite ER; assumption| exact (G1 m b ai Hb)].
      * exact G2.
      * intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MRE. eapply G3; eassumption.
      * intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (hosts_ext s s' EG), MRE. auto.
      * exact G5.
    + apply (inv_S_ext X s s' BL); [exact EM| exact EG| exact ESL| exact IS].
    + apply (inv_SH_view s s'); auto; intros; rewrite MRE; reflexivity.
  - constructor; rewrite ?EG, ?ESL, ?ESH, ?ETK, ?EC8, ?EC9, ?EC10, ?EN; auto; try reflexivity.
    + intros sc. unfold active, ctx. rewrite EC3. reflexivity.
    + intros sc. unfold usage, ctx. rewrite EC4. reflexivity.
    + intros rid r H _. rewrite ER. exact H.
  - rewrite EAC. unfold NSLOTS. lia.
Qed.
End CARVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma above_frontier X st L BL LS rid r (p : aptr) :
  INVL X st L BL LS -> s_regions st !! rid = Some r -> fst p = rid -> frontier st rid r <= snd p ->
  s_areas st !! p = None /\ forall k, 0 <= k < NSLOTS -> s_metas st !! mslot p k = None.
Proof.
  intros INV Hr Hf Hfr. pose proof (proj1 (proj2 INV)) as IA. split.
  - destruct (s_areas st !! p) as [ar|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _ & _ & _ & F) & _). rewrite Hf, Hr in Hr'. inversion Hr'. subst r'. rewrite Hf in F. unfold PGSZ in F. lia.
  - intros k Hk. destruct (s_metas st !! mslot p k) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em).
    destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _).
    unfold mslot, aadd in Em. inversion Em. rewrite Hf in H0. rewrite <- H0, Hr in Hr'. inversion Hr'. subst r'. rewrite <- H0 in F.
    unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section META_ADV.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcur : c_avail_meta_areas (s_ctx st) = Some (rid, off).
Hypothesis Hcnt : 0 < c_avail_meta_area_count (s_ctx st).
Let p : aptr := (rid, off).
Let a : Z := conc st p.
Let st' := adv st p.
Let L' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas (map (bump_meta a) (ld_metas L)) L.

#[using="X L BL LS INV Hcur Hcnt p a"] Lemma ma_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ PGSZ <= off /\ off mod PGSZ = 0
  /\ off + c_avail_meta_area_count (s_ctx st) * PGSZ = r_len r /\ r_len r mod PGSZ = 0 /\ 0 < r_base r
  /\ r_base r + r_len r <= alloc_ceiling.
Proof.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3). destruct (C3 _ _ Hcur) as (r & Hr & K & P1 & P2 & P3 & P4).
  pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 K) as [S7 S8].
  exists r. repeat split; auto.
  pose proof (round_up_ge (r_len r)). lia.
Qed.

#[using="Hcur"] Lemma ma_frontier q rq : frontier st q rq = if (rid =? q)%N then off else r_len rq.
Proof. unfold frontier. rewrite Hcur. reflexivity. Qed.
#[using="Type"] Lemma ma_frontier' q rq : frontier st' q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st', adv. cbn. reflexivity. Qed.

(* [comment removed for export] *)
#[using="CE X BL LS INV Hcur Hcnt"] Lemma ma_event_pre : event_pre L (EMprotect a PGSZ PROT_RW).
Proof.
  destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|].
  exists (r_base r), (r_len r), (frontier st rid r / PGSZ - 1).
  split.
  - pose proof (ir_metas _ _ _ (proj1 INV)) as P. eapply Permutation_in; [apply Permutation_sym; exact P|].
    apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [apply In_map_to_list_regions; exact Hr| cbn; rewrite K; reflexivity].
  - rewrite ma_frontier, N.eqb_refl. unfold a, conc, get_region, p. cbn [fst snd]. rewrite Hr.
    unfold PGSZ in *. pose proof (round_up_ge (r_len r)).
    pose proof (Z.div_mod off 4096 ltac:(lia)) as DM. rewrite P2 in DM. set (q := off / 4096) in *. clearbody q. nia.
Qed.

#[using="INV Hcur Hcnt"] Theorem INVL_meta_adv : INVL X st' L' BL LS
  /\ c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)
  /\ s_areas st' !! p = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st' !! mslot p k = None)
  /\ PGSZ <= snd p /\ snd p mod PGSZ = 0 /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ AM_frame st st'.
Proof.
  destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  destruct (above_frontier X st L BL LS rid r p INV Hr eq_refl ltac:(rewrite ma_frontier, N.eqb_refl; cbn; lia)) as [NA NM].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [cbn; lia| split; [exact P2| split; [reflexivity|]]]]]]].
  2:{ constructor; cbn; auto; first [reflexivity| lia]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - assert (Rg : s_regions st' = s_regions st) by reflexivity. assert (Rn : s_next_rid st' = s_next_rid st) by reflexivity.
    assert (Rv : s_reserved st' = s_reserved st) by reflexivity. assert (Rgr : s_groups st' = s_groups st) by reflexivity.
    assert (Csh : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) by reflexivity.
    assert (Cbrk : c_brk (s_ctx st') = c_brk (s_ctx st)) by reflexivity.
    assert (Cam : c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)) by reflexivity.
    assert (Cac : c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) - 1) by reflexivity.
    unfold L'. destruct IR; constructor; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_metas OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_groups OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_resv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_live OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas];
      rewrite ?Rg, ?Rn, ?Rv, ?Rgr, ?Csh, ?Cbrk, ?Cam, ?Cac; try assumption.
    + (* [comment removed for export] *)
      eapply Permutation_trans; [apply Permutation_map; exact ir_metas|]. rewrite map_map.
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. cbn in Hk |- *.
      apply In_map_to_list_regions in Hin. destruct (r_kind rq) eqn:Ekq; try discriminate.
      rewrite ma_frontier.
      pose proof (ir_shape q rq Hin) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(right; exact Ekq)) as [S7 S8].
      destruct (N.eqb_spec rid q) as [<-|NE].
      * rewrite Hr in Hin. inversion Hin. subst rq.
        replace (r_base r + (1 + (off / PGSZ - 1)) * PGSZ) with a.
        2:{ unfold a, conc, get_region, p. cbn. rewrite Hr. unfold PGSZ in *. pose proof (Z.div_mod off 4096 ltac:(lia)). lia. }
        rewrite Z.eqb_refl. f_equal. unfold PGSZ in *.
        pose proof (Z.div_mod off 4096 ltac:(lia)). rewrite P2 in H.
        replace (off + 4096) with ((off / 4096 + 1) * 4096) by lia. rewrite Z.div_mul by lia. lia.
      * destruct (Z.eqb_spec (r_base rq + (1 + (r_len rq / PGSZ - 1)) * PGSZ) a) as [E|NE2]; [| reflexivity]. exfalso.
        unfold a, conc, get_region, p in E. cbn in E. rewrite Hr in E.
        pose proof (Z.div_mod (r_len rq) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite S7 in DM.
        pose proof (ir_disj q rid rq r Hin Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ekq, K in D.
        pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). unfold PGSZ in *. nia.
    + intros q rq Hq Kq. rewrite ma_frontier'. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite ma_frontier in F1, F2.
      split; [exact J|]. destruct (N.eqb_spec rid q) as [<-|NE]; [| auto].
      rewrite Hr in Hq. inversion Hq. subst rq. unfold PGSZ in *. split; [lia|].
      rewrite <- Zplus_mod_idemp_l, P2. reflexivity.
    + intros q rq Hq Kq. rewrite ma_frontier'. destruct (N.eqb_spec rid q) as [<-|NE]; [rewrite Hr in Hq; inversion Hq; subst rq; rewrite Kq in K; discriminate|].
      pose proof (ir_brkfront q rq Hq Kq) as F. rewrite ma_frontier in F. destruct (N.eqb_spec rid q); [congruence| exact F].
    + split; [lia|]. split; [intros _; discriminate|]. intros q o E. inversion E. subst q o. exists r.
      split; [exact Hr|]. split; [right; exact K|]. split; [lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, P2; reflexivity|].
      split; [unfold PGSZ in *; lia| intros _; exact K].
  - destruct IA; constructor; cbn -[frontier PGSZ]; try assumption.
    intros a0 ar Ha. destruct (ia_areas a0 ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
    exists rq. split; [exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
    rewrite ma_frontier'. rewrite ma_frontier in F. destruct (N.eqb_spec rid (fst a0)); lia.
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End META_ADV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma frontier_full X st L rid r :
  inv_R X st L -> c_avail_meta_area_count (s_ctx st) = 0 -> s_regions st !! rid = Some r -> frontier st rid r = r_len r.
Proof.
  intros IR Hc Hr. unfold frontier. destruct (c_avail_meta_areas (s_ctx st)) as [[q off]|] eqn:E; [| reflexivity].
  destruct (N.eqb_spec q rid) as [->|NE]; [| reflexivity].
  destruct (ir_cursor _ _ _ IR) as (_ & _ & C3). destruct (C3 _ _ E) as (r' & Hr' & _ & _ & _ & Eq & _).
  rewrite Hr in Hr'. inversion Hr'. subst r'. rewrite Hc in Eq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEW_META.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKMeta r len st).
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                              (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Let L' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas ((r, len, 0) :: ld_metas L) L.

#[using="CE X L BL LS INV len rid"] Lemma nm_n : n = 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) /\ 2 <= n.
Proof.
  pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0. unfold n. rewrite Z.shiftl_mul_pow2 by exact S0.
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. split; [lia|].
  pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (s_ctx st))). lia.
Qed.

#[using="CE X L BL LS INV rid"] Lemma nm_len : 0 < len < LEN_MAX.
Proof.
  destruct nm_n as [En N2]. unfold len. split; [unfold PGSZ; lia|].
  destruct (ir_shift _ _ _ (proj1 INV)) as [S0 [S1|(q & rq & Hq & K & E)]].
  - unfold n. rewrite S1. change (Z.shiftl 2 0 * PGSZ) with 8192. unfold LEN_MAX. lia.
  - pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hq) as (A1 & _ & _ & _ & A5 & _). pose proof (round_up_ge (r_len rq)).
    rewrite En. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite E in *. ceil_bounds. unfold LEN_MAX, PGSZ in *. nia.
Qed.

#[using="CE X L BL LS INV n len"] Lemma nm_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
#[using="Type"] Lemma nm_lookup q : s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKMeta r len) else s_regions st !! q.
Proof. unfold st2, st1. cbn -[new_region]. apply lookup_new_region. Qed.
#[using="CE X L BL LS INV"] Lemma nm_keep q rq : s_regions st !! q = Some rq -> s_regions st2 !! q = Some rq.
Proof. intros H. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite nm_fresh in H; discriminate| exact H]. Qed.
#[using="Type"] Lemma nm_some q rq : s_regions st2 !! q = Some rq -> (q = rid /\ rq = mkRegion RKMeta r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma nm_frontier q rq : frontier st2 q rq = if (rid =? q)%N then PGSZ else r_len rq.
Proof. reflexivity. Qed.
#[using="CE X L BL LS INV Hcnt"] Lemma nm_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="CE X BL LS INV rid"] Lemma nm_event_pre : event_pre L (EMmap 0 len PROT_NONE MAPF).
Proof. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| exact nm_len]. Qed.

#[using="INV Hcnt HOK NERR"] Theorem INVL_new_meta : INVL X st2 L' BL LS /\ 0 < c_avail_meta_area_count (s_ctx st2)
  /\ c_init_done (s_ctx st2) = c_init_done (s_ctx st) /\ AM_frame st st2.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
  destruct nm_n as [En N2]. pose proof nm_len as [L0 L1].
  assert (LPG : len mod PGSZ = 0) by (unfold len; apply Z_mod_mult).
  assert (RU : round_up_pg len = len).
  { unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
    rewrite Z.mod_opp_l_z; [lia| lia| ]. change (2 ^ 12) with 4096. exact LPG. }
  split; [| split; [cbn; lia| split; [reflexivity| constructor; cbn; auto; try reflexivity; [intros q rq H _; apply nm_keep; exact H| unfold rid; lia]]]].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_metas OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_groups OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_resv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_live OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas].
    + intros q rq Hq. unfold st2, st1. cbn -[new_region]. rewrite s_next_rid_new_region. apply nm_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
      rewrite RU. rewrite RU in RCEIL. split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros _. split; [exact LPG|]. unfold len, PGSZ in *. nia.
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply nm_some in H1 as [[-> ->]|[N1 H1]]; apply nm_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. rewrite RU in RFREE |- *. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D. rewrite RU in D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
    + exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|].
      change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
      cbn. apply Permutation_refl.
    + eapply Permutation_trans; [apply perm_skip; exact ir_metas|].
      change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
      cbn -[frontier PGSZ Z.div Z.sub]. rewrite nm_frontier, N.eqb_refl. replace (PGSZ / PGSZ - 1) with 0 by reflexivity. apply perm_skip.
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn.
      rewrite (nm_frontier_old q rq Hin). destruct (N.eqb_spec rid q) as [<-|]; [rewrite nm_fresh in Hin; discriminate| reflexivity].
    + intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]].
      * rewrite N.eqb_refl. cbn. split; [exists (c_meta_alloc_shift (s_ctx st) + 1); split; [pose proof (proj1 ir_shift); lia| unfold len; rewrite En; reflexivity]|].
        unfold len, PGSZ in *. split; [nia| reflexivity].
      * destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (nm_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence| reflexivity].
    + cbn. split; [pose proof (proj1 ir_shift); lia|]. right. exists rid, (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|].
      split; [reflexivity|]. cbn. unfold len. rewrite En. reflexivity.
    + intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
      * split; [apply nm_keep; exact Hq| auto].
      * apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
    + intros q1 q2 r1 r2 H1 H2 K1 K2. apply nm_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply nm_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
      exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + revert ir_brk. change (c_brk (s_ctx st2)) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply nm_keep; exact Hq| auto].
    + cbn. split; [lia|]. split; [intros _; discriminate|]. intros q off E. inversion E. subst q off.
      exists (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|]. cbn. split; [right; reflexivity|].
      split; [lia|]. split; [reflexivity|]. split; [unfold len; lia| reflexivity].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & K & NG). exists rq. split; [apply nm_keep; exact Hrq| auto].
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite nm_frontier. split; [apply nm_keep; exact Hq|]. split; [exact K|]. split; [exact M|]. split; [exact P|].
      rewrite (nm_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E|]; [| exact F]. exfalso. rewrite <- E, nm_fresh in Hq. discriminate.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
  - apply (inv_M_ext X st st2); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st2); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X st st2); [reflexivity| reflexivity| intros q rq Hq K E; apply nm_keep; exact Hq| exact (G1 m b ai Hb)].
    + exact G2.
    + exact G3.
    + intros q rq Hq K Ho. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq K Ho).
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply nm_keep; exact Hq| exact K].
  - apply (inv_S_ext X st st2 BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
Qed.
End NEW_META.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma INVL_brk_dead X st L L' BL LS :
  INVL X st L BL LS ->
  ld_resv L' = ld_resv L -> ld_groups L' = ld_groups L -> ld_metas L' = ld_metas L -> ld_brkreg L' = ld_brkreg L ->
  ld_brk L' = BPDead ->
  INVL X (upd_ctx (set_brk BrkDead) st) L' BL LS /\ AM_frame st (upd_ctx (set_brk BrkDead) st).
Proof.
  intros INV E1 E2 E3 E4 E5. destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  set (st' := upd_ctx (set_brk BrkDead) st).
  assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by reflexivity.
  split; [| constructor; cbn; auto; first [reflexivity| lia]].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[frontier]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try reflexivity.
    all: try (intros q rq H1 H2; rewrite FR; first [exact (ir_metalen q rq H1 H2)| exact (ir_brkfront q rq H1 H2)]).
    all: try (eapply Permutation_trans; [exact ir_metas|]; erewrite map_ext; [apply Permutation_refl|]; intros [q rq]; cbn -[frontier]; rewrite FR; reflexivity).
  - destruct IA; constructor; cbn -[frontier]; try assumption.
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma round_up_pg_mod x : round_up_pg x mod PGSZ = 0.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  pose proof (Z.div_mod (-x) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as B.
  replace (x + (- x) mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z_mod_mult.
Qed.
#[using="Type"] Lemma round_up_pg_id x : x mod PGSZ = 0 -> round_up_pg x = x.
Proof.
  intros H. unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H in D.
  replace (- x) with ((- (x / 4096)) * 4096) by lia. rewrite Z_mod_mult. lia.
Qed.

#[using="Type"] Lemma brk_pages_ok_facts st lo len :
  brk_pages_ok st lo len = true -> 0 < lo /\ lo + len <= alloc_ceiling /\ ranges_free (live_ranges st) lo len = true.
Proof.
  unfold brk_pages_ok. intros H. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. auto.
Qed.

#[using="Type"] Lemma regions_update_perm (st : mstate) rid r r' (F : N * region -> bool) :
  s_regions st !! rid = Some r -> F (rid, r) = false -> F (rid, r') = false ->
  Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F (map_to_list (<[rid := r']> (s_regions st)))).
Proof.
  intros H F1 F2.
  eapply Permutation_trans; [apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ H)|].
  eapply Permutation_trans; [| apply perm_filter; apply (map_to_list_delete _ rid r'); rewrite lookup_insert_eq; reflexivity].
  cbn. rewrite F1, F2. rewrite delete_insert_eq. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BRK_GROW.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let old : Z := conc st (rid, off).
Hypothesis HOK : brk_pages_ok st old PGSZ = true.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).

#[using="CE X BL LS INV Hbrk"] Lemma bg_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off /\ ld_brk L = BPLive
  /\ ld_brkreg L = Some (r_base r, off) /\ 0 < r_base r /\ r_base r mod PGSZ = 0 /\ off mod PGSZ = 0 /\ 2 * PGSZ <= off
  /\ old = r_base r + off.
Proof.
  pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [BP (r & Hr & K & E)].
  pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(left; exact K)) as [S7 S8].
  exists r. split; [exact Hr|]. split; [exact K|]. split; [exact E|]. split; [exact BP|].
  split; [rewrite <- E; apply (proj2 (ir_brkreg _ _ _ (proj1 INV) (r_base r) (r_len r))); exists rid, r; auto|].
  split; [exact S1|]. split; [exact S2|]. split; [rewrite <- E; exact S7|]. split; [rewrite <- E; exact S8|].
  unfold old, conc, get_region. rewrite Hr. reflexivity.
Qed.

Let L' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkreg (Some (old - off, off + PGSZ)) L.

#[using="Type"] Lemma bg_lookup q : s_regions st3 !! q = if (q =? rid)%N then option_map (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) (s_regions st !! rid) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[upd_region]. apply lookup_upd_region. Qed.
#[using="Type"] Lemma bg_frontier q rq : frontier st3 q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st3, adv. cbn. reflexivity. Qed.
#[using="CE X L BL LS INV Hcnt"] Lemma bg_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="CE X BL LS INV Hbrk"] Lemma bg_event_pre : event_pre L (EBrk (old + PGSZ)).
Proof.
  destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
  right. right. exists (r_base r), off. split; [exact BP|]. split; [exact BR|]. lia.
Qed.

#[using="INV Hbrk Hcnt HOK"] Theorem INVL_brk_grow : INVL X st3 L' BL LS
  /\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, off) 4096)
  /\ s_areas st3 !! (rid, off) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, off) k = None)
  /\ PGSZ <= off /\ off mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
  destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
  destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF).
  destruct (above_frontier X st L BL LS rid r (rid, off) INV Hr eq_refl ltac:(rewrite (bg_frontier_old _ _ Hr); cbn; lia)) as [NA NM].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  set (r' := mkRegion RKBrk (r_base r) (off + PGSZ)).
  assert (LK : forall q, s_regions st3 !! q = if (q =? rid)%N then Some r' else s_regions st !! q).
  { intros q. rewrite bg_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite Hr; cbn; rewrite K; reflexivity| reflexivity]. }
  assert (KEEP : forall q rq, s_regions st !! q = Some rq -> q <> rid -> s_regions st3 !! q = Some rq).
  { intros q rq Hq NE. rewrite LK. destruct (N.eqb_spec q rid); [congruence| exact Hq]. }
  assert (SOME : forall q rq, s_regions st3 !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq)).
  { intros q rq. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. }
  assert (KEEPG : forall q rq, s_regions st !! q = Some rq -> r_kind rq = RKGroup -> s_regions st3 !! q = Some rq).
  { intros q rq Hq Kq. apply KEEP; [exact Hq|]. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
  assert (KEEPM : forall q rq, s_regions st !! q = Some rq -> is_metakind rq -> exists rq', s_regions st3 !! q = Some rq' /\ is_metakind rq').
  { intros q rq Hq Kq. destruct (N.eq_dec q rid) as [->|NE]; [exists r'; rewrite LK, N.eqb_refl; split; [reflexivity| left; reflexivity]|].
    exists rq. split; [apply KEEP; assumption| exact Kq]. }
  assert (RU : round_up_pg (off + PGSZ) = off + PGSZ) by (apply round_up_pg_id; unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity).
  assert (RUo : round_up_pg off = off) by (apply round_up_pg_id; exact OM).
  assert (F3 : s_metas st3 = s_metas st /\ s_areas st3 = s_areas st /\ s_groups st3 = s_groups st /\ s_slots st3 = s_slots st
               /\ s_shadow st3 = s_shadow st /\ s_tick st3 = s_tick st /\ s_next_rid st3 = s_next_rid st /\ s_secret st3 = s_secret st
               /\ s_reserved st3 = s_reserved st /\ (forall h, get_head st3 h = get_head st h)
               /\ c_usage (s_ctx st3) = c_usage (s_ctx st) /\ c_bounces (s_ctx st3) = c_bounces (s_ctx st) /\ c_seq (s_ctx st3) = c_seq (s_ctx st)
               /\ c_mmap_counter (s_ctx st3) = c_mmap_counter (s_ctx st) /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st)
               /\ c_meta_alloc_shift (s_ctx st3) = c_meta_alloc_shift (s_ctx st) /\ c_secret (s_ctx st3) = c_secret (s_ctx st)
               /\ c_avail_meta (s_ctx st3) = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st)
               /\ c_meta_area_head (s_ctx st3) = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st3) = c_meta_area_tail (s_ctx st)
               /\ c_free_meta_head (s_ctx st3) = c_free_meta_head (s_ctx st) /\ c_unmap_seq (s_ctx st3) = c_unmap_seq (s_ctx st)).
  { unfold st3, adv, st2, st1, upd_region, get_region. rewrite Hr. repeat split; try reflexivity. all: intros h; destruct h; reflexivity. }
  destruct F3 as (FM & FA & FG & FS & FSH & FT & FN & FSE & FRS & FH & FU & FB & FQ & FMC & FI & FSF & FSC & FAM & FAC & FMH & FMT & FFH & FUS).
  split; [| split; [reflexivity| split; [rewrite FA; exact NA| split; [rewrite FM; exact NM| split; [clear -O2; unfold PGSZ in *; lia| split; [exact OM| split; [exact FI|]]]]]]].
  2:{ constructor; rewrite ?FG, ?FS, ?FSH, ?FT, ?FB, ?FQ, ?FMC, ?FN; auto; try reflexivity; try lia.
      - intros sc. exact (FH (LActive sc)).
      - intros sc. unfold usage, ctx. rewrite FU. reflexivity. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_metas OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_groups OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_resv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_live OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkreg].
    + intros q rq Hq. rewrite FN.
      apply SOME in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids _ _ Hq)].
    + intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
      pose proof (ir_shape _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6).
      split; [lia|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [ceil_bounds; unfold LEN_MAX, PGSZ in *; lia|]. split; [unfold PGSZ in *; lia|].
      intros _. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity| lia].
    + intros q1 q2 r1 r2 H1 H2 NE.
      assert (GROW : forall q rq, s_regions st !! q = Some rq -> q <> rid ->
                let '(b2, l2) := region_live_range rq in r_base r + PGSZ + (round_up_pg (off + PGSZ) - PGSZ) <= b2 \/ b2 + l2 <= r_base r + PGSZ).
      { intros q rq Hq NEq. pose proof (ir_disj rid q r rq Hr Hq ltac:(congruence)) as D. unfold region_live_range in D at 1. rewrite K, E, RUo in D.
        pose proof (ranges_free_regions st _ _ q rq PF Hq) as D2. rewrite Eold in D2.
        pose proof (ir_shape q rq Hq) as (T1 & _ & T3 & _). pose proof (round_up_ge (r_len rq)) as T4.
        assert (NB : r_kind rq <> RKBrk) by (intros Kq; apply NEq; exact (ir_brk1 q rid rq r Hq Hr Kq K)).
        unfold region_live_range in *. destruct (r_kind rq); [congruence| |]; rewrite RU; unfold PGSZ in *; lia. }
      apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. pose proof (GROW q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (GROW q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn. lia.
    + rewrite FRS. exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|]. apply Permutation_map.
      change (s_regions st3) with (s_regions st1). unfold st1, upd_region, get_region. rewrite Hr. cbn -[map_to_list].
      apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity.
    + eapply Permutation_trans; [exact ir_metas|].
      eapply Permutation_trans; [| apply Permutation_map; change (s_regions st3) with (s_regions st1); unfold st1, upd_region, get_region; rewrite Hr; cbn -[map_to_list];
                                   apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity].
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. apply In_map_to_list_regions in Hin. cbn in Hk. cbn [fst snd].
      rewrite (bg_frontier_old q rq Hin), bg_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite Hr in Hin; inversion Hin; subst rq; rewrite K in Hk; discriminate| reflexivity].
    + intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite (bg_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|].
      exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
    + rewrite FSF. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
      exists q, rq. split; [apply KEEP; [exact Hq| intros ->; rewrite Hr in Hq; inversion Hq; subst; congruence]| auto].
    + intros b l. split.
      * intros Eb. inversion Eb. subst b l. exists rid, r'. split; [rewrite LK, N.eqb_refl; reflexivity|]. cbn. repeat split; auto. lia.
      * intros (q & rq & Hq & Kq & Eb & El). apply SOME in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; f_equal; f_equal; lia|].
        exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
    + intros q1 q2 r1 r2 H1 H2 K1 K2.
      apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
      * exfalso. apply N2. exact (ir_brk1 q2 rid r2 r H2 Hr K2 K).
      * exfalso. apply N1. exact (ir_brk1 q1 rid r1 r H1 Hr K1 K).
      * exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + change (c_brk (s_ctx st3)) with (BrkLive rid (off + PGSZ)). split; [exact BP|]. exists r'. rewrite LK, N.eqb_refl. cbn. auto.
    + change (c_avail_meta_area_count (s_ctx st3)) with (1 - 1). change (c_avail_meta_areas (s_ctx st3)) with (Some (aadd (rid, off) 4096)).
      split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists r'. rewrite LK, N.eqb_refl.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity|].
      cbn. split; [unfold PGSZ; lia| intros; lia].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply KEEPG; assumption|]. split; [exact Kq|]. rewrite FG. exact NG.
  - destruct IA; constructor; rewrite ?FA, ?FM, ?FSE, ?FU, ?FB, ?FQ, ?FMC, ?FI, ?FSC, ?FAM, ?FAC, ?FMH, ?FMT, ?FUS; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
      destruct (KEEPM _ _ Hq Kq) as (rq' & Hq' & Kq'). exists rq'. rewrite bg_frontier. split; [exact Hq'|]. split; [exact Kq'|]. split; [exact M|]. split; [exact P|].
      rewrite (bg_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|NE1].
      * rewrite <- E1, Hr in Hq. inversion Hq. subst rq. lia.
      * rewrite LK in Hq'. destruct (N.eqb_spec (fst a) rid); [congruence|]. rewrite Hq in Hq'. inversion Hq'. subst. lia.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). destruct (KEEPM _ _ Hrq Kq) as (rq' & Hq' & Kq'). exists rq'. auto.
    + intros sc Hsc. unfold usage, ctx. rewrite FU. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply (gcnt_ext st st3 FG FM).
    + intros sc g. unfold active, ctx in FH. rewrite <- !get_head_active, (FH (LActive sc)). apply ia_active_keys.
  - apply (inv_M_ext X st st3); [exact FM| exact FG| exact IM].
  - apply (inv_L_ext st st3); [exact FM| exact FG| exact FH| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor; rewrite ?FG.
    + intros m b ai Hb. apply (group_ok_ext X st st3); [exact FM| exact FS| intros q rq Hq Kq _; apply KEEPG; assumption| exact (G1 m b ai Hb)].
    + exact G2.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !(MR_ext st st3 FM). eapply G3; eassumption.
    + intros q rq Hq Kq Ho. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m.
      rewrite (hosts_ext st st3 FG), (MR_ext st st3 FM). auto.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply KEEPG; assumption| exact Kq].
  - apply (inv_S_ext X st st3 BL); [exact FM| exact FG| exact FS| exact IS].
  - apply (inv_SH_view' st st3 BL FSH FT KEEPG FG FS FM ISH).
Qed.
End BRK_GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BRK_FIRST.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis Hcur : brk0_answer_ok cur = true.
Let base : Z := round_up_pg cur.
Hypothesis HOK : brk_pages_ok st base (2 * PGSZ) = true.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).
Variable L0 : mled.
Hypothesis HL0 : ld_resv L0 = ld_resv L /\ ld_groups L0 = ld_groups L /\ ld_metas L0 = ld_metas L.
Let L' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph BPLive (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkreg (Some (base, 2 * PGSZ)) L0).

#[using="HOK"] Lemma bf_base : 0 < base /\ base mod PGSZ = 0 /\ base + 2 * PGSZ <= alloc_ceiling /\ ranges_free (live_ranges st) base (2 * PGSZ) = true.
Proof.
  destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF). split; [exact P0|]. split; [apply round_up_pg_mod|]. auto.
Qed.

#[using="CE X L BL LS cur INV base"] Lemma bf_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
#[using="CE X L BL LS INV Hbrk"] Lemma bf_nobrk q rq : s_regions st !! q = Some rq -> r_kind rq <> RKBrk.
Proof. pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [_ NB]. apply NB. Qed.
#[using="Type"] Lemma bf_lookup q : s_regions st3 !! q = if (q =? rid)%N then Some (mkRegion RKBrk base (2 * PGSZ)) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[new_region Z.mul]. apply lookup_new_region. Qed.
#[using="CE X L BL LS INV"] Lemma bf_keep q rq : s_regions st !! q = Some rq -> s_regions st3 !! q = Some rq.
Proof. intros H. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite bf_fresh in H; discriminate| exact H]. Qed.
#[using="Type"] Lemma bf_some q rq : s_regions st3 !! q = Some rq -> (q = rid /\ rq = mkRegion RKBrk base (2 * PGSZ)) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma bf_frontier q rq : frontier st3 q rq = if (rid =? q)%N then PGSZ + 4096 else r_len rq.
Proof. reflexivity. Qed.
#[using="CE X L BL LS INV Hcnt"] Lemma bf_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="L INV Hbrk Hcnt HOK HL0"] Theorem INVL_brk_first : INVL X st3 L' BL LS
  /\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, PGSZ) 4096)
  /\ s_areas st3 !! (rid, PGSZ) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, PGSZ) k = None)
  /\ PGSZ <= PGSZ /\ PGSZ mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
  destruct bf_base as (B0 & BM & BC & BF). destruct HL0 as (HL1 & HL2 & HL3).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (NA : s_areas st !! (rid, PGSZ) = None).
  { destruct (s_areas st !! (rid, PGSZ)) as [ar|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _) & _). cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
  assert (NM : forall k, 0 <= k < NSLOTS -> s_metas st !! mslot (rid, PGSZ) k = None).
  { intros k Hk. destruct (s_metas st !! mslot (rid, PGSZ) k) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em). destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _) & _).
    unfold mslot, aadd in Em. inversion Em. rewrite <- H0 in Hr'. cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
  assert (RU : round_up_pg (2 * PGSZ) = 2 * PGSZ) by reflexivity.
  split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [lia| split; [reflexivity| split; [reflexivity|]]]]]]].
  2:{ constructor; cbn -[Z.mul]; auto; try reflexivity; [intros q rq H _; apply bf_keep; exact H| unfold rid; lia]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_metas OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_groups OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_resv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_live OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph]; rewrite ?HL1, ?HL2, ?HL3.
    + intros q rq Hq. change (s_next_rid st3) with (N.succ (s_next_rid st)). apply bf_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply bf_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn -[Z.mul]. rewrite RU.
      split; [exact B0|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold PGSZ, LEN_MAX; lia|]. split; [exact BC|]. intros _. split; [apply Z_mod_mult| lia].
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn -[Z.mul]. rewrite RU. pose proof (ranges_free_regions st _ _ q2 r2 BF H2) as D. destruct (region_live_range r2) as [b2 l2]. unfold PGSZ in *. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 BF H1) as D. destruct (region_live_range r1) as [b1 l1]. cbn -[Z.mul]. rewrite RU. unfold PGSZ in *. lia.
    + exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|].
      change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
      cbn -[Z.mul map_to_list]. apply Permutation_refl.
    + eapply Permutation_trans; [exact ir_metas|].
      change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
      cbn -[frontier PGSZ Z.div Z.sub Z.mul map_to_list].
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn [fst snd].
      rewrite (bf_frontier_old q rq Hin), bf_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite bf_fresh in Hin; discriminate| reflexivity].
    + intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (bf_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq K).
    + cbn. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
      exists q, rq. split; [apply bf_keep; exact Hq| auto].
    + intros b l. split.
      * intros Eb. inversion Eb. subst b l. exists rid, (mkRegion RKBrk base (2 * PGSZ)). split; [rewrite bf_lookup, N.eqb_refl; reflexivity|]. cbn. auto.
      * intros (q & rq & Hq & Kq & Eb & El). apply bf_some in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq Kq).
    + intros q1 q2 r1 r2 H1 H2 K1 K2.
      apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
      * exfalso. exact (bf_nobrk q2 r2 H2 K2).
      * exfalso. exact (bf_nobrk q1 r1 H1 K1).
      * exfalso. exact (bf_nobrk q1 r1 H1 K1).
    + cbn -[Z.mul]. split; [reflexivity|]. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl. cbn. auto.
    + cbn -[Z.mul]. split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl.
      split; [reflexivity|]. split; [left; reflexivity|]. cbn -[Z.mul]. unfold PGSZ. split; [lia|]. split; [reflexivity|]. split; [lia| intros; lia].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply bf_keep; exact Hrq| auto].
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite bf_frontier. split; [apply bf_keep; exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
      rewrite (bf_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|]; [| exact F]. exfalso. rewrite <- E1, bf_fresh in Hq. discriminate.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
  - apply (inv_M_ext X st st3); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st3); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X st st3); [reflexivity| reflexivity| intros q rq Hq Kq E; apply bf_keep; exact Hq| exact (G1 m b ai Hb)].
    + exact G2.
    + exact G3.
    + intros q rq Hq Kq Ho. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq Kq Ho).
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply bf_keep; exact Hq| exact Kq].
  - apply (inv_S_ext X st st3 BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
Qed.
End BRK_FIRST.

End WithCeil.
End MI_WAMeta.

(* [comment removed for export] *)
Module MI_WAMeta2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

#[using="Type"] Lemma INVL_am_init X st L BL LS : INVL X st L BL LS ->
  INVL X (am_init st) L BL LS /\ c_init_done (s_ctx (am_init st)) = 1 /\ AM_frame st (am_init st).
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 (Some m)) Post.

#[using="KS"] Lemma am_take_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
  intros INV AF LF HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

#[using="KS"] Lemma am_carve_ft s p L LS : INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

#[using="KN KS"] Lemma am_finish_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
  ftree L (am_finish st true k bail) Post.
Proof.
  intros INV AF LF HC HI.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

#[using="KN KS"] Lemma am_after_brk_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
  intros INV AF LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

#[using="Type"] Lemma lbrk_pages_ok_ext L1 L2 lo len :
  ld_resv L1 = ld_resv L2 -> ld_groups L1 = ld_groups L2 -> ld_metas L1 = ld_metas L2 -> ld_brkreg L1 = ld_brkreg L2 ->
  lbrk_pages_ok L1 lo len = lbrk_pages_ok L2 lo len.
Proof. intros E1 E2 E3 E4. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4. reflexivity. Qed.

#[using="KN KS"] Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 LF.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    eapply KS; [exact INV1| | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPGuard cur) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph BPDead (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.

End WithCeil.
End MI_WAMeta2.

(* [comment removed for export] *)
Module MI_WCreate.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Bits OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WKill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma res_excl a o : a mod 16 = 0 -> 12 <= o mod 16 -> ~ (a <= o < a + 12).
Proof.
  intros Ha Ho [H1 H2]. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod o 16 ltac:(lia)) as Do.
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)) as Bo. rewrite Ha in Da.
  set (qa := a / 16) in *. set (qo := o / 16) in *. set (r := o mod 16) in *. clearbody qa qo r. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma one5_iff_create (A B E : Prop) (C D : Prop) : one5 A B False False E -> ~ C -> ~ D -> one5 A B C D E.
Proof. unfold one5. tauto. Qed.

Section CREATE.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m p : aptr) (ai : Z) (mr' : meta).
Hypothesis INV : INVL X st L BL LS.
Hypothesis IDLE : In m (x_idle X).

(* [comment removed for export] *)
Let sc' := m_sizeclass mr'.
Let last' := m_last_idx mr'.
Let cnt := last' + 1.
Let stride' := get_stride mr'.
Hypothesis R_prev : m_prev mr' = None.
Hypothesis R_next : m_next mr' = None.
Hypothesis R_mem : m_mem mr' = Some p.
Hypothesis R_freeable : m_freeable mr' = 1.
Hypothesis R_maplen : 0 <= m_maplen mr'.
Hypothesis R_li : 0 <= last' <= 31.
Hypothesis R_ai : 0 <= ai <= last'.
Hypothesis R_full0 : sc' = 0 -> ai = last'.
Hypothesis R_sc : (0 <= sc' < 48 /\ m_maplen mr' <= 256) \/ (sc' = 63 /\ last' = 0 /\ m_maplen mr' <> 0).
Hypothesis R_masks : 0 <= m_avail mr' /\ 0 <= m_freed mr'
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit (m_freed mr') i = true -> i <= last')
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> tbit (m_freed mr') i = true -> False)
  /\ (forall i, ai < i <= last' -> tbit (m_freed mr') i = true).
Hypothesis R_stride : sc' < 48 ->
  (stride' <= UNIT * size_class sc' \/ 28 <= sc') /\ (last' = 0 -> m_maplen mr' <> 0 /\ 27 <= sc') /\ stride' * cnt < 2^20.
Hypothesis R_stride16 : 16 <= stride' /\ stride' mod 16 = 0.
Hypothesis R_align : 0 <= snd p /\ snd p mod UNIT = 0.

(* [comment removed for export] *)
Hypothesis X_fresh : x_fresh X' = Some m \/ (sc' = 63 /\ x_fresh X' = x_fresh X).
Hypothesis X_fresh_old : x_fresh X = None.
Hypothesis X_idle : forall x, In x (x_idle X') -> In x (x_idle X) /\ x <> m.
Hypothesis X_zomb : x_zomb X' = x_zomb X.
Hypothesis X_nozomb : x_zomb X = [].
Hypothesis X_part : forall i, 0 <= i <= last' ->
  one5 (tbit (m_avail mr') i = true) (tbit (m_freed mr') i = true) False False (x_pend X' = Some (fst p, snd p + UNIT + stride' * i)).
Hypothesis X_pend' : forall s, x_pend X' = Some s -> exists i, 0 <= i <= last' /\ s = (fst p, snd p + UNIT + stride' * i).
(* [comment removed for export] *)
Hypothesis NOPART : ai < last' -> LS (LActive sc') = [].

(* [comment removed for export] *)
Hypothesis SITE :
  (m_maplen mr' <> 0 /\ snd p = 0 /\ x_orph X = Some (fst p) /\ x_orph X' = None /\ x_pend X = None
     /\ exists r, s_regions st !! (fst p) = Some r /\ r_kind r = RKGroup /\ m_maplen mr' * 4096 = round_up_pg (r_len r)
        /\ snd p + UNIT + stride' * cnt <= m_maplen mr' * 4096)
  \/ (m_maplen mr' = 0 /\ x_pend X = Some p /\ x_pend X' = None /\ x_orph X' = x_orph X /\ x_orph X = None
     /\ exists pm ip bpm, s_slots st !! p = Some (pm, ip) /\ hosts st bpm pm /\ fst bpm = fst p /\ 0 <= ip <= m_last_idx (MR st pm)
        /\ p = (fst bpm, sstart (MR st pm) ip)
        /\ snd p + UNIT + stride' * cnt <= sstart (MR st pm) ip + get_stride (MR st pm)
        /\ sc' < m_sizeclass (MR st pm) < 48 /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
        /\ (exists v3, known st (fst p, snd p - 3) v3 /\ Z.land v3 31 = ip /\ 0 <= v3 < 256)
        /\ known st (fst p, snd p - 2) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 0)
        /\ known st (fst p, snd p - 1) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 1)
        /\ 0 <= (snd p - snd bpm - UNIT) / UNIT < 2^16).

(* [comment removed for export] *)
Hypothesis SH_hdr0 : forall i, 0 <= i <= cnt -> known st (fst p, snd p + UNIT + stride' * i - IB) 0.
Hypothesis SH_ghdr : forall o v tk, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, tk) -> (tk < s_tick st)%N.

(* [comment removed for export] *)
Hypothesis E_metas : s_metas st' = <[m := mr']> (s_metas st).
Hypothesis E_groups : s_groups st' = <[p := mkGhdr (Some m) ai]> (s_groups st).
Hypothesis E_slots : forall s, s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride' =? 0) && ((snd s - snd p - UNIT) / stride' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride') else s_slots st !! s.
Hypothesis E_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Hypotheses (E_regions : s_regions st' = s_regions st) (E_areas : s_areas st' = s_areas st) (E_next_rid : s_next_rid st' = s_next_rid st)
           (E_tick : s_tick st' = s_tick st) (E_secret : s_secret st' = s_secret st) (E_reserved : s_reserved st' = s_reserved st).
Hypothesis E_ctx :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st)
  /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st)
  /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st) /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st)
  /\ c_active (s_ctx st') = c_active (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st).
Hypothesis E_mc : 0 <= c_mmap_counter (s_ctx st') < 2^32.
Hypothesis E_usage : forall sc0, 0 <= sc0 < 48 -> usage st' sc0 = usage st sc0 + (if sc0 =? sc' then cnt else 0).
Hypothesis E_usage_keys : forall sc0 v, c_usage (s_ctx st') !! sc0 = Some v -> 0 <= sc0 < 48.

(* [comment removed for export] *)
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Ltac slim := try clear SITE; try clear E_ctx; try clear E_slots; try clear X_part; try clear X_pend'; try clear R_masks; try clear R_stride; try clear R_sc;
             try clear E_usage; try clear E_usage_keys; try clear SH_hdr0; try clear SH_ghdr; try clear X_idle; try clear NOPART.
Local Tactic Notation "lia" := slim; Lia.lia.
Local Tactic Notation "nia" := slim; Lia.nia.

#[using="CE X L BL LS INV IDLE IM"] Lemma m_meta0 : s_metas st !! m = Some meta0. Proof. exact (proj1 (im_idle _ _ _ IM m IDLE)). Qed.
#[using="CE X st L BL INV IDLE IM"] Lemma m_unlisted h : ~ In m (LS h). Proof. intros H. apply (proj2 (im_idle _ _ _ IM m IDLE)). exists h. exact H. Qed.
#[using="CE X L BL LS INV IDLE IM"] Lemma MRm : MR st m = meta0. Proof. unfold MR, get_meta_rec. rewrite m_meta0. reflexivity. Qed.
#[using="CE X L BL LS INV IDLE"] Lemma m_not_live : ~ live_group st m. Proof. exact (idle_not_live _ _ _ _ _ INV m IDLE). Qed.

#[using="E_metas"] Lemma C_MR x : MR st' x = if aptr_eqb x m then mr' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="mr' E_metas"] Lemma C_MR_other x : x <> m -> MR st' x = MR st x. Proof. intros NE. rewrite C_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="st E_metas"] Lemma C_MR_m : MR st' m = mr'. Proof. rewrite C_MR, aptr_eqb_refl. reflexivity. Qed.
#[using="CE X X' L BL LS m p ai mr' INV IDLE sc' last' cnt stride' R_li R_ai R_sc R_masks R_stride R_stride16 R_align X_fresh SITE E_metas E_ctx E_mc IM"] Lemma C_keys x : s_metas st' !! x <> None <-> s_metas st !! x <> None.
Proof. rewrite E_metas. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite lookup_insert_eq, m_meta0; split; discriminate| rewrite lookup_insert_ne by congruence; tauto]. Qed.

(* [comment removed for export] *)
#[using="CE X X' L BL LS mr' INV sc' last' cnt stride' SITE IR IM IS"] Lemma p_free : s_groups st !! p = None.
Proof.
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & _)].
  - destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). apply NG. reflexivity.
  - destruct Hpm as [aipm Hpm]. pose proof (is_part _ _ _ IS _ _ _ ip Hpm Hip) as P. cbn zeta in P.
    rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm)), <- Ep, HP in P. unfold one5 in P.
    destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.

#[using="E_groups"] Lemma C_groups b : s_groups st' !! b = if aptr_eqb b p then Some (mkGhdr (Some m) ai) else s_groups st !! b.
Proof. rewrite E_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="ai E_groups"] Lemma C_hosts b x : hosts st' b x <-> (b = p /\ x = m) \/ (b <> p /\ hosts st b x).
Proof.
  unfold hosts. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
  - split; [intros [a H]; inversion H; auto| intros [[_ ->]|[NE _]]; [exists ai; reflexivity| congruence]].
  - split; [intros H; right; auto| intros [[E _]|[_ H]]; [congruence| exact H]].
Qed.
#[using="CE X X' L BL LS m p ai mr' INV sc' last' cnt stride' SITE E_groups IR IM IS"] Lemma C_hosts_old b x : hosts st b x -> hosts st' b x.
Proof. intros H. apply C_hosts. destruct (aptr_eq_dec b p) as [->|NE]; [| right; auto]. destruct H as [a H]. rewrite p_free in H. discriminate. Qed.
#[using="CE X L BL LS INV IDLE"] Lemma C_hosts_old_ne b x : hosts st b x -> x <> m.
Proof. intros H ->. exact (m_not_live (ex_intro _ b H)). Qed.
#[using="CE X L BL LS m mr' INV IDLE E_metas"] Lemma C_MR_hosted b x : hosts st b x -> MR st' x = MR st x.
Proof. intros H. apply C_MR_other. exact (C_hosts_old_ne b x H). Qed.

(* [comment removed for export] *)
#[using="R_mem"] Lemma gbase' : gbase mr' = p. Proof. unfold gbase. rewrite R_mem. reflexivity. Qed.
#[using="R_mem"] Lemma sstart' i : sstart mr' i = snd p + UNIT + stride' * i. Proof. unfold sstart. rewrite gbase'. reflexivity. Qed.
#[using="R_mem"] Lemma slot' i : slot_start' mr' i = (fst p, snd p + UNIT + stride' * i). Proof. rewrite slot_start'_sstart, gbase', sstart'. reflexivity. Qed.

(* [comment removed for export] *)
Definition nslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j).
#[using="R_stride16 E_slots"] Lemma C_slots s : (s_slots st' !! s = s_slots st !! s /\ ~ nslot s) \/ (exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j) /\ s_slots st' !! s = Some (m, j)).
Proof.
  unfold nslot. pose proof (E_slots s) as ES. destruct R_stride16 as [SP SM]. clear - ES SP SM. subst cnt last'.
  rewrite ES. clear ES. set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod stride' =? 0) && (d / stride' <? m_last_idx mr' + 1)) eqn:E.
  - right. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / stride'). split; [split; [apply Z.div_pos; lia| exact E4]|]. split; [| reflexivity].
    pose proof (Z.div_mod d stride' ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. lia.
  - left. split; [reflexivity|]. intros (j & Hj & Es). subst s. cbn in d.
    assert (Ed : d = stride' * j) by (unfold d; lia). clearbody d.
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod stride' =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult). rewrite E3 in E. cbn in E.
    assert (E4 : (d / stride' <? m_last_idx mr' + 1) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia). rewrite E4 in E. discriminate.
Qed.
#[using="m R_stride16 E_slots"] Lemma C_slots_old s : ~ nslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros N. destruct (C_slots s) as [[E _]|(j & Hj & Es & _)]; [exact E|]. exfalso. apply N. exists j. auto. Qed.
#[using="st R_stride16 E_slots"] Lemma C_slots_new j : 0 <= j < cnt -> s_slots st' !! (fst p, snd p + UNIT + stride' * j) = Some (m, j).
Proof.
  intros Hj. destruct (C_slots (fst p, snd p + UNIT + stride' * j)) as [[_ N]|(j' & Hj' & Es & E)]; [exfalso; apply N; exists j; auto|].
  rewrite E. inversion Es. destruct R_stride16 as [SP _]. assert (j' = j) by (clear - H0 SP Hj Hj'; nia). subst. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="R_stride16"] Lemma new_key_range j : 0 <= j < cnt -> snd p < snd p + UNIT + stride' * j /\ snd p + UNIT + stride' * j + 16 <= snd p + UNIT + stride' * cnt.
Proof. intros Hj. destruct R_stride16 as [SP _]. clear - Hj SP. subst cnt last'. unfold UNIT. split; [nia|]. assert (stride' * j + stride' <= stride' * (m_last_idx mr' + 1)) by nia. lia. Qed.

#[using="CE X X' L BL LS INV sc' R_stride16 SITE IR IM IG IS"] Lemma old_slot_not_new s x i : s_slots st !! s = Some (x, i) -> ~ nslot s.
Proof.
  intros Hs (j & Hj & ->). destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es. inversion Es.
  destruct (new_key_range j Hj) as [K1 K2].
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hf & Hip & Ep & FIT & _)].
  - (* [comment removed for export] *)
    destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx]. rewrite (NG bx) in Hxx; [discriminate|]. rewrite <- H0. reflexivity.
  - (* [comment removed for export] *)
    destruct Hpm as [aipm Hpm'].
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Ep in H0; cbn in H0; congruence).
    assert (Hi2 : 0 <= i <= m_last_idx (MR st x) + 1) by (clear - Hi; lia).
    pose proof (@sep_hdr0 _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi2) as D.
    rewrite sstart_succ in D. rewrite Ep in H1, K1, K2, FIT. cbn in H1, K1, K2, FIT.
    assert (NEQ : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->. clear - H1 K1. lia. }
    specialize (D NEQ). clear - D H1 K1 K2 FIT Hj. lia.
Qed.

#[using="CE X X' L BL LS INV sc' R_stride16 R_align SITE IR IM IG IS"] Lemma old_hosts_not_new b x : hosts st b x -> ~ nslot b.
Proof.
  intros Hx N. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO).
  destruct (Z.eq_dec (m_maplen (MR st x)) 0) as [Hml|Hml].
  - destruct (g_nest _ _ _ _ _ _ GO Hml) as (px & ix & Hs & _). exact (old_slot_not_new _ _ _ Hs N).
  - destruct (g_top _ _ _ _ _ _ GO Hml) as [B0 _]. destruct N as (j & Hj & ->). cbn in B0. destruct (new_key_range j Hj) as [K1 K2]. destruct R_align as [A0 _]. clear - B0 K1 A0. lia.
Qed.

#[using="R_stride16"] Lemma p_not_new : ~ nslot p.
Proof. intros (j & Hj & E). destruct (new_key_range j Hj) as [K _]. apply (f_equal snd) in E. cbn in E. clear - K E. lia. Qed.

#[using="CE X X' st L LS INV sc' R_stride16 SITE IR IM IG IS"] Lemma blk_not_new k : In k BL -> ~ nslot (bslot k).
Proof. intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). exact (old_slot_not_new _ _ _ Hs). Qed.

(* [comment removed for export] *)
#[using="CE X X' L BL LS INV sc' R_stride16 R_align SITE IR IM IG IS"] Lemma new_not_group j : 0 <= j < cnt -> s_groups st !! (fst p, snd p + UNIT + stride' * j) = None.
Proof.
  intros Hj. destruct (s_groups st !! (fst p, snd p + UNIT + stride' * j)) as [h|] eqn:E; [| reflexivity]. exfalso.
  destruct (im_hdr _ _ _ IM _ _ E) as (x & Ex & _). apply (old_hosts_not_new (fst p, snd p + UNIT + stride' * j) x); [| exists j; auto].
  destruct h as [hm ha]. cbn in Ex. subst hm. exists ha. exact E.
Qed.

#[using="CE X X' L BL LS m p ai INV IDLE stride' SITE E_metas E_groups IR IM IS"] Lemma gcnt_C sc0 : gcnt st' sc0 = (if sc' =? sc0 then cnt else 0) + gcnt st sc0.
Proof.
  rewrite !gcnt_unfold, E_groups.
  rewrite (zsum_perm _ _ (Permutation_map (gterm st' sc0) (map_to_list_insert (s_groups st) p (mkGhdr (Some m) ai) p_free))). cbn.
  unfold gterm at 1. cbn. rewrite C_MR_m. fold sc' cnt. f_equal.
  f_equal. apply map_ext_in. intros [b hb] Hin. apply In_map_to_list_regions in Hin || (apply (proj2 (list_elem_of_In _ _)) in Hin; apply elem_of_map_to_list in Hin).
  unfold gterm. cbn. destruct (g_meta hb) as [x|] eqn:Ex; [| reflexivity].
  rewrite (C_MR_other x); [reflexivity|]. intros ->.
  destruct (im_hdr _ _ _ IM _ _ Hin) as (x' & Ex' & Hmem & _). rewrite Ex in Ex'. inversion Ex'. subst x'. rewrite MRm in Hmem. discriminate.
Qed.

#[using="E_ctx"] Lemma C_get_head h : get_head st' h = get_head st h.
Proof.
  destruct E_ctx as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _). destruct h; cbn; unfold active, ctx; rewrite ?F11, ?F3; reflexivity.
Qed.
#[using="E_ctx"] Lemma C_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. destruct E_ctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _). unfold frontier. rewrite F10. reflexivity. Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV ISH"] Lemma C_TK u hl : r_hav (get_shadow st (fst p)) !! u = Some hl -> hl_ticks hl (s_tick st).
Proof.
  intros Hu ch Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn in Hu.
  - exact (proj1 (proj2 (ish_ticks _ _ ISH _ _ E)) u hl ch Hu Hin).
  - rewrite lookup_empty in Hu. discriminate.
Qed.
#[using="CE X L BL LS INV R_align E_shadow ISH"] Lemma C_read_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros Hq. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst q) E_shadow). apply (cell_read_hdr_havoc_out p st (proj2 R_align) C_TK q Hq). Qed.
#[using="CE X L BL LS INV R_align E_shadow ISH"] Lemma C_known_out q v : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
#[using="CE X L BL LS INV R_align E_shadow ISH"] Lemma C_unknown_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
#[using="st mr' sc' last' cnt stride' R_align SH_ghdr E_shadow E_next_rid E_tick"] Lemma C_unknown_hdr o : 0 <= o < 12 -> unknown st' (fst p, snd p + o).
Proof.
  intros Ho. unfold unknown, SHd. cbn [fst snd]. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst p) E_shadow).
  apply (cell_read_hdr_havoc_in p st (proj2 R_align) (fst p, snd p + o)); [reflexivity| cbn; lia|].
  cbn [fst snd]. intros v tk H. apply (SH_ghdr (snd p + o) v tk); [clear - Ho; lia| exact H].
Qed.

#[using="CE X st' L BL LS p mr' INV sc' last' cnt stride' R_stride16 R_align E_next_rid E_tick IM IG"] Lemma hdr0_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

#[using="CE X X' L BL LS m p ai mr' INV sc' last' cnt stride' R_li R_ai R_sc R_masks R_stride R_stride16 R_align X_fresh SITE SH_ghdr E_shadow E_next_rid E_tick E_ctx E_mc ISH"] Lemma C_unknown_any q : unknown st q -> unknown st' q.
Proof.
  intros U. destruct (N.eq_dec (fst q) (fst p)) as [E|NE]; [| apply C_unknown_out; [tauto| exact U]].
  destruct (Z.lt_ge_cases (snd q) (snd p)) as [L1|G1]; [apply C_unknown_out; [lia| exact U]|].
  destruct (Z.lt_ge_cases (snd q) (snd p + 12)) as [L2|G2]; [| apply C_unknown_out; [lia| exact U]].
  replace q with (fst p, snd p + (snd q - snd p)) by (destruct q; cbn in *; subst; f_equal; lia). apply C_unknown_hdr. lia.
Qed.

#[using="CE X L BL LS p INV R_align E_shadow ISH"] Lemma C_known_res q v : 12 <= snd q mod 16 -> known st q v -> known st' q v.
Proof. intros R K. apply C_known_out; [| exact K]. intros [_ H]. exact (res_excl _ _ (proj2 R_align) R H). Qed.

(* [comment removed for export] *)
#[using="CE X X' L LS mr' INV sc' last' cnt stride' SITE IR IM IG IS"] Lemma blk_clear k x i : In k BL -> s_slots st !! bslot k = Some (x, i) -> fst (bslot k) = fst p ->
  snd (bslot k) + get_stride (MR st x) - IB <= snd p \/ snd p + 12 <= snd (bslot k) - IB.
Proof.
  intros Hk Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  destruct SITE as [(Hml & P0 & HO & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hfp & Hip & Ep & _)].
  - exfalso. destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx].
    rewrite (NG bx) in Hxx; [discriminate|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ a Hxx)) in Es. rewrite Es in Hf. exact Hf.
  - destruct Hpm as [aipm Hpm']. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es.
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Es, Ep in Hf; cbn in Hf; exact Hf).
    pose proof (is_part _ _ _ IS _ _ _ i (proj2 (hosts_ok _ _ _ IG _ _ Hx) ) Hi) as P5 || pose proof I as P5.
    destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx).
    pose proof (is_part _ _ _ IS _ _ _ i Hbx Hi) as Q5. cbn zeta in Q5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx), <- Es in Q5. unfold one5 in Q5.
    assert (U : In (bslot k) (map bslot BL)) by (apply in_map; exact Hk).
    assert (NH2 : s_groups st !! (fst bx, sstart (MR st x) i) = None).
    { rewrite <- Es. apply none_of. intros Hh. destruct Q5 as (_ & _ & _ & _ & _ & _ & _ & _ & nCD & _). apply nCD. split; [exact U| exact Hh]. }
    assert (NE : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->.
      pose proof (is_part _ _ _ IS _ _ _ ip Hpm' Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm')), <- Ep, HP in P.
      unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity].
      pose proof (hosts_inj _ _ _ IM _ _ _ Hx (ex_intro _ aipm Hpm')) as Ebx. rewrite Ebx in Es. rewrite Ep, <- Es. exact U. }
    pose proof (@sep_ext _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi NE NH2) as D.
    rewrite !sstart_succ in D. rewrite Es. cbn [snd]. rewrite Ep. cbn [snd].
    pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ aipm Hpm')) as [SGp _]. unfold IB, UNIT in *. clear - D SGp. lia.
Qed.

#[using="X st m p ai mr' INV IDLE sc' last' cnt stride' R_prev R_next R_mem R_freeable R_maplen R_li R_ai R_full0 R_sc R_masks R_stride R_stride16 R_align X_fresh X_fresh_old X_idle X_zomb X_nozomb X_part X_pend' NOPART SITE SH_hdr0 SH_ghdr E_metas E_groups E_slots E_shadow E_regions E_areas E_next_rid E_tick E_secret E_reserved E_ctx E_mc E_usage E_usage_keys IR IA IM IL IG IS ISH"] Theorem INVL_create : INVL X' st' L BL LS.
Proof.
  destruct E_ctx as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  destruct R_masks as (W1 & W2 & W3 & W4 & W5 & W6). destruct R_stride16 as [SP SM]. destruct R_align as [P0 P16].
  assert (XO : forall rid, x_orph X' = Some rid -> x_orph X = Some rid /\ m_maplen mr' = 0).
  { intros rid Ho. destruct SITE as [(_ & _ & _ & HO' & _)|(Hml & _ & _ & HO' & _)]; [rewrite HO' in Ho; discriminate| rewrite HO' in Ho; auto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?E_regions, ?E_next_rid, ?E_reserved, ?F6, ?F7, ?F10, ?F15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite C_frontier. reflexivity.
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_brkfront rid r H1 H2).
    + intros rid Ho. destruct (XO rid Ho) as [Ho' Hml]. destruct (ir_orph rid Ho') as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
      intros b Hb. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [| exact (NG b Hb)]. exfalso.
      destruct SITE as [(Hml' & _)|(_ & _ & _ & _ & HO0 & _)]; [exact (Hml' Hml)| rewrite HO0 in Ho'; discriminate].
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?E_regions, ?E_areas, ?E_secret, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14; try assumption.
    + destruct ia_ctx as (_ & C2 & C3 & C4). split; [exact E_mc|]. auto.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite C_frontier. auto.
    + intros x mr Hx. assert (K : s_metas st' !! x <> None) by congruence. apply C_keys in K. destruct (s_metas st !! x) as [mr0|] eqn:E; [| congruence]. exact (ia_metas x mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply C_keys in K. apply K. apply Hk. exact Hk2.
    + intros sc0 Hsc0. rewrite (E_usage sc0 Hsc0), (ia_usage sc0 Hsc0), gcnt_C. rewrite Z.eqb_sym. destruct (sc' =? sc0); lia.
  - (* [comment removed for export] *) destruct IM as [Q1 Q2 Q3 Q4 Q5] eqn:EIM; constructor.
    + intros x Hx. destruct (aptr_eq_dec x m) as [E|NE]; [subst x; rewrite C_MR_m, R_mem in Hx; discriminate|]. rewrite (C_MR_other x NE) in Hx |- *. exact (Q1 x Hx).
    + intros x b Hx. rewrite X_zomb. destruct (aptr_eq_dec x m) as [E|NE].
      * subst x. rewrite C_MR_m, R_mem in Hx. inversion Hx. subst b. left. apply C_hosts. left. auto.
      * rewrite (C_MR_other x NE) in Hx. destruct (Q2 x b Hx) as [H|H]; [left; apply C_hosts_old; exact H| right; exact H].
    + intros b h. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
      * intros E. inversion E. subst h. exists m. cbn. rewrite C_MR_m, R_mem. fold last'. auto.
      * intros Hb. destruct (Q3 b h Hb) as (x & Ex & Hmem & Hai). exists x.
        assert (NEx : x <> m) by (intros ->; rewrite MRm in Hmem; discriminate). rewrite (C_MR_other x NEx). auto.
    + intros x Hx. destruct (X_idle x Hx) as [Hx' NE]. destruct (Q4 x Hx') as [E NI]. split; [| exact NI]. rewrite E_metas, lookup_insert_ne by congruence. exact E.
    + intros z Hz. rewrite X_zomb, X_nozomb in Hz. destruct Hz.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. rewrite C_get_head. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite C_MR_other; try reflexivity; intros ->; apply (m_unlisted h); rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros x. destruct (aptr_eqb_spec x m) as [->|NE].
      * rewrite C_MR_m, R_next, R_prev. split; [| reflexivity]. split; [intros [h H]; exfalso; exact (m_unlisted h H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (C_MR_other x NE). apply L5.
    + intros x Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE). apply L6. exact Hx.
    + intros sc x Hx. destruct (L7 sc x Hx) as (A1 & [b Hb] & A3).
      destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE).
      split; [exact A1|]. split; [exists b; apply C_hosts_old; exact Hb| exact A3].
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros x b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * (* [comment removed for export] *)
        intros E. inversion E. subst x aix. constructor; rewrite ?C_MR_m, ?E_regions; fold sc' last' stride'.
        -- apply C_keys. rewrite m_meta0. discriminate.
        -- exact R_li.
        -- exact R_ai.
        -- destruct R_sc as [A|(A1 & A2 & A3)]; [left; exact A| right]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros [h H]. exact (m_unlisted h H).
        -- exact R_freeable.
        -- exact R_maplen.
        -- exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 W6))))).
        -- intros NF Hlt. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)|]. destruct R_sc as [[A _]|(_ & L0 & _)]; unfold sc' in *; lia.
        -- intros NF Hsc NI. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- intros NF sc Hin Hnh. exfalso. exact (m_unlisted _ Hin).
        -- exact R_stride.
        -- intros NF Hsc LT. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- exact (conj P0 P16).
        -- intros Hml. destruct SITE as [(_ & B0 & _ & _ & _ & r & Hr & Hk & Hlen & Hend)|(Hml0 & _)]; [| exfalso; exact (Hml Hml0)].
           split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact Hend.
        -- intros Hml. destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & FIT & Hsc & Hstr & _)]; [exfalso; exact (Hml1 Hml)|].
           exists pm, ip. rewrite (C_MR_hosted _ _ Hpm). split; [rewrite C_slots_old; [exact Hs| exact p_not_new]|].
           rewrite (hosts_gbase _ _ _ IM _ _ Hpm). split; [exact Hf|]. split; [| split; [exact Hsc| exact Hstr]].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact FIT.
        -- exact R_full0.
      * (* [comment removed for export] *)
        intros Hb. pose proof (G1 x b aix Hb) as GO. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        pose proof (C_hosts_old_ne _ _ Hx) as NEx. assert (NF : x_fresh X <> Some x) by (rewrite X_fresh_old; discriminate).
        assert (NF' : x_fresh X' <> Some x) by (destruct X_fresh as [XF|[_ XF]]; rewrite XF; [congruence| rewrite X_fresh_old; discriminate]).
        destruct GO; constructor; rewrite ?(C_MR_other x NEx), ?E_regions; try assumption.
        -- apply C_keys. exact g_present.
        -- intros _. exact (g_partial NF).
        -- intros _. exact (g_unlisted NF).
        -- intros _. exact (g_rest NF).
        -- intros _. exact (g_under NF).
        -- intros Hml. destruct (g_nest Hml) as (px & ix & Hs & REST). exists px, ix.
           destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
           split; [rewrite C_slots_old; [exact Hs| exact (old_slot_not_new _ _ _ Hs)]| exact REST].
    + intros b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb]; [discriminate| exact (G2 b aix)].
    + intros m1 m2 b1 b2 ai1 ai2. rewrite !C_groups.
      destruct (aptr_eqb_spec b1 p) as [->|N1]; destruct (aptr_eqb_spec b2 p) as [->|N2].
      * intros E1 E2. inversion E1. inversion E2. subst. reflexivity.
      * intros E1 H2. inversion E1. subst m1 ai1. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai2 H2)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H2) ltac:(rewrite X_fresh_old; discriminate) P2) as IN. rewrite <- Esc, (NOPART P1) in IN. exact IN.
      * intros H1 E2. inversion E2. subst m2 ai2. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai1 H1)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H1) ltac:(rewrite X_fresh_old; discriminate) P1) as IN. rewrite Esc, (NOPART P2) in IN. exact IN.
      * intros H1 H2. rewrite (C_MR_hosted _ _ (ex_intro _ ai1 H1)), (C_MR_hosted _ _ (ex_intro _ ai2 H2)). exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2).
    + intros rid r Hr Hk Ho. rewrite E_regions in Hr.
      destruct (N.eq_dec rid (fst p)) as [->|NE].
      * destruct SITE as [(Hml & B0 & HO & _)|(Hml & _ & _ & HO' & HO & _)].
        -- exists m. split; [apply C_hosts; left; split; [destruct p; cbn in B0 |- *; subst; reflexivity| reflexivity]|]. rewrite C_MR_m. exact Hml.
        -- destruct (G4 (fst p) r Hr Hk ltac:(rewrite HO; discriminate)) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
      * assert (Ho0 : x_orph X <> Some rid).
        { destruct SITE as [(_ & _ & HO & _)|(_ & _ & _ & HO' & HO & _)]; [rewrite HO; congruence| rewrite HO; discriminate]. }
        destruct (G4 rid r Hr Hk Ho0) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
    + intros b h. rewrite C_groups, E_regions. destruct (aptr_eqb_spec b p) as [->|NEb]; [| exact (G5 b h)]. intros _.
      destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & _)]; [exists r; auto|].
      destruct Hpm as [a Hpm]. destruct (G5 _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto.
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s x i Hs. destruct (C_slots s) as [[Es NS]|(j & Hj & -> & Es)].
      * rewrite Es in Hs. destruct (S1' s x i Hs) as ([b Hb] & Hi & E). rewrite (C_MR_hosted _ _ Hb). split; [exists b; apply C_hosts_old; exact Hb| auto].
      * rewrite Es in Hs. inversion Hs. subst x i. rewrite C_MR_m. fold last'. split; [exists p; apply C_hosts; left; auto|]. split; [lia|]. rewrite slot'. reflexivity.
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite slot'. apply C_slots_new. fold last' in Hi. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. rewrite C_slots_old; [exact (S2 b x i Hx Hi)|].
        apply (old_hosts_not_new_slot b x i Hx Hi) || (intros N; destruct N as (j & Hj & E); exact (old_slot_not_new _ _ _ (S2 b x i Hx Hi) (ex_intro _ j (conj Hj E)))).
    + intros b x aix i. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * intros E Hi. inversion E. subst x aix. rewrite C_MR_m in Hi |- *. cbn zeta. rewrite slot', C_groups. fold last' in Hi.
        pose proof (X_part i Hi) as P5.
        eapply one5_iff_create; [exact P5| |]; cbn.
        -- intros Hin. apply in_map_iff in Hin as (k & Ek & Hk). apply (blk_not_new k Hk). exists i. split; [clear -Hi; lia| exact Ek].
        -- destruct (aptr_eqb_spec (fst p, snd p + UNIT + stride' * i) p) as [Eip|NE]; [exfalso; apply p_not_new; exists i; split; [clear -Hi; lia| symmetry; exact Eip]|].
           rewrite (new_not_group i ltac:(clear -Hi; lia)). intros H; apply H; reflexivity.
      * intros Hb Hi. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        rewrite (C_MR_hosted _ _ Hx) in Hi |- *. cbn zeta. rewrite C_groups.
        pose proof (S3 b x aix i Hb Hi) as P5. cbn zeta in P5.
        set (s := slot_start' (MR st x) i) in *.
        assert (NSs : ~ nslot s) by (apply (old_slot_not_new s x i); exact (S2 b x i Hx Hi)).
        destruct (aptr_eqb_spec s p) as [Esp|NEsp].
        -- (* [comment removed for export] *)
           destruct SITE as [(_ & B0 & _ & _ & HPX & _)|(_ & HPX & HPX' & _)].
           ++ exfalso. rewrite Esp in *. pose proof (S2 b x i Hx Hi) as Hs. fold s in Hs. rewrite Esp in Hs.
              destruct (S1' _ _ _ Hs) as ([bb Hbb] & _ & Eps). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbb) in Eps.
              pose proof (sstart0 _ _ _ IM _ _ Hbb). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbb ltac:(lia)).
              destruct (hosts_ok _ _ _ IG _ _ Hbb) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0) as [A00 _].
              apply (f_equal snd) in Eps. cbn in Eps. unfold UNIT in *. clear - B0 Eps H H0 A00. lia.
           ++ rewrite Esp in P5 |- *. rewrite HPX in P5. rewrite HPX'.
              revert P5. unfold one5. clear. intros P5.
              assert (NN : ~ (@None aptr = Some p)) by discriminate. assert (SS : Some (mkGhdr (Some m) ai) <> None) by discriminate.
              tauto.
        -- eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P5].
           split.
           ++ intros HPs. exfalso. destruct SITE as [(_ & _ & _ & _ & HPX & _)|(_ & HPX & _)]; rewrite HPX in HPs; [discriminate| inversion HPs; exact (NEsp (eq_sym H0))].
           ++ intros HPs. exfalso. destruct (X_pend' _ HPs) as (j & Hj & Ej). apply NSs. exists j. split; [fold last' in Hj; lia| exact Ej].
    + intros s Hs. destruct (X_pend' _ Hs) as (j & Hj & ->). rewrite C_slots_new; [discriminate| fold last' in Hj; lia].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (x & i & Hs & REST). exists x, i.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hbx] & _). rewrite (C_MR_hosted _ _ Hbx).
      split; [rewrite C_slots_old; [exact Hs| exact (blk_not_new k Hk)]| exact REST].
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (REGp : exists r, s_regions st !! fst p = Some r /\ r_kind r = RKGroup).
    { destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & [a Hpm] & Hf & _)]; [exists r; auto|].
      destruct (ig_region _ _ _ IG _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto. }
    constructor.
    + intros rid sh. rewrite E_shadow, E_regions. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst p)) as [->|NE].
      * intros _. exact REGp.
      * rewrite lookup_insert_ne by congruence. exact (D1 rid sh).
    + intros rid sh Hsh. rewrite E_tick. rewrite E_shadow in Hsh. exact (TKS_hdr_havoc st p D2 rid sh Hsh).
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite sstart'. apply C_known_out; [| apply SH_hdr0; unfold cnt_of in Hi; fold last' cnt in Hi; exact Hi].
        cbn. intros [_ H]. unfold IB, UNIT in H. destruct (Z.eq_dec i 0) as [->|NZ]; [lia|]. unfold cnt_of in Hi. assert (stride' * 1 <= stride' * i) by nia. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. apply C_known_res; [cbn; rewrite (hdr0_res _ _ i Hx); lia| exact (D3 b x i Hx Hi)].
    + intros b x o Hx Ho. apply C_hosts in Hx as [[-> ->]|[NEb Hx]]; [apply C_unknown_hdr; exact Ho| apply C_unknown_any; exact (D4 b x o Hx Ho)].
    + intros b x px ix Hx Hml Hs. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * (* [comment removed for export] *)
        rewrite C_MR_m in Hml. rewrite (C_slots_old p p_not_new) in Hs.
        destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs0 & Hpm & Hf & Hip & Ep & _ & _ & _ & (v3 & K3 & E3 & R3) & K2 & K1 & Q)]; [exfalso; exact (Hml1 Hml)|].
        rewrite Hs0 in Hs. inversion Hs. subst px ix. rewrite (C_MR_hosted _ _ Hpm), (hosts_gbase _ _ _ IM _ _ Hpm). cbn zeta.
        split; [exists v3; split; [apply C_known_out; [cbn; lia| exact K3]| auto]|].
        split; [apply C_known_out; [cbn; lia| exact K2]|]. split; [apply C_known_out; [cbn; lia| exact K1]| exact Q].
      * rewrite (C_MR_hosted _ _ Hx) in Hml. rewrite (C_slots_old b (old_hosts_not_new _ _ Hx)) in Hs.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
        destruct (D5 b x px ix Hx Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
        destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx). pose proof (g_align _ _ _ _ _ _ GOx) as [A0 A16]. unfold UNIT in A16.
        assert (RS : forall d r, 0 <= r < 16 -> d = r - 16 -> 12 <= r -> 12 <= (snd b + d) mod 16).
        { intros d r Hr -> H12. pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as Db. rewrite A16 in Db.
          replace (snd b + (r - 16)) with (r + (snd b / 16 - 1) * 16) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. exact H12. }
        split; [exists v3; split; [apply C_known_res; [cbn; replace (snd b - 3) with (snd b + (13 - 16)) by lia; apply (RS _ 13); lia| exact K3]| auto]|].
        split; [apply C_known_res; [cbn; replace (snd b - 2) with (snd b + (14 - 16)) by lia; apply (RS _ 14); lia| exact K2]|].
        split; [apply C_known_res; [cbn; replace (snd b - 1) with (snd b + (15 - 16)) by lia; apply (RS _ 15); lia| exact K1]| exact Q].
    + intros k x i Hk Hs. rewrite (C_slots_old _ (blk_not_new k Hk)) in Hs.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es). rewrite (C_MR_hosted _ _ Hx).
      pose proof (D6 k x i Hk Hs) as B. cbn zeta in B |- *. destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      (* [comment removed for export] *)
      assert (OUT : forall o, snd (bslot k) - IB <= o < snd (bslot k) + get_stride (MR st x) - IB -> ~ (fst (bslot k) = fst p /\ snd p <= o < snd p + 12)).
      { intros o Ho [Hf Hin]. pose proof (blk_clear k x i Hk Hs Hf) as D. unfold IB in *. clear - Ho Hin D. lia. }
      destruct (is_blocks _ _ _ IS k Hk) as (x' & i' & Hs' & Hoff & Hn & Hfit). rewrite Hs in Hs'. inversion Hs'. subst x' i'.
      pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG _]. unfold IB, UNIT in *.
      assert (K : forall o v, snd (bslot k) - 4 <= o < snd (bslot k) + get_stride (MR st x) - 4 -> known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v).
      { intros o v Ho Ko. apply C_known_out; [apply (OUT o Ho)| exact Ko]. }
      split; [apply K; [lia| exact A1]|]. split; [apply K; [lia| exact A2]|]. split; [apply K; [lia| exact A3]|]. split; [apply K; [lia| exact A4]|].
      split; [exact A5|]. split.
      * intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). split; [apply K; [lia| exact B1]|]. split; [apply K; [lia| exact B2]|]. split; [apply K; [lia| exact B3]|].
        split; [apply K; [lia| exact B4]|]. split; [apply K; [lia| exact B5]| exact B6].
      * split; [intros Hr; apply K; [lia| apply A7; exact Hr]|]. intros a Ha. apply C_unknown_any. apply A8. exact Ha.
Qed.

End CREATE.

End WithCeil.
End MI_WCreate.

(* [comment removed for export] *)
Module MI_WCreate2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WCreate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
#[using="Type"] Lemma land31_id x : 0 <= x <= 31 -> Z.land x 31 = x.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land63_id x : 0 <= x <= 63 -> Z.land x 63 = x.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land52_id x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma one5_A (A B E : Prop) : A -> ~ B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
#[using="Type"] Lemma one5_B (A B E : Prop) : ~ A -> B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
#[using="Type"] Lemma one5_E (A B E : Prop) : ~ A -> ~ B -> E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.

#[using="Type"] Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.

#[using="Type"] Lemma known_noshadow st rid o : s_shadow st !! rid = None -> known st (rid, o) 0.
Proof. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st0 := hdr_havoc p st in
  let st1 := set_usage sc (usage st0 sc + cnt) st0 in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

#[using="Type"] Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).

#[using="Type"] Lemma agt_metas : s_metas st' = <[m := mr']> (s_metas st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_MR_m : MR st' m = mr'.
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
#[using="mr'"] Lemma agt_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma agt_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_rec3 :
  get_meta_rec (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p st) sc + cnt) (hdr_havoc p st)))) m = mr'.
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
  s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
#[using="Type"] Lemma agt_shadow : s_shadow st' = s_shadow (hdr_havoc p st). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_next_rid : s_next_rid st' = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_tick : s_tick st' = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_secret : s_secret st' = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_reserved : s_reserved st' = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_ctx : s_ctx st' = set_usage_map (<[sc := usage st sc + cnt]> (c_usage (s_ctx st))) (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
  unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
#[using="Type"] Lemma agt_active sc0 : active st' sc0 = active st sc0. Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_get_head h : get_head st' h = get_head st h. Proof. destruct h; reflexivity. Qed.

#[using="Type"] Lemma agt_TF0 : TF0 st -> TF0 st'.
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
#[using="Type"] Lemma agt_TW P : TW st P -> TW st' P.
Proof. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG_TOP.
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).

Let IM := proj1 (proj2 (proj2 INV)).
#[using="CEc idle0 L BL LS rid X INV IM"] Lemma top_MRm : MR st2 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.

#[using="INV"] Lemma top_INV3 : INVL X st3 L BL LS.
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.

#[using="CEc idle0 L BL LS rid X INV IM"] Lemma top_MR4 : MR st4 m = m_set_maplen ml meta0.
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.

#[using="GRP Hsc"] Lemma top_facts :
  let size := UNIT * size_class sc in
  let stride := get_stride mr' in
  1 <= cnt <= 32 /\ ml = needed / 4096 /\ 1 <= ml <= 256 /\ UNIT + stride * cnt <= ml * 4096
  /\ (stride <= size \/ 28 <= sc) /\ (cnt - 1 = 0 -> 27 <= sc) /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0
  /\ ml * 4096 = round_up_pg needed /\ 0 < needed
  /\ mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Proof.
  unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
  { cbv beta iota delta [mr' agG m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen meta0 m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
  assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
  { rewrite Emr. unfold get_stride. cbn. reflexivity. }
  cbn zeta. unfold ml in *.
  assert (RU : needed / 4096 * 4096 = round_up_pg needed).
  { destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
    pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. nia. }
  rewrite Es. repeat split; try assumption; try lia.
Qed.

#[using="r X INV Hr Kr Lr NS GRP Hsc Hai Hai0 EMP TF NIm IM"] Theorem ag_top_ok :
  INVL X' st' L BL LS /\ TF0 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) ai)
  /\ (forall sc0, active st' sc0 = active st2 sc0) /\ (forall h, get_head st' h = get_head st2 h)
  /\ s_tick st' = s_tick st2.
Proof.
  pose proof top_facts as TFX. cbn zeta in TFX. destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  pose proof top_INV3 as INV3. pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
  pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  assert (Sp : get_stride mr' > 0) by lia.
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Hai0.
    - left. lia.
    - unfold tbit. repeat split; try lia; assumption.
    - intros _. rewrite <- Emr. repeat split; lia.
    - rewrite <- Emr. lia.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X'].
      destruct (Z.le_gt_cases i ai).
      + apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
      + apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
      split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
      rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma set_metas_id st v : v = s_metas st -> Malloc.set_metas v st = st.
Proof. destruct st; cbn; intros ->; reflexivity. Qed.

Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
#[using="Type"] Lemma hdr3_all : forallb hdr3_f (zrange 0 32) = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma hdr3_facts i : 0 <= i <= 31 -> Z.land (Z.lor (Z.land i 31) 192) 255 = i + 192 /\ Z.land (i + 192) 31 = i.
Proof.
  intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Section AG_NESTED.
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="CEc idle0 L BL LS g bg idx p X INV IM"] Lemma nst_MRm : MR st1 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
#[using="aig Hg"] Lemma nst_hosts : hosts st1 bg g. Proof. exists aig. exact Hg. Qed.

#[using="NEST Hsc"] Lemma nst_facts :
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20
  /\ 16 <= size /\ size mod 16 = 0 /\ size_class j <= 127
  /\ mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0
  /\ get_stride mr' = size.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
  destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  pose proof (size_class_bound sc Hsc) as SB.
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
  { cbv beta iota delta [mr' agG m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail meta0 m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
  assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
  repeat split; try lia.
  - unfold size, UNIT. lia.
  - unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
  - exact Emr.
  - rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="aig INV Hg Hidx STR NEST Hsc TF mr'"] Lemma nst_layout :
  INVL X st2 L BL LS /\ ctrl_eq st1 st2 /\ s_tick st2 = s_tick st1
  /\ known st2 (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st2 (aadd p (-2)) (Z.land ((snd p - (snd bg + UNIT)) / UNIT) 255)
  /\ known st2 (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr ((snd p - (snd bg + UNIT)) / UNIT) 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st2 (aadd p (UNIT + k * size - 4)) 0)
  /\ st2 = wrs (nl_list st1 g bg idx size cnt) st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _).
  pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _).
  refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.

#[using="CEc idle0 L BL LS bg aig p X INV Hg Hidx STR NEST Hsc TF mr' IM"] Lemma nst_st3 : st3 = st2.
Proof.
  pose proof nst_layout as (INV2 & CE & _).
  unfold st3, upd_meta, put_meta. apply set_metas_id.
  assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
  rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.

#[using="aig X INV Hg Hidx SCg STR NEST Hsc EMP TF NIm IM"] Theorem ag_nested_ok :
  INVL X' st' L BL LS /\ TF2 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) (cnt - 1))
  /\ (forall sc0, active st' sc0 = active st1 sc0) /\ (forall h, get_head st' h = get_head st1 h)
  /\ s_tick st' = s_tick st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es).
  pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs).
  pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH).
  pose proof nst_st3 as E3.
  assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
  pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  rewrite Z.sub_diag in *.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
  pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
  pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
  assert (P16 : snd p mod 16 = 0).
  { unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
  pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
  assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
  assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
  { unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
  assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
  { pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
    destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT).
    rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
  assert (NH : s_groups st1 !! p = None).
  { pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
    destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - left. lia.
    - unfold tbit. repeat split; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
    - intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. repeat split; lia.
    - rewrite <- Emr, Es. lia.
    - unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
      destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists g, idx, bg. rewrite !MR2.
      split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
      split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
      split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
      split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
      split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
      split; [rewrite STR, SCg; reflexivity|].
      split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
      rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
      replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
      split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
      replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
    - rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
      apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
    - intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
      + rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
      + unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
        * cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
        * apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
          assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
    - unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
      rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - unfold st'. rewrite agt_shadow, E3. reflexivity.
    - unfold st'. rewrite agt_regions, E3. reflexivity.
    - unfold st'. rewrite agt_areas, E3. reflexivity.
    - unfold st'. rewrite agt_next_rid, E3. reflexivity.
    - unfold st'. rewrite agt_tick, E3. reflexivity.
    - unfold st'. rewrite agt_secret, E3. reflexivity.
    - unfold st'. rewrite agt_reserved, E3. reflexivity.
    - unfold st'. rewrite agt_ctx, E3. repeat split; reflexivity.
    - unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
  split; [exact INV'|]. split.
  { (* [comment removed for export] *)
    unfold TF2. unfold st'. rewrite E3.
    apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
    2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
    intros q [Hq|Hq].
    - apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
      + intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
        rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
      + intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
        intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
    - assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
      assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
      exists p, m. split; [exact Hm'|]. rewrite R'.
      unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
      + cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
        { destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
        destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
      + apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
        split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
        unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
  split; [exact MR'm|].
  split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma round_up_pg_div x : 0 < x -> (x + 4095) / 4096 * 4096 = round_up_pg x.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.

Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).

Section CREATE63.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).

#[using="CEc L BL LS rid X INV IM"] Lemma c63_MRg : MR st3 g = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.

#[using="Hn"] Lemma c63_ml : 1 <= ml < 2 ^ 52 /\ ml * 4096 = round_up_pg needed.
Proof.
  unfold ml. split; [| apply round_up_pg_div; lia].
  split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

#[using="Hn"] Lemma c63_F : F63 rid ml meta0 = mr'.
Proof.
  pose proof c63_ml as [M _]. cbv beta iota delta [F63 mr' m_set_freed m_set_avail m_set_maplen m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
  rewrite land52_id by lia. reflexivity.
Qed.

#[using="Hn"] Lemma c63_stride : get_stride mr' = ml * 4096 - UNIT.
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

#[using="CEc L BL LS g X INV IR"] Lemma c63_nogroup : s_groups st3 !! p = None.
Proof. destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG). apply NG. reflexivity. Qed.

#[using="CEc L BL LS X INV Hn IM"] Lemma c63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.

#[using="r X INV Hr Kr Lr NS Hn TF IR IM"] Theorem create63_ok :
  INVL X' st6 L BL LS /\ TF0 st6 /\ MR st6 g = mr' /\ s_groups st6 !! p = Some (mkGhdr (Some g) 0)
  /\ s_ctx st6 = s_ctx st3 /\ s_tick st6 = s_tick st3 /\ s_regions st6 = s_regions st3
  /\ get_stride mr' = ml * 4096 - UNIT /\ ml * 4096 = round_up_pg needed.
Proof.
  pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
  pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
  assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
  { change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
  assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
  assert (GAI : group_active_idx st4 p = 0).
  { unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
  assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
  { change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
  assert (INV' : INVL X' st6 L BL LS).
  { apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
    all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - right. lia.
    - unfold tbit. repeat split; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
    - lia.
    - fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - right. split; reflexivity.
    - reflexivity.
    - intros x Hx. destruct Hx.
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
      assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
    - intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
    - intros H. lia.
    - left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - exact Emetas.
    - exact Egroups.
    - intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
    - intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.

End WithCeil.
End MI_WCreate2.
