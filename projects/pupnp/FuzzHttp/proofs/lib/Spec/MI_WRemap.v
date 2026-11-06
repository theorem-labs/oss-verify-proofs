(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Ext2 MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_Ledger MI_WAMeta MI_WEnframe MI_WEnframe2 MI_WMalloc MI_WRealloc MRemapOp.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma shadow_cut_cells M r o : r_cells (shadow_cut M r) !! o = if o <? M then r_cells r !! o else None.
Proof.
  unfold shadow_cut; cbn. rewrite map_lookup_filter. destruct (r_cells r !! o) as [c|]; cbn; [| destruct (o <? M); reflexivity].
  rewrite option_guard_bool_decide. destruct (o <? M); reflexivity.
Qed.

Lemma cell_read_cut_lt M r o : o < M -> cell_read (shadow_cut M r) o = cell_read r o.
Proof. intros H. unfold cell_read. rewrite shadow_cut_cells. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma cell_read_cut_ge M r o v : M <= o -> cell_read (shadow_cut M r) o = Known v -> v = 0.
Proof.
  intros H. unfold cell_read. rewrite shadow_cut_cells. rewrite (proj2 (Z.ltb_ge _ _) H). cbn [r_hav r_havp shadow_cut].
  destruct (_ || _); intros E; inversion E; reflexivity.
Qed.

Lemma stale_weaken hl b t : stale hl b (Some t) = true -> stale hl b None = true.
Proof.
  unfold stale. rewrite !existsb_exists. intros ([c h] & Hin & Hb). exists (c, h). split; [exact Hin|].
  apply andb_prop in Hb as [Hb _]. cbn. rewrite Hb. reflexivity.
Qed.

Lemma cell_read_cut_unknown M r o h : cell_read r o = Unknown h -> exists h', cell_read (shadow_cut M r) o = Unknown h'.
Proof.
  intros E. unfold cell_read in *. rewrite shadow_cut_cells. cbn [r_hav r_havp shadow_cut].
  destruct (o <? M); [rewrite E; eexists; reflexivity|].
  destruct (r_cells r !! o) as [[v t]|]; [| rewrite E; eexists; reflexivity].
  destruct (stale_pg (r_havp r !! (o `div` 4096)) (Some t) || stale (default [] (r_hav r !! (o `div` 16))) (o `mod` 16) (Some t)) eqn:S; [| discriminate].
  apply orb_prop in S. assert (S' : stale_pg (r_havp r !! (o / 4096)) None || stale (default [] (r_hav r !! (o / 16))) (o mod 16) None = true).
  { destruct S as [S|S].
    - destruct (r_havp r !! (o / 4096)); [reflexivity| discriminate].
    - rewrite (stale_weaken _ _ _ S). apply orb_true_r. }
  rewrite S'. eexists. reflexivity.
Qed.

Lemma shadow_cut_ticks M r t : sh_ticks r t -> sh_ticks (shadow_cut M r) t.
Proof. intros [A B]. split; cbn; auto. Qed.

Lemma TKS_cut st rid M T : TKS st T -> TKS (upd_shadow rid (shadow_cut M) st) T.
Proof.
  intros TK q sh Hsh. unfold upd_shadow, set_shadow in Hsh. cbn [s_shadow] in Hsh.
  destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_insert_eq in Hsh. injection Hsh as <-. unfold get_shadow.
    destruct (s_shadow st !! rid) as [sh0|] eqn:E0; cbn [default].
    + destruct (TK rid sh0 E0) as (A & B & C). split; [| split; [exact B| exact C]].
      intros o w t Ho. rewrite shadow_cut_cells in Ho. destruct (o <? M); [eapply A; exact Ho| discriminate].
    + split; [| split; [intros ? ? ? H; cbn in H; rewrite lookup_empty in H; discriminate| intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate]].
      intros o w t Ho. rewrite shadow_cut_cells in Ho. destruct (o <? M); [cbn in Ho; rewrite lookup_empty in Ho|]; discriminate.
  - rewrite lookup_insert_ne in Hsh by congruence. exact (TK q sh Hsh).
Qed.

Section REBASE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (g : aptr) (dst nn on : Z).
Let rid : N := fst c.
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Hypothesis HO : x_orph X = None.
Hypothesis Hs : s_slots st !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (MR st g) = 63.
Hypothesis Hon : on = m_maplen (MR st g) * 4096.
Hypothesis D0 : 0 < dst.
Hypothesis DA : dst mod PGSZ = 0.
Hypothesis NA : nn mod PGSZ = 0.
Hypothesis N2 : 2 * PGSZ <= nn.
Hypothesis NL : nn < LEN_MAX.
Hypothesis DC : dst + nn <= s_ceil st.
Hypothesis RESV : ranges_free (s_reserved st) dst nn = true.
Hypothesis DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> rid ->
  let '(b2, l2) := region_live_range r2 in dst + nn <= b2 \/ b2 + l2 <= dst.

Let IR := proj1 INV.
Let IA := proj1 (proj2 INV).
Let IM := proj1 (proj2 (proj2 INV)).
Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Definition rb_st : mstate := rebase_st st rid g dst nn on.
Let r' : region := mkRegion RKGroup dst nn.
Let mg' : meta := m_set_maplen (nn / 4096) (MR st g).

#[using="X L BL LS INV Hs IS"] Lemma g_live : live_group st g /\ c = slot_start' (MR st g) 0.
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as (A & _ & B). auto. Qed.

#[using="X L BL dst nn INV Hs SC Hon IM IG IS"] Lemma g_facts : hosts st (rid, 0) g /\ c = (rid, 16) /\ m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ ~ in_list LS g
  /\ get_stride (MR st g) = on - UNIT /\ gbase (MR st g) = (rid, 0)
  /\ exists rg, s_regions st !! rid = Some rg /\ r_kind rg = RKGroup /\ on = round_up_pg (r_len rg).
Proof.
  destruct g_live as [[[br bo] Hbg] Ec].
  destruct (hosts_ok X st LS IG _ _ Hbg) as (ai & Hg & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & LI & ML & NIL)]; [rewrite SC in S48; lia|].
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & rg & Hrg & Krg & EML & _). cbn [fst snd] in B0, Hrg. subst bo.
  pose proof (slot_start'_eq X st LS IM g _ 0 Hbg) as E0. rewrite <- Ec in E0. cbn [fst] in E0.
  pose proof (hosts_gbase X st LS IM _ _ Hbg) as GB.
  assert (Ebr : br = rid) by (unfold rid; rewrite E0; reflexivity). subst br.
  split; [exact Hbg|]. split; [rewrite E0; unfold sstart; rewrite GB; cbn; rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
  split; [exact LI|]. split; [exact ML|]. split; [exact NIL|].
  split; [unfold get_stride; rewrite LI, (proj2 (Z.eqb_neq _ _) ML); cbn; rewrite Hon; reflexivity|].
  split; [exact GB|]. exists rg. rewrite Hon. auto.
Qed.

#[using="X L BL LS dst nn on INV Hs SC Hon D0 IM IG IS"] Lemma rid_groups : forall b m, hosts st b m -> fst b = rid -> m = g /\ b = (rid, 0).
Proof.
  destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg & Hrg & Krg & Eon).
  assert (NEST : forall n m b, hosts st b m -> fst b = rid -> m_sizeclass (MR st m) < 48 -> 48 - m_sizeclass (MR st m) <= Z.of_nat n -> False).
  { induction n as [|n IH]; intros m b Hb Fb S48 Hn.
    - pose proof (hosts_ok X st LS IG _ _ Hb) as (ai & _ & GO). destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & _)]; cbn in Hn; lia.
    - pose proof (hosts_ok X st LS IG _ _ Hb) as (ai & Hbb & GO).
      destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [M0|M0].
      + destruct (g_nest _ _ _ _ _ _ GO M0) as (p & i & Hsl & Fp & _ & [S1 S2] & _).
        destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([bp Hbp] & Hi & Eb).
        pose proof (hosts_gbase X st LS IM _ _ Hbp) as GBp. rewrite GBp in Fp.
        apply (IH p bp Hbp); [rewrite Fp; exact Fb| lia| lia].
      + destruct (g_top _ _ _ _ _ _ GO M0) as (B0 & _). destruct b as [br bo]; cbn in B0, Fb; subst bo br.
        pose proof (hosts_fun st _ _ _ Hb Hg) as ->. rewrite SC in S48. lia. }
  intros b m Hb Fb. pose proof (hosts_ok X st LS IG _ _ Hb) as (ai & Hbb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(S63 & _ & ML' & _)].
  - exfalso. apply (NEST (Z.to_nat 48) m b Hb Fb); lia.
  - destruct (g_top _ _ _ _ _ _ GO ML') as (B0 & _). destruct b as [br bo]; cbn in B0, Fb; subst bo br.
    split; [exact (hosts_fun st _ _ _ Hb Hg)| reflexivity].
Qed.

#[using="X L BL LS dst nn on INV Hs SC Hon D0 IM IG IS"] Lemma rid_slots : forall s m i, s_slots st !! s = Some (m, i) -> fst s = rid -> s = c /\ m = g /\ i = 0.
Proof.
  destruct g_facts as (Hg & Ec & LI & _).
  intros s m i Hsl Fs. destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq X st LS IM _ _ _ Hb) in Es.
  assert (Fb : fst b = rid) by (rewrite Es in Fs; exact Fs).
  destruct (rid_groups b m Hb Fb) as [-> ->]. rewrite LI in Hi. assert (i = 0) as -> by lia.
  split; [| auto]. rewrite Es, Ec. cbn. unfold sstart. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 g_facts))))))). cbn.
  rewrite Z.mul_0_r. reflexivity.
Qed.

#[using="X st L LS g dst nn on INV HP Hs SC Hon D0 IM IG IS"] Lemma rid_blocks : forall k, In k BL -> fst (bslot k) <> rid.
Proof.
  intros k Hk F. destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hsl & _). destruct (rid_slots _ _ _ Hsl F) as (E & _).
  destruct g_facts as (Hg & _). destruct Hg as [ai Hgg].
  pose proof (is_part _ _ _ IS _ _ _ 0 Hgg ltac:(rewrite (proj1 (proj2 (proj2 g_facts))); lia)) as P. cbn zeta in P.
  rewrite <- (proj2 g_live), HP in P. unfold one5 in P.
  assert (In c (map bslot BL)) by (rewrite <- E; apply in_map; exact Hk).
  assert (Some c = Some c) by reflexivity. tauto.
Qed.

#[using="X L BL LS g dst nn on INV Hs SC Hon D0 IM IG IS"] Lemma rid_nogroup : forall b h, s_groups st !! b = Some h -> fst b = rid -> b = (rid, 0).
Proof.
  intros b h Hb Fb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Hm & _). destruct h as [gm ai]; cbn in Hm; subst gm.
  exact (proj2 (rid_groups b m (ex_intro _ ai Hb) Fb)).
Qed.

Let st1 : mstate := rebase_ctrl st rid g dst nn.
#[using="Type"] Lemma RB_regions : s_regions rb_st = <[rid := r']> (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_metas : s_metas rb_st = <[g := mg']> (s_metas st).
Proof. unfold rb_st, rebase_st, rebase_ctrl. cbn -[upd_meta rebase_regions]. rewrite s_metas_upd_meta. reflexivity. Qed.
#[using="Type"] Lemma RB_groups : s_groups rb_st = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_slots : s_slots rb_st = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_areas : s_areas rb_st = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_ctx : s_ctx rb_st = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_tick : s_tick rb_st = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_next_rid : s_next_rid rb_st = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_secret : s_secret rb_st = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_reserved : s_reserved rb_st = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_ceil : s_ceil rb_st = s_ceil st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_st1_shadow : s_shadow st1 = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_st1_tick : s_tick st1 = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma RB_eq : rb_st = wr8 (rid, nn - 4) 0 (upd_shadow rid (shadow_cut (Z.min on nn)) st1). Proof. reflexivity. Qed.

#[using="Type"] Lemma RB_lookup q : s_regions rb_st !! q = if (q =? rid)%N then Some r' else s_regions st !! q.
Proof. rewrite RB_regions. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="Type"] Lemma RB_some q rq : s_regions rb_st !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite RB_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros E; inversion E; auto| auto]. Qed.
#[using="r'"] Lemma RB_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions rb_st !! q = Some rq.
Proof. intros H NE. rewrite RB_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.

#[using="Type"] Lemma RB_MR x : MR rb_st x = if aptr_eqb x g then mg' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite RB_metas. destruct (aptr_eqb_spec x g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="mg'"] Lemma RB_MR_other x : x <> g -> MR rb_st x = MR st x.
Proof. intros NE. rewrite RB_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma RB_MR_g : MR rb_st g = mg'. Proof. rewrite RB_MR, aptr_eqb_refl. reflexivity. Qed.

#[using="c dst rid D0 NA N2 NL"] Lemma nn_pages : nn / 4096 * 4096 = nn /\ 2 <= nn / 4096 /\ Z.land (nn / 4096) (2 ^ 52 - 1) = nn / 4096.
Proof.
  unfold PGSZ, LEN_MAX in *. pose proof (Z.div_mod nn 4096 ltac:(lia)). split; [lia|]. split; [nia|].
  change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. split; [nia|].
  apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

#[using="c dst rid D0 NA N2 NL"] Lemma mg'_fields : m_prev mg' = m_prev (MR st g) /\ m_next mg' = m_next (MR st g) /\ m_mem mg' = m_mem (MR st g)
  /\ m_avail mg' = m_avail (MR st g) /\ m_freed mg' = m_freed (MR st g) /\ m_last_idx mg' = m_last_idx (MR st g)
  /\ m_freeable mg' = m_freeable (MR st g) /\ m_sizeclass mg' = m_sizeclass (MR st g) /\ m_maplen mg' = nn / 4096.
Proof. unfold mg', m_set_maplen. cbn. repeat split; try reflexivity. apply (proj2 (proj2 nn_pages)). Qed.

#[using="D0 NA N2 NL mg'"] Lemma RBv x : m_prev (MR rb_st x) = m_prev (MR st x) /\ m_next (MR rb_st x) = m_next (MR st x) /\ m_mem (MR rb_st x) = m_mem (MR st x)
  /\ m_avail (MR rb_st x) = m_avail (MR st x) /\ m_freed (MR rb_st x) = m_freed (MR st x) /\ m_last_idx (MR rb_st x) = m_last_idx (MR st x)
  /\ m_freeable (MR rb_st x) = m_freeable (MR st x) /\ m_sizeclass (MR rb_st x) = m_sizeclass (MR st x)
  /\ gbase (MR rb_st x) = gbase (MR st x) /\ cnt_of (MR rb_st x) = cnt_of (MR st x).
Proof.
  rewrite RB_MR. destruct (aptr_eqb_spec x g) as [->|NE]; [| repeat split; reflexivity].
  pose proof mg'_fields as (A & B & C & D & E & F & G & H & I). unfold gbase, cnt_of. rewrite A, B, C, D, E, F, G, H. repeat split; reflexivity.
Qed.
#[using="D0 NA N2 NL mg'"] Lemma RB_maplen_g : m_maplen (MR rb_st g) = nn / 4096. Proof. rewrite RB_MR_g. apply mg'_fields. Qed.
#[using="X L BL LS INV Hs SC Hon D0 NA N2 NL IM IG IS mg'"] Lemma RB_stride_g : get_stride (MR rb_st g) = nn - UNIT.
Proof.
  rewrite RB_MR_g. unfold get_stride. pose proof mg'_fields as (_ & _ & _ & _ & _ & F & _ & _ & I). rewrite F, I.
  rewrite (proj1 (proj2 (proj2 g_facts))). cbn [Z.eqb]. pose proof nn_pages as (P & P2 & _).
  destruct (Z.eqb_spec (nn / 4096) 0); [lia|]. cbn. lia.
Qed.
#[using="mg'"] Lemma RB_stride_other x : x <> g -> get_stride (MR rb_st x) = get_stride (MR st x).
Proof. intros NE. rewrite RB_MR_other by exact NE. reflexivity. Qed.
#[using="X L BL LS INV Hs SC Hon D0 NA N2 NL IM IG IS mg'"] Lemma RB_sstart_g i : sstart (MR rb_st g) i = 16 + (nn - UNIT) * i.
Proof.
  unfold sstart. pose proof (RBv g) as (_ & _ & _ & _ & _ & _ & _ & _ & GB & _). rewrite GB, RB_stride_g.
  pose proof g_facts as (_ & _ & _ & _ & _ & _ & GB0 & _). rewrite GB0. cbn [snd]. unfold UNIT. lia.
Qed.
#[using="mg'"] Lemma RB_sstart_other x i : x <> g -> sstart (MR rb_st x) i = sstart (MR st x) i.
Proof. intros NE. unfold sstart. rewrite RB_MR_other by exact NE. reflexivity. Qed.

#[using="X L BL LS INV"] Lemma TKS0 : TKS st (s_tick st). Proof. exact (TKS_of _ _ _ _ _ INV). Qed.

#[using="st1"] Lemma RB_read_other q1 q2 : q1 <> rid -> cell_read (get_shadow rb_st q1) q2 = cell_read (get_shadow st q1) q2.
Proof.
  intros NE. rewrite RB_eq. rewrite (cell_read_wr8_other (rid, nn - 4) 0 _ (q1, q2)) by (intros E; injection E; congruence). cbn [fst snd].
  rewrite get_shadow_upd_shadow. destruct (N.eqb_spec q1 rid); [congruence|]. reflexivity.
Qed.
#[using="D0 DA NA N2 st1"] Lemma RB_read_lt o : o < Z.min on nn -> o <> nn - 4 -> cell_read (get_shadow rb_st rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros Ho NE. rewrite RB_eq. rewrite (cell_read_wr8_other (rid, nn - 4) 0 _ (rid, o)) by (intros E; injection E; lia). cbn [fst snd].
  rewrite get_shadow_upd_shadow, N.eqb_refl. apply cell_read_cut_lt. exact Ho.
Qed.
#[using="X L BL LS INV st1"] Lemma RB_read_end : cell_read (get_shadow rb_st rid) (nn - 4) = Known 0.
Proof.
  rewrite RB_eq. pose proof (cell_read_wr8_same (rid, nn - 4) 0 (upd_shadow rid (shadow_cut (Z.min on nn)) st1)) as E. cbn [fst snd] in E. rewrite E; [reflexivity|].
  rewrite get_shadow_upd_shadow, N.eqb_refl. apply shadow_cut_ticks. change (s_tick (upd_shadow _ _ st1)) with (s_tick st).
  change (get_shadow st1 rid) with (get_shadow st rid). apply sh_ticks_of. exact TKS0.
Qed.
#[using="st1"] Lemma RB_known_other q1 q2 v : q1 <> rid -> known rb_st (q1, q2) v <-> known st (q1, q2) v.
Proof. intros NE. unfold known, SHd. cbn [fst snd]. rewrite RB_read_other by exact NE. tauto. Qed.
#[using="st1"] Lemma RB_unknown_other q1 q2 : q1 <> rid -> unknown rb_st (q1, q2) <-> unknown st (q1, q2).
Proof. intros NE. unfold unknown, SHd. cbn [fst snd]. rewrite RB_read_other by exact NE. tauto. Qed.

#[using="X L BL LS INV st1"] Lemma RB_TKS : TKS rb_st (s_tick st).
Proof. rewrite RB_eq. apply TKS_wr8; [cbn; lia|]. apply TKS_cut. exact TKS0. Qed.

#[using="X L BL LS INV ISH r' st1"] Lemma RB_DOMS : forall q sh, s_shadow rb_st !! q = Some sh -> exists r, s_regions rb_st !! q = Some r /\ r_kind r = RKGroup.
Proof.
  intros q sh Hsh. rewrite RB_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [exists r'; split; reflexivity|].
  rewrite RB_eq in Hsh. unfold wr8, upd_shadow, set_shadow in Hsh. cbn [s_shadow fst] in Hsh.
  rewrite lookup_insert_ne in Hsh by congruence. rewrite lookup_insert_ne in Hsh by congruence.
  exact (ish_dom _ _ ISH q sh Hsh).
Qed.

#[using="Type"] Lemma NoDup_map_on {A B} (h : A -> B) (l : list A) :
  List.NoDup l -> (forall x y, In x l -> In y l -> h x = h y -> x = y) -> List.NoDup (map h l).
Proof.
  induction l as [|a l IH]; intros ND INJ; cbn; constructor.
  - intros Hin. apply in_map_iff in Hin as (y & E & Hy). inversion ND; subst.
    assert (y = a) by (apply INJ; cbn; auto). subst y. contradiction.
  - inversion ND; subst. apply IH; [assumption|]. intros x y Hx Hy E. apply INJ; cbn; auto.
Qed.

#[using="Type"] Lemma g_remove_split : forall a l0 (l : list (Z * Z)), In (a, l0) l -> List.NoDup (map fst l) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Definition GF : N * region -> bool := fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition Gf : N * region -> Z * Z := fun kr => (r_base (snd kr), r_len (snd kr)).

#[using="X st BL LS c dst nn rid INV D0 DA NA N2 IR"] Lemma groups_nodup : List.NoDup (map fst (ld_groups L)).
Proof.
  pose proof (ir_groups _ _ _ IR) as PG. fold GF Gf in PG.
  eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PG|].
  rewrite map_map. apply NoDup_map_on.
  - apply List.NoDup_filter. apply NoDup_ListNoDup. apply NoDup_map_to_list.
  - intros [q1 r1] [q2 r2] H1 H2 E. cbn in E. apply filter_In in H1 as [H1 K1]. apply filter_In in H2 as [H2 K2].
    apply In_map_to_list_regions in H1. apply In_map_to_list_regions in H2. unfold GF in K1, K2. cbn in K1, K2.
    destruct (N.eq_dec q1 q2) as [->|NE]; [rewrite H1 in H2; inversion H2; reflexivity|]. exfalso.
    pose proof (ir_disj _ _ _ IR q1 q2 r1 r2 H1 H2 NE) as D. unfold region_live_range in D.
    destruct (r_kind r1); try discriminate. destruct (r_kind r2); try discriminate.
    pose proof (ir_shape _ _ _ IR _ _ H1) as (_ & _ & P1 & _). pose proof (ir_shape _ _ _ IR _ _ H2) as (_ & _ & P2 & _).
    pose proof (round_up_ge (r_len r1)). pose proof (round_up_ge (r_len r2)). lia.
Qed.

Definition rb_L (b : Z) : mled := lremap L b dst nn.

#[using="Type"] Lemma RB_frontier q rq : frontier rb_st q rq = frontier st q rq.
Proof. reflexivity. Qed.

#[using="BL LS INV HO Hs SC Hon D0 DA NA N2 NL DC DISJ IR IM IG IS r'"] Theorem RB_inv_R : forall rg, s_regions st !! rid = Some rg -> inv_R X rb_st (rb_L (r_base rg)).
Proof.
  intros rg Hrg.
  destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg0 & Hrg0 & Krg & Eon). rewrite Hrg in Hrg0. injection Hrg0 as <-.
  pose proof (round_up_ge (r_len rg)) as RUo. pose proof (ir_shape _ _ _ IR _ _ Hrg) as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (RUn : round_up_pg nn = nn) by (apply round_up_pg_id; exact NA).

  pose proof (ir_groups _ _ _ IR) as PG. fold GF Gf in PG.
  assert (INold : In (r_base rg, r_len rg) (ld_groups L)).
  { eapply Permutation_in; [apply Permutation_sym; exact PG|]. apply in_map_iff. exists (rid, rg). split; [reflexivity|].
    apply filter_In. split; [apply In_map_to_list_regions; exact Hrg| unfold GF; cbn; rewrite Krg; reflexivity]. }
  destruct (g_remove_split (r_base rg) (r_len rg) (ld_groups L) INold groups_nodup) as (l1 & l2 & EL & EG).
  assert (PREST : Permutation (l1 ++ l2) (map Gf (List.filter GF (map_to_list (delete rid (s_regions st)))))).
  { apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (r_base rg, r_len rg)). rewrite <- EL. apply Permutation_sym.
    eapply Permutation_trans; [exact PG|].
    eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ Hrg)|].
    cbn. unfold GF at 1. cbn. rewrite Krg. cbn. apply Permutation_refl. }
  assert (PNEW : Permutation (ld_groups (rb_L (r_base rg))) (map Gf (List.filter GF (map_to_list (s_regions rb_st))))).
  { unfold rb_L, lremap. cbn [ld_groups KLedger.set_groups]. rewrite EG. rewrite RB_regions. rewrite <- (insert_delete_eq (s_regions st) rid r').
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply perm_filter; apply map_to_list_insert; apply lookup_delete_eq].
    cbn. apply perm_skip. exact PREST. }
  destruct IR; constructor; unfold rb_L, lremap; cbn [ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil KLedger.set_groups]; try exact ir_ceil.
  - intros q rq Hq. rewrite RB_next_rid. apply RB_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hrg)| exact (ir_ids _ _ Hq)].
  - intros q rq Hq. apply RB_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RUn.
    split; [exact D0|]. split; [exact DA|]. split; [unfold PGSZ in *; lia|]. split; [exact NL|]. split; [lia|]. intros [K|K]; discriminate.
  - intros q1 q2 r1 r2 H1 H2 NE.
    apply RB_some in H1 as [[-> ->]|[N1 H1]]; apply RB_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
    + cbn. rewrite RUn. pose proof (DISJ q2 r2 H2 N2') as D. destruct (region_live_range r2) as [b2 l2']. lia.
    + pose proof (DISJ q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1']. cbn. rewrite RUn. lia.
  - rewrite RB_reserved. exact ir_resv.
  - exact PNEW.
  - eapply Permutation_trans; [exact ir_metas|]. rewrite RB_regions.
    eapply Permutation_trans; [apply Permutation_map; apply (regions_update_perm st rid rg r' _ Hrg); cbn; rewrite ?Krg; reflexivity|].
    erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn [fst snd]. rewrite RB_frontier. reflexivity.
  - intros q rq Hq Kq. rewrite RB_frontier. apply RB_some in Hq as [[-> ->]|[NE Hq]]; [discriminate| exact (ir_metalen q rq Hq Kq)].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply RB_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply RB_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
    exact (ir_metainj q1 q2 r1 r2 H1 H2 K1 K2).
  - intros q rq Hq Kq. rewrite RB_frontier. apply RB_some in Hq as [[-> ->]|[NE Hq]]; [discriminate| exact (ir_brkfront q rq Hq Kq)].
  - rewrite RB_ctx. destruct ir_shift as [T1 [T2|(q & rq & Hq & Kq & Eq)]]; split; [exact T1| left; exact T2| exact T1|].
    right. exists q, rq. split; [apply RB_keep; [exact Hq| intros ->; rewrite Hrg in Hq; inversion Hq; subst; congruence]| auto].
  - intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & Kq & E1 & E2); exists q, rq.
    + split; [apply RB_keep; [exact Hq| intros ->; rewrite Hrg in Hq; inversion Hq; subst; congruence]| auto].
    + apply RB_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply RB_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply RB_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
    exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
  - rewrite RB_ctx. revert ir_brk. destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
    + destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply RB_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
    + exact IBK.
    + destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply RB_keep; [exact Hq| intros ->; rewrite Hrg in Hq; inversion Hq; subst; congruence]| auto].
  - rewrite RB_ctx. destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
    intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [| auto].
    apply RB_keep; [exact Hq|]. intros ->. rewrite Hrg in Hq. inversion Hq; subst. destruct K as [K|K]; congruence.
  - intros q Hq. rewrite HO in Hq. discriminate.
Qed.

#[using="D0 NA N2 NL mg'"] Lemma RB_gcnt sc : gcnt rb_st sc = gcnt st sc.
Proof.
  unfold gcnt. rewrite RB_groups. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h) as [m|]; [| reflexivity].
  pose proof (RBv m) as (_ & _ & _ & _ & _ & _ & _ & E8 & _ & E10). rewrite E8, E10. reflexivity.
Qed.

#[using="X L BL LS INV Hs SC Hon D0 NA N2 NL IA IM IG IS r' mg'"] Theorem RB_inv_A : inv_A rb_st.
Proof.
  destruct g_facts as (Hg & _). destruct (hosts_ok X st LS IG _ _ Hg) as (ai & Hgg & GO). pose proof (g_present _ _ _ _ _ _ GO) as GP.
  destruct IA; constructor; rewrite ?RB_ctx, ?RB_areas, ?RB_secret; try assumption.
  - intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
    exists rq. rewrite RB_frontier. split; [| auto]. apply RB_keep; [exact Hq|]. intros E.
    destruct g_facts as (_ & _ & _ & _ & _ & _ & _ & rg & Hrg & Krg & _). rewrite E, Hrg in Hq. inversion Hq; subst. destruct Kq as [Kq|Kq]; congruence.
  - intros m mr Hm. rewrite RB_metas in Hm. destruct (aptr_eqb_spec m g) as [->|NE].
    + destruct (s_metas st !! g) as [mr0|] eqn:E; [exact (ia_metas g mr0 E)| exfalso; apply GP; reflexivity].
    + rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
  - destruct ia_avail as [A1 A2]. split; [exact A1|]. intros H. destruct (A2 H) as (a & T & AV & NM). exists a. split; [exact T|]. split; [exact AV|].
    intros k Hk. rewrite RB_metas. rewrite lookup_insert_ne; [apply NM; exact Hk|]. intros E. apply GP. rewrite E. apply NM. exact Hk.
  - intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [| exact Kq]. apply RB_keep; [exact Hrq|]. intros E.
    destruct g_facts as (_ & _ & _ & _ & _ & _ & _ & rg & Hrg & Krg & _). rewrite E, Hrg in Hrq. inversion Hrq; subst. destruct Kq as [Kq|Kq]; congruence.
  - intros sc Hsc. unfold usage, ctx. rewrite RB_ctx, RB_gcnt. apply ia_usage. exact Hsc.
Qed.

#[using="L BL INV Hs SC Hon D0 NA N2 NL IM IG IS mg'"] Theorem RB_inv_M : inv_M X rb_st LS.
Proof.
  pose proof (hosts_ext st rb_st RB_groups) as HE.
  destruct IM as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. pose proof (RBv m) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
    destruct (aptr_eqb_spec m g) as [->|NE].
    + exfalso. rewrite E3 in Hm. destruct g_facts as (Hg & _). rewrite (hosts_mem X st LS (mkIM _ _ _ M1 M2 M3 M4 M5) _ _ Hg) in Hm. discriminate.
    + rewrite !RB_MR_other by exact NE. apply M1. rewrite RB_MR_other in Hm by exact NE. exact Hm.
  - intros m b Hm. pose proof (RBv m) as (_ & _ & E3 & _). rewrite E3 in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite RB_groups in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m.
    pose proof (RBv m) as (_ & _ & E3 & _ & _ & E6 & _). rewrite E3, E6. auto.
  - intros m Hm. destruct (M4 m Hm) as [S NI]. split; [| exact NI]. rewrite RB_metas. rewrite lookup_insert_ne; [exact S|].
    intros E. rewrite <- E in S. destruct g_facts as (Hg & _). pose proof (hosts_mem X st LS (mkIM _ _ _ M1 M2 M3 M4 M5) _ _ Hg) as MM.
    unfold MR, get_meta_rec in MM. rewrite S in MM. cbn in MM. discriminate.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). pose proof (RBv z) as (E1 & E2 & E3 & _).
    rewrite E1, E2, E3, RB_groups. repeat split; auto. exists b. auto.
Qed.

#[using="X L BL INV Hs SC Hon D0 NA N2 NL IM IL IG IS mg'"] Theorem RB_inv_L : inv_L rb_st LS.
Proof.
  assert (HE : forall h, get_head rb_st h = get_head st h) by (intros h; destruct h; reflexivity).
  assert (LK : forall l, linked st l -> linked rb_st l).
  { induction l as [|x [|y l] IH]; cbn; intros H; [exact I| exact I|]. destruct H as (A & B & C).
    pose proof (RBv x) as (_ & E2 & _). pose proof (RBv y) as (E1 & _). rewrite E1, E2. split; [exact A|]. split; [exact B|]. apply IH. exact C. }
  destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. specialize (L2 h). unfold dll in *. destruct (LS h); [exact I| apply LK; exact L2].
  - exact L3.
  - exact L4.
  - intros m. pose proof (RBv m) as (E1 & E2 & _). rewrite E1, E2. apply L5.
  - intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE].
    + exfalso. destruct g_facts as (_ & _ & _ & _ & NIL & _). apply NIL. exists LFree. exact Hm.
    + rewrite !RB_MR_other by exact NE. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st rb_st RB_groups).
    pose proof (RBv m) as (_ & _ & _ & _ & _ & _ & _ & E8 & _). rewrite E8. auto.
  - exact L9.
Qed.

#[using="X L BL LS dst nn on INV Hs SC Hon IM IG IS"] Lemma g_base_unique b : hosts st b g -> b = (rid, 0).
Proof. intros Hb. destruct g_facts as (Hg & _). exact (hosts_inj X st LS IM _ _ _ Hb Hg). Qed.

#[using="X L BL LS dst nn on INV Hs SC Hon D0 IM IG IS"] Lemma other_not_rid b m : hosts st b m -> m <> g -> fst b <> rid.
Proof. intros Hb NE F. apply NE. exact (proj1 (rid_groups _ _ Hb F)). Qed.

#[using="L BL INV Hs SC Hon D0 NA N2 NL IM IG IS r' mg'"] Lemma RB_group_ok_g ai : group_ok X st LS g (rid, 0) ai -> group_ok X rb_st LS g (rid, 0) ai.
Proof.
  intros GO. destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg & Hrg & Krg & Eon).
  pose proof nn_pages as (P1 & P2 & P3). pose proof mg'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct GO as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14 G15 G16]; constructor; rewrite ?RB_MR_g, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9; try assumption.
  - rewrite RB_metas, lookup_insert_eq. discriminate.
  - right. rewrite SC, LI. repeat split; try reflexivity; try lia. exact NIL.
  - lia.
  - rewrite SC. intros H. lia.
  - rewrite SC. intros _ H. lia.
  - intros _. split; [reflexivity|]. exists r'. rewrite RB_lookup. cbn [fst]. rewrite N.eqb_refl. split; [reflexivity|]. split; [reflexivity|].
    cbn [r_len]. rewrite (round_up_pg_id nn NA). split; [lia|].
    split; [| rewrite ?F8, ?SC; intros H48; exfalso; clear -H48; lia].
    unfold gend. rewrite <- RB_MR_g. rewrite RB_sstart_g. unfold cnt_of. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (RBv g))))))), LI. unfold UNIT. lia.
  - intros H. lia.
  -
    intros NF AF. split; [lia|]. apply (proj2 (G16 NF ltac:(unfold allfree in AF |- *; rewrite ?F4, ?F5, ?F6 in AF; exact AF))).
Qed.

#[using="L BL INV Hs SC Hon D0 IM IG IS r' mg'"] Lemma RB_group_ok_other m b ai : m <> g -> hosts st b m -> group_ok X st LS m b ai -> group_ok X rb_st LS m b ai.
Proof.
  intros NE Hb GO. pose proof (other_not_rid _ _ Hb NE) as NR.
  destruct GO as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14 G15]; constructor; rewrite ?(RB_MR_other m NE), ?RB_slots; try assumption.
  - rewrite RB_metas, lookup_insert_ne by congruence. exact G1.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [apply RB_keep; [exact Hr| exact NR]| auto].
  - intros H. destruct (G14 H) as (p & i & S1 & S2 & S3 & S4 & S5). exists p, i.
    assert (NP : p <> g). { intros ->. apply NR. rewrite <- S2. destruct g_facts as (_ & _ & _ & _ & _ & _ & GB & _). rewrite GB. reflexivity. }
    rewrite !(RB_MR_other p NP). auto 10.
Qed.

#[using="L BL INV Hs SC Hon D0 NA N2 NL IM IG IS r' mg'"] Theorem RB_inv_G : inv_G X rb_st LS.
Proof.
  destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg & Hrg & Krg & Eon).
  pose proof (hosts_ext st rb_st RB_groups) as HE.
  pose proof IG as IG0. destruct IG0 as [G1 G2 G3 G4 G5 G6]; constructor.
  - intros m b ai H. rewrite RB_groups in H. destruct (aptr_eqb_spec m g) as [->|NE].
    + pose proof (g_base_unique b (ex_intro _ ai H)) as ->. apply RB_group_ok_g. exact (G1 _ _ _ H).
    + apply RB_group_ok_other; [exact NE| exists ai; exact H| exact (G1 _ _ _ H)].
  - intros b ai H. rewrite RB_groups in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite RB_groups in H1, H2.
    pose proof (RBv m1) as (_ & _ & _ & _ & _ & E6 & _ & E8 & _). pose proof (RBv m2) as (_ & _ & _ & _ & _ & E6' & _ & E8' & _).
    rewrite E6, E8, E6', E8'. eapply G3; eassumption.
  - intros q rq Hq Kq Ho. apply RB_some in Hq as [[-> ->]|[NE Hq]].
    + exists g. split; [apply HE; exact Hg|]. rewrite RB_maplen_g. pose proof nn_pages. lia.
    + destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m. split; [apply HE; exact Hm|].
      assert (m <> g) by (intros ->; apply NE; pose proof (g_base_unique _ Hm) as E; injection E; auto).
      rewrite RB_MR_other by assumption. exact Hml.
  - intros b h H. rewrite RB_groups in H. destruct (G5 b h H) as (rq & Hq & Kq).
    destruct (N.eq_dec (fst b) rid) as [E|NE]; [exists r'; rewrite E, RB_lookup, N.eqb_refl; split; reflexivity|].
    exists rq. split; [apply RB_keep; assumption| exact Kq].
  -
    intros m1 m2 b1 b2 ai1 ai2 H1 H2 NF1 NF2 A1 A2 E. rewrite RB_groups in H1, H2.
    pose proof (RBv m1) as (_ & _ & _ & E4 & E5 & E6 & _ & E8 & _). pose proof (RBv m2) as (_ & _ & _ & E4' & E5' & E6' & _ & E8' & _).
    unfold allfree in A1, A2. rewrite E4, E5, E6 in A1. rewrite E4', E5', E6' in A2. rewrite E8, E8' in E.
    exact (G6 _ _ _ _ _ _ H1 H2 NF1 NF2 A1 A2 E).
Qed.

#[using="X L BL LS INV Hs SC Hon D0 NA N2 NL IM IG IS mg'"] Lemma RB_slot_start m i : (m = g -> i = 0) -> slot_start' (MR rb_st m) i = slot_start' (MR st m) i.
Proof.
  intros Hi. destruct (aptr_eqb_spec m g) as [->|NE]; [| rewrite RB_MR_other by exact NE; reflexivity].
  rewrite !slot_start'_sstart. pose proof (RBv g) as (_ & _ & _ & _ & _ & _ & _ & _ & GBE & _). rewrite GBE, RB_sstart_g, (Hi eq_refl).
  destruct g_facts as (_ & _ & _ & _ & _ & STR & GB0 & _). unfold sstart. rewrite GB0, STR. cbn -[Z.mul Z.add Z.sub]. f_equal. unfold UNIT. lia.
Qed.

#[using="L LS INV HP Hs SC Hon D0 NA N2 NL IM IG IS mg'"] Theorem RB_inv_S : inv_S X rb_st BL.
Proof.
  destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg & Hrg & Krg & Eon).
  pose proof (hosts_ext st rb_st RB_groups) as HE.
  pose proof IS as IS0. destruct IS0 as [S1 S2 S3 S4 S5 S6 S7]; constructor; rewrite ?RB_slots, ?RB_groups.
  - intros s m i H. destruct (S1 s m i H) as (A & B & C). rewrite (live_group_ext st rb_st RB_groups).
    pose proof (RBv m) as (_ & _ & _ & _ & _ & E6 & _). rewrite E6. split; [exact A|]. split; [exact B|].
    rewrite RB_slot_start; [exact C|]. intros ->. destruct (rid_slots s g i H) as (_ & _ & Hi); [| exact Hi].
    rewrite C, slot_start'_sstart, GB. reflexivity.
  - intros b m i Hb Hi. apply HE in Hb. pose proof (RBv m) as (_ & _ & _ & _ & _ & E6 & _). rewrite E6 in Hi.
    rewrite RB_slot_start; [apply (S2 b); assumption|]. intros ->. rewrite LI in Hi. lia.
  - intros b m ai i Hb Hi. pose proof (RBv m) as (_ & _ & _ & E4 & E5 & E6 & _). rewrite E6 in Hi. rewrite E4, E5.
    rewrite RB_slot_start; [apply (S3 b m ai i); assumption|]. intros ->. rewrite LI in Hi. lia.
  - exact S4.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & Hsl & rest). exists m, i. split; [exact Hsl|].
    rewrite RB_MR_other; [exact rest|]. intros ->. apply (rid_blocks k Hk).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([b Hb] & _ & Es). rewrite Es, (slot_start'_eq X st LS IM _ _ _ Hb). cbn. pose proof (g_base_unique _ Hb) as ->. reflexivity.
  -
    intros k m i Hk Hsl. rewrite RB_MR_other; [exact (S7 k m i Hk Hsl)|]. intros ->. apply (rid_blocks k Hk).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([b Hb] & _ & Es). rewrite Es, (slot_start'_eq X st LS IM _ _ _ Hb). cbn. pose proof (g_base_unique _ Hb) as ->. reflexivity.
Qed.

#[using="X L LS INV HP Hs SC Hon D0 DA NA N2 NL IM IG IS ISH r' mg' st1"] Theorem RB_inv_SH : inv_SH rb_st BL.
Proof.
  destruct g_facts as (Hg & Ec & LI & ML & NIL & STR & GB & rg & Hrg & Krg & Eon).
  pose proof (hosts_ext st rb_st RB_groups) as HE. assert (PG : PGSZ = 4096) by reflexivity.
  assert (MIN : 4096 <= Z.min on nn).
  { apply Z.min_glb; [| lia]. rewrite Hon. destruct (hosts_ok X st LS IG _ _ Hg) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). lia. }
  destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
  - exact RB_DOMS.
  - rewrite RB_tick. exact RB_TKS.
  - intros b m i Hb Hi. apply HE in Hb. destruct (aptr_eqb_spec m g) as [->|NE].
    + pose proof (g_base_unique _ Hb) as ->. cbn [fst]. rewrite RB_sstart_g.
      pose proof (RBv g) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CE). rewrite CE in Hi. unfold cnt_of in Hi. rewrite LI in Hi.
      assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      * unfold known, SHd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. change (16 - IB) with 12. rewrite RB_read_lt by lia.
        pose proof (D3 _ _ 0 Hb ltac:(unfold cnt_of; lia)) as K. unfold known, SHd in K. cbn [fst snd] in K. unfold sstart in K. rewrite GB, Z.mul_0_r in K. cbn in K. exact K.
      * unfold known, SHd. cbn [fst snd]. replace (16 + (nn - UNIT) * 1 - IB) with (nn - 4) by (unfold UNIT, IB; lia). exact RB_read_end.
    + pose proof (other_not_rid _ _ Hb NE) as NR. rewrite RB_sstart_other by exact NE. destruct b as [b1 b2]. cbn [fst] in NR |- *.
      apply (RB_known_other _ _ _ NR). pose proof (RBv m) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CE). rewrite CE in Hi. exact (D3 _ _ i Hb Hi).
  - intros b m o Hb Ho. apply HE in Hb. destruct (aptr_eqb_spec m g) as [->|NE].
    + pose proof (g_base_unique _ Hb) as ->. cbn [fst snd]. unfold unknown, SHd. cbn [fst snd]. rewrite RB_read_lt by lia.
      pose proof (D4 _ _ o Hb Ho) as U. exact U.
    + pose proof (other_not_rid _ _ Hb NE) as NR. destruct b as [b1 b2]. cbn [fst snd] in NR |- *. apply (RB_unknown_other _ _ NR). exact (D4 _ _ o Hb Ho).
  - intros b m p i Hb Hml Hsl. apply HE in Hb. rewrite RB_slots in Hsl. destruct (aptr_eqb_spec m g) as [->|NE]; [rewrite RB_maplen_g in Hml; pose proof nn_pages; lia|].
    pose proof (other_not_rid _ _ Hb NE) as NR. rewrite RB_MR_other in Hml by exact NE.
    assert (NP : p <> g).
    { intros ->. apply NR. destruct (rid_slots b g i Hsl) as (-> & _); [| rewrite Ec; reflexivity].
      destruct (is_valid _ _ _ IS _ _ _ Hsl) as (_ & _ & Es). rewrite Es, slot_start'_sstart, GB. reflexivity. }
    rewrite (RB_MR_other p NP). destruct b as [b1 b2]. cbn [fst snd] in NR |- *.
    destruct (D5 _ _ p i Hb Hml Hsl) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply (RB_known_other _ _ _ NR); exact K3| auto]|].
    split; [apply (RB_known_other _ _ _ NR); exact K2|]. split; [apply (RB_known_other _ _ _ NR); exact K1| exact Q].
  - intros k m i Hk Hsl. rewrite RB_slots in Hsl. pose proof (rid_blocks k Hk) as NR.
    assert (NE : m <> g).
    { intros ->. apply NR. destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([b Hb] & _ & Es). rewrite Es, (slot_start'_eq X st LS IM _ _ _ Hb). cbn. pose proof (g_base_unique _ Hb) as ->. reflexivity. }
    rewrite !(RB_MR_other m NE). destruct (bslot k) as [k1 k2] eqn:EK. cbn [fst snd] in NR |- *.
    destruct (D6 k m i Hk ltac:(rewrite EK; exact Hsl)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite EK in *. cbn [fst snd] in *.
    split; [apply (RB_known_other _ _ _ NR); exact A1|]. split; [apply (RB_known_other _ _ _ NR); exact A2|].
    split; [apply (RB_known_other _ _ _ NR); exact A3|]. split; [apply (RB_known_other _ _ _ NR); exact A4|]. split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try (apply (RB_known_other _ _ _ NR)); assumption.
    + split; [intros Hr; apply (RB_known_other _ _ _ NR); apply A7; exact Hr|]. intros a Ha. apply (RB_unknown_other _ _ NR). apply A8. exact Ha.
Qed.

#[using="INV HP HO Hs SC Hon D0 DA NA N2 NL DC DISJ IR IA IM IL IG IS ISH r' mg' st1"] Theorem INVL_rebase : forall rg, s_regions st !! rid = Some rg -> INVL X rb_st (rb_L (r_base rg)) BL LS.
Proof.
  intros rg Hrg. split; [exact (RB_inv_R rg Hrg)|]. split; [exact RB_inv_A|]. split; [exact RB_inv_M|]. split; [exact RB_inv_L|].
  split; [exact RB_inv_G|]. split; [exact RB_inv_S| exact RB_inv_SH].
Qed.

#[using="Type"] Lemma RB_strip : strip rb_st = cremap (strip st) rid g dst nn.
Proof. unfold rb_st. apply strip_rebase_st. Qed.

#[using="D0 DA NA N2 st1"] Lemma RB_read_ge o v : Z.min on nn <= o -> o <> nn - 4 -> cell_read (get_shadow rb_st rid) o = Known v -> v = 0.
Proof.
  intros Ho NE. rewrite RB_eq. rewrite (cell_read_wr8_other (rid, nn - 4) 0 _ (rid, o)) by (intros E; injection E; lia). cbn [fst snd].
  rewrite get_shadow_upd_shadow, N.eqb_refl. apply cell_read_cut_ge. exact Ho.
Qed.
End REBASE.

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (g : aptr) (off n n' dst : Z).
Let k : blk := ((c, off), n).
Let k' : blk := ((c, off), n').
Let rid : N := fst c.
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Hypothesis HO : x_orph X = None.
Hypothesis Hs : s_slots st !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (MR st g) = 63.
Hypothesis Hn' : 0 <= n'.
Let on : Z := m_maplen (MR st g) * 4096.
Let nn : Z := mremap_needed off n'.
Hypothesis D0 : 0 < dst.
Hypothesis DA : dst mod PGSZ = 0.
Hypothesis NL : nn < LEN_MAX.
Hypothesis N2 : 2 * PGSZ <= nn.
Hypothesis DC : dst + nn <= s_ceil st.
Hypothesis RESV : ranges_free (s_reserved st) dst nn = true.
Hypothesis DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> rid ->
  let '(b2, l2) := region_live_range r2 in dst + nn <= b2 \/ b2 + l2 <= dst.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Let stride := get_stride (MR st g).
Let p : aptr := aadd c (UNIT * off).
Let e : aptr := aadd c (nn - UNIT - IB).
Let res : Z := stride - IB - UNIT * off - n.
Let res' : Z := snd e - snd p - n'.
Let b3 : Z := 0 + 32 * Z.min res 5.
Let t1 : N := N.succ (s_tick st).
Definition rm_st1 : mstate := set_tick t1 st.
Definition rm_st2 : mstate := rebase_st rm_st1 rid g dst nn on.
Definition rm_st3 : mstate := wrs (ss_list p e n' b3) rm_st2.
Definition rm_st4 : mstate := havoc p n' rm_st3.
Let X' := mkX (x_idle X) (x_zomb X) (Some c) (x_orph X) (x_fresh X).
Let L' (b : Z) := lremap L b dst nn.

#[using="Type"] Lemma nn_mod : nn mod PGSZ = 0.
Proof. unfold nn, mremap_needed. apply round_up_pg_mod. Qed.

#[using="Hs"] Lemma rm_eq : rm_st4 = mremap_full st c off n n' dst.
Proof. unfold mremap_full. rewrite Hs. reflexivity. Qed.

#[using="X L BL LS c k INV Hk Hs SC IS"] Lemma rm_blocks : 0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= stride - IB.
Proof. destruct (is_blocks _ _ _ IS k Hk) as (m2 & i2 & Hs2 & A & B & C). rewrite Hs in Hs2. inversion Hs2; subst. auto. Qed.
#[using="X L BL LS INV Hk Hs ISH"] Lemma rm_old : blk_shadow_ok st k g 0.
Proof. exact (ish_blk _ _ ISH k g 0 Hk Hs). Qed.

#[using="c g off n n' dst rid INV on nn stride p e res res' b3"] Lemma INV1 : INVL X rm_st1 L BL LS.
Proof. apply INVL_set_tick; [unfold t1; lia| exact INV]. Qed.

#[using="g off n n' dst k rid INV Hk NP on nn stride p e res res' b3"] Lemma INVp : INVL X' rm_st1 L (bl_remove c BL) LS.
Proof.
  change c with (bslot k). apply (INVL_remove_block X rm_st1 rm_st1 L BL LS k INV1 Hk NP).
  - apply ctrl_eq_refl.
  - reflexivity.
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ INV1).
  - exact (TKS_of _ _ _ _ _ INV1).
Qed.

#[using="X L BL off n n' dst k INV Hk NP Hs SC nn stride p e res res' b3 t1 X'"] Lemma g_facts' : hosts st (rid, 0) g /\ c = (rid, 16) /\ m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ ~ in_list LS g
  /\ get_stride (MR st g) = on - UNIT /\ gbase (MR st g) = (rid, 0)
  /\ exists rg, s_regions st !! rid = Some rg /\ r_kind rg = RKGroup /\ on = round_up_pg (r_len rg).
Proof. exact (g_facts X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp Hs SC eq_refl). Qed.

#[using="n k INV Hk NP HO Hs SC D0 DA NL N2 DC DISJ stride p e res res' b3"] Lemma INV2 : forall rg, s_regions st !! rid = Some rg -> INVL X' rm_st2 (L' (r_base rg)) (bl_remove c BL) LS.
Proof.
  intros rg Hrg. unfold rm_st2.
  apply (INVL_rebase X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp eq_refl HO Hs SC eq_refl D0 DA nn_mod N2 NL DC DISJ rg Hrg).
Qed.

#[using="X st L BL LS g off n n' dst k INV Hk NP Hs SC on nn stride p e res res' b3 t1 X'"] Lemma c16 : c = (rid, 16). Proof. exact (proj1 (proj2 g_facts')). Qed.
#[using="X L BL LS c off n n' dst k rid INV Hk NP Hs SC nn p e res res' b3 t1 X'"] Lemma old_stride : stride = on - UNIT. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 g_facts')))))). Qed.
#[using="X L BL LS n k INV Hk NP Hs SC D0 NL N2 stride p e res res' b3 X'"] Lemma st2_stride : get_stride (MR rm_st2 g) = nn - UNIT.
Proof. exact (RB_stride_g X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp Hs SC eq_refl D0 nn_mod N2 NL). Qed.
#[using="X L BL LS n k INV Hk NP Hs SC D0 NL N2 stride p e res res' b3 X'"] Lemma st2_sstart i : sstart (MR rm_st2 g) i = 16 + (nn - UNIT) * i.
Proof. exact (RB_sstart_g X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp Hs SC eq_refl D0 nn_mod N2 NL i). Qed.
#[using="X L BL LS n k INV Hk NP Hs SC D0 NL N2 stride p e res res' b3 X'"] Lemma st2_gbase : gbase (MR rm_st2 g) = (rid, 0).
Proof.
  pose proof (RBv rm_st1 c g dst nn on D0 nn_mod N2 NL g) as (_ & _ & _ & _ & _ & _ & _ & _ & GB & _). unfold rm_st2. rewrite GB.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 g_facts'))))))).
Qed.
#[using="Type"] Lemma st2_slots : s_slots rm_st2 = s_slots st. Proof. unfold rm_st2. rewrite RB_slots. reflexivity. Qed.
#[using="Type"] Lemma st2_tick : s_tick rm_st2 = t1. Proof. unfold rm_st2. rewrite RB_tick. reflexivity. Qed.
#[using="X L BL LS n k INV Hk NP stride p e res res' b3 X'"] Lemma TKS2 : TKS rm_st2 t1.
Proof. pose proof (RB_TKS X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp) as T. exact T. Qed.
#[using="Type"] Lemma st4_ctrl : ctrl_eq rm_st2 rm_st4 /\ s_tick rm_st4 = t1.
Proof.
  destruct (wrs_ctrl (ss_list p e n' b3) rm_st2) as [C2 T2]. destruct (havoc_ctrl p n' rm_st3) as [C3 T3].
  split; [eapply ctrl_eq_trans; [exact C2| exact C3]|]. unfold rm_st4. rewrite T3. unfold rm_st3. rewrite T2. exact st2_tick.
Qed.
#[using="Type"] Lemma st3_tick : s_tick rm_st3 = t1. Proof. unfold rm_st3. rewrite (proj2 (wrs_ctrl _ _)). exact st2_tick. Qed.
#[using="X L BL LS k INV Hk NP res' X'"] Lemma TKS3 : TKS rm_st3 t1.
Proof. unfold rm_st3. apply wrs_TKS; [rewrite st2_tick; lia| exact TKS2]. Qed.
#[using="X L BL LS k INV Hk NP res' X'"] Lemma st3_hav u hl : r_hav (get_shadow rm_st3 (fst p)) !! u = Some hl -> hl_ticks hl (s_tick rm_st3).
Proof. intros Hu ch Hch. pose proof TKS3 as TK. rewrite <- st3_tick in TK. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
#[using="X st L BL LS g n n' dst k INV Hk NP Hs SC on nn stride e res res' b3 t1 X'"] Lemma pp : snd p = 16 + UNIT * off /\ fst p = rid.
Proof. unfold p, aadd. rewrite c16. cbn. lia. Qed.
#[using="X st L BL LS g n n' dst k rid INV Hk NP Hs SC on nn D0 DA stride e res res' b3 t1 X'"] Lemma p16 : snd p mod 16 = 0.
Proof. rewrite (proj1 pp). unfold UNIT. Z.div_mod_to_equations. nia. Qed.
#[using="X L BL LS k INV Hk NP Hs SC Hn' D0 DA res' X'"] Lemma TKS4 : TKS rm_st4 t1.
Proof.
  unfold rm_st4. destruct (Z.eq_dec n' 0) as [Z0|NZ]; [rewrite havoc_le0 by lia; exact TKS3|].
  rewrite <- st3_tick. apply TKS_havoc; [apply p16| lia| rewrite st3_tick; exact TKS3].
Qed.
#[using="X st L BL LS g n dst k INV Hk NP Hs SC on stride p res res' b3 t1 X'"] Lemma ee : snd e = nn - IB /\ fst e = rid.
Proof. unfold e, aadd. rewrite c16. cbn. unfold UNIT. lia. Qed.
#[using="Type"] Lemma nn_ge : n' + UNIT * off + UNIT + IB <= nn.
Proof. unfold nn, mremap_needed. apply round_up_ge. Qed.
#[using="X st L BL LS g n dst k rid INV Hk NP Hs SC on stride res b3 t1 X'"] Lemma res'_eq : res' = nn - UNIT - IB - UNIT * off - n'.
Proof. unfold res'. rewrite (proj1 ee), (proj1 pp). unfold UNIT. lia. Qed.
#[using="X st L BL LS g n dst k rid INV Hk NP Hs SC on stride res b3 t1 X'"] Lemma res'_bnd : 0 <= res'.
Proof. rewrite res'_eq. pose proof nn_ge. lia. Qed.

#[using="X L BL LS dst k INV Hk NP Hs SC on D0 IS res' t1 X'"] Lemma ss_addrs a : In a (map fst (ss_list p e n' b3)) ->
  fst a = rid /\ ((snd a = snd p - 3) \/ (snd p + n' <= snd a < nn - IB)).
Proof.
  intros Hin. pose proof rm_blocks as (Ho & _ & _). pose proof pp as [PP FP]. pose proof ee as [EE FE]. pose proof res'_bnd as R.
  unfold ss_list in Hin. fold res' in Hin.
  destruct (Z.eqb_spec res' 0) as [R0|R0]; destruct (Z.leb_spec 5 res') as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold res' in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold aadd; cbn [fst snd]; rewrite ?FP, ?FE;
    (split; [reflexivity|]); unfold IB, UNIT in *; first [left; lia | right; lia].
Qed.
#[using="X L BL LS dst k INV Hk NP Hs SC on D0 IS res' t1 X'"] Lemma ss_not_in a : snd p <= a < snd p + n' -> ~ In (rid, a) (map fst (ss_list p e n' b3)).
Proof. intros Ha Hin. destruct (ss_addrs _ Hin) as (_ & [E|E]); cbn [fst snd] in E; lia. Qed.

#[using="X L BL LS k INV Hk NP Hs SC Hn' D0 DA res' X'"] Lemma st4_read_out r : ~ (fst r = fst p /\ snd p <= snd r < snd p + n') ->
  cell_read (get_shadow rm_st4 (fst r)) (snd r) = cell_read (get_shadow rm_st3 (fst r)) (snd r).
Proof.
  intros Hr. unfold rm_st4. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out p n' rm_st3 p16 ltac:(lia) st3_hav). exact Hr.
Qed.
#[using="X L BL LS k INV Hk NP Hs SC Hn' D0 DA res' X' L'"] Lemma st4_known_w x w : ~ (snd p <= x < snd p + n') ->
  lastw (ss_list p e n' b3) (rid, x) None = Some w -> known rm_st4 (rid, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd]. pose proof pp as [_ FP].
  rewrite (st4_read_out (rid, x)) by (cbn [fst snd]; tauto).
  unfold rm_st3. pose proof TKS2 as TK. rewrite <- st2_tick in TK. rewrite (wrs_lastw (ss_list p e n' b3) rm_st2 (rid, x) TK). rewrite HL. reflexivity.
Qed.
#[using="X L BL LS k INV Hk NP Hs SC Hn' D0 DA res' X' L'"] Lemma st4_known_old x v : ~ (snd p <= x < snd p + n') ->
  lastw (ss_list p e n' b3) (rid, x) None = None -> known rm_st2 (rid, x) v -> known rm_st4 (rid, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *. pose proof pp as [_ FP].
  rewrite (st4_read_out (rid, x)) by (cbn [fst snd]; tauto).
  unfold rm_st3. pose proof TKS2 as TK. rewrite <- st2_tick in TK. rewrite (wrs_lastw (ss_list p e n' b3) rm_st2 (rid, x) TK). rewrite HL. exact K.
Qed.

#[using="D0 DA N2"] Lemma K12 o v : o < Z.min on nn -> o <> nn - 4 -> known st (rid, o) v -> known rm_st2 (rid, o) v.
Proof.
  intros Ho NE K. unfold known, SHd in *. cbn [fst snd] in *. unfold rm_st2, rid.
  rewrite (RB_read_lt rm_st1 c g dst nn on D0 DA nn_mod N2 o Ho NE). exact K.
Qed.
#[using="X L BL LS k INV Hk NP Hs SC D0 DA IS res' X'"] Lemma st4_unknown a : snd p <= a < snd p + n' -> unknown rm_st4 (rid, a).
Proof.
  intros Ha. pose proof pp as [PP FP]. unfold unknown, SHd, rm_st4. cbn [fst snd].
  destruct (cell_read_havoc_in p n' rm_st3 p16 ltac:(lia) st3_hav (rid, a) ltac:(cbn; symmetry; exact FP) Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. rewrite st3_tick.
  unfold rm_st3 in Hc. rewrite ?FP in Hc. rewrite wrs_cells_other in Hc by (apply ss_not_in; exact Ha).
  unfold rm_st2, rebase_st in Hc.
  rewrite wr8_cells_other in Hc by (intros E; injection E; pose proof nn_ge; unfold UNIT, IB in *; lia).
  rewrite get_shadow_upd_shadow, N.eqb_refl, shadow_cut_cells in Hc.
  destruct (a <? Z.min on nn); [| discriminate].
  change (get_shadow (rebase_ctrl rm_st1 rid g dst nn) rid) with (get_shadow st rid) in Hc.
  destruct (get_shadow_cells_some st rid a (v, tk) Hc) as (sh & Hsh & Hc').
  pose proof (proj1 (TKS_of _ _ _ _ _ INV _ _ Hsh) a v tk Hc') as [_ LE]. unfold t1. lia.
Qed.

Ltac raeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold e, p, aadd; rewrite c16; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold e, p, aadd; rewrite c16; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

#[using="X L BL LS k INV Hk NP Hs SC Hn' D0 DA NL N2 DC IS ISH res' X' L'"] Lemma rm_blk_ok : blk_shadow_ok rm_st4 k' g 0.
Proof.
  pose proof rm_blocks as (Ho & Hn & Hfit). pose proof pp as [PP FP]. pose proof ee as [EE FE]. pose proof nn_ge as NG. pose proof res'_bnd as R0.
  pose proof nn_mod as NNM. unfold PGSZ in NNM.
  destruct st4_ctrl as [CE TK].
  assert (MRE : MR rm_st4 g = MR rm_st2 g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof rm_old as OLD. unfold blk_shadow_ok in OLD |- *. unfold k, k' in OLD |- *. cbn [bslot boff bsize fst snd] in OLD |- *.
  rewrite MRE, st2_stride, st2_gbase. fold stride in OLD. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 g_facts'))))))) in OLD. cbn [snd] in OLD |- *.
  fold rid in OLD |- *.
  destruct OLD as (O4 & O3 & O2 & O1 & OQ & O5 & OC & OU).
  rewrite c16 in *. cbn [fst snd] in *.
  replace (16 + (nn - UNIT) - IB - (16 + UNIT * off) - n') with res' by (rewrite res'_eq; lia).
  assert (NPn : forall x, x < snd p \/ snd p + n' <= x -> ~ (snd p <= x < snd p + n')) by (intros; lia).

  assert (ONN : 16 + UNIT * off - 1 < Z.min on nn /\ 16 + UNIT * off + 4 <= nn).
  { pose proof old_stride as OS. unfold on in *. unfold IB, UNIT in *. lia. }
  split; [| split; [| split; [| split; [| split; [exact OQ| split; [| split]]]]]].
  -   apply st4_known_old; [apply NPn; rewrite PP; unfold UNIT in *; lia| |].
    + unfold ss_list. fold res'. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [lastw app]; repeat raeq; reflexivity.
    + apply K12; [unfold UNIT in *; lia| unfold UNIT in *; lia| exact O4].
  -
    replace (0 + 32 * Z.min res' 5) with (Z.land (Z.land b3 31 + Z.shiftl (if 5 <=? res' then 5 else res') 5) 255).
    2:{ unfold b3. replace (Z.land (0 + 32 * Z.min res 5) 31) with 0.
        2:{ symmetry. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
            pose proof (Z.le_min_r res 5). unfold res, stride in *. pose proof old_stride.
            assert (0 <= Z.min (get_stride (MR st g) - IB - UNIT * off - n) 5) by (apply Z.min_glb; unfold IB, UNIT in *; lia).
            clear. change (2 ^ 5) with 32. rewrite Z.add_0_l, Z.mul_comm. apply Z.mod_mul. discriminate. }
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 res').
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply st4_known_w; [apply NPn; rewrite PP; unfold UNIT in *; lia|].
    unfold ss_list. fold res'. destruct (negb (res' =? 0)); destruct (5 <=? res'); cbn [negb lastw app]; repeat raeq; reflexivity.
  -   apply st4_known_old; [apply NPn; rewrite PP; unfold UNIT in *; lia| |].
    + unfold ss_list. fold res'. destruct (Z.eqb_spec res' 0) as [RZ0|RZ0]; destruct (Z.leb_spec 5 res') as [RL5|RL5]; cbn [negb lastw app]; try (exfalso; clear - RZ0 RL5; lia); repeat raeq; reflexivity.
    + apply K12; [unfold UNIT in *; lia| unfold UNIT in *; lia| exact O2].
  -   apply st4_known_old; [apply NPn; rewrite PP; unfold UNIT in *; lia| |].
    + unfold ss_list. fold res'. destruct (Z.eqb_spec res' 0) as [RZ0|RZ0]; destruct (Z.leb_spec 5 res') as [RL5|RL5]; cbn [negb lastw app]; try (exfalso; clear - RZ0 RL5; lia); repeat raeq; reflexivity.
    + apply K12; [unfold UNIT in *; lia| unfold UNIT in *; lia| exact O1].
  -   intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : res' < 2 ^ 32). { rewrite res'_eq. unfold nn, mremap_needed. pose proof (round_up_pg_spec (n' + UNIT * off + UNIT + IB)). unfold UNIT, IB in *. lia. }
    assert (E5 : (5 <=? res') = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply st4_known_w; [apply NPn; rewrite ?res'_eq, PP; unfold IB, UNIT in *; lia|];
         unfold ss_list; fold res'; rewrite E5, EZ; cbn [negb lastw app]; repeat raeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (st4_known_w _ 0); [apply NPn; rewrite ?res'_eq, PP; unfold IB, UNIT in *; lia|].
    unfold ss_list; fold res'; rewrite E5, EZ; cbn [negb lastw app]; repeat raeq; reflexivity.
  -   intros RP.
    replace (16 + (nn - UNIT) - IB - res') with (snd p + n') by (rewrite res'_eq, PP; lia).
    apply (st4_known_w _ 0); [apply NPn; unfold IB, UNIT in *; lia|].
    assert (EZ : (res' =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold ss_list; fold res'; rewrite EZ. destruct (Z.leb_spec 5 res'); cbn [negb lastw app];
      try (destruct (Z.eq_dec res' 5)); try (exfalso; lia); repeat raeq; reflexivity.
  -   intros a Ha. apply st4_unknown. rewrite PP. exact Ha.
Qed.

#[using="k INV Hk NP HO Hs SC Hn' D0 DA NL N2 DC DISJ IS ISH res' X'"] Theorem INVL_remap : forall rg, s_regions st !! rid = Some rg -> INVL X rm_st4 (L' (r_base rg)) (k' :: bl_remove c BL) LS.
Proof.
  intros rg Hrg. pose proof (INV2 rg Hrg) as I2. pose proof rm_blocks as (Ho & Hn & Hfit). pose proof pp as [PP FP]. pose proof nn_ge as NG.
  destruct st4_ctrl as [CE24 TK4].
  assert (EX : X = mkX (x_idle X') (x_zomb X') None (x_orph X') (x_fresh X')) by (destruct X; cbn; cbn in NP; rewrite NP; reflexivity).
  assert (REG' : exists r, s_regions rm_st2 !! rid = Some r /\ r_kind r = RKGroup).
  { unfold rm_st2. rewrite (RB_regions rm_st1 c g dst nn on). fold rid. rewrite lookup_insert_eq. eexists; split; [reflexivity| reflexivity]. }
  rewrite EX. apply (INVL_add_block X' rm_st2 rm_st4 (L' (r_base rg)) (bl_remove c BL) LS c off n' I2 eq_refl CE24).
  - rewrite TK4. symmetry. exact st2_tick.
  - intros m2 i2 Hs2 q Hq. rewrite st2_slots, Hs in Hs2. inversion Hs2. subst m2 i2.
    rewrite !st2_sstart in Hq.
    assert (NQ : ~ (fst q = fst p /\ snd p <= snd q < snd p + n')).
    { intros [F R]. apply Hq. unfold inT. split; [rewrite F; exact FP|]. unfold IB, UNIT in *. lia. }
    rewrite (st4_read_out q NQ). unfold rm_st3. apply wrs_read_other.
    intros Hin. destruct (ss_addrs q Hin) as (F & [R|R]); apply Hq; unfold inT; (split; [exact F|]); unfold IB, UNIT in *; lia.
  - change (DOMS rm_st2 rm_st4). unfold rm_st4. destruct (Z.eq_dec n' 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. unfold rm_st3. apply wrs_DOMS; [| intros q Hin; destruct (ss_addrs q Hin) as (F & _); rewrite F; exact REG'].
      intros q sh H. exact (RB_DOMS X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp q sh H).
    + apply DOMS_havoc; [lia| | rewrite FP; exact REG']. unfold rm_st3. apply wrs_DOMS; [| intros q Hin; destruct (ss_addrs q Hin) as (F & _); rewrite F; exact REG'].
      intros q sh H. exact (RB_DOMS X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp q sh H).
  - rewrite st2_tick. exact TKS4.
  - intros m2 i2 Hs2. rewrite st2_slots, Hs in Hs2. inversion Hs2. subst m2 i2.
    split; [exact Ho|]. split; [exact Hn'|]. split; [rewrite st2_stride; unfold IB, UNIT in *; lia|]. exact rm_blk_ok.
  -
    intros m2 i2 Hs2. rewrite st2_slots, Hs in Hs2. inversion Hs2. subst m2 i2.
    pose proof (RBv rm_st1 c g dst nn on D0 nn_mod N2 NL g) as (_ & _ & _ & _ & _ & _ & _ & E8 & _). unfold rm_st2. rewrite E8.
    change (MR rm_st1 g) with (MR st g). rewrite SC. split; [intros H48; exfalso; clear -H48; lia| intros _].
    fold rm_st2. rewrite st2_stride. unfold nn, mremap_needed. pose proof (round_up_pg_spec (n' + UNIT * off + UNIT + IB)). unfold UNIT, IB in *. lia.
Qed.

#[using="Hs"] Lemma rm_strip : strip rm_st4 = cremap (strip st) rid g dst nn.
Proof. rewrite rm_eq. exact (strip_mremap_full st c off n n' dst g 0 Hs). Qed.

#[using="Type"] Lemma rm_regions : s_regions rm_st4 = <[rid := mkRegion RKGroup dst nn]> (s_regions st).
Proof. rewrite (ce_regions _ _ (proj1 st4_ctrl)). unfold rm_st2. rewrite (RB_regions rm_st1 c g dst nn on). reflexivity. Qed.
#[using="Type"] Lemma rm_secret : s_secret rm_st4 = s_secret st.
Proof. rewrite (ce_secret _ _ (proj1 st4_ctrl)). reflexivity. Qed.
#[using="Type"] Lemma rm_slots : s_slots rm_st4 = s_slots st.
Proof. rewrite (ce_slots _ _ (proj1 st4_ctrl)). exact st2_slots. Qed.
#[using="X st L LS g off n n' dst k INV Hk NP Hs SC on nn D0 stride p e res res' b3 t1 X'"] Lemma rm_other_blocks : forall k0, In k0 (bl_remove c BL) -> fst (bslot k0) <> rid.
Proof. exact (rid_blocks X' rm_st1 L (bl_remove c BL) LS c g dst nn on INVp eq_refl Hs SC eq_refl D0). Qed.
#[using="X L BL LS k INV Hk NP Hs SC res' X'"] Lemma rm_conc_c : conc rm_st4 c = dst + 16.
Proof. unfold conc, get_region. rewrite rm_regions. fold rid. rewrite lookup_insert_eq. rewrite c16. reflexivity. Qed.
#[using="Type"] Lemma rm_conc_other q : fst q <> rid -> conc rm_st4 q = conc st q.
Proof. intros NE. unfold conc, get_region. rewrite rm_regions, lookup_insert_ne by congruence. reflexivity. Qed.
End REMAP.
