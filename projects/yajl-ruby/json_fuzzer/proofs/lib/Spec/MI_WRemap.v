(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Read
  MI_WFree MI_WFree2 MI_WGroup MI_TF2 MI_WAMeta MI_Ledger Realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma lookup_filter_lt {A} (len : Z) (c : Z) (m : gmap Z A) (k : Z) :
  (filter (fun kv : Z * A => kv.1 * c <? len) m : gmap Z A) !! k = if k * c <? len then m !! k else None.
Proof.
  rewrite map_lookup_filter. destruct (m !! k) as [v|]; cbn; [| destruct (k * c <? len); reflexivity].
  destruct (k * c <? len); cbn; [rewrite option_guard_True by exact I| rewrite option_guard_False by (intros H; exact H)]; reflexivity.
Qed.

Lemma lookup_filter_lt1 {A} (len : Z) (m : gmap Z A) (k : Z) :
  (filter (fun kv : Z * A => kv.1 <? len) m : gmap Z A) !! k = if k <? len then m !! k else None.
Proof.
  rewrite map_lookup_filter. destruct (m !! k) as [v|]; cbn; [| destruct (k <? len); reflexivity].
  destruct (k <? len); cbn; [rewrite option_guard_True by exact I| rewrite option_guard_False by (intros H; exact H)]; reflexivity.
Qed.

Lemma cell_read_trunc len sh o : 0 <= o < len -> cell_read (shadow_trunc len sh) o = cell_read sh o.
Proof.
  intros Ho. unfold cell_read, shadow_trunc. cbn [r_cells r_hav r_havp].
  rewrite lookup_filter_lt1, (lookup_filter_lt len 16), (lookup_filter_lt len 4096).
  replace (o <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (o / 16 * 16 <? len) with true by (symmetry; apply Z.ltb_lt; pose proof (Z.mul_div_le o 16); lia).
  replace (o / 4096 * 4096 <? len) with true by (symmetry; apply Z.ltb_lt; pose proof (Z.mul_div_le o 4096); lia).
  reflexivity.
Qed.

Lemma sh_ticks_trunc len sh t : sh_ticks sh t -> sh_ticks (shadow_trunc len sh) t.
Proof.
  intros [H1 H2]. split; unfold shadow_trunc; cbn [r_hav r_havp].
  - intros u hl ch Hu Hin. rewrite (lookup_filter_lt len 16) in Hu. destruct (u * 16 <? len); [| discriminate]. eauto.
  - intros pg t' Hp. rewrite (lookup_filter_lt len 4096) in Hp. destruct (pg * 4096 <? len); [| discriminate]. eauto.
Qed.

(* [comment removed for export] *)
Lemma g_remove_split' a l0 (l : list (Z * Z)) : In (a, l0) l -> NoDup (map fst l) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst] in Hnd. apply NoDup_cons in Hnd as [Hni Hnd'].
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply list_elem_of_In. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. split; [reflexivity|]. cbn. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bm : aptr) (r needed : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bm g.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Let rid := fst bm.
Let c : aptr := (rid, sstart (MR st g) 0).
Hypothesis HP : x_pend X = Some c.
Hypothesis HO : x_orph X = None.
Let old := r_base (default (mkRegion RKGroup 0 0) (s_regions st !! rid)).
Let old_len := m_maplen (MR st g) * 4096.
Hypothesis OK : mremap_answer_ok (live_ranges st) old old_len needed r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HN : 0 < needed < PTRDIFF_MAX.
Hypothesis HNA : needed mod PGSZ = 0.
Hypothesis HNE : needed <> old_len.
Hypothesis T0 : TF0 st.
Let L' := KInv.set_groups ((r, needed) :: g_remove old (ld_groups L)) L.
Let st' := wr8 (rid, needed - IB) 0 (remap_region rid g r needed st).

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Let F : meta -> meta := m_set_maplen (needed / 4096).
Let nr : region := mkRegion RKGroup r needed.
Let TR : shadow := shadow_trunc needed (get_shadow st rid).
Let SHn : shadow := mkShadow (<[needed - IB := (0, s_tick st)]> (r_cells TR)) (r_hav TR) (r_havp TR).

(* [comment removed for export] *)
Lemma GOg : exists ai, s_groups st !! bm = Some (mkGhdr (Some g) ai) /\ group_ok X st LS g bm ai.
Proof. exact (hosts_ok _ _ _ IG _ _ Hg). Qed.
Lemma g_facts : m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ 0 <= m_maplen (MR st g) /\ ~ in_list LS g /\ snd bm = 0
  /\ exists rg, s_regions st !! rid = Some rg /\ r_kind rg = RKGroup /\ old_len = round_up_pg (r_len rg) /\ old = r_base rg
     /\ 0 < old /\ old mod PGSZ = 0 /\ 0 < r_len rg /\ old + old_len <= alloc_ceiling.
Proof.
  destruct GOg as (ai & Hb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[? ?]|(_ & L0 & ML & NL)]; [lia|].
  pose proof (g_maplen _ _ _ _ _ _ GO) as MLG.
  destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & rg & Hrg & Hk & Hml & _).
  pose proof (ir_shape _ _ _ IR _ _ Hrg) as (S1 & S2 & S3 & S4 & S5 & S6).
  repeat split; auto. exists rg. unfold old. fold rid in Hrg. rewrite Hrg. cbn. repeat split; auto; lia.
Qed.
Lemma g_stride : get_stride (MR st g) = old_len - UNIT.
Proof.
  destruct g_facts as (L0 & ML & _). unfold get_stride, old_len. rewrite L0, (proj2 (Z.eqb_neq _ _) ML). reflexivity.
Qed.
Lemma gbase_g : gbase (MR st g) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
Lemma c_eq : c = (rid, UNIT). Proof. unfold c, sstart. rewrite gbase_g, (proj1 (proj2 (proj2 (proj2 (proj2 g_facts))))). f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma grp_alone b' m' : hosts st b' m' -> fst b' = rid -> m' = g.
Proof.
  intros Hm' Hf. destruct (aptr_eq_dec m' g) as [->|NE]; [reflexivity|]. exfalso.
  destruct g_facts as (L0 & ML & _).
  destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [Hml'|Hml'].
  - destruct (@top_chain _ _ _ _ IM IG IS m' b' Hm' Hml') as (t & j & cc & bt & Ha & Ht & Htop & Hft).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt bm Ht Hg Htop ML); unfold rid in Hf; congruence). subst t.
    destruct (@anc_facts _ _ _ _ IM IG IS m' g j cc Ha) as (bm' & bp' & _ & _ & _ & _ & _ & _ & _ & _ & SC). lia.
  - apply NE. exact (@top_unique _ _ _ IG m' g b' bm Hm' Hg Hml' ML Hf).
Qed.
Lemma grp_alone_b b' m' : hosts st b' m' -> fst b' = rid -> b' = bm.
Proof. intros Hm' Hf. pose proof (grp_alone b' m' Hm' Hf) as ->. exact (hosts_inj _ _ _ IM _ _ _ Hm' Hg). Qed.

(* [comment removed for export] *)
Lemma slot_alone s m' j : s_slots st !! s = Some (m', j) -> fst s = rid -> m' = g /\ j = 0 /\ s = c.
Proof.
  intros Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & Hj & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ j Hb') in Es. subst s. cbn [fst] in Hf.
  pose proof (grp_alone b' m' Hb' Hf) as ->. destruct g_facts as (L0 & _). assert (j = 0) by lia. subst j.
  split; [reflexivity|]. split; [reflexivity|]. unfold c. f_equal. exact Hf.
Qed.
Lemma no_blk k : In k BL -> fst (bslot k) <> rid.
Proof.
  intros Hk Hf. destruct (is_blocks _ _ _ IS k Hk) as (m' & j & Hs & _).
  destruct (slot_alone _ _ _ Hs Hf) as (-> & -> & Es).
  destruct GOg as (ai & Hb & GO). destruct g_facts as (L0 & _).
  pose proof (is_part _ _ _ IS _ _ _ 0 Hb ltac:(lia)) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ 0 Hg) in P. fold rid c in P.
  unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| exact HP].
  rewrite <- Es. apply in_map. exact Hk.
Qed.
Lemma no_grp_c : s_groups st !! c = None.
Proof.
  destruct GOg as (ai & Hb & GO). destruct g_facts as (L0 & _).
  pose proof (is_part _ _ _ IS _ _ _ 0 Hb ltac:(lia)) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ 0 Hg) in P. fold rid c in P.
  unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE).
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. apply nDE. split; [congruence| exact HP].
Qed.
Lemma no_nested b' m' : hosts st b' m' -> m_maplen (MR st m') = 0 -> fst b' <> rid.
Proof. intros Hm' Hml Hf. pose proof (grp_alone _ _ Hm' Hf) as ->. destruct g_facts as (_ & ML & _). exact (ML Hml). Qed.

(* [comment removed for export] *)
Lemma ans_facts :
  0 < r /\ r mod PGSZ = 0 /\ r + needed <= alloc_ceiling
  /\ ((r = old /\ (needed < old_len \/ ranges_free (live_ranges st) (old + old_len) (needed - old_len) = true))
      \/ (r <> old /\ ranges_free (live_ranges st) r needed = true)).
Proof.
  destruct g_facts as (_ & _ & _ & _ & _ & rg & Hrg & Hk & Hol & Hold & O0 & OM & RL & OC).
  pose proof OK as H. unfold mremap_answer_ok in H.
  assert (EF : is_errno_form r = false).
  { unfold is_errno_form, is_err, TWO64 in *. apply Z.ltb_ge in NERR. apply Bool.andb_false_iff. left. apply Z.leb_gt. lia. }
  rewrite EF in H. cbn [orb] in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.andb_true_iff in H as [E H]. apply Z.eqb_eq in E. subst r.
    split; [exact O0|]. split; [exact OM|].
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + apply Z.ltb_lt in H. split; [lia|]. left. auto.
    + apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|]. left. auto.
  - apply Bool.andb_true_iff in H as [H H5]. apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3].
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4.
    split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. right. auto.
Qed.

(* [comment removed for export] *)
Local Ltac peel := unfold st', remap_region, upd_meta, put_meta;
  rewrite ?s_ctx_wr8, ?s_groups_wr8, ?s_slots_wr8, ?s_areas_wr8, ?s_tick_wr8, ?s_secret_wr8, ?s_reserved_wr8, ?s_next_rid_wr8, ?s_regions_wr8, ?s_metas_wr8,
          ?s_ctx_set_metas, ?s_groups_set_metas, ?s_slots_set_metas, ?s_areas_set_metas, ?s_tick_set_metas, ?s_secret_set_metas, ?s_reserved_set_metas, ?s_next_rid_set_metas, ?s_regions_set_metas, ?s_shadow_set_metas,
          ?s_ctx_upd_shadow, ?s_groups_upd_shadow, ?s_slots_upd_shadow, ?s_areas_upd_shadow, ?s_tick_upd_shadow, ?s_secret_upd_shadow, ?s_reserved_upd_shadow, ?s_next_rid_upd_shadow, ?s_regions_upd_shadow, ?s_metas_upd_shadow,
          ?s_ctx_upd_region, ?s_groups_upd_region, ?s_slots_upd_region, ?s_areas_upd_region, ?s_tick_upd_region, ?s_secret_upd_region, ?s_reserved_upd_region, ?s_next_rid_upd_region, ?s_shadow_upd_region, ?s_metas_upd_region.

Lemma E_ctx : s_ctx st' = s_ctx st. Proof. peel. reflexivity. Qed.
Lemma E_groups : s_groups st' = s_groups st. Proof. peel. reflexivity. Qed.
Lemma E_slots : s_slots st' = s_slots st. Proof. peel. reflexivity. Qed.
Lemma E_areas : s_areas st' = s_areas st. Proof. peel. reflexivity. Qed.
Lemma E_tick : s_tick st' = s_tick st. Proof. peel. reflexivity. Qed.
Lemma E_secret : s_secret st' = s_secret st. Proof. peel. reflexivity. Qed.
Lemma E_reserved : s_reserved st' = s_reserved st. Proof. peel. reflexivity. Qed.
Lemma E_next_rid : s_next_rid st' = s_next_rid st. Proof. peel. reflexivity. Qed.
Lemma E_regions : s_regions st' = <[rid := nr]> (s_regions st).
Proof.
  destruct g_facts as (_ & _ & _ & _ & _ & rg & Hrg & Hk & _).
  peel. unfold upd_region, get_region. fold rid. rewrite Hrg. rewrite s_regions_set_regions. unfold nr. rewrite Hk. reflexivity.
Qed.
Lemma E_metas : s_metas st' = <[g := F (MR st g)]> (s_metas st).
Proof.
  unfold st', remap_region. rewrite s_metas_wr8, s_metas_upd_meta. unfold MR. f_equal; [| rewrite s_metas_upd_shadow, s_metas_upd_region; reflexivity].
  f_equal. apply get_meta_rec_ext. rewrite s_metas_upd_shadow, s_metas_upd_region. reflexivity.
Qed.
Lemma E_shadow : s_shadow st' = <[rid := SHn]> (s_shadow st).
Proof.
  unfold st', wr8. rewrite s_shadow_upd_shadow. cbn [fst snd].
  assert (E3 : s_shadow (remap_region rid g r needed st) = <[rid := TR]> (s_shadow st)).
  { unfold remap_region, upd_meta, put_meta. rewrite s_shadow_set_metas, s_shadow_upd_shadow, s_shadow_upd_region. unfold TR. f_equal. f_equal.
    apply get_shadow_ext. apply s_shadow_upd_region. }
  assert (ET : s_tick (remap_region rid g r needed st) = s_tick st).
  { unfold remap_region, upd_meta, put_meta. rewrite s_tick_set_metas, s_tick_upd_shadow, s_tick_upd_region. reflexivity. }
  rewrite ET, (get_shadow_eq _ rid), E3, lookup_insert_eq. cbn [default from_option id]. rewrite insert_insert_eq. unfold SHn. change (Z.land 0 255) with 0. reflexivity.
Qed.

Lemma LK q : s_regions st' !! q = if (q =? rid)%N then Some nr else s_regions st !! q.
Proof. rewrite E_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| apply lookup_insert_ne; congruence]. Qed.
Lemma SOME q rq : s_regions st' !! q = Some rq -> (q = rid /\ rq = nr) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma KEEP q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st' !! q = Some rq.
Proof. intros Hq NE. rewrite LK. destruct (N.eqb_spec q rid); [congruence| exact Hq]. Qed.
Lemma KEEPM q rq : s_regions st !! q = Some rq -> is_metakind rq -> s_regions st' !! q = Some rq.
Proof.
  intros Hq K. apply KEEP; [exact Hq|]. intros ->. destruct g_facts as (_ & _ & _ & _ & _ & rg & Hrg & Hk & _).
  rewrite Hrg in Hq. inversion Hq. subst. destruct K; congruence.
Qed.
Lemma KEEPK q rq knd : s_regions st !! q = Some rq -> r_kind rq = knd -> knd <> RKGroup -> s_regions st' !! q = Some rq.
Proof.
  intros Hq K NK. apply KEEP; [exact Hq|]. intros ->. destruct g_facts as (_ & _ & _ & _ & _ & rg & Hrg & Hk & _).
  rewrite Hrg in Hq. inversion Hq. subst. congruence.
Qed.
Lemma E_frontier q rq : frontier st' q rq = frontier st q rq.
Proof. unfold frontier. rewrite E_ctx. reflexivity. Qed.

Lemma R'_eq x : MR st' x = if aptr_eqb x g then F (MR st g) else MR st x.
Proof.
  unfold MR at 1, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x g) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma R'_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite R'_eq, (aptr_eqb_neq _ _ NE). reflexivity. Qed.
Lemma R'_g : MR st' g = F (MR st g). Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
Lemma F_maplen : m_maplen (F (MR st g)) = needed / 4096.
Proof.
  unfold F, m_set_maplen. cbn. pose proof (Z.div_pos needed 4096 ltac:(lia) ltac:(lia)).
  assert (needed / 4096 < 2 ^ 52) by (apply Z.div_lt_upper_bound; unfold PTRDIFF_MAX in *; lia).
  change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma ND : needed / 4096 * 4096 = needed.
Proof. pose proof (Z.div_mod needed 4096 ltac:(lia)). unfold PGSZ in *. lia. Qed.
Lemma N1 : 1 <= needed / 4096.
Proof. apply Z.div_le_lower_bound; [lia|]. pose proof ND. pose proof (Z.div_pos needed 4096). unfold PGSZ in *. nia. Qed.
Lemma F_stride : get_stride (F (MR st g)) = needed - UNIT.
Proof.
  destruct g_facts as (L0 & _). unfold get_stride. rewrite F_maplen. replace (m_last_idx (F (MR st g))) with 0 by (unfold F, m_set_maplen; cbn; lia).
  cbn [Z.eqb andb negb]. pose proof N1. destruct (Z.eqb_spec (needed / 4096) 0); [lia|]. cbn. rewrite ND. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma F_last x : m_last_idx (F x) = m_last_idx x. Proof. reflexivity. Qed.
Lemma F_sc x : m_sizeclass (F x) = m_sizeclass x. Proof. reflexivity. Qed.
Lemma F_freeable x : m_freeable (F x) = m_freeable x. Proof. reflexivity. Qed.
Lemma F_avail x : m_avail (F x) = m_avail x. Proof. reflexivity. Qed.
Lemma F_freed x : m_freed (F x) = m_freed x. Proof. reflexivity. Qed.
Lemma F_memf x : m_mem (F x) = m_mem x. Proof. reflexivity. Qed.
Lemma F_gbase x : gbase (F x) = gbase x. Proof. reflexivity. Qed.
Lemma R'_mem x : m_mem (MR st' x) = m_mem (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev x : m_prev (MR st' x) = m_prev (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next x : m_next (MR st' x) = m_next (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last x : m_last_idx (MR st' x) = m_last_idx (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freeable x : m_freeable (MR st' x) = m_freeable (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc x : m_sizeclass (MR st' x) = m_sizeclass (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_avail x : m_avail (MR st' x) = m_avail (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freed x : m_freed (MR st' x) = m_freed (MR st x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase x : gbase (MR st' x) = gbase (MR st x). Proof. unfold gbase. rewrite R'_mem. reflexivity. Qed.
Lemma R'_cnt x : cnt_of (MR st' x) = cnt_of (MR st x). Proof. unfold cnt_of. rewrite R'_last. reflexivity. Qed.
Lemma R'_maplen_other x : x <> g -> m_maplen (MR st' x) = m_maplen (MR st x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_stride_other x : x <> g -> get_stride (MR st' x) = get_stride (MR st x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_maplen_g : m_maplen (MR st' g) = needed / 4096. Proof. rewrite R'_g. apply F_maplen. Qed.
Lemma R'_maplen_g_nz : m_maplen (MR st' g) <> 0. Proof. rewrite R'_maplen_g. pose proof N1. lia. Qed.
Lemma R'_sstart0 x : sstart (MR st' x) 0 = sstart (MR st x) 0. Proof. unfold sstart. rewrite R'_gbase. lia. Qed.
Lemma R'_slot_start'0 x : slot_start' (MR st' x) 0 = slot_start' (MR st x) 0.
Proof. rewrite !slot_start'_sstart, R'_gbase, R'_sstart0. reflexivity. Qed.
Lemma R'_sstart_other x i : x <> g -> sstart (MR st' x) i = sstart (MR st x) i. Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_slot_start'_other x i : x <> g -> slot_start' (MR st' x) i = slot_start' (MR st x) i. Proof. intros; rewrite R'_other; auto. Qed.

Lemma hosts' b m : hosts st' b m <-> hosts st b m. Proof. apply hosts_ext. exact E_groups. Qed.
Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. exact E_groups. Qed.
Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  rewrite E_metas. destruct (aptr_eq_dec x g) as [->|NE]; [rewrite lookup_insert_eq; split; [auto| discriminate]|].
  rewrite lookup_insert_ne by congruence. tauto.
Qed.
Lemma Gpres : s_metas st !! g <> None. Proof. destruct GOg as (ai & Hb & GO). exact (g_present _ _ _ _ _ _ GO). Qed.
Lemma g_mem : m_mem (MR st g) = Some bm. Proof. exact (hosts_mem _ _ _ IM _ _ Hg). Qed.

(* [comment removed for export] *)
Lemma R'_slot_start' x i : (x = g -> i = 0) -> slot_start' (MR st' x) i = slot_start' (MR st x) i.
Proof.
  intros Hi. destruct (aptr_eq_dec x g) as [->|NE]; [rewrite (Hi eq_refl); apply R'_slot_start'0| apply R'_slot_start'_other; exact NE].
Qed.

(* [comment removed for export] *)
Lemma get_shadow' q : get_shadow st' q = if (q =? rid)%N then SHn else get_shadow st q.
Proof.
  unfold get_shadow. rewrite E_shadow. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma sh_ticks_st q : sh_ticks (get_shadow st q) (s_tick st).
Proof.
  unfold get_shadow. destruct (s_shadow st !! q) as [sh|] eqn:E; cbn; [| split; cbn; intros; rewrite lookup_empty in *; discriminate].
  destruct (ish_ticks _ _ ISH q sh E) as (_ & H2 & H3). split; eauto.
Qed.
Lemma cell_read_other q : fst q <> rid -> cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros NE. rewrite get_shadow'. destruct (N.eqb_spec (fst q) rid); [congruence| reflexivity]. Qed.
Lemma cell_read_low o : 0 <= o < needed -> o <> needed - IB -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros Ho NE. rewrite get_shadow', N.eqb_refl. unfold SHn. rewrite <- (cell_read_trunc needed (get_shadow st rid) o Ho). fold TR.
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma cell_read_end : cell_read (get_shadow st' rid) (needed - IB) = Known 0.
Proof.
  rewrite get_shadow', N.eqb_refl. unfold SHn, cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  pose proof (sh_ticks_trunc needed _ _ (sh_ticks_st rid)) as HT. fold TR in HT.
  rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
Lemma known_keep q v : (fst q = rid -> 0 <= snd q < needed /\ snd q <> needed - IB) -> known st q v -> known st' q v.
Proof.
  intros Hq K. unfold known, SHd in *. destruct (N.eq_dec (fst q) rid) as [E|NE].
  - destruct (Hq E) as [Ho No]. rewrite E in K |- *. rewrite cell_read_low; assumption.
  - rewrite cell_read_other; assumption.
Qed.
Lemma unknown_keep q : (fst q = rid -> 0 <= snd q < needed /\ snd q <> needed - IB) -> unknown st q -> unknown st' q.
Proof.
  intros Hq [h K]. exists h. unfold SHd in *. destruct (N.eq_dec (fst q) rid) as [E|NE].
  - destruct (Hq E) as [Ho No]. rewrite E in K |- *. rewrite cell_read_low; assumption.
  - rewrite cell_read_other; assumption.
Qed.


(* [comment removed for export] *)
Lemma groups_nodup : NoDup (map fst (ld_groups L)).
Proof.
  pose proof (ir_groups _ _ _ IR) as PG.
  apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact (Permutation_map fst (Permutation_sym PG))|]. apply (proj1 (NoDup_ListNoDup _)).
  rewrite map_map. cbn [fst snd].
  assert (GEN : forall l : list (N * region), NoDup (map fst l) -> (forall q rq, In (q, rq) l -> s_regions st !! q = Some rq) ->
            NoDup (map (fun x : N * region => r_base (snd x)) (List.filter (fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end) l))).
  { intros l. induction l as [|[q rq] l IH]; intros ND HIn; cbn; [constructor|].
    cbn in ND. apply NoDup_cons in ND as [N1 N2].
    assert (IH' := IH N2 ltac:(intros q' rq' H'; apply HIn; right; exact H')).
    destruct (r_kind rq) eqn:K; cbn; try exact IH'.
    apply NoDup_cons. split; [| exact IH'].
    intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin as ([q2 rq2] & E & Hin2). cbn in E.
    apply filter_In in Hin2 as [Hin2 K2]. cbn in K2. destruct (r_kind rq2) eqn:K2'; try discriminate.
    pose proof (HIn q rq (or_introl eq_refl)) as Hq. pose proof (HIn q2 rq2 (or_intror Hin2)) as Hq2.
    assert (NEq : q <> q2).
    { intros ->. apply N1. apply list_elem_of_In. apply in_map_iff. exists (q2, rq2). auto. }
    pose proof (ir_disj _ _ _ IR q q2 rq rq2 Hq Hq2 NEq) as D. unfold region_live_range in D. rewrite K, K2' in D.
    pose proof (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & P1 & _). pose proof (ir_shape _ _ _ IR _ _ Hq2) as (_ & _ & P2 & _).
    pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len rq2)). lia. }
  apply GEN.
  - apply NoDup_fst_map_to_list.
  - intros q rq H. apply In_map_to_list_regions. exact H.
Qed.

Lemma R_part : inv_R X st' L'.
Proof.
  destruct g_facts as (L0 & ML & MLG & NL & B0 & rg & Hrg & Hk & Hol & Hold & O0 & OM & RL & OC).
  destruct ans_facts as (R0 & RM & RC & CASES).
  assert (RU : round_up_pg needed = needed) by (apply round_up_pg_id; exact HNA).
  pose proof (round_up_ge (r_len rg)) as RG.
  (* [comment removed for export] *)
  assert (LPOS : forall q rq, s_regions st !! q = Some rq -> let '(b2, l2) := region_live_range rq in 0 < l2).
  { intros q rq Hq. pose proof (ir_shape _ _ _ IR _ _ Hq) as (T1 & T2 & T3 & T4 & T5 & T6). pose proof (round_up_ge (r_len rq)).
    unfold region_live_range. destruct (r_kind rq) eqn:K; lazy beta iota zeta;
      first [ destruct (T6 ltac:(left; exact K)) as [M2 L2]; rewrite (round_up_pg_id _ M2); clear -M2 L2; unfold PGSZ in *; lia
            | clear -T3 H; lia ]. }
  assert (DISJ : forall q rq, s_regions st !! q = Some rq -> q <> rid ->
            let '(b2, l2) := region_live_range rq in r + needed <= b2 \/ b2 + l2 <= r).
  { intros q rq Hq NEq. pose proof (ir_disj _ _ _ IR rid q rg rq Hrg Hq ltac:(congruence)) as D. unfold region_live_range in D at 1. rewrite Hk in D.
    rewrite <- Hol, <- Hold in D. pose proof (LPOS q rq Hq) as LP.
    destruct CASES as [[-> [SH|FR]]|[NE FR]].
    - destruct (region_live_range rq) as [b2 l2]. clear -D SH LP. lia.
    - pose proof (ranges_free_regions st _ _ q rq FR Hq) as D2. destruct (region_live_range rq) as [b2 l2]. clear -D D2 LP HN. lia.
    - pose proof (ranges_free_regions st _ _ q rq FR Hq) as D2. destruct (region_live_range rq) as [b2 l2]. exact D2. }
  destruct IR; constructor; rewrite ?E_next_rid, ?E_reserved, ?E_ctx.
  - intros q rq Hq. apply SOME in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hrg)| exact (ir_ids _ _ Hq)].
  - intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
    split; [exact R0|]. split; [exact RM|]. split; [lia|]. split; [unfold PTRDIFF_MAX, LEN_MAX in *; lia|]. split; [exact RC|].
    intros [K|K]; discriminate.
  - intros q1 q2 r1 r2 H1 H2 NE.
    apply SOME in H1 as [[-> ->]|[N1' H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
    + cbn. rewrite RU. pose proof (DISJ q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
    + pose proof (DISJ q1 r1 H1 N1') as D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
  - exact ir_resv.
  - (* [comment removed for export] *) unfold L'. cbn [KInv.ld_groups KInv.set_groups].
    assert (P1 : Permutation (map (fun kr : N * region => (r_base (snd kr), r_len (snd kr)))
                                  (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st))))
                             ((old, r_len rg) :: map (fun kr : N * region => (r_base (snd kr), r_len (snd kr)))
                                  (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (delete rid (s_regions st)))))).
    { eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ Hrg)|].
      cbn [List.filter map snd]. rewrite Hk. cbn [map snd]. rewrite Hold. apply Permutation_refl. }
    assert (P2 : Permutation (map (fun kr : N * region => (r_base (snd kr), r_len (snd kr)))
                                  (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st'))))
                             ((r, needed) :: map (fun kr : N * region => (r_base (snd kr), r_len (snd kr)))
                                  (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (delete rid (s_regions st)))))).
    { rewrite E_regions.
      eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ rid nr); apply lookup_insert_eq|].
      rewrite delete_insert_eq. cbn [List.filter map snd nr r_kind r_base r_len]. apply Permutation_refl. }
    eapply Permutation_trans; [| apply Permutation_sym; exact P2]. apply perm_skip.
    assert (Hin : In (old, r_len rg) (ld_groups L)).
    { eapply Permutation_in; [apply Permutation_sym; exact ir_groups|]. eapply Permutation_in; [apply Permutation_sym; exact P1|]. left. reflexivity. }
    destruct (g_remove_split' old (r_len rg) (ld_groups L) Hin groups_nodup) as (l1 & l2 & EL & ->).
    apply Permutation_sym. apply Permutation_cons_app_inv with (a := (old, r_len rg)). rewrite <- EL.
    eapply Permutation_trans; [| apply Permutation_sym; exact ir_groups]. apply Permutation_sym. exact P1.
  - (* [comment removed for export] *) unfold L'. cbn [KInv.ld_metas KInv.set_groups].
    eapply Permutation_trans; [exact ir_metas|].
    eapply Permutation_trans; [| apply Permutation_map; rewrite E_regions; apply (regions_update_perm st rid rg nr _ Hrg); [cbn [snd]; rewrite Hk; reflexivity| reflexivity]].
    erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn [fst snd]. rewrite E_frontier. reflexivity.
  - intros q rq Hq Kq. rewrite E_frontier. apply SOME in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (ir_metalen q rq Hq Kq)].
  - intros q rq Hq Kq. rewrite E_frontier. apply SOME in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (ir_brkfront q rq Hq Kq)].
  - destruct ir_shift as [S1 [S2|(q & rq & Hq & Kq & Eq)]]; split; [exact S1| left; exact S2| exact S1|].
    right. exists q, rq. split; [apply (KEEPK q rq RKMeta Hq Kq); discriminate| auto].
  - intros b l. unfold L'. cbn [KInv.ld_brkreg KInv.set_groups]. rewrite ir_brkreg. split; intros (q & rq & Hq & Kq & E1 & E2); exists q, rq.
    + split; [apply (KEEPK q rq RKBrk Hq Kq); discriminate| auto].
    + apply SOME in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply SOME in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply SOME in H2 as [[-> ->]|[_ H2]]; [discriminate|].
    exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
  - unfold L'. cbn [KInv.ld_brk KInv.set_groups]. revert ir_brk. destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
    + destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
    + exact IBK.
    + destruct IBK as [B (rq & Hq & Kq & Eq)]. split; [exact B|]. exists rq. split; [apply (KEEPK _ rq RKBrk Hq Kq); discriminate| auto].
  - destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
    intros q off Eo. destruct (C3 q off Eo) as (rq & Hq & Kq & Bq). exists rq. split; [apply KEEPM; assumption| auto].
  - intros q Hq. rewrite HO in Hq. discriminate.
Qed.


(* [comment removed for export] *)
Lemma A_part : inv_A st'.
Proof.
  destruct IA; constructor; rewrite ?E_ctx, ?E_areas, ?E_secret; try assumption.
  - intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & Fr) & rest). split; [| exact rest].
    exists rq. rewrite E_frontier. split; [apply KEEPM; assumption| auto].
  - intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
    destruct K as [K| ->].
    + destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct (s_metas st !! g) as [mr0|] eqn:E; [| exfalso; exact (Gpres E)]. exact (ia_metas g mr0 E).
  - destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
    intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
    assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
    + apply K. apply Hk. exact Hk2.
    + apply Gpres. rewrite <- K. apply Hk. exact Hk2.
  - intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [apply KEEPM; assumption| exact Kq].
  - intros sc Hsc. unfold usage, ctx. rewrite E_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
    unfold gcnt. rewrite E_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
    rewrite R'_sc, R'_cnt. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma M_part : inv_M X st' LS.
Proof.
  pose proof IM as IM0. destruct IM as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; pose proof g_mem; congruence|].
    apply M1. exact Hm.
  - intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
  - intros bb h Hb. rewrite E_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
  - intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
    rewrite E_metas. destruct (aptr_eq_dec m g) as [->|NE]; [| rewrite lookup_insert_ne by congruence; exact E].
    exfalso. pose proof g_mem as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
  - intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, E_groups. repeat split; auto. exists bb. auto.
Qed.

(* [comment removed for export] *)
Lemma L_part : inv_L st' LS.
Proof.
  pose proof IM as IM0. destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite <- (L1 h). apply get_head_ext. exact E_ctx.
  - intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
    eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
  - exact L3.
  - exact L4.
  - intros m. rewrite R'_next, R'_prev. apply L5.
  - intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
    exfalso. pose proof (L6 g Hm) as Z0. pose proof g_mem as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
  - intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
  - exact L9.
Qed.

(* [comment removed for export] *)
Lemma G_part : inv_G X st' LS.
Proof.
  pose proof IM as IM0. pose proof IS as IS0. destruct g_facts as (L0 & ML & MLG & NL & B0 & rg & Hrg & Hk & Hol & Hold & O0 & OM & RL & OC).
  destruct ans_facts as (R0 & RM & RC & _).
  destruct IG as [G1 G2 G3 G4 G5]; constructor.
  - intros m bb aim Hm. rewrite E_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
    destruct (aptr_eqb_spec m g) as [->|NE].
    + (* [comment removed for export] *)
      pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) Hg) as Ebb. subst bb.
      pose proof N1 as N1'.
      destruct GO; constructor; rewrite ?R'_g, ?F_last, ?F_sc, ?F_freeable, ?F_avail, ?F_freed, ?F_maplen, ?F_stride, ?E_slots; try assumption.
      all: lazymatch goal with
           | |- s_metas st' !! g <> None => apply keys'; right; reflexivity
           | |- _ \/ _ => right; rewrite SC63; split; [reflexivity|]; split; [exact L0|]; split; [clear -N1'; lia| exact NL]
           | |- 0 <= needed / 4096 => clear -N1'; lia
           | |- x_fresh X <> Some g -> _ -> In g _ => intros NF Hp; exfalso; pose proof g_ai; clear -Hp g_ai L0; lia
           | |- x_fresh X <> Some g -> m_sizeclass _ < 48 -> _ => intros NF Hsc; exfalso; rewrite SC63 in Hsc; clear -Hsc; lia
           | |- x_fresh X <> Some g -> forall sc, _ => intros NF sc Hin; exfalso; apply NL; exists (LActive sc); exact Hin
           | |- m_sizeclass _ < 48 -> _ => intros Hsc; exfalso; rewrite SC63 in Hsc; clear -Hsc; lia
           | |- needed / 4096 = 0 -> _ => intros H; exfalso; clear -H N1'; lia
           | |- needed / 4096 <> 0 -> _ =>
               intros _; split; [exact B0|]; exists nr; split; [unfold rid; rewrite LK, N.eqb_refl; reflexivity|]; split; [reflexivity|];
               cbn [nr r_len]; rewrite ND, (round_up_pg_id _ HNA); split; [reflexivity|];
               unfold gend, cnt_of, sstart; rewrite F_last, F_gbase, F_stride, gbase_g, B0, L0; clear; unfold UNIT; lia
           | |- ?G => idtac "REMAINS" G
           end.
    + assert (NEb : fst bb <> rid) by (intros Hf; apply NE; exact (grp_alone bb m (ex_intro _ aim Hm) Hf)).
      destruct GO; constructor; rewrite ?(R'_other m NE), ?E_slots; try assumption.
      * apply keys'. left. assumption.
      * intros Hml. destruct (g_top Hml) as (H0 & rq & Hq & Kq & E1 & E2). split; [exact H0|]. exists rq. split; [apply KEEP; assumption| auto].
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hstr). exists p, i.
        assert (NEp : p <> g) by (intros ->; rewrite SC63 in Hsc; lia).
        rewrite !(R'_other p NEp). auto 10.
  - intros bb aim H. rewrite E_groups in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite E_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
  - intros q rq Hq Kq Ho. apply SOME in Hq as [[-> ->]|[NEq Hq]].
    + exists g. split; [| exact R'_maplen_g_nz]. apply hosts'. replace (rid, 0) with bm by (unfold rid; destruct bm; cbn in B0 |- *; subst; reflexivity). exact Hg.
    + destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m. rewrite hosts'. split; [exact Hm|].
      rewrite R'_maplen_other; [exact Hml|]. intros ->. apply NEq. symmetry. pose proof (hosts_inj _ _ _ IM0 _ _ _ Hm Hg) as Eq. unfold rid. rewrite <- Eq. reflexivity.
  - intros bb h H. rewrite E_groups in H. destruct (G5 bb h H) as (rq & Hq & Kq).
    destruct (N.eq_dec (fst bb) rid) as [E|NEq]; [exists nr; rewrite E, LK, N.eqb_refl; split; reflexivity|].
    exists rq. split; [apply KEEP; assumption| exact Kq].
Qed.

(* [comment removed for export] *)
Lemma S_part : inv_S X st' BL.
Proof.
  pose proof IM as IM0. destruct g_facts as (L0 & ML & _).
  assert (SS : forall m i, (m = g -> 0 <= i <= m_last_idx (MR st m)) -> slot_start' (MR st' m) i = slot_start' (MR st m) i).
  { intros m i Hi. apply R'_slot_start'. intros ->. specialize (Hi eq_refl). lia. }
  destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite E_slots in H. destruct (S1 s m i H) as (? & Hi & ?). rewrite live', R'_last, SS; auto.
  - intros bb m i Hb Hi. rewrite R'_last in Hi. rewrite E_slots, SS by auto. apply (S2 bb); [apply hosts'; exact Hb| exact Hi].
  - intros bb m aim i Hb Hi. rewrite E_groups in Hb. rewrite R'_last in Hi. rewrite E_groups, R'_avail, R'_freed, SS by auto.
    exact (S3 bb m aim i Hb Hi).
  - intros s Hs. rewrite E_slots. apply S4. exact Hs.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & Hs & REST). exists m, i. rewrite E_slots. split; [exact Hs|].
    rewrite R'_stride_other; [exact REST|]. intros ->. apply (no_blk k Hk).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & _ & Es). rewrite (slot_start'_eq _ _ _ IM0 _ _ i Hb') in Es. rewrite Es. cbn [fst].
    pose proof (hosts_inj _ _ _ IM0 _ _ _ Hb' Hg) as ->. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma N4096 : 4096 <= needed.
Proof. pose proof ND. pose proof N1. lia. Qed.

Lemma SH_part : inv_SH st' BL.
Proof.
  pose proof IM as IM0. pose proof IS as IS0.
  destruct g_facts as (L0 & ML & MLG & NL & B0 & rg & Hrg & Hk & Hol & Hold & O0 & OM & RL & OC).
  pose proof N4096 as N4.
  assert (Ebm : bm = (rid, 0)) by (unfold rid; destruct bm; cbn in B0 |- *; subst; reflexivity).
  destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros q sh Hq. rewrite E_shadow in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + exists nr. split; [rewrite LK, N.eqb_refl; reflexivity| reflexivity].
    + rewrite lookup_insert_ne in Hq by congruence. destruct (D1 q sh Hq) as (rq & Hrq & Kq). exists rq. split; [apply KEEP; assumption| exact Kq].
  - intros q sh Hq. rewrite E_tick. rewrite E_shadow in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-.
      assert (OLD : forall sh0, s_shadow st !! rid = Some sh0 ->
                (forall o v t, r_cells sh0 !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
                /\ (forall u hl ch, r_hav sh0 !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
                /\ (forall pg t, r_havp sh0 !! pg = Some t -> (t <= s_tick st)%N)) by (intros sh0 H0; exact (D2 rid sh0 H0)).
      unfold SHn, TR, shadow_trunc, get_shadow. cbn [r_cells r_hav r_havp].
      destruct (s_shadow st !! rid) as [sh0|] eqn:E0; cbn [default from_option id].
      * destruct (OLD sh0 eq_refl) as (C1 & C2 & C3). split; [| split].
        -- intros o v t Ho. destruct (Z.eq_dec o (needed - IB)) as [->|NEo].
           ++ rewrite lookup_insert_eq in Ho. injection Ho as <- <-. split; [lia| reflexivity].
           ++ rewrite lookup_insert_ne in Ho by congruence. rewrite lookup_filter_lt1 in Ho. destruct (o <? needed); [| discriminate]. eauto.
        -- intros u hl ch Hu Hin. rewrite (lookup_filter_lt needed 16) in Hu. destruct (u * 16 <? needed); [| discriminate]. eauto.
        -- intros pg t Hp. rewrite (lookup_filter_lt needed 4096) in Hp. destruct (pg * 4096 <? needed); [| discriminate]. eauto.
      * split; [| split].
        -- intros o v t Ho. destruct (Z.eq_dec o (needed - IB)) as [->|NEo].
           ++ rewrite lookup_insert_eq in Ho. injection Ho as <- <-. split; [lia| reflexivity].
           ++ rewrite lookup_insert_ne in Ho by congruence. rewrite lookup_filter_lt1 in Ho. cbn in Ho. destruct (o <? needed); rewrite ?lookup_empty in Ho; discriminate.
        -- intros u hl ch Hu Hin. rewrite (lookup_filter_lt needed 16) in Hu. cbn in Hu. destruct (u * 16 <? needed); rewrite ?lookup_empty in Hu; discriminate.
        -- intros pg t Hp. rewrite (lookup_filter_lt needed 4096) in Hp. cbn in Hp. destruct (pg * 4096 <? needed); rewrite ?lookup_empty in Hp; discriminate.
    + rewrite lookup_insert_ne in Hq by congruence. exact (D2 q sh Hq).
  - intros b m i Hb Hi. apply hosts' in Hb. rewrite R'_cnt in Hi.
    destruct (aptr_eq_dec m g) as [->|NE].
    + pose proof (hosts_inj _ _ _ IM0 _ _ _ Hb Hg) as ->. rewrite Ebm. cbn [fst].
      unfold cnt_of in Hi. rewrite L0 in Hi.
      assert (S0 : sstart (MR st' g) 0 = UNIT) by (rewrite R'_sstart0; unfold sstart; rewrite gbase_g, B0; lia).
      assert (S1 : sstart (MR st' g) 1 = needed) by (unfold sstart; rewrite R'_gbase, R'_g, F_stride, gbase_g, B0; lia).
      destruct (Z.eq_dec i 0) as [->|NEi].
      * rewrite S0. apply known_keep; [cbn; intros _; unfold UNIT, IB; lia|].
        pose proof (D3 bm g 0 Hg ltac:(unfold cnt_of; lia)) as K. rewrite Ebm in K. cbn [fst] in K. unfold sstart in K. rewrite gbase_g, Ebm in K. cbn [snd] in K.
        replace (0 + UNIT + get_stride (MR st g) * 0 - IB) with (UNIT - IB) in K by lia. exact K.
      * assert (i = 1) by lia. subst i. rewrite S1. unfold known, SHd. cbn [fst snd]. apply cell_read_end.
    + assert (NEb : fst b <> rid) by (intros Hf; exact (NE (grp_alone b m Hb Hf))).
      rewrite (R'_sstart_other m i NE). apply known_keep; [cbn; intros E; exfalso; exact (NEb E)|]. apply (D3 b m i Hb). rewrite <- (R'_cnt m) in Hi. rewrite R'_other in Hi by exact NE. exact Hi.
  - intros b m o Hb Ho. apply hosts' in Hb. apply unknown_keep; [| exact (D4 b m o Hb Ho)]. cbn. intros Hf.
    pose proof (grp_alone_b b m Hb Hf) as ->. rewrite B0. unfold IB. lia.
  - intros b m p i Hb Hml Hs. apply hosts' in Hb. rewrite E_slots in Hs.
    destruct (aptr_eq_dec m g) as [->|NE]; [exfalso; exact (R'_maplen_g_nz Hml)|].
    rewrite R'_maplen_other in Hml by exact NE.
    assert (NEb : fst b <> rid) by (exact (no_nested b m Hb Hml)).
    rewrite !R'_gbase.
    destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
    split; [exists v3; split; [apply known_keep; [cbn; intros E; exfalso; exact (NEb E)| exact K3]| auto]|].
    split; [apply known_keep; [cbn; intros E; exfalso; exact (NEb E)| exact K2]|].
    split; [apply known_keep; [cbn; intros E; exfalso; exact (NEb E)| exact K1]| exact Q].
  - intros k m i Hkk Hs. rewrite E_slots in Hs. pose proof (no_blk k Hkk) as NEb.
    assert (NE : m <> g).
    { intros ->. apply NEb. destruct (is_valid _ _ _ IS0 _ _ _ Hs) as ([b' Hb'] & _ & Es). rewrite (slot_start'_eq _ _ _ IM0 _ _ i Hb') in Es. rewrite Es. cbn [fst].
      pose proof (hosts_inj _ _ _ IM0 _ _ _ Hb' Hg) as ->. reflexivity. }
    rewrite !(R'_other m NE). pose proof (D6 k m i Hkk Hs) as B. cbn zeta in B |- *.
    destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (KK : forall o v, known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v) by (intros o v; apply known_keep; cbn; intros E; exfalso; exact (NEb E)).
    assert (UU : forall o, unknown st (fst (bslot k), o) -> unknown st' (fst (bslot k), o)) by (intros o; apply unknown_keep; cbn; intros E; exfalso; exact (NEb E)).
    split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
    + intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; auto.
    + split; [intros Hres; apply KK; apply A7; exact Hres|]. intros a Ha. apply UU. apply A8. exact Ha.
Qed.

Theorem remap_INVL_full :
  INVL X st' L' BL LS
  /\ hosts st' bm g /\ MR st' g = m_set_maplen (needed / 4096) (MR st g)
  /\ (forall o v, 0 <= o < needed - IB -> known st (rid, o) v -> known st' (rid, o) v)
  /\ s_secret st' = s_secret st
  /\ (forall rid' x, rid' <> rid -> s_regions st' !! rid' = Some x <-> s_regions st !! rid' = Some x)
  /\ s_regions st' !! rid = Some (mkRegion RKGroup r needed)
  /\ TW st' (fun q => q = (rid, needed - IB)).
Proof.
  pose proof HNE as HNE'. pose proof OK as OK'. pose proof NERR as NERR'. pose proof HN as HN'. pose proof HNA as HNA'.
  split; [exact (conj R_part (conj A_part (conj M_part (conj L_part (conj G_part (conj S_part SH_part))))))|].
  split; [apply hosts'; exact Hg|]. split; [exact R'_g|].
  split; [intros o v Ho K; apply known_keep; [cbn; intros _; unfold IB in *; lia| exact K]|].
  split; [exact E_secret|].
  split; [intros rid' x NE; rewrite LK; destruct (N.eqb_spec rid' rid); [congruence| tauto]|].
  split; [rewrite LK, N.eqb_refl; reflexivity|].
  intros q sh o v t Hq Ho Ht. rewrite E_tick in Ht. rewrite E_shadow in Hq. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_insert_eq in Hq. injection Hq as <-. unfold SHn in Ho. cbn [r_cells] in Ho.
    destruct (Z.eq_dec o (needed - IB)) as [->|NEo]; [reflexivity|]. exfalso.
    rewrite lookup_insert_ne in Ho by congruence. unfold TR, shadow_trunc in Ho. cbn [r_cells] in Ho. rewrite lookup_filter_lt1 in Ho.
    destruct (o <? needed); [| discriminate]. unfold get_shadow in Ho.
    destruct (s_shadow st !! rid) as [sh0|] eqn:E0; cbn in Ho; [| rewrite lookup_empty in Ho; discriminate].
    pose proof (T0 rid sh0 o v t E0 Ho). lia.
  - rewrite lookup_insert_ne in Hq by congruence. pose proof (T0 q sh o v t Hq Ho). lia.
Qed.

End REMAP.
End RC__1.
