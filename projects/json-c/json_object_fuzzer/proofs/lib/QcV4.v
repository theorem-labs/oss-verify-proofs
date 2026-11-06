(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QPiB Qatc QSfG QdBa QpFQ Ql2m QYTG QjcB QaiD QLaA Q1am QoCS QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ Ql2m.Mq1 QPiB Ql2m.Mq2 QYTG.Mq1 QjcB QdBa.Mq2 QaiD QLaA.Mq0 Q1am.Mq1 QSfG QoCS.Mq0 Q1am.Mq0 QoCS QQCz.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land_52 x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros Hx. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma g_remove_perm a l0 (l : list (Z * Z)) : NoDup (map fst l) -> In (a, l0) l -> Permutation l ((a, l0) :: g_remove a l).
Proof.
induction l as [|[x1 x2] l IH]; intros ND Hin; [destruct Hin|]. cbn [g_remove fst]. cbn [map fst] in ND.
apply NoDup_cons in ND as [N1 N2].
destruct (Z.eqb_spec x1 a) as [->|NE].
- destruct Hin as [E|Hin]; [injection E as ->; apply Permutation_refl|].
exfalso. apply N1. apply list_elem_of_In. apply in_map_iff. exists (a, l0). auto.
- destruct Hin as [E|Hin]; [injection E; intros; subst; congruence|].
eapply Permutation_trans; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

#[using="Type"] Lemma strip_upd_shadow rid f st : strip (upd_shadow rid f st) = strip st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_region_strip st rid : get_region (strip st) rid = get_region st rid.
Proof. reflexivity. Qed.
#[using="Type"] Lemma strip_remap_region rid nb nd g st :
strip (remap_region rid nb nd g st) = strip (remap_region rid nb nd g (strip st)).
Proof.
unfold remap_region, remap_bound. rewrite get_region_strip.
rewrite <- !strip_upd_meta, ?strip_upd_shadow, <- !strip_upd_region, ?strip_strip; reflexivity.
Qed.
#[using="Type"] Lemma get_shadow_upd_region rid f st q : get_shadow (upd_region rid f st) q = get_shadow st q.
Proof. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma get_shadow_upd_meta g f st q : get_shadow (upd_meta g f st) q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma cell_read_truncate len sh o : 0 <= o < len -> cell_read (shadow_truncate len sh) o = cell_read sh o.
Proof.
intros Ho. unfold cell_read, shadow_truncate. cbn [r_cells r_hav r_havp].
rewrite !map_lookup_filter.
assert (H16 : 16 * (o / 16) < len) by (pose proof (Z_div_mod_eq_full o 16); pose proof (Z.mod_pos_bound o 16); lia).
assert (H4k : 4096 * (o / 4096) < len) by (pose proof (Z_div_mod_eq_full o 4096); pose proof (Z.mod_pos_bound o 4096); lia).
destruct (r_cells sh !! o) as [[v t]|] eqn:E1; destruct (r_hav sh !! (o / 16)) as [hl|] eqn:E2; destruct (r_havp sh !! (o / 4096)) as [hp|] eqn:E3; cbn;
repeat (rewrite option_guard_True by (cbn; lia)); cbn; reflexivity.
Qed.
#[using="Type"] Lemma cell_read_remap_region rid nb nd g st q :
(fst q = rid -> 0 <= snd q < remap_bound st rid nd) ->
cell_read (get_shadow (remap_region rid nb nd g st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
intros Hq. unfold remap_region. rewrite get_shadow_upd_meta.
rewrite get_shadow_upd_shadow. destruct (N.eqb_spec (fst q) rid) as [E|NE].
- rewrite cell_read_truncate by (apply Hq; exact E). rewrite get_shadow_upd_region. rewrite E. reflexivity.
- rewrite get_shadow_upd_region. reflexivity.
Qed.

#[using="Type"] Lemma sh_ticks_truncate len sh t : sh_ticks sh t -> sh_ticks (shadow_truncate len sh) t.
Proof.
intros [A B]. split; cbn [shadow_truncate r_hav r_havp]; intros; rewrite map_lookup_filter in H.
- destruct (r_hav sh !! u) as [hl'|] eqn:E; cbn in H; [| discriminate].
destruct (decide (16 * u < len)) as [Hlt|Hge]; [rewrite option_guard_True in H by exact Hlt| rewrite option_guard_False in H by exact Hge]; cbn in H; [| discriminate].
inversion H; subst. eapply A; eauto.
- destruct (r_havp sh !! pg) as [t''|] eqn:E; cbn in H; [| discriminate].
destruct (decide (4096 * pg < len)) as [Hlt|Hge]; [rewrite option_guard_True in H by exact Hlt| rewrite option_guard_False in H by exact Hge]; cbn in H; [| discriminate].
inversion H; subst. eapply B; eauto.
Qed.

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (z nl : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).
Hypothesis SC : m_sizeclass (MR st g) = 63.
Hypothesis HP : x_pend X = Some (fst b, sstart (MR st g) 0).
Hypothesis HXo : x_orph X = None.
Hypothesis HXf : x_fresh X = None.
Hypothesis HXz : x_zomb X = [].
Hypothesis HXi : x_idle X = [].
Hypothesis Hz : 0 < z /\ z mod PGSZ = 0.
Hypothesis Hnl : 0 < nl < LEN_MAX /\ nl mod PGSZ = 0.
Hypothesis Hceil : z + nl <= alloc_ceiling.
Let rid := fst b.
Hypothesis DISJ : forall rid2 r2, rid2 <> rid -> s_regions st !! rid2 = Some r2 ->
let '(b2, l2) := region_live_range r2 in z + nl <= b2 \/ b2 + l2 <= z.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Local Notation R := (MR st).

#[using="ai Hg"] Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.
#[using="RC__ L BL INV Hg IG"] Lemma GO : group_ok X st LS g b ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
#[using="RC__ X L BL ai z nl INV Hg SC rid IM IG"] Lemma g_facts : m_last_idx (R g) = 0 /\ m_maplen (R g) <> 0 /\ ~ in_list LS g /\ snd b = 0 /\ m_mem (R g) = Some b.
Proof.
destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(_ & A1 & A2 & A3)]; [rewrite SC in Hsc; lia|].
destruct (g_top _ _ _ _ _ _ GO A2) as [B0 _]. pose proof (hosts_mem _ _ _ IM _ _ g_hosts). auto 6.
Qed.
#[using="RC__ X L BL LS ai z nl INV Hg SC IM IG"] Lemma g_region : exists r0, s_regions st !! rid = Some r0 /\ r_kind r0 = RKGroup /\ m_maplen (R g) * 4096 = round_up_pg (r_len r0).
Proof.
destruct g_facts as (_ & ML & _). destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & H1 & H2 & H3 & _). exists r0. auto.
Qed.
Definition r0 : region := default (mkRegion RKGroup 0 0) (s_regions st !! rid).
#[using="RC__ X L BL LS ai z nl INV Hg SC IM IG"] Lemma r0_eq : s_regions st !! rid = Some r0 /\ r_kind r0 = RKGroup /\ m_maplen (R g) * 4096 = round_up_pg (r_len r0).
Proof. unfold r0. destruct g_region as (r & -> & K & E). cbn. auto. Qed.

Definition rm_r : region := mkRegion RKGroup z nl.
Definition st1 : mstate := upd_region rid (fun _ => rm_r) st.
Definition rm_B : Z := Z.min nl (round_up_pg (r_len r0)).
Definition st2 : mstate := upd_shadow rid (shadow_truncate rm_B) st1.
Definition st3 : mstate := upd_meta g (m_set_maplen (nl / 4096)) st2.
Definition rm_e : aptr := (rid, nl - IB).
Definition st4 : mstate := wr8 rm_e 0 st3.
Definition L' : mled := Qfya.set_groups ((z, nl) :: g_remove (r_base r0) (ld_groups L)) L.
Local Notation R' := (MR st4).

#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma remap_region_st3 : remap_region rid z nl g st = st3.
Proof.
unfold remap_region, remap_bound, st3, st2, st1, rm_B. unfold get_region. rewrite (proj1 r0_eq). reflexivity.
Qed.
#[using="RC__ X L BL LS ai z INV Hg SC IM IG"] Lemma rm_B_eq : rm_B = Z.min nl (m_maplen (R g) * 4096).
Proof. unfold rm_B. rewrite (proj2 (proj2 r0_eq)). reflexivity. Qed.
#[using="RC__ X L BL LS g ai z INV Hg SC Hz Hnl IM IG"] Lemma rm_B_ge : 4096 <= rm_B <= nl.
Proof.
rewrite rm_B_eq. destruct g_facts as (_ & ML & _). pose proof (g_maplen _ _ _ _ _ _ GO) as M0. fold (R g) in M0 |- *.
unfold PGSZ, LEN_MAX in Hnl. destruct Hnl as [[N1 _] N2]. unfold MR in *. lia.
Qed.

#[using="Type"] Lemma st4_ctx : s_ctx st4 = s_ctx st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_groups : s_groups st4 = s_groups st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_slots : s_slots st4 = s_slots st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_areas : s_areas st4 = s_areas st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_secret : s_secret st4 = s_secret st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_reserved : s_reserved st4 = s_reserved st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_next_rid : s_next_rid st4 = s_next_rid st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_tick : s_tick st4 = s_tick st. Proof. unfold st4, st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma st4_regions : s_regions st4 = <[rid := rm_r]> (s_regions st).
Proof.
unfold st4, st3, st2, st1. cbn; unfold upd_region, get_region; rewrite (proj1 r0_eq); reflexivity.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma st4_lookup q : s_regions st4 !! q = if (q =? rid)%N then Some rm_r else s_regions st !! q.
Proof.
rewrite st4_regions. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma st4_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st4 !! q = Some rq.
Proof. intros H NE. rewrite st4_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma st4_some q rq : s_regions st4 !! q = Some rq -> (q = rid /\ rq = rm_r) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite st4_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma st2_metas : s_metas st2 = s_metas st.
Proof. unfold st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma st4_metas : s_metas st4 = <[g := m_set_maplen (nl / 4096) (R g)]> (s_metas st).
Proof.
unfold st4. change (s_metas (wr8 rm_e 0 st3)) with (s_metas st3). unfold st3. rewrite s_metas_upd_meta.
unfold MR. rewrite (get_meta_rec_ext st st2 g st2_metas). rewrite st2_metas. reflexivity.
Qed.
#[using="Type"] Lemma R'_eq x : R' x = if aptr_eqb x g then m_set_maplen (nl / 4096) (R g) else R x.
Proof.
unfold MR, get_meta_rec. rewrite st4_metas. destruct (aptr_eqb_spec x g) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_g : R' g = m_set_maplen (nl / 4096) (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
#[using="RC__ b z Hz Hnl rid"] Lemma nl_pages : nl / 4096 * 4096 = nl /\ 1 <= nl / 4096 < 2 ^ 52.
Proof.
destruct Hnl as [[N1 N2] N3]. unfold PGSZ in N3. unfold LEN_MAX in N2.
pose proof (Z_div_mod_eq_full nl 4096). split; [lia|]. split; [| apply Z.div_lt_upper_bound; lia].
apply Z.div_le_lower_bound; lia.
Qed.
#[using="RC__ Hz Hnl"] Lemma maplen' : m_maplen (R' g) = nl / 4096.
Proof. rewrite R'_g. cbn. apply land_52. pose proof nl_pages. lia. Qed.
#[using="Type"] Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_avail x : m_avail (R' x) = m_avail (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freed x : m_freed (R' x) = m_freed (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_maplen_other x : x <> g -> m_maplen (R' x) = m_maplen (R x). Proof. intros; rewrite R'_other; auto. Qed.
#[using="Type"] Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. unfold gbase. rewrite R'_mem. reflexivity. Qed.
#[using="Type"] Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. unfold cnt_of. rewrite R'_last. reflexivity. Qed.
#[using="Type"] Lemma R'_stride_other x : x <> g -> get_stride (R' x) = get_stride (R x). Proof. intros; rewrite R'_other; auto. Qed.
#[using="RC__ X L BL LS ai INV Hg SC Hz Hnl IM IG"] Lemma stride' : get_stride (R' g) = nl - UNIT.
Proof.
unfold get_stride. rewrite R'_last, maplen'. destruct g_facts as (-> & _). pose proof nl_pages as [E B].
replace (nl / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. rewrite E. reflexivity.
Qed.
#[using="RC__ X L BL LS b ai z nl INV Hg SC rid IM IG"] Lemma stride0 : get_stride (R g) = m_maplen (R g) * 4096 - UNIT.
Proof.
unfold get_stride. destruct g_facts as (-> & ML & _). replace (m_maplen (R g) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). reflexivity.
Qed.
#[using="Type"] Lemma R'_sstart_other x i : x <> g -> sstart (R' x) i = sstart (R x) i. Proof. intros; rewrite R'_other; auto. Qed.
#[using="RC__"] Lemma R'_sstart0 x : sstart (R' x) 0 = sstart (R x) 0. Proof. unfold sstart. rewrite R'_gbase. lia. Qed.
#[using="Type"] Lemma R'_slot_start'_other x i : x <> g -> slot_start' (R' x) i = slot_start' (R x) i. Proof. intros; rewrite R'_other; auto. Qed.
#[using="RC__"] Lemma R'_slot_start'0 x : slot_start' (R' x) 0 = slot_start' (R x) 0. Proof. rewrite !slot_start'_sstart, R'_gbase, R'_sstart0. reflexivity. Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma R'_slot_start' x i : 0 <= i <= m_last_idx (R x) -> slot_start' (R' x) i = slot_start' (R x) i.
Proof.
intros Hi. destruct (aptr_eq_dec x g) as [->|NE]; [| apply R'_slot_start'_other; exact NE].
destruct g_facts as (L0 & _). rewrite L0 in Hi. replace i with 0 by lia. apply R'_slot_start'0.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC Hz Hnl IM IG"] Lemma gend' : gend (R' g) = nl. Proof. unfold gend, sstart. rewrite R'_cnt, R'_gbase, stride'. unfold cnt_of. destruct g_facts as (-> & _ & _ & B0 & Hm). unfold gbase. rewrite Hm. cbn. rewrite B0. lia. Qed.
#[using="Type"] Lemma hosts' bb m : hosts st4 bb m <-> hosts st bb m. Proof. apply hosts_ext. apply st4_groups. Qed.
#[using="Type"] Lemma live' m : live_group st4 m <-> live_group st m. Proof. apply live_group_ext. apply st4_groups. Qed.
#[using="Hz Hnl"] Lemma keys' x : s_metas st4 !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
rewrite st4_metas. destruct (aptr_eqb_spec x g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [| tauto].
split; [auto| intros _; discriminate].
Qed.
#[using="Type"] Lemma frontier' q rq : frontier st4 q rq = frontier st q rq. Proof. unfold frontier. rewrite st4_ctx. reflexivity. Qed.

#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma st3_remap : st3 = remap_region rid z nl g st. Proof. symmetry. apply remap_region_st3. Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma read4_other q : (fst q = rid -> 0 <= snd q < rm_B /\ snd q <> nl - IB) ->
cell_read (get_shadow st4 (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
intros Hq. unfold st4. rewrite cell_read_wr8_other.
2:{ intros ->. unfold rm_e in Hq. cbn in Hq. destruct (Hq eq_refl) as [_ NE]. apply NE. reflexivity. }
rewrite st3_remap. apply cell_read_remap_region. intros E.
replace (remap_bound st rid nl) with rm_B by (unfold remap_bound, rm_B, get_region; rewrite (proj1 r0_eq); reflexivity).
pose proof (Hq E). lia.
Qed.
#[using="RC__ X L BL LS INV"] Lemma TKS3 : TKS st3 (s_tick st).
Proof.
pose proof (TKS_of _ _ _ _ _ INV) as TK. unfold st3, st2, st1.
intros q sh. rewrite s_shadow_upd_meta.
rewrite s_shadow_upd_shadow, get_shadow_upd_region, s_shadow_upd_region.
destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence; apply TK].
intros E. inversion E; subst sh; clear E.
pose proof (sh_ticks_of st rid TK) as [A B].
assert (C : forall o w t, r_cells (get_shadow st rid) !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N).
{ intros o w t Ho. destruct (get_shadow_cells_some st rid o (w, t) Ho) as (sh' & Hs & Ho'). exact (proj1 (TK rid sh' Hs) o w t Ho'). }
split; [| exact (sh_ticks_truncate rm_B _ _ (conj A B))].
intros o w t Ho. cbn [shadow_truncate r_cells] in Ho. rewrite map_lookup_filter in Ho.
destruct (r_cells (get_shadow st rid) !! o) as [[w' t']|] eqn:E; cbn in Ho; [| discriminate].
destruct (decide (o < rm_B)) as [Hlt|Hge]; [rewrite option_guard_True in Ho by exact Hlt| rewrite option_guard_False in Ho by exact Hge]; cbn in Ho; [| discriminate].
inversion Ho; subst. eapply C; eauto.
Qed.
#[using="Type"] Lemma tick3 : s_tick st3 = s_tick st.
Proof. unfold st3, st2, st1, upd_region. destruct (get_region st rid); reflexivity. Qed.
#[using="RC__ X L BL LS INV"] Lemma TKS4 : TKS st4 (s_tick st).
Proof. unfold st4. apply TKS_wr8; [| exact TKS3]. rewrite tick3. apply N.le_refl. Qed.
#[using="RC__ X L BL LS INV"] Lemma read4_e : cell_read (get_shadow st4 rid) (nl - IB) = Known 0.
Proof.
unfold st4. change rid with (fst rm_e). change (nl - IB) with (snd rm_e). rewrite cell_read_wr8_same; [reflexivity|].
apply sh_ticks_of. rewrite tick3. exact TKS3.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma shadow4_dom q sh : s_shadow st4 !! q = Some sh -> exists r, s_regions st !! q = Some r /\ r_kind r = RKGroup.
Proof.
pose proof (DOMS_of _ _ _ _ _ INV) as D. destruct r0_eq as (Hr0 & K0 & _).
assert (Hrid : exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup) by (exists r0; auto).
unfold st4, st3, st2, st1. intros H. revert q sh H.
apply (wr8_dom _ _ _ (fun q => exists r, s_regions st !! q = Some r /\ r_kind r = RKGroup)); [| exact Hrid].
intros q sh. rewrite s_shadow_upd_meta.
rewrite s_shadow_upd_shadow, s_shadow_upd_region. destruct (N.eqb_spec q rid) as [->|NE]; [intros _; exact Hrid| rewrite lookup_insert_ne by congruence; apply D].
Qed.

#[using="RC__ X L BL LS ai z nl INV Hg SC IM IG IS"] Lemma rid_only bb m : hosts st bb m -> fst bb = rid -> m = g.
Proof.
intros Hm Hf. destruct g_facts as (_ & ML & _).
destruct (Z.eq_dec (m_maplen (R m)) 0) as [Z0|NZ].
- exfalso. destruct (@top_chain _ _ _ _ IM IG IS m bb Hm Z0) as (t & j & c & bt & Ha & Ht & Htop & Hft).
assert (t = g) by (apply (@top_unique _ _ _ IG t g bt b Ht g_hosts Htop ML); rewrite Hft, Hf; reflexivity). subst t.
destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). rewrite SC in Hsc. lia.
- apply (@top_unique _ _ _ IG m g bb b Hm g_hosts NZ ML). rewrite Hf. reflexivity.
Qed.

Definition isG (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition isM (kr : N * region) : bool := match r_kind (snd kr) with RKMeta => true | _ => false end.

#[using="RC__ X L BL LS g ai z nl INV Hg SC IM IG"] Lemma group_regions_perm :
Permutation (map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter isG (map_to_list (s_regions st))))
((r_base r0, r_len r0) :: map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter isG (map_to_list (delete rid (s_regions st))))).
Proof.
destruct r0_eq as (Hr0 & K0 & _).
pose proof (map_to_list_delete (s_regions st) rid r0 Hr0) as P.
eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply Permutation_sym; exact P|].
cbn. unfold isG at 1. cbn. rewrite K0. cbn. apply Permutation_refl.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma group_regions_perm4 :
Permutation (map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter isG (map_to_list (s_regions st4))))
((z, nl) :: map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter isG (map_to_list (delete rid (s_regions st))))).
Proof.
rewrite st4_regions.
pose proof (map_to_list_delete (<[rid := rm_r]> (s_regions st)) rid rm_r ltac:(apply lookup_insert_eq)) as P. rewrite delete_insert_eq in P.
eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply Permutation_sym; exact P|].
cbn. apply Permutation_refl.
Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma meta_regions_perm4 :
Permutation (List.filter isM (map_to_list (s_regions st4))) (List.filter isM (map_to_list (s_regions st))).
Proof.
destruct r0_eq as (Hr0 & K0 & _). rewrite st4_regions. apply Permutation_sym.
apply (regions_update_perm st rid r0 rm_r isM Hr0); unfold isM; cbn; rewrite ?K0; reflexivity.
Qed.

#[using="RC__ X st BL LS b z nl INV Hz Hnl rid IR"] Lemma bases_nodup : NoDup (map fst (ld_groups L)).
Proof.
eapply (NoDup_Permutation_proper _ _ (Permutation_map fst (Permutation_sym (ir_groups _ _ _ IR)))).
rewrite map_map. cbn. change (NoDup ((fun x : N * region => r_base (snd x)) <$> List.filter isG (map_to_list (s_regions st)))).
apply NoDup_fmap_2_strong.
- intros [q1 r1] [q2 r2] H1 H2 E. cbn in E. apply list_elem_of_In in H1. apply list_elem_of_In in H2.
apply filter_In in H1 as [H1 K1]. apply filter_In in H2 as [H2 K2]. apply In_map_to_list_regions in H1. apply In_map_to_list_regions in H2.
unfold isG in K1, K2. cbn in K1, K2.
destruct (N.eq_dec q1 q2) as [->|NE]; [rewrite H1 in H2; inversion H2; reflexivity|]. exfalso.
pose proof (ir_disj _ _ _ IR q1 q2 r1 r2 H1 H2 NE) as D. unfold region_live_range in D.
pose proof (ir_shape _ _ _ IR _ _ H1) as (_ & _ & P1 & _). pose proof (ir_shape _ _ _ IR _ _ H2) as (_ & _ & P2 & _).
pose proof (round_up_ge (r_len r1)). pose proof (round_up_ge (r_len r2)).
destruct (r_kind r1); try discriminate. destruct (r_kind r2); try discriminate. lia.
- apply NoDup_ListNoDup. apply List.NoDup_filter. apply NoDup_ListNoDup. apply NoDup_map_to_list.
Qed.

#[using="RC__ X BL LS g ai z nl INV Hg SC IR IM IG"] Lemma r0_in_groups : In (r_base r0, r_len r0) (ld_groups L).
Proof.
eapply Permutation_in; [apply Permutation_sym; exact (ir_groups _ _ _ IR)|].
eapply Permutation_in; [apply Permutation_sym; exact group_regions_perm|]. left. reflexivity.
Qed.

#[using="BL LS ai INV Hg SC HXo Hz Hnl Hceil DISJ IR IM IG"] Lemma IR4 : inv_R X st4 L'.
Proof.
destruct r0_eq as (Hr0 & K0 & ML0). destruct Hz as [Z0 ZM]. destruct Hnl as [[N0 NL] NM]. destruct g_facts as (LI0 & ML & NIL & B0 & MEM).
pose proof (ir_shape _ _ _ IR _ _ Hr0) as (S1 & S2 & S3 & S4 & S5 & S6).
assert (RU : round_up_pg nl = nl) by (apply round_up_pg_id; exact NM).
assert (NB0 : r_kind r0 <> RKBrk) by (rewrite K0; discriminate).
unfold L'. destruct IR; constructor; cbn [Qfya.ld_metas Qfya.ld_groups Qfya.ld_resv Qfya.ld_brkreg Qfya.ld_brk Qfya.ld_live Qfya.set_groups].
- intros q rq Hq. rewrite st4_next_rid. apply st4_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr0)| exact (ir_ids _ _ Hq)].
- intros q rq Hq. apply st4_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
split; [lia|]. split; [exact ZM|]. split; [lia|]. split; [lia|]. split; [lia|]. intros [K|K]; discriminate.
- intros q1 q2 r1 r2 H1 H2 NE.
apply st4_some in H1 as [[-> ->]|[N1 H1]]; apply st4_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
+ cbn. rewrite RU. pose proof (DISJ q2 r2 N2 H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
+ pose proof (DISJ q1 r1 N1 H1) as D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
- rewrite st4_reserved. exact ir_resv.
- eapply Permutation_trans; [| apply Permutation_sym; exact group_regions_perm4]. apply perm_skip.
apply (Permutation_cons_inv (a := (r_base r0, r_len r0))).
eapply Permutation_trans; [apply Permutation_sym; apply (g_remove_perm _ _ _ bases_nodup r0_in_groups)|].
eapply Permutation_trans; [exact ir_groups| exact group_regions_perm].
- eapply Permutation_trans; [exact ir_metas|].
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; exact meta_regions_perm4].
erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn. rewrite frontier'. reflexivity.
- intros q rq Hq Kq. rewrite frontier'. apply st4_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (ir_metalen q rq Hq Kq)].
- intros q rq Hq Kq. rewrite frontier'. apply st4_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (ir_brkfront q rq Hq Kq)].
- rewrite st4_ctx. destruct ir_shift as [SH1 [SH2|(q & rq & Hq & Kq & Eq)]]; split; [exact SH1| left; exact SH2| exact SH1|].
right. exists q, rq. split; [apply st4_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; rewrite K0 in Kq; discriminate]| auto].
- intros bb l. rewrite ir_brkreg. split; intros (q & rq & Hq & Kq & E1 & E2); exists q, rq.
+ split; [apply st4_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; congruence]| auto].
+ apply st4_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
- intros q1 q2 r1 r2 H1 H2 K1 K2. apply st4_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply st4_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
- rewrite st4_ctx. revert ir_brk. destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
+ destruct IBK as [BP NB]. split; [exact BP|]. intros q rq Hq. apply st4_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
+ exact IBK.
+ destruct IBK as [BP (rq & Hq & Kq & E)]. split; [exact BP|]. exists rq.
split; [apply st4_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; congruence]| auto].
- rewrite st4_ctx. destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
intros q off E. destruct (C3 q off E) as (rq & Hq & Kq & Bq). exists rq.
split; [apply st4_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; destruct Kq as [Kq|Kq]; rewrite K0 in Kq; discriminate]| auto].
- intros q Hq. rewrite HXo in Hq. discriminate.
Qed.

#[using="RC__ X L BL LS b ai INV Hg IG"] Lemma g_present4 : s_metas st !! g <> None.
Proof. exact (g_present _ _ _ _ _ _ GO). Qed.

#[using="RC__ X L BL LS ai INV Hg SC Hz Hnl IA IM IG"] Lemma IA4 : inv_A st4.
Proof.
destruct r0_eq as (Hr0 & K0 & _).
assert (KEEPM : forall q rq, s_regions st !! q = Some rq -> is_metakind rq -> s_regions st4 !! q = Some rq).
{ intros q rq Hq Kq. apply st4_keep; [exact Hq|]. intros ->. rewrite Hr0 in Hq. inversion Hq. subst. destruct Kq as [Kq|Kq]; rewrite K0 in Kq; discriminate. }
destruct IA; constructor; rewrite ?st4_ctx, ?st4_areas, ?st4_secret; try assumption.
- intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite frontier'. split; [apply KEEPM; assumption| auto].
- intros m mr Hm. assert (K : s_metas st4 !! m <> None) by congruence. apply keys' in K.
destruct K as [K| ->].
+ destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
+ destruct (s_metas st !! g) as [mr0|] eqn:E; [| exfalso; exact (g_present4 E)]. exact (ia_metas g mr0 E).
- destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
intros k Hk2. destruct (s_metas st4 !! mslot a k) eqn:E; [| reflexivity]. exfalso.
assert (K : s_metas st4 !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
+ apply K. apply Hk. exact Hk2.
+ apply g_present4. rewrite <- K. apply Hk. exact Hk2.
- intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply KEEPM; assumption| exact K].
- intros sc Hsc. unfold usage, ctx. rewrite st4_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
unfold gcnt. rewrite st4_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
rewrite R'_sc, R'_cnt. reflexivity.
Qed.

#[using="RC__ L BL ai INV Hg SC HXz HXi IM IG"] Lemma IM4 : inv_M X st4 LS.
Proof.
destruct g_facts as (LI0 & ML & NIL & B0 & MEM).
destruct IM as [M1 M2 M3 M4 M5]; constructor.
- intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; congruence| apply M1; exact Hm].
- intros m bb Hm. rewrite R'_mem in Hm. rewrite hosts'. apply M2. exact Hm.
- intros bb h Hb. rewrite st4_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
- intros m Hm. rewrite HXi in Hm. destruct Hm.
- intros zz Hz0. rewrite HXz in Hz0. destruct Hz0.
Qed.

#[using="RC__ X L BL ai INV Hg SC IM IL IG"] Lemma IL4 : inv_L st4 LS.
Proof.
destruct g_facts as (LI0 & ML & NIL & B0 & MEM).
destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
- intros h. rewrite (get_head_ext st st4 st4_ctx). apply L1.
- intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
- exact L3.
- exact L4.
- intros m. rewrite R'_next, R'_prev. apply L5.
- intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
exfalso. apply NIL. exists LFree. exact Hm.
- intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
- exact L9.
Qed.

#[using="RC__ L BL ai INV Hg SC Hz Hnl IM IG IS"] Lemma IG4 : inv_G X st4 LS.
Proof.
destruct r0_eq as (Hr0 & K0 & ML0). destruct g_facts as (LI0 & ML & NIL & B0 & MEM). pose proof nl_pages as [NP1 NP2].
destruct Hnl as [[N0 NL] NM]. assert (RU : round_up_pg nl = nl) by (apply round_up_pg_id; exact NM).
assert (KEEPG : forall bb m, hosts st bb m -> m <> g -> forall rq, s_regions st !! fst bb = Some rq -> s_regions st4 !! fst bb = Some rq).
{ intros bb m Hm NE rq Hq. apply st4_keep; [exact Hq|]. intros E. apply NE. exact (rid_only _ _ Hm E). }
destruct IG as [G1 G2 G3 G4 G5]. constructor.
- intros m bb aim Hm. rewrite st4_groups in Hm. pose proof (G1 m bb aim Hm) as GOm.
destruct (aptr_eqb_spec m g) as [->|NE].
+ pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
destruct GOm; constructor; rewrite ?R'_last, ?R'_sc, ?maplen', ?R'_freeable, ?R'_avail, ?R'_freed, ?st4_slots; try assumption.
all: match goal with
| |- s_metas st4 !! g <> None => apply keys'; right; reflexivity
| |- _ \/ _ => right; rewrite SC, LI0; split; [reflexivity|]; split; [reflexivity|]; split; [clear -NP2; lia| exact NIL]
| |- 0 <= nl / 4096 => clear -NP2; lia
| |- x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> _ => intros _ Hsc; exfalso; rewrite SC in Hsc; clear -Hsc; lia
| |- m_sizeclass (R g) < 48 -> _ => intros Hsc; exfalso; rewrite SC in Hsc; clear -Hsc; lia
| |- x_fresh X <> Some g -> forall sc, _ => intros NF sc Hin; exfalso; apply NIL; exists (LActive sc); exact Hin
| |- nl / 4096 = 0 -> _ => intros Z0; exfalso; clear -Z0 NP2; lia
| |- m_sizeclass (R g) = 0 -> _ => intros Hsc; exfalso; rewrite SC in Hsc; clear -Hsc; lia
| |- nl / 4096 <> 0 -> _ =>
intros _; split; [exact B0|]; exists rm_r; rewrite st4_lookup; unfold rid; rewrite N.eqb_refl; split; [reflexivity|]; split; [reflexivity|];
cbn [r_len rm_r]; rewrite RU, gend'; clear -NP1; lia
| |- _ => idtac
end.
+ assert (Hmh : hosts st bb m) by (exists aim; exact Hm).
destruct GOm; constructor; rewrite ?(R'_other m NE), ?st4_slots; try assumption.
* apply keys'. left. assumption.
* intros Hml. destruct (g_top Hml) as (H0 & rq & Hrq & Hk & E1 & E2). split; [exact H0|]. exists rq. split; [exact (KEEPG bb m Hmh NE rq Hrq)| auto].
* intros Hml. destruct (g_nest Hml) as (p & ip & Hsl & Hfp & Hend & Hsc & Hstr).
assert (NEp : p <> g) by (intros ->; rewrite SC in Hsc; lia).
exists p, ip. rewrite !(R'_other p NEp). auto 10.
- intros bb aim H. rewrite st4_groups in H. eapply G2. exact H.
- intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st4_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
- intros q rq Hq Kq Ho. apply st4_some in Hq as [[-> ->]|[NE Hq]].
+ exists g. rewrite hosts', maplen'. assert (Eb : (rid, 0) = b) by (unfold rid; rewrite <- B0; symmetry; apply surjective_pairing). rewrite Eb.
split; [exact g_hosts| clear -NP2; lia].
+ destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m. rewrite hosts'. split; [exact Hm|].
rewrite R'_other; [exact Hml|]. intros ->. apply NE. pose proof (hosts_inj _ _ _ IM _ _ _ Hm g_hosts) as Eb. apply (f_equal fst) in Eb. cbn in Eb. exact Eb.
- intros bb h H. rewrite st4_groups in H. destruct (N.eq_dec (fst bb) rid) as [E|NE].
+ exists rm_r. rewrite st4_lookup, E, N.eqb_refl. split; reflexivity.
+ destruct (G5 bb h H) as (rq & Hq & Kq). exists rq. split; [apply st4_keep; assumption| exact Kq].
Qed.

#[using="RC__ X L LS b ai z nl INV Hg SC HP Hz Hnl rid IM IG IS"] Lemma no_block_g k i : In k BL -> s_slots st !! bslot k = Some (g, i) -> False.
Proof.
intros Hk Hs. destruct g_facts as (LI0 & _).
destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi & Ek). rewrite LI0 in Hi. assert (i = 0) by lia. subst i.
pose proof (is_part _ _ _ IS _ _ _ 0 Hg ltac:(lia)) as P. cbn zeta in P.
destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split.
- rewrite <- Ek. apply in_map. exact Hk.
- rewrite HP. rewrite slot_start'_sstart, (hosts_gbase _ _ _ IM _ _ g_hosts). reflexivity.
Qed.

#[using="RC__ L LS ai INV Hg SC HP Hz Hnl IM IG IS"] Lemma IS4 : inv_S X st4 BL.
Proof.
pose proof IS as [S1 S2 S3 S4 S5 S6]. constructor.
- intros s m i H. rewrite st4_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start' by assumption. auto.
- intros bb m i Hb Hi. rewrite R'_last in Hi. rewrite st4_slots, R'_slot_start' by exact Hi. apply (S2 bb); [apply hosts'; exact Hb| exact Hi].
- intros bb m aim i Hb Hi. rewrite st4_groups in Hb. rewrite R'_last in Hi. cbn zeta. rewrite R'_slot_start' by exact Hi. rewrite R'_avail, R'_freed, st4_groups.
exact (S3 bb m aim i Hb Hi).
- intros s Hs. rewrite st4_slots. apply S4. exact Hs.
- exact S5.
- intros k Hk. destruct (S6 k Hk) as (m & i & Hs & Ho & Hn & Hf). exists m, i. rewrite st4_slots. split; [exact Hs|]. split; [exact Ho|]. split; [exact Hn|].
rewrite R'_stride_other; [exact Hf|]. intros ->. exact (no_block_g k i Hk Hs).
Qed.

#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma known4 q v : (fst q = rid -> 0 <= snd q < rm_B /\ snd q <> nl - IB) -> known st q v -> known st4 q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite (read4_other q Hq). exact K. Qed.
#[using="RC__ X L BL LS ai INV Hg SC IM IG"] Lemma unknown4 q : (fst q = rid -> 0 <= snd q < rm_B /\ snd q <> nl - IB) -> unknown st q -> unknown st4 q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite (read4_other q Hq). exact K. Qed.

#[using="RC__ X L BL LS ai z nl INV Hg SC IM IG IS"] Lemma other_region bb m : hosts st bb m -> m <> g -> fst bb <> rid.
Proof. intros Hm NE E. apply NE. exact (rid_only _ _ Hm E). Qed.

#[using="RC__ b z Hz Hnl rid"] Lemma nl_ge : 4096 <= nl.
Proof. pose proof nl_pages as [E B]. lia. Qed.

#[using="RC__ X L LS ai INV Hg SC HP Hz Hnl IM IG IS ISH"] Lemma ISH4 : inv_SH st4 BL.
Proof.
destruct r0_eq as (Hr0 & K0 & _). destruct g_facts as (LI0 & ML & NIL & B0 & MEM). pose proof nl_ge as NG.
pose proof (hosts_gbase _ _ _ IM _ _ g_hosts) as GB.
destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
- intros q sh Hq. destruct (shadow4_dom q sh Hq) as (r & Hr & Kr).
destruct (N.eq_dec q rid) as [->|NE]; [exists rm_r; rewrite st4_lookup, N.eqb_refl; split; reflexivity| exists r; split; [apply st4_keep; assumption| exact Kr]].
- intros q sh Hq. rewrite st4_tick. exact (TKS4 q sh Hq).
- intros bb m i Hb Hi. apply hosts' in Hb. rewrite R'_cnt in Hi.
destruct (aptr_eq_dec m g) as [->|NE].
+ pose proof (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) as ->. unfold cnt_of in Hi. rewrite LI0 in Hi.
assert (C : i = 0 \/ i = 1) by lia. destruct C as [-> | ->].
* rewrite R'_sstart0. apply known4; [| apply (D3 b g 0 g_hosts); unfold cnt_of; lia].
intros _. unfold sstart. rewrite GB, B0. cbn [snd]. pose proof rm_B_ge. unfold UNIT, IB. lia.
* unfold known, SHd. cbn [fst snd]. unfold sstart. rewrite R'_gbase, GB, stride', B0. cbn [snd].
replace (0 + UNIT + (nl - UNIT) * 1 - IB) with (nl - IB) by lia. exact read4_e.
+ rewrite R'_sstart_other by exact NE. apply known4; [| exact (D3 bb m i Hb Hi)]. intros E. exfalso. exact (other_region _ _ Hb NE E).
- intros bb m o Hb Ho. apply hosts' in Hb. apply unknown4; [| exact (D4 bb m o Hb Ho)].
destruct (aptr_eq_dec m g) as [->|NE].
+ pose proof (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) as ->. intros _. cbn [snd]. rewrite B0. pose proof rm_B_ge. unfold IB. lia.
+ intros E. exfalso. exact (other_region _ _ Hb NE E).
- intros bb m p i Hb Hml Hs. apply hosts' in Hb. rewrite st4_slots in Hs.
assert (NE : m <> g) by (intros ->; rewrite maplen' in Hml; pose proof nl_pages; lia).
rewrite R'_maplen_other in Hml by exact NE. rewrite R'_gbase.
pose proof (other_region _ _ Hb NE) as NR.
destruct (D5 bb m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
split; [exists v3; split; [apply known4; [intros E; exfalso; exact (NR E)| exact K3]| auto]|].
split; [apply known4; [intros E; exfalso; exact (NR E)| exact K2]|].
split; [apply known4; [intros E; exfalso; exact (NR E)| exact K1]| exact Q].
- intros k m i Hk Hs. rewrite st4_slots in Hs.
assert (NE : m <> g) by (intros ->; exact (no_block_g k i Hk Hs)).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
assert (NR : fst (bslot k) <> rid).
{ rewrite Ek, slot_start'_sstart, (hosts_gbase _ _ _ IM _ _ Hm). cbn [fst]. exact (other_region _ _ Hm NE). }
rewrite (R'_other m NE).
destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (KN : forall o v, known st (fst (bslot k), o) v -> known st4 (fst (bslot k), o) v) by (intros o v; apply known4; intros E; exfalso; exact (NR E)).
assert (UN : forall o, unknown st (fst (bslot k), o) -> unknown st4 (fst (bslot k), o)) by (intros o; apply unknown4; intros E; exfalso; exact (NR E)).
split; [apply KN; exact A1|]. split; [apply KN; exact A2|]. split; [apply KN; exact A3|]. split; [apply KN; exact A4|].
split; [exact A5|]. split.
+ intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KN; assumption.
+ split; [intros Hr; apply KN; apply A7; exact Hr|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

#[using="Type"] Lemma cells4 q o v t : r_cells (get_shadow st4 q) !! o = Some (v, t) ->
(q = rid /\ o = nl - IB /\ t = s_tick st) \/ r_cells (get_shadow st q) !! o = Some (v, t).
Proof.
intros H. destruct (aptr_eq_dec (q, o) rm_e) as [E|NE].
- left. unfold rm_e in E. inversion E; subst. unfold st4 in H. unfold get_shadow in H. rewrite (wr8_shadow_lookup st3 rm_e 0 rid) in H.
unfold rm_e in H. cbn [fst snd] in H. rewrite N.eqb_refl in H. cbn [default r_cells] in H. rewrite lookup_insert_eq in H.
inversion H; subst. split; [reflexivity|]. split; [reflexivity|]. unfold st2, st1, upd_region; destruct (get_region st rid); reflexivity.
- right. unfold st4 in H. rewrite (wr8_cells_other st3 rm_e 0 q o NE) in H.
unfold st3 in H. unfold get_shadow in H. rewrite s_shadow_upd_meta in H. fold (get_shadow st2 q) in H.
unfold st2, st1 in H.
rewrite get_shadow_upd_shadow in H. destruct (N.eqb_spec q rid) as [->|NQ]; [| rewrite get_shadow_upd_region in H; exact H]. rewrite get_shadow_upd_region in H.
cbn [shadow_truncate r_cells] in H. rewrite map_lookup_filter in H.
destruct (r_cells (get_shadow st rid) !! o) as [[v' t']|] eqn:E; cbn in H; [| discriminate].
destruct (decide (o < rm_B)) as [Hlt|Hge]; [rewrite option_guard_True in H by exact Hlt| rewrite option_guard_False in H by exact Hge]; cbn in H; [| discriminate].
inversion H; subst. reflexivity.
Qed.

#[using="RC__ X L BL LS ai INV Hg SC Hz Hnl IM IG"] Lemma TF2_4 : TF0 st -> TF2 st4.
Proof.
intros T0 q sh o v t Hs Hc Et. rewrite st4_tick in Et. subst t.
assert (Hc' : r_cells (get_shadow st4 q) !! o = Some (v, s_tick st)) by (unfold get_shadow; rewrite Hs; exact Hc).
destruct (cells4 q o v _ Hc') as [(-> & -> & _)|Hold].
- exists b, g. rewrite hosts'. split; [exact g_hosts|]. split; [reflexivity|]. left. exists 1.
rewrite R'_cnt. unfold cnt_of. destruct g_facts as (-> & _ & _ & B0 & MEM). split; [lia|]. cbn [snd].
unfold sstart. rewrite R'_gbase, stride', (hosts_gbase _ _ _ IM _ _ g_hosts), B0. lia.
- exfalso. destruct (get_shadow_cells_some st q o _ Hold) as (sh0 & Hs0 & Hc0). pose proof (T0 q sh0 o v _ Hs0 Hc0). lia.
Qed.

#[using="ai INV Hg SC HP HXo HXz HXi Hz Hnl Hceil DISJ IR IA IM IL IG IS ISH"] Theorem remap_core_INVL : INVL X st4 L' BL LS.
Proof.
split; [exact IR4| split; [exact IA4| split; [exact IM4| split; [exact IL4| split; [exact IG4| split; [exact IS4| exact ISH4]]]]]].
Qed.

End REMAP.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPWv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition undersized (r : meta) : Prop := 48 <= m_sizeclass r \/ get_stride r < UNIT * size_class (m_sizeclass r).
Definition fresh_beyond (st : mstate) (b : aptr) : Prop :=
forall o, snd b + UNIT <= o -> cell_read (get_shadow st (fst b)) o = Known 0.

#[using="Type"] Lemma fresh_beyond_hdr st b t :
s_shadow st !! fst b = Some (mkShadow ∅ (<[snd b / 16 := hav_add 12 t []]> ∅) ∅) -> 0 <= snd b -> snd b mod UNIT = 0 -> fresh_beyond st b.
Proof.
intros HS Hb Hal o Ho. unfold get_shadow. rewrite HS. cbn [default]. unfold cell_read. cbn [r_cells r_hav r_havp].
rewrite lookup_empty. rewrite lookup_empty. rewrite lookup_insert_ne; [rewrite lookup_empty; reflexivity|].
unfold UNIT in *. intros E.
pose proof (Z_div_mod_eq_full (snd b) 16). pose proof (Z.mod_pos_bound (snd b) 16 ltac:(lia)).
pose proof (Z_div_mod_eq_full o 16). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia.
Qed.

Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
(st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
(forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
\/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
/\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
/\ req + IB <= get_stride (MR st1 g)
/\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
/\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
/\ TF2 st1
/\ (undersized (MR st1 g) -> fresh_beyond st1 bg))).

Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
(st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
(forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
match go with
| None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
| Some m => exists b ai last ml,
s_groups st2 !! b = Some (mkGhdr (Some m) ai)
/\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
/\ 0 <= ai <= last /\ last <= 31
/\ req + IB <= get_stride (MR st2 m)
/\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
/\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
/\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
/\ (undersized (MR st2 m) -> fresh_beyond st2 b)
end.

Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
sc < j < 48 ->
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
(forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
ftree L (rec st j req k bail) Post.

Definition ag_cnt1 (sc u0 : Z) : Z :=
let size := UNIT * size_class sc in
let cnt := cnt0_of sc u0 in
if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
let size := UNIT * size_class sc in
let needed := round_up_pg (size * cnt2 + UNIT) in
if negb nosmall && (cnt2 <=? 7) then
let req' := round_up_pg (req + IB + UNIT) in
if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
else (cnt2, needed).

#[using="Type"] Lemma ag_arith sc req u0 u1 ns c3 n3 :
0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
let size := UNIT * size_class sc in
(PGSZ / 2 < size * ag_cnt1 sc u0 + UNIT ->
ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
grp_ok sc c3 n3 = true /\ ((c3 = 1 /\ n3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (size * c3 + UNIT <= n3)))
/\ (size * ag_cnt1 sc u0 + UNIT <= PGSZ / 2 -> nest_ok sc (ag_cnt1 sc u0) = true).
Proof.
intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
intros HB E. specialize (AR1 HB).
change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
else ag_cnt1 sc u0
else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
unfold ag_cn3 in E. cbn zeta in E.
destruct (negb ns && (c2 <=? 7)).
- destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
+ inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
+ inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
- inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.

#[using="Type"] Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

#[using="Type"] Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

#[using="Type"] Lemma step_seq_fields st : let st' := step_seq st in
s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
/\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.

#[using="Type"] Lemma account_bounce_fields sc0 st : let st' := account_bounce sc0 st in
s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
/\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof.
unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.

Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

#[using="INV1 TF1"] Lemma st1'_facts :
INVL (X_as (m :: idle)) st1' L1 BL LS1 /\ s_shadow st1' = s_shadow st1 /\ s_tick st1' = s_tick st1
/\ (forall sc', active st1' sc' = active st1 sc') /\ TF0 st1' /\ s_regions st1' = s_regions st1 /\ s_secret st1' = s_secret st1.
Proof.
destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

#[using="Type"] Lemma st1'_init : c_init_done (s_ctx st1') = c_init_done (s_ctx st1).
Proof.
unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

#[using="idle st0 L0 BL LS1 req INV1 NIm TF1 Hsc Hfit HA1 HA0 HL1 HG1 GRP RED HK"] Theorem ag_mmap_ft :
ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r needed st1' in
ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
apply ftree_vis; [reflexivity| reflexivity| | |].
-  cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
split; [right; reflexivity|]. unfold LEN_MAX. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then Qfya.set_metas ((a, needed, 0) :: ld_metas L1) L1 else Qfya.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
destruct (is_err a) eqn:ER.
+
rewrite free_meta_eq.
destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
split.
{ eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity| | ]].
- unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'.
- rewrite (free_idle_init idle m st1' L1 BL LS1 INV1'). exact st1'_init. }
split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
+
destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
{ rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
assert (NS : s_shadow st2 !! rid = None).
{ rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
assert (HAI0 : sc = 0 -> AI = cnt - 1).
{ intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite ag_tail_eq.
change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
destruct (ag_top_ok idle st2 (Qfya.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
split.
{ eapply GP_trans; [exact HG1|]. split; [|split].
- intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
- rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'.
- intros HI. rewrite agt_ctx. cbn. rewrite Est2. cbn. rewrite st1'_init. exact HI. }
exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
= if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
{ rewrite MR'. unfold get_stride. cbn. reflexivity. }
assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
assert (FB : fresh_beyond (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) (rid, 0)).
{ apply (fresh_beyond_hdr _ (rid, 0) (s_tick st2)); [| cbn; lia| reflexivity]. cbn [fst snd].
unfold agt. autorewrite with mst. unfold hdr_havoc, upd_shadow. autorewrite with mst. rewrite lookup_insert_eq.
unfold get_shadow. autorewrite with mst. rewrite NS. cbn. reflexivity. }
split; [| split; [| split; [| split; [exact INV'| split; [apply TF0_TF2; exact TF'| intros _; exact FB]]]]].
* destruct RED as [(C1 & Nd & S28)|NR].
-- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
-- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
* intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
* intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
-- clear - HAI C1. lia.
-- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.

Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

#[using="idle st0 L0 BL LS1 req REC INV1 NIm ND TF1 Hsc Hfit HA1 HA0 HL1 HG1 NEST HK"] Theorem ag_nest_ft :
ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
else match active st2 j with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
end) bail) Post.
Proof.
pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
- apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
- exact N5.
- lia.
- intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2' & AZg)].
+
change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
split.
{ eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5| |]]].
- unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity.
- exact (free_idle_init idle m st2 L2 BL LS2 INV2). }
split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
+ replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
{ unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
rewrite Ep. rewrite ag_tail_eq.
specialize (STR ltac:(lia)).
assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
rewrite Emr in MR'. rewrite Emr in Es.
eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
split.
{ eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
- rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
- rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
- rewrite agt_ctx. cbn. change (c_init_done (s_ctx (nest_layout st2 g idx j size cnt)) = c_init_done (s_ctx st2)).
rewrite <- (s_ctx_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
split; [exact INV'|]. split; [exact TF'|]. intros U. exfalso. destruct U as [U|U]; [cbn in U; lia|]. rewrite Es in U. cbn [m_sizeclass] in U. unfold size in U. lia.
Qed.
End NEST_BRANCH.

Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

#[using="REC"] Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
active st sc = None ->
(forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
-
intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
-
intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
with (cnt0_of sc (usage st1 sc)).
change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
with (ag_cnt1 sc (usage st1 sc)).
change (lh_nest full_lay) with nest_layout.
assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
pose proof (ag_arith sc req (usage st1 sc)) as AR.
set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
+
set (ns := is_bouncing sc st1).
set (st1' := step_seq (account_bounce sc st1)).
set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
change (if (u1 <? 4 * c1) && negb ns
then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
else c1
else c1) with (ag_cnt2 sc c1 u1 ns).
set (c2 := ag_cnt2 sc c1 u1 ns).
specialize (AR u1 ns).
assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r n3 st1' in
ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
(let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
{ intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
unfold ag_cn3 in GO. cbn zeta in GO.
destruct (negb ns && (c2 <=? 7)).
* destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
-- cbn beta iota. exact (GO _ _ eq_refl).
-- cbn beta iota. exact (GO _ _ eq_refl).
* cbn beta iota. exact (GO _ _ eq_refl).
+
pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.

End RC__1.
