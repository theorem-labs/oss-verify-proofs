(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Ext2 MI_Shadow
  MI_WFree2 MI_WGroup MI_TF2 MI_Pres1 MI_Pres2 MI_Ledger MI_WAMeta MI_WMalloc MI_WFree Realloc MI_Realloc.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section REMAP_CORE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (ai : Z) (nb needed : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! (rid, 0) = Some (mkGhdr (Some g) ai).
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Hypothesis HP : x_pend X = Some (rid, 16).
Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NDA : needed mod 4096 = 0.
Hypothesis NDP : 0 < needed.
Hypothesis NDM : needed < 2 ^ 62.
Hypothesis NCEIL : nb + needed <= alloc_ceiling.
Hypothesis DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> rid ->
  let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb.

Let mp := needed / 4096.
Let f := m_set_maplen mp.
Let r' := mkRegion RKGroup nb needed.
Let bg : aptr := (rid, 0).
Let c : aptr := (rid, 16).
Definition stR : mstate := upd_meta g f (set_regions (<[rid := r']> (s_regions st)) st).
Definition e' : aptr := (rid, needed - 4).

Definition kt : Z := Z.min (m_maplen (MR st g) * 4096) needed.
Definition stT : mstate := trim_shadow rid kt stR.
Definition stB : mstate := wr8 e' 0 stT.
Definition isgroup (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition L' : mled := KInv.set_groups (map (fun kr => (r_base (snd kr), r_len (snd kr))) (List.filter isgroup (map_to_list (s_regions stR)))) L.

Local Notation R := (MR st).
Local Notation R' := (MR stB).

Let IR := proj1 INV.
Let IA := proj1 (proj2 INV).
Let IM := proj1 (proj2 (proj2 INV)).
Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g_hosts : hosts st bg g. Proof. exists ai. exact Hg. Qed.
Lemma GO : group_ok X st LS g bg ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
Lemma g_top_facts : m_last_idx (R g) = 0 /\ m_maplen (R g) <> 0 /\ ~ in_list LS g.
Proof. destruct (g_sc _ _ _ _ _ _ GO) as [[A _]|(A & B & C & D)]; [rewrite SC63 in A; lia| auto]. Qed.
Lemma g_region : exists r0, s_regions st !! rid = Some r0 /\ r_kind r0 = RKGroup /\ m_maplen (R g) * 4096 = round_up_pg (r_len r0).
Proof.
  destruct g_top_facts as (_ & ML & _). destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr & Kr & E & _). exists r0. auto.
Qed.
Lemma g_mem : m_mem (R g) = Some bg. Proof. exact (hosts_mem _ _ _ IM _ _ g_hosts). Qed.
Lemma g_present : s_metas st !! g <> None. Proof. exact (MI_Inv.g_present _ _ _ _ _ _ GO). Qed.

Lemma mp_pos : 1 <= mp < 2 ^ 50.
Proof. unfold mp. Z.div_mod_to_equations. lia. Qed.
Lemma mp_eq : mp * 4096 = needed.
Proof. unfold mp. Z.div_mod_to_equations. lia. Qed.

Lemma fR_maplen r : m_maplen (f r) = mp.
Proof. unfold f, m_set_maplen. cbn. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. pose proof mp_pos. lia. Qed.
Lemma fR_mem r : m_mem (f r) = m_mem r. Proof. reflexivity. Qed.
Lemma fR_prev r : m_prev (f r) = m_prev r. Proof. reflexivity. Qed.
Lemma fR_next r : m_next (f r) = m_next r. Proof. reflexivity. Qed.
Lemma fR_last r : m_last_idx (f r) = m_last_idx r. Proof. reflexivity. Qed.
Lemma fR_freeable r : m_freeable (f r) = m_freeable r. Proof. reflexivity. Qed.
Lemma fR_sc r : m_sizeclass (f r) = m_sizeclass r. Proof. reflexivity. Qed.
Lemma fR_avail r : m_avail (f r) = m_avail r. Proof. reflexivity. Qed.
Lemma fR_freed r : m_freed (f r) = m_freed r. Proof. reflexivity. Qed.
Lemma fR_gbase r : gbase (f r) = gbase r. Proof. reflexivity. Qed.
Lemma fRg_stride : get_stride (f (R g)) = needed - UNIT.
Proof.
  unfold get_stride. rewrite fR_last, fR_maplen, fR_sc. destruct g_top_facts as (L0 & _). rewrite L0. cbn [Z.eqb andb].
  pose proof mp_pos. replace (mp =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. rewrite mp_eq. reflexivity.
Qed.
Lemma fRg_sstart i : sstart (f (R g)) i = 16 + (needed - UNIT) * i.
Proof. unfold sstart. rewrite fR_gbase, (hosts_gbase _ _ _ IM _ _ g_hosts), fRg_stride. cbn. unfold UNIT. lia. Qed.

Lemma stB_groups : s_groups stB = s_groups st. Proof. reflexivity. Qed.
Lemma stB_slots : s_slots stB = s_slots st. Proof. reflexivity. Qed.
Lemma stB_ctx : s_ctx stB = s_ctx st. Proof. reflexivity. Qed.
Lemma stB_areas : s_areas stB = s_areas st. Proof. reflexivity. Qed.
Lemma stB_secret : s_secret stB = s_secret st. Proof. reflexivity. Qed.
Lemma stB_reserved : s_reserved stB = s_reserved st. Proof. reflexivity. Qed.
Lemma stB_tick : s_tick stB = s_tick st. Proof. reflexivity. Qed.
Lemma stB_next_rid : s_next_rid stB = s_next_rid st. Proof. reflexivity. Qed.
Lemma stB_metas : s_metas stB = s_metas stR. Proof. reflexivity. Qed.
Lemma stB_regions : s_regions stB = <[rid := r']> (s_regions st). Proof. reflexivity. Qed.
Lemma stR_regions : s_regions stR = <[rid := r']> (s_regions st). Proof. reflexivity. Qed.
Lemma regions_lookup q : s_regions stB !! q = if (q =? rid)%N then Some r' else s_regions st !! q.
Proof. rewrite stB_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| apply lookup_insert_ne; congruence]. Qed.
Lemma regions_some q rq : s_regions stB !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite regions_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma regions_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions stB !! q = Some rq.
Proof. intros H NE. rewrite regions_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.

Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold MR. change (get_meta_rec stB x) with (get_meta_rec stR x). unfold stR. rewrite get_meta_rec_upd. reflexivity. Qed.
Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : R' g = f (R g). Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_avail x : m_avail (R' x) = m_avail (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freed x : m_freed (R' x) = m_freed (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. unfold cnt_of. rewrite R'_last. reflexivity. Qed.
Lemma R'_maplen_other x : x <> g -> m_maplen (R' x) = m_maplen (R x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_stride_other x : x <> g -> get_stride (R' x) = get_stride (R x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_sstart_other x i : x <> g -> sstart (R' x) i = sstart (R x) i. Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_slot_start'_other x i : x <> g -> slot_start' (R' x) i = slot_start' (R x) i. Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_gend_other x : x <> g -> gend (R' x) = gend (R x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_maplen_ne0 x : m_maplen (R' x) <> 0 <-> m_maplen (R x) <> 0.
Proof.
  rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; [| split; intros H; exact H]. rewrite fR_maplen. pose proof mp_pos. destruct g_top_facts as (_ & ML & _). split; intros; lia.
Qed.
Lemma R'_maplen_0 x : m_maplen (R' x) = 0 <-> m_maplen (R x) = 0.
Proof.
  rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; [| split; intros H; exact H]. rewrite fR_maplen. pose proof mp_pos. destruct g_top_facts as (_ & ML & _). split; intros; lia.
Qed.

Lemma hosts' b m : hosts stB b m <-> hosts st b m. Proof. apply hosts_ext. reflexivity. Qed.
Lemma live' m : live_group stB m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
Lemma keys' x : s_metas stB !! x <> None <-> s_metas st !! x <> None.
Proof.
  rewrite stB_metas. unfold stR. rewrite lookup_metas_upd. change (s_metas (set_regions _ st)) with (s_metas st). change (get_meta_rec (set_regions _ st) g) with (get_meta_rec st g).
  destruct (aptr_eqb_spec x g) as [->|NE]; [| split; intros H; exact H]. split; [intros _; exact g_present| intros _; discriminate].
Qed.

Lemma rid_groups b h : s_groups st !! b = Some h -> fst b = rid -> b = bg /\ g_meta h = Some g.
Proof.
  intros Hb Hf. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _).
  assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
  destruct g_top_facts as (_ & ML & _).
  destruct (Z.eq_dec (m_maplen (R m)) 0) as [Z0|NZ].
  - exfalso. destruct (@top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & j & c' & bt & Ha & Ht & Htop & Hft).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt bg Ht g_hosts Htop ML); rewrite Hft, Hf; reflexivity). subst t.
    destruct (@anc_facts _ _ _ _ IM IG IS m g j c' Ha) as (bm' & bp' & _ & _ & _ & _ & _ & _ & _ & _ & SC). rewrite SC63 in SC. lia.
  - pose proof (@top_unique _ _ _ IG m g b bg Hm g_hosts NZ ML Hf) as ->.
    split; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)| exact Em].
Qed.

Lemma rid_slots s m i : s_slots st !! s = Some (m, i) -> fst s = rid -> s = c /\ m = g /\ i = 0.
Proof.
  intros Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb) in Es.
  assert (Fb : fst b = rid) by (rewrite Es in Hf; exact Hf).
  destruct Hb as [aib Hb']. destruct (rid_groups b _ Hb' Fb) as [-> Em]. cbn in Em. inversion Em. subst m.
  destruct g_top_facts as (L0 & _). rewrite L0 in Hi. assert (i = 0) by lia. subst i.
  split; [| auto]. rewrite Es. rewrite (sstart0 _ _ _ IM _ _ g_hosts). reflexivity.
Qed.

Lemma rid_blocks k : In k BL -> fst (bslot k) <> rid.
Proof.
  intros Hk Hf. destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (rid_slots _ _ _ Hs Hf) as (Es & -> & ->).
  pose proof (is_part _ _ _ IS _ _ _ 0 Hg ltac:(destruct g_top_facts as (L0 & _); rewrite L0; lia)) as P. cbn zeta in P.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts), (sstart0 _ _ _ IM _ _ g_hosts) in P. cbn [fst snd] in P. change (0 + UNIT) with 16 in P.
  rewrite HP in P. unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _).
  apply nCE. split; [| reflexivity]. replace (rid, 16) with (bslot k) by (rewrite Es; reflexivity). apply in_map. exact Hk.
Qed.

Lemma c_nogroup : s_groups st !! c = None.
Proof.
  destruct (s_groups st !! c) as [h|] eqn:E; [| reflexivity]. exfalso.
  destruct (rid_groups c h E eq_refl) as [Ec _]. unfold c, bg in Ec. inversion Ec.
Qed.

Lemma no_nested m b : hosts st b m -> m_maplen (R m) = 0 -> fst b <> rid.
Proof. intros [aib Hb] Z0 Hf. destruct (rid_groups b _ Hb Hf) as [-> Em]. cbn in Em. inversion Em. subst m. destruct g_top_facts as (_ & ML & _). exact (ML Z0). Qed.

Lemma L'_live : ld_live L' = ld_live L. Proof. reflexivity. Qed.
Lemma L'_resv : ld_resv L' = ld_resv L. Proof. reflexivity. Qed.
Lemma L'_metas : ld_metas L' = ld_metas L. Proof. reflexivity. Qed.
Lemma L'_brk : ld_brk L' = ld_brk L. Proof. reflexivity. Qed.
Lemma L'_brkreg : ld_brkreg L' = ld_brkreg L. Proof. reflexivity. Qed.

Lemma regions_perm : Permutation (map_to_list (s_regions stB)) ((rid, r') :: map_to_list (delete rid (s_regions st))).
Proof.
  rewrite stB_regions. rewrite <- (insert_delete_eq (s_regions st) rid r'). apply map_to_list_insert. apply lookup_delete_eq.
Qed.
Lemma regions_perm_old r0 : s_regions st !! rid = Some r0 -> Permutation (map_to_list (s_regions st)) ((rid, r0) :: map_to_list (delete rid (s_regions st))).
Proof. intros H. symmetry. apply map_to_list_delete. exact H. Qed.

Lemma round_up_needed : round_up_pg needed = needed.
Proof. apply round_up_pg_id. unfold PGSZ. exact NDA. Qed.

Lemma frontier' q rq : frontier stB q rq = frontier st q rq. Proof. reflexivity. Qed.

Lemma inv_R_B : inv_R X stB L'.
Proof.
  destruct g_region as (r0 & Hr0 & Kr0 & ML0).
  pose proof IR as IR0. destruct IR0; constructor; rewrite ?stB_ctx, ?stB_next_rid, ?stB_reserved, ?L'_resv, ?L'_metas, ?L'_brk, ?L'_brkreg.
  - intros q rq Hq. apply regions_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr0)| exact (ir_ids q rq Hq)].
  - intros q rq Hq. apply regions_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn [r_base r_len r_kind r'].
    rewrite round_up_needed. split; [lia|]. split; [unfold PGSZ; exact NBA|]. split; [lia|]. split; [unfold LEN_MAX; lia|]. split; [lia|].
    intros [K|K]; discriminate.
  - intros q1 q2 r1 r2 H1 H2 NE.
    apply regions_some in H1 as [[-> ->]|[N1 H1]]; apply regions_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
    + cbn [region_live_range r_kind r_base r_len r']. rewrite round_up_needed. pose proof (DISJ q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
    + pose proof (DISJ q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn [region_live_range r_kind r_base r_len r']. rewrite round_up_needed. lia.
  - exact ir_resv.
  - unfold L'. cbn [ld_groups KInv.set_groups]. rewrite stR_regions, <- stB_regions. apply Permutation_refl.
  - eapply Permutation_trans; [exact ir_metas|].
    eapply Permutation_trans; [apply Permutation_map; apply perm_filter; apply (regions_perm_old r0 Hr0)|].
    eapply Permutation_trans; [| apply Permutation_map; apply perm_filter; apply Permutation_sym; apply regions_perm].
    cbn [List.filter r_kind snd r']. rewrite Kr0. erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. cbn. rewrite frontier'. reflexivity.
  - intros q rq Hq K. apply regions_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite frontier'. exact (ir_metalen q rq Hq K).
  - intros q rq Hq K. apply regions_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite frontier'. exact (ir_brkfront q rq Hq K).
  - destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
    right. exists q, rq. split; [apply regions_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; rewrite Kr0 in K; discriminate]| auto].
  - intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
    + split; [apply regions_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; rewrite Kr0 in K; discriminate]| auto].
    + apply regions_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply regions_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply regions_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
    exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
  - revert ir_brk. destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
    + destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply regions_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
    + exact IBK.
    + destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq.
      split; [apply regions_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; rewrite Kr0 in K; discriminate]| auto].
  - destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
    intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq.
    split; [apply regions_keep; [exact Hq| intros ->; rewrite Hr0 in Hq; inversion Hq; subst; destruct K as [K|K]; rewrite Kr0 in K; discriminate]| auto].
  - intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & K & NG).
    destruct (N.eq_dec q rid) as [->|NE].
    + exfalso. specialize (NG bg eq_refl). rewrite Hg in NG. discriminate.
    + exists rq. split; [apply regions_keep; assumption|]. split; [exact K|]. intros b Hb. rewrite stB_groups. exact (NG b Hb).
Qed.

Lemma inv_A_B : inv_A stB.
Proof.
  pose proof IA as IA0. destruct IA0; constructor; rewrite ?stB_ctx, ?stB_areas, ?stB_secret; try assumption.
  - intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
    exists rq. rewrite frontier'. split; [| auto]. apply regions_keep; [exact Hq|].
    intros Ea. rewrite Ea in Hq. destruct g_region as (r0 & Hr0 & Kr0 & _). rewrite Hr0 in Hq. inversion Hq. subst. destruct K as [K|K]; rewrite Kr0 in K; discriminate.
  - intros m mr Hm. assert (K : s_metas stB !! m <> None) by congruence. apply keys' in K.
    destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
  - destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
    intros k Hk2. destruct (s_metas stB !! mslot a k) eqn:E; [| reflexivity]. exfalso.
    assert (K : s_metas stB !! mslot a k <> None) by congruence. apply keys' in K. apply K. apply Hk. exact Hk2.
  - intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [| exact K]. apply regions_keep; [exact Hrq|].
    intros Eq. rewrite Eq in Hrq. destruct g_region as (r0 & Hr0 & Kr0 & _). rewrite Hr0 in Hrq. inversion Hrq. subst. destruct K as [K|K]; rewrite Kr0 in K; discriminate.
  - intros sc Hsc. unfold usage, ctx. rewrite stB_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
    unfold gcnt. rewrite stB_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
    rewrite R'_sc, R'_cnt. reflexivity.
Qed.

Lemma inv_M_B : inv_M X stB LS.
Proof.
  pose proof IM as IM0. destruct IM0 as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply M1; exact Hm].
    exfalso. rewrite g_mem in Hm. discriminate.
  - intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
  - intros bb h Hb. rewrite stB_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
  - intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
    rewrite stB_metas. unfold stR. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
    exfalso. pose proof g_mem as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
  - intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, stB_groups. repeat split; auto. exists bb. auto.
Qed.

Lemma inv_L_B : inv_L stB LS.
Proof.
  pose proof IL as IL0. destruct IL0 as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. transitivity (get_head st h); [| apply L1]. destruct h; reflexivity.
  - intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
    eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
  - exact L3.
  - exact L4.
  - intros m. rewrite R'_next, R'_prev. apply L5.
  - intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
    exfalso. destruct g_top_facts as (_ & _ & NIL). apply NIL. exists LFree. exact Hm.
  - intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
  - exact L9.
Qed.

Lemma bb_not_rid m bb aim : s_groups st !! bb = Some (mkGhdr (Some m) aim) -> m <> g -> fst bb <> rid.
Proof. intros Hb NE Hf. destruct (rid_groups bb _ Hb Hf) as [_ Em]. cbn in Em. apply NE. congruence. Qed.

Lemma inv_G_B : inv_G X stB LS.
Proof.
  pose proof IG as IG0. destruct IG0 as [G1 G2 G3 G4 G5]. constructor.
  - intros m bb aim Hm. rewrite stB_groups in Hm. pose proof (G1 m bb aim Hm) as GOm.
    destruct (aptr_eqb_spec m g) as [->|NE].
    +
      pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
      rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
      destruct g_top_facts as (L0 & ML & NIL). pose proof mp_pos as MP.
      destruct GOm; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_gbase, ?stB_slots; try assumption.
      * apply keys'. exact g_present0.
      * right. split; [exact SC63|]. split; [exact L0|]. split; [lia| exact NIL].
      * lia.
      * intros Hsc. rewrite SC63 in Hsc. lia.
      * intros _ Hsc. rewrite SC63 in Hsc. lia.
      * intros _. split; [reflexivity|]. exists r'. split; [rewrite regions_lookup, N.eqb_refl; reflexivity|]. split; [reflexivity|].
        rewrite round_up_needed, mp_eq. split; [reflexivity|].
        unfold gend, cnt_of. rewrite fR_last, L0, fRg_sstart. unfold UNIT. lia.
      * intros Z0. exfalso. lia.
    + pose proof (bb_not_rid m bb aim Hm NE) as NR.
      destruct GOm; constructor; rewrite ?(R'_other m NE), ?stB_slots; try assumption.
      * apply keys'. exact g_present0.
      * intros Hml. destruct (g_top Hml) as (B0 & rq & Hrq & K & E & GE). split; [exact B0|]. exists rq. split; [apply regions_keep; [exact Hrq| exact NR]| auto].
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Fp & GE & SC & ST).
        assert (NEp : p <> g) by (intros ->; rewrite SC63 in SC; lia).
        exists p, i. rewrite !(R'_other p NEp). auto 10.
      all: match goal with |- ?gg => idtac "REMAINS-O" gg end.
  - intros bb aim H. rewrite stB_groups in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite stB_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
  - intros q rq Hq K Ho. apply regions_some in Hq as [[-> ->]|[NEq Hq]].
    + exists g. split; [apply hosts'; exact g_hosts|]. apply R'_maplen_ne0. exact (proj1 (proj2 g_top_facts)).
    + destruct (G4 q rq Hq K Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen_ne0. auto.
  - intros bb h H. rewrite stB_groups in H. destruct (G5 bb h H) as (rq & Hrq & K).
    destruct (N.eq_dec (fst bb) rid) as [E|NE].
    + exists r'. rewrite E, regions_lookup, N.eqb_refl. split; [reflexivity| reflexivity].
    + exists rq. split; [apply regions_keep; assumption| exact K].
Qed.

Lemma fRg_slot_start'0 : slot_start' (f (R g)) 0 = slot_start' (R g) 0.
Proof. unfold slot_start'. rewrite fR_mem. rewrite !Z.mul_0_r. reflexivity. Qed.
Lemma R'_slot_start' m i : (m = g -> i = 0) -> slot_start' (R' m) i = slot_start' (R m) i.
Proof. intros Hi. destruct (aptr_eqb_spec m g) as [->|NE]; [rewrite (Hi eq_refl), R'_g; apply fRg_slot_start'0| apply R'_slot_start'_other; exact NE]. Qed.

Lemma inv_S_B : inv_S X stB BL.
Proof.
  destruct g_top_facts as (L0 & ML & NIL).
  pose proof IS as IS0. destruct IS0 as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite stB_slots in H. destruct (S1 s m i H) as (LV & Hi & Es). rewrite live', R'_last. split; [exact LV|]. split; [exact Hi|].
    rewrite R'_slot_start'; [exact Es|]. intros ->. rewrite L0 in Hi. lia.
  - intros bb m i Hb Hi. rewrite stB_slots. rewrite R'_last in Hi. apply hosts' in Hb. rewrite R'_slot_start'; [exact (S2 bb m i Hb Hi)|]. intros ->. rewrite L0 in Hi. lia.
  - intros bb m aim i Hb Hi. rewrite stB_groups in Hb. rewrite R'_last in Hi. rewrite stB_groups, R'_avail, R'_freed.
    rewrite R'_slot_start' by (intros ->; rewrite L0 in Hi; lia). exact (S3 bb m aim i Hb Hi).
  - intros s Hs. rewrite stB_slots. exact (S4 s Hs).
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & Hs & Ho & Hz & Hf). exists m, i. rewrite stB_slots. split; [exact Hs|]. split; [exact Ho|]. split; [exact Hz|].
    rewrite R'_stride_other; [exact Hf|]. intros ->. destruct (rid_slots _ _ _ Hs) as (Es & _); [| apply (rid_blocks k Hk); rewrite Es; reflexivity].
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es'). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb) in Es'.
    rewrite (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) in Es'. rewrite Es'. reflexivity.
Qed.

Lemma kt_ge : 4096 <= kt.
Proof.
  unfold kt. pose proof mp_pos as MP. pose proof mp_eq as ME. destruct g_top_facts as (_ & ML & _).
  pose proof (g_maplen _ _ _ _ _ _ GO) as M0. lia.
Qed.
Lemma TKS_R : TKS stR (s_tick st). Proof. exact (TKS_of _ _ _ _ _ INV). Qed.
Lemma s_shadow_stT : s_shadow stT = <[rid := mkShadow (trim_cells kt (r_cells (get_shadow stR rid))) (r_hav (get_shadow stR rid)) (r_havp (get_shadow stR rid))]> (s_shadow st).
Proof. reflexivity. Qed.
Lemma get_shadow_stT_other q : q <> rid -> get_shadow stT q = get_shadow st q.
Proof. intros NE. rewrite (get_shadow_eq stT), s_shadow_stT, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma get_shadow_stT_rid : get_shadow stT rid = mkShadow (trim_cells kt (r_cells (get_shadow st rid))) (r_hav (get_shadow st rid)) (r_havp (get_shadow st rid)).
Proof. rewrite (get_shadow_eq stT), s_shadow_stT, lookup_insert_eq. reflexivity. Qed.
Lemma trim_cells_lookup_lt k cs o : o < k -> trim_cells k cs !! o = cs !! o.
Proof.
  intros Ho. unfold trim_cells. rewrite map_lookup_filter. destruct (cs !! o) as [x|]; cbn; [| reflexivity].
  rewrite option_guard_True by (cbn; exact Ho). reflexivity.
Qed.
Lemma trim_cells_lookup_Some k cs o x : trim_cells k cs !! o = Some x -> cs !! o = Some x /\ o < k.
Proof. intros H. unfold trim_cells in H. apply map_lookup_filter_Some in H. cbn in H. exact H. Qed.
Lemma TKS_T : TKS stT (s_tick st).
Proof.
  intros q sh Hq. rewrite s_shadow_stT in Hq. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_insert_eq in Hq. injection Hq as <-. cbn [r_cells r_hav r_havp].
    pose proof (sh_ticks_of _ rid TKS_R) as [B C]. change (get_shadow stR rid) with (get_shadow st rid) in B, C.
    split; [| split; [exact B| exact C]].
    intros o w t Ho. apply trim_cells_lookup_Some in Ho as [Ho _].
    destruct (get_shadow_cells_some st rid o (w, t) Ho) as (sh0 & Hs0 & Hc0). exact (proj1 (TKS_R rid sh0 Hs0) o w t Hc0).
  - rewrite lookup_insert_ne in Hq by congruence. exact (TKS_R q sh Hq).
Qed.
Definition keepB (q : aptr) : Prop := fst q <> rid \/ (snd q < needed - 4 /\ snd q < kt).
Lemma read_T q : fst q <> rid \/ snd q < kt -> cell_read (get_shadow stT (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros HD. destruct (N.eq_dec (fst q) rid) as [E|NE].
  - rewrite E, get_shadow_stT_rid. destruct HD as [HD|HD]; [congruence|]. unfold cell_read. cbn [r_cells r_hav r_havp].
    rewrite trim_cells_lookup_lt by exact HD. reflexivity.
  - rewrite get_shadow_stT_other by exact NE. reflexivity.
Qed.
Lemma read_B q : keepB q -> cell_read (get_shadow stB (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros HD. unfold stB. rewrite (cell_read_wr8_other e' 0 stT q) by (intros ->; unfold e', keepB in HD; cbn in HD; clear - HD; lia).
  apply read_T. unfold keepB, kt in *. clear - HD. lia.
Qed.
Lemma known_B q v : known st q v -> keepB q -> known stB q v.
Proof. intros K NE. unfold known, SHd in *. rewrite (read_B q NE). exact K. Qed.
Lemma unknown_B q : unknown st q -> keepB q -> unknown stB q.
Proof. intros K NE. unfold unknown, SHd in *. rewrite (read_B q NE). exact K. Qed.
Lemma known_e' : known stB e' 0.
Proof. unfold known, SHd, stB. cbn [fst snd]. rewrite (cell_read_wr8_same e' 0 stT); [reflexivity|]. apply sh_ticks_of. exact TKS_T. Qed.
Lemma ne_e' q : keepB q -> keepB q.
Proof. exact (fun H => H). Qed.

Lemma inv_SH_B : inv_SH stB BL.
Proof.
  destruct g_top_facts as (L0 & ML & NIL). pose proof mp_pos as MP. pose proof kt_ge as KG.
  pose proof ISH as ISH0. destruct ISH0 as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros q sh Hq. unfold stB, wr8, upd_shadow in Hq. cbn [s_shadow e' fst] in Hq. rewrite s_shadow_stT in Hq.
    destruct (N.eq_dec q rid) as [->|NE].
    + exists r'. rewrite regions_lookup, N.eqb_refl. split; reflexivity.
    + rewrite !lookup_insert_ne in Hq by congruence. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply regions_keep; assumption| exact K].
  - change (TKS stB (s_tick st)). unfold stB. apply TKS_wr8; [cbn; lia| exact TKS_T].
  - intros b m i Hb Hi. apply hosts' in Hb. rewrite R'_cnt in Hi.
    destruct (aptr_eqb_spec m g) as [->|NE].
    + pose proof (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) as ->. rewrite R'_g, fRg_sstart. unfold cnt_of in Hi. rewrite L0 in Hi.
      assert (i = 0 \/ i = 1) as [Ei|Ei] by lia; rewrite Ei.
      * replace (16 + (needed - UNIT) * 0 - IB) with (sstart (R g) 0 - IB) by (rewrite (sstart0 _ _ _ IM _ _ g_hosts); cbn -[Z.add Z.mul Z.sub]; unfold UNIT; lia).
        apply known_B; [exact (D3 bg g 0 g_hosts ltac:(unfold cnt_of; lia))|]. apply ne_e'. right. rewrite (sstart0 _ _ _ IM _ _ g_hosts). cbn -[Z.add Z.mul Z.sub]. unfold UNIT, IB. lia.
      * replace (fst bg, 16 + (needed - UNIT) * 1 - IB) with e' by (unfold e', UNIT, IB; cbn; f_equal; lia). apply known_e'.
    + rewrite R'_sstart_other by exact NE. apply known_B; [exact (D3 b m i Hb Hi)|]. apply ne_e'. left. destruct Hb as [aim Hb]. exact (bb_not_rid m b aim Hb NE).
  - intros b m o Hb Ho. apply hosts' in Hb. apply unknown_B; [exact (D4 b m o Hb Ho)|]. apply ne_e'.
    destruct (aptr_eqb_spec m g) as [->|NE]; [| left; destruct Hb as [aim Hb]; exact (bb_not_rid m b aim Hb NE)].
    right. pose proof (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) as ->. cbn. lia.
  - intros b m p i Hb Hml Hs. apply hosts' in Hb. rewrite R'_maplen_0 in Hml. rewrite stB_slots in Hs.
    assert (NE : m <> g) by (intros ->; exact (ML Hml)).
    pose proof (no_nested m b Hb Hml) as NR.
    assert (NEp : p <> g).
    { intros ->. destruct (rid_slots _ _ _ Hs) as (Es & _ & _); [| rewrite Es in NR; exact (NR eq_refl)].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & _ & Es'). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb'), (hosts_inj _ _ _ IM _ _ _ Hb' g_hosts) in Es'.
      rewrite Es'. reflexivity. }
    rewrite !(R'_other p NEp).
    destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply known_B; [exact K3| apply ne_e'; left; exact NR]| auto]|].
    split; [apply known_B; [exact K2| apply ne_e'; left; exact NR]|]. split; [apply known_B; [exact K1| apply ne_e'; left; exact NR]| exact Q].
  - intros k m i Hk Hs. rewrite stB_slots in Hs. pose proof (rid_blocks k Hk) as NR.
    assert (NE : m <> g).
    { intros ->. destruct (rid_slots _ _ _ Hs) as (Es & _ & _); [| rewrite Es in NR; exact (NR eq_refl)].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & _ & Es'). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb'), (hosts_inj _ _ _ IM _ _ _ Hb' g_hosts) in Es'.
      rewrite Es'. reflexivity. }
    rewrite !(R'_other m NE).
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply known_B; [exact A1| apply ne_e'; left; exact NR]|]. split; [apply known_B; [exact A2| apply ne_e'; left; exact NR]|].
    split; [apply known_B; [exact A3| apply ne_e'; left; exact NR]|]. split; [apply known_B; [exact A4| apply ne_e'; left; exact NR]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try (apply known_B; [assumption| apply ne_e'; left; exact NR]). exact B6.
    + split; [intros Hr; apply known_B; [apply A7; exact Hr| apply ne_e'; left; exact NR]|]. intros x Hx. apply unknown_B; [apply A8; exact Hx| apply ne_e'; left; exact NR].
Qed.

Theorem remap_core_INVL : INVL X stB L' BL LS.
Proof.
  split; [exact inv_R_B|]. split; [exact inv_A_B|]. split; [exact inv_M_B|]. split; [exact inv_L_B|].
  split; [exact inv_G_B|]. split; [exact inv_S_B| exact inv_SH_B].
Qed.
End REMAP_CORE.

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off old n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In ((c, off), old) BL.
Hypothesis NP : x_pend X = None.
Hypothesis Hn : 0 <= n < 2 ^ 48.
Variables (g bg : aptr) (idx ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off old g bg idx ai a ar ka.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Variable nb : Z.
Let rid : N := fst c.
Let needed : Z := remap_needed (UNIT * off) n.
Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NCEIL : nb + needed <= alloc_ceiling.
Hypothesis DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> rid ->
  let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let st_t := set_tick (N.succ (s_tick st)) st.
Let X1 := mkX (x_idle X) (x_zomb X) (Some c) (x_orph X) (x_fresh X).
Let BL1 := bl_remove c BL.
Let stBB := stB st_t g rid nb needed.
Definition LR : mled := L' st_t L g rid nb needed.

Lemma rm_hosts : hosts st bg g. Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
Lemma rm_GO : group_ok X st LS g bg ai. Proof. exact (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)). Qed.
Lemma rm_top : m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ idx = 0 /\ bg = (rid, 0) /\ c = (rid, 16).
Proof.
  destruct (g_sc _ _ _ _ _ _ rm_GO) as [[A _]|(A & B & C & D)]; [rewrite SC63 in A; lia|].
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  destruct (g_top _ _ _ _ _ _ rm_GO C) as [B0 _].
  assert (I0 : idx = 0) by lia.
  assert (Ebg : bg = (rid, 0)) by (unfold rid; rewrite Ec; cbn [fst]; destruct bg; cbn in B0 |- *; subst; reflexivity).
  split; [exact B|]. split; [exact C|]. split; [exact I0|]. split; [exact Ebg|].
  rewrite Ec at 1. rewrite Ebg. cbn [fst]. f_equal. rewrite I0, (sstart0 _ _ _ IM _ _ rm_hosts), Ebg. reflexivity.
Qed.
Lemma needed_facts : needed mod 4096 = 0 /\ n + UNIT * off + UNIT + IB <= needed < n + UNIT * off + UNIT + IB + 4096.
Proof. split; [apply remap_needed_pg| apply remap_needed_ge; [lia| pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); unfold UNIT; lia]]. Qed.

Lemma INV_t : INVL X st_t L BL LS. Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
Lemma INV1 : INVL X1 st_t L BL1 LS.
Proof.
  apply (INVL_remove_block X st_t st_t L BL LS ((c, off), old) INV_t Hk NP); [apply ctrl_eq_refl| reflexivity| intros; reflexivity| exact (DOMS_of _ _ _ _ _ INV_t)| exact (TKS_of _ _ _ _ _ INV_t)].
Qed.
Lemma HgT : s_groups st_t !! (rid, 0) = Some (mkGhdr (Some g) ai).
Proof. destruct rm_top as (_ & _ & _ & Ebg & _). rewrite <- Ebg. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
Lemma HPT : x_pend X1 = Some (rid, 16).
Proof. destruct rm_top as (_ & _ & _ & _ & Ec). cbn. rewrite Ec. reflexivity. Qed.
Lemma ND : needed mod 4096 = 0 /\ 0 < needed /\ needed < 2 ^ 62.
Proof. destruct needed_facts as [A B]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). unfold UNIT, IB in B. split; [exact A| lia]. Qed.

Lemma INVB : INVL X1 stBB LR BL1 LS.
Proof.
  destruct ND as (NDA & NDP & NDM).
  exact (remap_core_INVL X1 st_t L BL1 LS g rid ai nb needed INV1 HgT SC63 HPT NB0 NBA NDA NDP NDM NCEIL DISJ).
Qed.

Lemma strideB : get_stride (MR stBB g) = needed - UNIT.
Proof.
  destruct ND as (NDA & NDP & NDM). unfold stBB. rewrite (R'_g st_t g rid nb needed).
  exact (fRg_stride X1 st_t L BL1 LS g rid ai nb needed INV1 HgT SC63 NDA NDP NDM).
Qed.

Definition stRF : mstate := stf stBB c off n g 0.

Lemma remap_full_eq : remap_full st c off n nb needed = stRF.
Proof.
  destruct rm_top as (L0 & ML & I0 & Ebg & Ec).
  unfold remap_full. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). rewrite I0.
  unfold stRF, stf, stw, SL, ee.
  assert (E1 : set_tick (N.succ (s_tick st)) (trim_shadow (fst c) (Z.min (m_maplen (get_meta_rec st g) * 4096) needed) (remap_update st (fst c) g nb needed))
               = stT st_t g rid nb needed) by reflexivity.
  rewrite E1.
  assert (E2 : get_stride (get_meta_rec (stT st_t g rid nb needed) g) = needed - UNIT).
  { change (get_meta_rec (stT st_t g rid nb needed) g) with (MR stBB g). exact strideB. }
  rewrite E2. change (get_stride (MR stBB g)) with (get_stride (MR stBB g)). rewrite strideB.
  assert (E3 : aadd c (needed - UNIT - IB) = e' rid needed) by (rewrite Ec; unfold aadd, e', UNIT, IB; cbn; f_equal; lia).
  rewrite E3. reflexivity.
Qed.

Theorem remap_INVL : INVL X (remap_full st c off n nb needed) LR (((c, off), n) :: bl_remove c BL) LS.
Proof.
  rewrite remap_full_eq. unfold stRF.
  destruct rm_top as (L0 & ML & I0 & Ebg & Ec). destruct needed_facts as [NDA NDR]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  assert (EX : mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1) = X).
  { destruct X as [xi xz xp xo xf]. cbn in NP |- *. rewrite NP. reflexivity. }
  rewrite <- EX.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) in SHB. destruct SHB as (K4 & K3 & K2 & K1 & Q & _).
  rewrite ?Ebg, ?Ec in K4. rewrite ?Ebg, ?Ec in K2. rewrite ?Ebg, ?Ec in K1. rewrite ?Ebg, ?Ec in Q. cbn [fst snd] in K4, K2, K1, Q.
  assert (HgB : hosts stBB bg g) by (apply hosts'; rewrite Ebg; exists ai; exact HgT).
  assert (KG : 4096 <= kt st g needed).
  { destruct ND as (NDA' & NDP' & NDM'). pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HB0. rewrite Ebg in HB0.
    eapply (kt_ge X st L BL LS g rid ai nb needed INV HB0 SC63); eauto. }
  assert (NEe : forall x, x < needed - 4 -> x < 4096 -> keepB st g rid needed (rid, x)) by (intros x Hx Hx'; right; cbn; change (kt st_t g needed) with (kt st g needed) || idtac; lia).
  assert (Hc' : c = (fst bg, sstart (MR stBB g) 0)).
  { rewrite Ec, Ebg. cbn [fst]. f_equal. unfold sstart. rewrite Z.mul_0_r, Z.add_0_r. unfold stBB. rewrite (R'_gbase st_t g rid nb needed). change (MR st_t g) with (MR st g).
    rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), Ebg. reflexivity. }
  apply (add_resized_INVL X1 stBB LR BL1 LS c off n g bg 0 INVB eq_refl HgB).
  - unfold stBB. rewrite (R'_last st_t g rid nb needed). change (MR st_t g) with (MR st g). rewrite L0. lia.
  - exact Hc'.
  - exact Hoff.
  - lia.
  - rewrite strideB. unfold UNIT, IB in *. lia.
  - rewrite strideB. unfold UNIT, IB in *. lia.
  - unfold qv. rewrite Ebg, Ec. cbn [fst snd pp aadd]. apply known_B; [exact K4| apply NEe; unfold UNIT, IB in *; lia].
  - unfold qv. rewrite Ebg, Ec. cbn [fst snd pp aadd]. apply known_B; [exact K2| apply NEe; unfold UNIT, IB in *; lia].
  - unfold qv. rewrite Ebg, Ec. cbn [fst snd pp aadd]. apply known_B; [exact K1| apply NEe; unfold UNIT, IB in *; lia].
  - unfold qv. rewrite Ebg, Ec. cbn [fst snd pp aadd]. exact Q.
  - intros x v t Hcl Hx. rewrite Ec in Hx. cbn [pp aadd snd] in Hx.
    change (s_tick stBB) with (N.succ (s_tick st)).
    assert (Hcl' : r_cells (get_shadow st (fst bg)) !! x = Some (v, t)).
    { unfold stBB, stB in Hcl.
      change (wr8 (e' rid needed) 0 (stT st_t g rid nb needed)) with (wrs [(e' rid needed, 0)] (stT st_t g rid nb needed)) in Hcl.
      rewrite wrs_cells_other in Hcl. 2:{ cbn [map fst In]. intros [E|[]]. unfold e' in E. rewrite Ebg in E. inversion E. unfold UNIT, IB in *. lia. }
      rewrite Ebg in Hcl |- *. cbn [fst] in Hcl |- *. rewrite (get_shadow_stT_rid st_t g rid nb needed) in Hcl. cbn [r_cells] in Hcl.
      apply trim_cells_lookup_Some in Hcl as [Hcl _]. exact Hcl. }
    destruct (get_shadow_cells_some st (fst bg) x (v, t) Hcl') as (sh & Hs & Hc'').
    destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C x v t Hc'') as [_ Hle]. lia.
Qed.
End REMAP.

Lemma INVL_groups_perm X st L BL LS gl :
  INVL X st L BL LS -> Permutation gl (ld_groups L) -> INVL X st (KInv.set_groups gl L) BL LS.
Proof.
  intros (IR & IA & IM & IL & IG & IS & ISH) HP.
  split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
  destruct IR; constructor; cbn; try assumption.
  eapply Permutation_trans; [exact HP| exact ir_groups].
Qed.

End CEIL.
