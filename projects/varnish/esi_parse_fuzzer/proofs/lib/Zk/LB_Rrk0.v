(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Cnt LB_T80p LB_Inv LB_Sum LB_Ljn7 LB_Bound LB_WNtf LB_QM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_WFree LB_Ctrl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_QM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG.LB_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ctrl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bl_resz (c : cptr) (n' : Z) (BL : list blk) : list blk :=
  map (fun k => if aptr_eqb (bslot k) c then ((bslot k, boff k), n') else k) BL.

Lemma bl_resz_slots c n' BL : map bslot (bl_resz c n' BL) = map bslot BL.
Proof. unfold bl_resz. rewrite map_map. apply map_ext. intros [[s o] z]. cbn. destruct (aptr_eqb s c); reflexivity. Qed.

Lemma zlen_bl_resz c n' BL : zlen (bl_resz c n' BL) = zlen BL.
Proof. unfold bl_resz. apply zlen_map. Qed.

Lemma In_bl_resz c n' BL k' : In k' (bl_resz c n' BL) ->
  exists k, In k BL /\ bslot k' = bslot k /\ ((bslot k = c /\ bsize k' = n') \/ (bslot k <> c /\ k' = k)).
Proof.
  unfold bl_resz. intros H. apply in_map_iff in H as (k & E & Hk). exists k. split; [exact Hk|].
  destruct (aptr_eqb_spec (bslot k) c) as [Ec|NE]; subst k'; cbn [bslot bsize fst snd]; split; auto.
Qed.

(* [comment removed for export] *)
Lemma n63_bl_resz c n' BL :
  (forall k, In k BL -> bslot k = c -> isbig k = (MMAP_THRESHOLD <=? n')) -> n63 (bl_resz c n' BL) = n63 BL.
Proof.
  intros H. unfold n63, bl_resz. rewrite zcount_map. apply zcount_ext. intros k Hk.
  destruct (aptr_eqb_spec (bslot k) c) as [Ec|NE]; [| reflexivity].
  rewrite (H k Hk Ec). unfold isbig. cbn [bsize snd]. reflexivity.
Qed.


(* [comment removed for export] *)
Definition rsz (c : cptr) (n' : Z) (q : cptr * Z) : cptr * Z := if aptr_eqb (fst q) c then (fst q, n') else q.
Lemma bs_bl_resz c n' BL : map bs (bl_resz c n' BL) = map (rsz c n') (map bs BL).
Proof.
  unfold bl_resz. rewrite !map_map. apply map_ext. intros k. unfold rsz, bs. cbn [fst snd].
  destruct (aptr_eqb (bslot k) c); reflexivity.
Qed.
Lemma bl_resz_perm c n' BL BL' : Permutation (map bs BL) (map bs BL') -> Permutation (map bs (bl_resz c n' BL)) (map bs (bl_resz c n' BL')).
Proof. intros H. rewrite !bs_bl_resz. apply Permutation_map. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SINV_resize X st BL c n' m i :
  SINV X st BL -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> n' < MMAP_THRESHOLD ->
  SINV X st (bl_resz c n' BL).
Proof.
  intros S Hs SC Hn. destruct S as [qb_cls qb_cnt qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; auto.
  - intros k' Hk'. destruct (In_bl_resz c n' BL k' Hk') as (k & Hk & Es & [[Ec En]|[NE ->]]); [| exact (qb_cls k Hk)].
    destruct (qb_cls k Hk) as (m0 & i0 & H0 & _). rewrite Ec, Hs in H0. injection H0 as <- <-.
    exists m, i. rewrite Es, Ec. split; [exact Hs|]. rewrite En. split; [intros _; exact Hn| intros E63; exfalso; lia].
  - rewrite zlen_bl_resz. exact qb_cnt.
  - intros b m0 ai Hg H63. rewrite bl_resz_slots. exact (qg_63 b m0 ai Hg H63).
Qed.

Lemma AQ_resize X st BL c n' m i :
  SINV X st BL -> AQ st BL PN -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> n' < MMAP_THRESHOLD ->
  AQ st (bl_resz c n' BL) PN.
Proof.
  intros S A Hs SC Hn. apply (AQ_PN_resize st BL).
  - rewrite zlen_bl_resz, <- NBCAP_NLIVE. exact (qb_cnt _ _ _ S).
  - apply n63_bl_resz. intros k Hk Ec. destruct (qb_cls _ _ _ S k Hk) as (m0 & i0 & H0 & C48 & _).
    rewrite Ec, Hs in H0. injection H0 as <- <-. specialize (C48 SC). unfold isbig.
    rewrite (proj2 (Z.leb_gt _ _) C48), (proj2 (Z.leb_gt _ _) Hn). reflexivity.
  - exact A.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msm_class v r : m_sizeclass (m_set_maplen v r) = m_sizeclass r. Proof. destruct r; reflexivity. Qed.
Lemma msm_last v r : m_last_idx (m_set_maplen v r) = m_last_idx r. Proof. destruct r; reflexivity. Qed.
Lemma msm_mem v r : m_mem (m_set_maplen v r) = m_mem r. Proof. destruct r; reflexivity. Qed.
Lemma msm_maplen v r : 0 <= v < 2 ^ 52 -> m_maplen (m_set_maplen v r) = v.
Proof. intros Hv. destruct r; cbn. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (rid : N) (r r' : region) (g : aptr) (c : cptr) (ML' n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hs : s_slots st !! c = Some (g, 0).
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Hypothesis Hr : s_regions st !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Kr' : r_kind r' = RKGroup.
Hypothesis ML1 : 1 <= ML' < 2 ^ 52.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis FIT : ML' * 4096 <= bigmap n.

Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Definition stR : mstate := upd_meta g (m_set_maplen ML') (set_regions (<[rid := r']> (s_regions st)) st).

Lemma R_groups : s_groups stR = s_groups st. Proof. reflexivity. Qed.
Lemma R_slots : s_slots stR = s_slots st. Proof. reflexivity. Qed.
Lemma R_ctx : s_ctx stR = s_ctx st. Proof. reflexivity. Qed.
Lemma R_regions : s_regions stR = <[rid := r']> (s_regions st). Proof. reflexivity. Qed.

Lemma g_hosted : exists b, hosts st b g.
Proof. exact (proj1 (is_valid _ _ _ IS _ _ _ Hs)). Qed.

Lemma g_present_R : s_metas st !! g <> None.
Proof. destruct g_hosted as (b & ai & Hb). exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)). Qed.

Lemma R_MR_g : MR stR g = m_set_maplen ML' (MR st g).
Proof. unfold stR, MR. rewrite get_meta_rec_upd_same. reflexivity. Qed.
Lemma R_MR_other x : x <> g -> MR stR x = MR st x.
Proof. intros NE. unfold stR, MR. rewrite get_meta_rec_upd_other by congruence. reflexivity. Qed.

Lemma R_class x : m_sizeclass (MR stR x) = m_sizeclass (MR st x).
Proof. destruct (aptr_eq_dec x g) as [->|NE]; [rewrite R_MR_g; apply msm_class| rewrite (R_MR_other x NE); reflexivity]. Qed.
Lemma R_cnt x : cnt_of (MR stR x) = cnt_of (MR st x).
Proof. destruct (aptr_eq_dec x g) as [->|NE]; [rewrite R_MR_g; unfold cnt_of; rewrite msm_last; reflexivity| rewrite (R_MR_other x NE); reflexivity]. Qed.
Lemma R_mem x : m_mem (MR stR x) = m_mem (MR st x).
Proof. destruct (aptr_eq_dec x g) as [->|NE]; [rewrite R_MR_g; apply msm_mem| rewrite (R_MR_other x NE); reflexivity]. Qed.
Lemma R_maplen_g : m_maplen (MR stR g) = ML'.
Proof. rewrite R_MR_g. apply msm_maplen. lia. Qed.

(* [comment removed for export] *)
Lemma cmax63 : cmax 63 <> 1. Proof. vm_compute. discriminate. Qed.
Lemma g_facts63 : m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0.
Proof.
  destruct g_hosted as (b & ai & Hb). pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(E & L0 & ML & NIL)]; [rewrite SC63 in SC; lia| auto].
Qed.
Lemma stdg_g_false s : MR s g = MR st g \/ MR s g = m_set_maplen ML' (MR st g) -> stdg s g = false.
Proof.
  intros E. destruct g_facts63 as [L0 _]. unfold stdg, cls, cnt_of.
  assert (EC : m_sizeclass (MR s g) = 63 /\ m_last_idx (MR s g) = 0).
  { destruct E as [-> | ->]; [auto|]. rewrite msm_class, msm_last. auto. }
  destruct EC as [-> ->]. apply andb_false_iff. left. apply Z.eqb_neq. pose proof cmax63. lia.
Qed.
Lemma R_stdg x : stdg stR x = stdg st x.
Proof.
  destruct (aptr_eq_dec x g) as [->|NE].
  - rewrite (stdg_g_false stR (or_intror R_MR_g)), (stdg_g_false st (or_introl eq_refl)). reflexivity.
  - unfold stdg, cls. rewrite (R_MR_other x NE). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma R_slot0 x : slot_start' (MR stR x) 0 = slot_start' (MR st x) 0.
Proof. unfold slot_start'. rewrite R_mem, !Z.mul_0_r. reflexivity. Qed.

Lemma R_ncarved : ncarved stR = ncarved st.
Proof. unfold stR. rewrite (ncarved_upd_meta_old _ g _); [reflexivity|]. exact g_present_R. Qed.

Lemma R_apages : apages stR = apages st.
Proof.
  rewrite !apages_msum. rewrite R_regions, (msum_insert_old _ _ rid r' r Hr).
  assert (E1 : apF stR (rid, r') = 0) by (unfold apF, is_metakind_b; cbn [snd]; rewrite Kr'; reflexivity).
  assert (E2 : apF stR (rid, r) = 0) by (unfold apF, is_metakind_b; cbn [snd]; rewrite Kr; reflexivity).
  rewrite E1, E2. rewrite Z.add_0_l, Z.sub_0_r. apply msum_ext. intros k v _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma R_region_meta q rq : s_regions stR !! q = Some rq -> r_kind rq <> RKGroup -> s_regions st !! q = Some rq.
Proof.
  rewrite R_regions. intros H K. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_insert_eq in H. injection H as <-. congruence.
  - rewrite lookup_insert_ne in H by congruence. exact H.
Qed.

Theorem SINV_remap : SINV X st BL -> SINV X stR (bl_resz c n BL).
Proof.
  intros S. destruct S as [qb_cls qb_cnt qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor.
  - (* [comment removed for export] *)
    intros k' Hk'. destruct (In_bl_resz c n BL k' Hk') as (k & Hk & Es & [[Ec En]|[NE ->]]).
    + exists g, 0. rewrite Es, Ec, R_slots. split; [exact Hs|]. rewrite R_class, SC63. split; [intros; exfalso; lia|].
      intros _. rewrite En, R_maplen_g. auto.
    + destruct (qb_cls k Hk) as (m0 & i0 & H0 & C48 & C63). exists m0, i0. rewrite R_slots, R_class. split; [exact H0|].
      split; [exact C48|]. intros E63. destruct (C63 E63) as [BIG ML]. split; [exact BIG|].
      destruct (aptr_eq_dec m0 g) as [->|NEm]; [| rewrite (R_MR_other m0 NEm); exact ML].
      (* [comment removed for export] *)
      exfalso. destruct g_facts63 as [L0 _].
      destruct (is_valid _ _ _ IS _ _ _ H0) as (_ & Hi0 & E0). destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Ec0).
      assert (i0 = 0) by lia. subst i0. apply NE. rewrite E0, Ec0. reflexivity.
  - rewrite zlen_bl_resz. exact qb_cnt.
  - intros b m ai Hb. rewrite R_groups in Hb. rewrite R_class, R_cnt. intros C48 ML.
    assert (NEg : m <> g) by (intros ->; rewrite SC63 in C48; lia).
    rewrite (R_MR_other m NEg) in ML |- *. exact (qg_map b m ai Hb C48 ML).
  - intros b m ai Hb. rewrite R_groups in Hb. rewrite R_stdg, R_class, R_slots. intros SD.
    assert (NEg : m <> g) by (intros ->; rewrite (stdg_g_false st (or_introl eq_refl)) in SD; discriminate).
    rewrite (R_MR_other m NEg). destruct (qg_std b m ai Hb SD) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p & i & Hp & Ep). exists p, i. rewrite R_class. auto.
  - intros c0 Hc0. replace (nsc stR c0) with (nsc st c0); [exact (qg_small c0 Hc0)|].
    unfold nsc, gmetas, groups_l. rewrite R_groups. apply zsum_map_ext. intros mb _. unfold cls. rewrite R_class, R_stdg, R_cnt. reflexivity.
  - intros b m ai Hb. rewrite R_groups in Hb. rewrite R_class, R_slot0, bl_resz_slots. exact (qg_63 b m ai Hb).
  - intros b m ai p i Hb. rewrite R_groups in Hb. rewrite R_slots, R_class. intros Z0 Hp.
    assert (NEg : m <> g) by (intros ->; rewrite R_maplen_g in Z0; lia).
    rewrite (R_MR_other m NEg) in Z0. exact (qg_host b m ai p i Hb Z0 Hp).
  - intros m mr Hm Hmem. unfold stR in Hm. rewrite lookup_metas_upd in Hm.
    destruct (aptr_eqb_spec m g) as [->|NEm].
    + exfalso. injection Hm as <-. destruct g_hosted as (b & ai & Hb).
      pose proof (im_hdr _ _ _ IM b _ Hb) as (m' & Em & Hmem' & _). cbn in Em. injection Em as <-.
      rewrite msm_mem in Hmem. unfold MR in Hmem'. rewrite Hmem in Hmem'. discriminate.
    + exact (qm_leak m mr Hm Hmem).
  - rewrite R_apages, R_ncarved, R_ctx. exact qm_pages.
  - intros q rq Hq K. rewrite R_ncarved. apply (qm_brk q rq); [apply R_region_meta; [exact Hq| congruence]| exact K].
  - intros q rq Hq K. rewrite R_ctx. apply (qm_len q rq); [apply R_region_meta; [exact Hq| congruence]| exact K].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply (qm_dist q1 q2 r1 r2); [apply R_region_meta; [exact H1| congruence]| apply R_region_meta; [exact H2| congruence]| exact K1| exact K2].
  - rewrite R_ctx, R_ncarved. exact qm_shift.
Qed.

Lemma R_gcnt c0 : gcnt stR c0 = gcnt st c0.
Proof.
  rewrite !gcnt_gmetas. unfold gmetas, groups_l. rewrite R_groups. apply zsum_map_ext. intros mb _. rewrite R_class, R_cnt. reflexivity.
Qed.

Theorem AQ_remap : SINV X st BL -> AQ st BL PN -> AQ stR (bl_resz c n BL) PN.
Proof.
  intros S A.
  assert (A' : AQ stR BL PN).
  { destruct A as [A1 A2 A3 A4 A5 A6]. constructor; auto.
    - intros c0 Hc0. rewrite R_gcnt. exact (A2 c0 Hc0).
    - rewrite R_ncarved. exact A4. }
  apply (AQ_PN_resize stR BL); [| | exact A'].
  - rewrite zlen_bl_resz, <- NBCAP_NLIVE. exact (qb_cnt _ _ _ S).
  - apply n63_bl_resz. intros k Hk Ec. destruct (qb_cls _ _ _ S k Hk) as (m0 & i0 & H0 & _ & C63).
    rewrite Ec, Hs in H0. injection H0 as <- <-. destruct (C63 SC63) as [BIG _]. unfold isbig.
    rewrite (proj2 (Z.leb_le _ _) BIG), (proj2 (Z.leb_le _ _) Hn). reflexivity.
Qed.

End REMAP.

End LBCEIL.
