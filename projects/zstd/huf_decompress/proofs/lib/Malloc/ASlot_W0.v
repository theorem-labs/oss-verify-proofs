(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (16 recorded proofs replaced by written proofs (ctx_ta_same_refl, geom_same_refl, ta_rel_refl and 13 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocKit_AB MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W0 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W0@ctx_ta_same_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W09geom_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01k59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C35stdpp6option;from_optionK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexivei59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W0;ctx_ta_sameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib7Classes?RelationClasses>iff_TransitiveK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc>set_active_mapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Malloc9MallocRepAactive_set_activeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB;aptr_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W0>geom_same_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB@get_meta_rec_putC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W0?ta_rel_put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A3;bounces_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes9andb_propC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib6Malloc8ASlot_W0Ata_rel_set_bounceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W0;ta_rel_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc9get_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W09tr_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ctx_ta_same (c c1 : mctx) : Prop :=
  c_secret c1 = c_secret c /\ c_init_done c1 = c_init_done c /\ c_mmap_counter c1 = c_mmap_counter c
  /\ c_free_meta_head c1 = c_free_meta_head c /\ c_avail_meta c1 = c_avail_meta c /\ c_avail_meta_count c1 = c_avail_meta_count c
  /\ c_avail_meta_area_count c1 = c_avail_meta_area_count c /\ c_meta_alloc_shift c1 = c_meta_alloc_shift c
  /\ c_meta_area_head c1 = c_meta_area_head c /\ c_meta_area_tail c1 = c_meta_area_tail c /\ c_avail_meta_areas c1 = c_avail_meta_areas c
  /\ c_usage c1 = c_usage c /\ c_unmap_seq c1 = c_unmap_seq c /\ c_seq c1 = c_seq c /\ c_brk c1 = c_brk c.

(* [comment removed for export] *)
Definition geom_same (r r1 : meta) : Prop :=
  m_mem r1 = m_mem r /\ m_last_idx r1 = m_last_idx r /\ m_freeable r1 = m_freeable r /\ m_sizeclass r1 = m_sizeclass r /\ m_maplen r1 = m_maplen r.

Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
  tr_regions : s_regions st1 = s_regions st;
  tr_shadow : s_shadow st1 = s_shadow st;
  tr_next : s_next_rid st1 = s_next_rid st;
  tr_areas : s_areas st1 = s_areas st;
  tr_slots : s_slots st1 = s_slots st;
  tr_tick : s_tick st1 = s_tick st;
  tr_secret : s_secret st1 = s_secret st;
  tr_reserved : s_reserved st1 = s_reserved st;
  tr_ctx : ctx_ta_same (ctx st) (ctx st1);
  tr_active : forall c, c <> sc -> active st1 c = active st c;
  tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
  tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
  (* [comment removed for export] *)
  tr_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
  tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
      0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
  (* [comment removed for export] *)
  tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
  tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
      exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
                 /\ (g_active_idx gh1 = g_active_idx gh
                     \/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.

Lemma ctx_ta_same_refl c : ctx_ta_same c c.
Proof. repeat split; reflexivity. Qed.
Lemma geom_same_refl r : geom_same r r.
Proof. repeat split; reflexivity. Qed.

End CANSEC1.
Ltac ta_auto :=
  first [ reflexivity
        | apply ctx_ta_same_refl
        | (cbn; repeat split; reflexivity)
        | (intros; apply geom_same_refl)
        | (intros ? ? ? Hb__; exact Hb__)
        | (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
        | (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
        | (intros; unfold bounces, ctx in *; cbn in *; lia)
        | idtac ].

Section CANSEC2. Context {rc : runConstT}.
Lemma ta_rel_refl sc st : ta_rel sc st st.
Proof. constructor; ta_auto. Qed.

Lemma ta_rel_trans sc st st1 st2 : ta_rel sc st st1 -> ta_rel sc st1 st2 -> ta_rel sc st st2.
Proof.
  intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
  destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
  constructor; try congruence.
  - unfold ctx_ta_same in *. destruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). destruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat split; congruence.
  - intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
  - intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
  - intros q. destruct (G1 q) as (?&?&?&?&?). destruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
  - intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
  - intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
  - intros b. rewrite GR2. apply GR1.
  - intros b gh2 H2. destruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). destruct (GM1 b gh1 H1) as (gh & H & M & AI).
    exists gh. split; [exact H|]. split; [congruence|].
    destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
    split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. destruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.

(* [comment removed for export] *)
Lemma ta_rel_set_active sc st v : ta_rel sc st (set_active sc v st).
Proof.
  constructor; ta_auto.
  intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.

Lemma ta_rel_put_meta sc st g r :
  geom_same (get_meta_rec st g) r ->
  (forall i, 0 <= i -> Z.testbit (m_avail r) i || Z.testbit (m_freed r) i = true ->
             Z.testbit (m_avail (get_meta_rec st g)) i || Z.testbit (m_freed (get_meta_rec st g)) i = true) ->
  (0 <= m_avail (get_meta_rec st g) < 2^32 -> 0 <= m_freed (get_meta_rec st g) < 2^32 -> 0 <= m_avail r < 2^32 /\ 0 <= m_freed r < 2^32) ->
  ta_rel sc st (put_meta g r st).
Proof.
  intros GS BS RS. constructor; ta_auto.
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
  - intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.

(* [comment removed for export] *)
Lemma ta_rel_put_links sc st g p n :
  ta_rel sc st (put_meta g (m_set_prev p (m_set_next n (get_meta_rec st g))) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_next sc st g n :
  ta_rel sc st (put_meta g (m_set_next n (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_prev sc st g p :
  ta_rel sc st (put_meta g (m_set_prev p (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.

Lemma ta_rel_set_bounce sc st i v : 0 <= v <= bounces st i -> ta_rel sc st (set_bounce i v st).
Proof.
  intros Hv. constructor; ta_auto.
  intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

Lemma ta_rel_decay sc st c : 0 <= bounces st (c - 7) -> ta_rel sc st (decay_bounces c st).
Proof.
  intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
  apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
  apply ta_rel_set_bounce. lia.
Qed.

Lemma ta_rel_set_gai sc st b ai : 0 <= Z.land ai 31 <= 31 ->
  (forall h g, (s_groups st) !! b = Some h -> g_meta h = Some g -> m_sizeclass (get_meta_rec st g) <> 0) ->
  ta_rel sc st (set_group_active_idx b ai st).
Proof.
  intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
  unfold get_group in Hb.
  constructor; ta_auto.
  - intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq. split; intros _; eauto.
    + rewrite lookup_insert_ne by congruence. split; intros X; exact X.
  - intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
    + rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.

Lemma tr_get_shadow sc st st1 rid : ta_rel sc st st1 -> get_shadow st1 rid = get_shadow st rid.
Proof. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
Lemma tr_conc sc st st1 q : ta_rel sc st st1 -> conc st1 q = conc st q.
Proof. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
Lemma rec_set_gai b ai st q : get_meta_rec (set_group_active_idx b ai st) q = get_meta_rec st q.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
Lemma active_set_gai b ai st i : active (set_group_active_idx b ai st) i = active st i.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.


End CANSEC2.
