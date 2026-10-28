(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocRep_u5 MallocKit_AB_u5 MallocKit_A_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_A3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
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
End CEIL_WRAP_1.


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
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


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
End CEIL_WRAP_2.

