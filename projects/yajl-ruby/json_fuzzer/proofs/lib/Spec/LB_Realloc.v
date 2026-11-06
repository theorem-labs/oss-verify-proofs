(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Realloc ReallocProto ReallocKeep KInv KLink KStep KStepX
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Read
  MI_WFree MI_WFree2 MI_WNtf2 MI_WGroup MI_TF2 MI_WEnframe MI_WEnframe2 MI_WSlot MI_WMalloc MI_Ledger MI_Cnt MI_Sim MI_Contracts
  MI_WRealloc MI_WRemap MI_WRealloc2
  LB_Kernel LB_Embed LB_Tables LB_Inv LB_Sum LB_QM LB_WNtf LB_Bound LB_Tree LB_StmtA LB_WFree LB_WMalloc LB_Raw LB_TreeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_bslot_remove_cons (c : cptr) (off n : Z) BL x :
  In c (map bslot BL) -> In x (map bslot BL) -> In x (map bslot (((c, off), n) :: bl_remove c BL)).
Proof.
  intros Hc Hx. cbn [map bslot fst]. destruct (aptr_eqb_spec x c) as [->|NE]; [left; reflexivity| right].
  rewrite bl_remove_map'. apply in_ap_remove; assumption.
Qed.

(* [comment removed for export] *)
Lemma SINV_reblock X st BL c (off off' n0 n : Z) :
  SINV X st BL -> In ((c, off), n0) BL ->
  (exists m i, s_slots st !! c = Some (m, i)
      /\ (m_sizeclass (MR st m) < 48 -> n < MMAP_THRESHOLD)
      /\ (m_sizeclass (MR st m) = 63 -> MMAP_THRESHOLD <= n /\
            round_up_pg (n + IB + UNIT) <= m_maplen (MR st m) * 4096 <= round_up_pg (n + IB + UNIT) + PGSZ)) ->
  SINV X st (((c, off'), n) :: bl_remove c BL).
Proof.
  intros SI Hk NEW. destruct SI. constructor; auto.
  - intros k [<-|Hin]; [exact NEW|]. apply qb_cls. eapply In_bl_remove. exact Hin.
  - intros b m ai Hg C63. apply In_bslot_remove_cons; [| exact (qg_63 _ _ _ Hg C63)].
    change c with (bslot ((c, off), n0)). apply in_map. exact Hk.
Qed.

Lemma AQ_reblock st BL P c (off' n : Z) :
  AQ st BL P -> 0 <= n -> ROOM (bl_remove c BL) P n -> AQ st (((c, off'), n) :: bl_remove c BL) P.
Proof. intros A Hn HR. apply AQ_add_block; [apply AQ_sub; exact A| exact Hn| exact HR]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma SG_remap63 st st1 BL g :
  s_groups st1 = s_groups st -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> m <> g -> geom (MR st1 m) = geom (MR st m)) ->
  (forall s m i, s_slots st !! s = Some (m, i) -> exists b, hosts st b m) ->
  (exists b, hosts st b g) ->
  m_sizeclass (MR st g) = 63 -> m_sizeclass (MR st1 g) = 63 ->
  m_last_idx (MR st1 g) = 0 -> 1 <= m_maplen (MR st1 g) -> m_mem (MR st1 g) = m_mem (MR st g) ->
  (forall k i, In k BL -> s_slots st !! bslot k = Some (g, i) ->
      round_up_pg (bsize k + IB + UNIT) <= m_maplen (MR st1 g) * 4096 <= round_up_pg (bsize k + IB + UNIT) + PGSZ) ->
  SG st BL -> SG st1 BL.
Proof.
  intros EG ES GEO SV Hg C63 C63' LI1 ML1 MM WIN S.
  assert (GM : forall m, (exists b, hosts st b m) -> m <> g ->
     m_sizeclass (MR st1 m) = m_sizeclass (MR st m) /\ m_maplen (MR st1 m) = m_maplen (MR st m)
     /\ get_stride (MR st1 m) = get_stride (MR st m) /\ cnt_of (MR st1 m) = cnt_of (MR st m)
     /\ (forall i, slot_start' (MR st1 m) i = slot_start' (MR st m) i) /\ stdg st1 m = stdg st m).
  { intros m Hm NE. pose proof (GEO m Hm NE) as G. pose proof (geom_stride _ _ G) as STR. unfold geom in G. inversion G.
    unfold cnt_of, slot_start', stdg, cls, cnt_of. rewrite STR, H0, H1, H2, H3. repeat split; reflexivity. }
  assert (HG : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> exists b', hosts st b' m) by (intros b m ai H; exists b, ai; exact H).
  (* [comment removed for export] *)
  assert (STD1 : stdg st1 g = false).
  { unfold stdg, cls. rewrite C63'. apply andb_false_iff. right. apply Z.eqb_neq.
    unfold get_stride. rewrite LI1. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st1 g)) 0); [lia|]. cbn [negb].
    unfold S_. change (size_class 63) with 0. unfold UNIT. lia. }
  assert (SS0 : slot_start' (MR st1 g) 0 = slot_start' (MR st g) 0).
  { unfold slot_start'. rewrite MM, !Z.mul_0_r. reflexivity. }
  destruct S as [S1 S3 S4 S5 S6 S7]. constructor.
  - intros k Hk. destruct (S1 k Hk) as (m & i & Hs & C1 & C2). exists m, i. rewrite ES. split; [exact Hs|].
    destruct (aptr_eq_dec m g) as [->|NE].
    + rewrite C63'. split; [intros; lia|]. intros _. split; [exact (proj1 (C2 C63))|]. exact (WIN k i Hk Hs).
    + destruct (GM m (SV _ _ _ Hs) NE) as (E1 & E2 & _). rewrite E1, E2. auto.
  - intros b m ai Hb. rewrite EG in Hb. destruct (aptr_eq_dec m g) as [->|NE]; [rewrite C63'; intros; lia|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & E2 & E3 & E4 & _). rewrite E1, E2, E4. exact (S3 _ _ _ Hb).
  - intros b m ai Hb. rewrite EG in Hb. destruct (aptr_eq_dec m g) as [->|NE]; [rewrite STD1; intros; discriminate|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & E2 & E3 & E4 & E5 & E6). rewrite E6, E1, E2, ES.
    intros SD. destruct (S4 _ _ _ Hb SD) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p & i & Hs & Ep). exists p, i. split; [exact Hs|].
    destruct (aptr_eq_dec p g) as [->|NEp]; [rewrite C63'; rewrite C63 in Ep; exact Ep|].
    destruct (GM p (SV _ _ _ Hs) NEp) as (Ep1 & _). rewrite Ep1. exact Ep.
  - intros c Hc. replace (nsc st1 c) with (nsc st c); [exact (S5 c Hc)|].
    unfold nsc, gmetas, groups_l. rewrite EG. apply zsum_map_ext. intros mb Hin.
    apply in_flat_map in Hin as ([b h] & Hbh & Hmb). apply mtl_in in Hbh. destruct h as [[m'|] ai]; cbn in Hmb; [| destruct Hmb].
    destruct Hmb as [Hmb|[]]. subst mb. cbn. unfold cls.
    destruct (aptr_eq_dec m' g) as [->|NE]; [rewrite C63, C63'; replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
    destruct (GM m' (HG _ _ _ Hbh) NE) as (E1 & _ & _ & E4 & _ & E6). rewrite E1, E4, E6. reflexivity.
  - intros b m ai Hb. rewrite EG in Hb. destruct (aptr_eq_dec m g) as [->|NE]; [intros _; rewrite SS0; exact (S6 _ _ _ Hb C63)|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & _ & _ & _ & E5 & _). rewrite E1, (E5 0). exact (S6 _ _ _ Hb).
  - intros b m ai p i Hb. rewrite EG in Hb. rewrite ES. intros Z0 Hs.
    destruct (aptr_eq_dec m g) as [->|NE]; [exfalso; lia|].
    destruct (GM m (HG _ _ _ Hb) NE) as (_ & E2 & _). rewrite E2 in Z0.
    destruct (aptr_eq_dec p g) as [->|NEp]; [exfalso; pose proof (S7 _ _ _ _ _ Hb Z0 Hs); lia|].
    destruct (GM p (SV _ _ _ Hs) NEp) as (Ep1 & _). rewrite Ep1. exact (S7 _ _ _ _ _ Hb Z0 Hs).
Qed.

(* [comment removed for export] *)
Lemma SG_remap63_reblock st st1 BL g c0 (off0 off' n0 n : Z) ig :
  s_groups st1 = s_groups st -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> m <> g -> geom (MR st1 m) = geom (MR st m)) ->
  (forall s m i, s_slots st !! s = Some (m, i) -> exists b, hosts st b m) ->
  (exists b, hosts st b g) ->
  m_sizeclass (MR st g) = 63 -> m_sizeclass (MR st1 g) = 63 ->
  m_last_idx (MR st1 g) = 0 -> 1 <= m_maplen (MR st1 g) -> m_mem (MR st1 g) = m_mem (MR st g) ->
  NoDup (map bslot BL) -> In ((c0, off0), n0) BL -> s_slots st !! c0 = Some (g, ig) ->
  (forall s i', s_slots st !! s = Some (g, i') -> s = c0) ->
  MMAP_THRESHOLD <= n ->
  round_up_pg (n + IB + UNIT) <= m_maplen (MR st1 g) * 4096 <= round_up_pg (n + IB + UNIT) + PGSZ ->
  SG st BL -> SG st1 (((c0, off'), n) :: bl_remove c0 BL).
Proof.
  intros EG ES GEO SV Hg C63 C63' LI1 ML1 MM ND Hk Hc0 ONE GE WIN S.
  assert (GM : forall m, (exists b, hosts st b m) -> m <> g ->
     m_sizeclass (MR st1 m) = m_sizeclass (MR st m) /\ m_maplen (MR st1 m) = m_maplen (MR st m)
     /\ get_stride (MR st1 m) = get_stride (MR st m) /\ cnt_of (MR st1 m) = cnt_of (MR st m)
     /\ (forall i, slot_start' (MR st1 m) i = slot_start' (MR st m) i) /\ stdg st1 m = stdg st m).
  { intros m Hm NE. pose proof (GEO m Hm NE) as G. pose proof (geom_stride _ _ G) as STR. unfold geom in G. inversion G.
    unfold cnt_of, slot_start', stdg, cls, cnt_of. rewrite STR, H0, H1, H2, H3. repeat split; reflexivity. }
  assert (HG : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> exists b', hosts st b' m) by (intros b m ai H; exists b, ai; exact H).
  assert (STD1 : stdg st1 g = false).
  { unfold stdg, cls. rewrite C63'. apply andb_false_iff. right. apply Z.eqb_neq.
    unfold get_stride. rewrite LI1. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st1 g)) 0); [lia|]. cbn [negb].
    unfold S_. change (size_class 63) with 0. unfold UNIT. lia. }
  assert (SS0 : slot_start' (MR st1 g) 0 = slot_start' (MR st g) 0).
  { unfold slot_start'. rewrite MM, !Z.mul_0_r. reflexivity. }
  assert (INc0 : In c0 (map bslot BL)) by (change c0 with (bslot ((c0, off0), n0)); apply in_map; exact Hk).
  destruct S as [S1 S3 S4 S5 S6 S7]. constructor.
  - intros k [<-|Hin].
    + exists g, ig. cbn [bslot bsize fst snd]. rewrite ES. split; [exact Hc0|]. rewrite C63'. split; [intros; lia|]. intros _. split; [exact GE| exact WIN].
    + pose proof (In_bl_remove _ _ _ Hin) as HinBL. pose proof (bl_remove_neq _ _ _ ND Hin) as NEc.
      destruct (S1 k HinBL) as (m & i & Hs & C1 & C2). exists m, i. rewrite ES. split; [exact Hs|].
      destruct (aptr_eq_dec m g) as [->|NE]; [exfalso; exact (NEc (ONE _ _ Hs))|].
      destruct (GM m (SV _ _ _ Hs) NE) as (E1 & E2 & _). rewrite E1, E2. auto.
  - intros b m ai Hb. rewrite EG in Hb. destruct (aptr_eq_dec m g) as [->|NE]; [rewrite C63'; intros; lia|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & E2 & E3 & E4 & _). rewrite E1, E2, E4. exact (S3 _ _ _ Hb).
  - intros b m ai Hb. rewrite EG in Hb. destruct (aptr_eq_dec m g) as [->|NE]; [rewrite STD1; intros; discriminate|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & E2 & E3 & E4 & E5 & E6). rewrite E6, E1, E2, ES.
    intros SD. destruct (S4 _ _ _ Hb SD) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p & i & Hs & Ep). exists p, i. split; [exact Hs|].
    destruct (aptr_eq_dec p g) as [->|NEp]; [rewrite C63'; rewrite C63 in Ep; exact Ep|].
    destruct (GM p (SV _ _ _ Hs) NEp) as (Ep1 & _). rewrite Ep1. exact Ep.
  - intros c Hc. replace (nsc st1 c) with (nsc st c); [exact (S5 c Hc)|].
    unfold nsc, gmetas, groups_l. rewrite EG. apply zsum_map_ext. intros mb Hin.
    apply in_flat_map in Hin as ([b h] & Hbh & Hmb). apply mtl_in in Hbh. destruct h as [[m'|] ai]; cbn in Hmb; [| destruct Hmb].
    destruct Hmb as [Hmb|[]]. subst mb. cbn. unfold cls.
    destruct (aptr_eq_dec m' g) as [->|NE]; [rewrite C63, C63'; replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
    destruct (GM m' (HG _ _ _ Hbh) NE) as (E1 & _ & _ & E4 & _ & E6). rewrite E1, E4, E6. reflexivity.
  - intros b m ai Hb. rewrite EG in Hb. intros C.
    apply (In_bslot_remove_cons c0 off' n BL); [exact INc0|].
    destruct (aptr_eq_dec m g) as [->|NE]; [rewrite SS0; exact (S6 _ _ _ Hb C63)|].
    destruct (GM m (HG _ _ _ Hb) NE) as (E1 & _ & _ & _ & E5 & _). rewrite E1 in C. rewrite (E5 0). exact (S6 _ _ _ Hb C).
  - intros b m ai p i Hb. rewrite EG in Hb. rewrite ES. intros Z0 Hs.
    destruct (aptr_eq_dec m g) as [->|NE]; [exfalso; lia|].
    destruct (GM m (HG _ _ _ Hb) NE) as (_ & E2 & _). rewrite E2 in Z0.
    destruct (aptr_eq_dec p g) as [->|NEp]; [exfalso; pose proof (S7 _ _ _ _ _ Hb Z0 Hs); lia|].
    destruct (GM p (SV _ _ _ Hs) NEp) as (Ep1 & _). rewrite Ep1. exact (S7 _ _ _ _ _ Hb Z0 Hs).
Qed.

(* [comment removed for export] *)
Lemma QM_regroup X st st1 d rid r r' g :
  s_ctx st1 = s_ctx st -> s_regions st !! rid = Some r -> r_kind r = RKGroup -> r_kind r' = RKGroup ->
  s_regions st1 = <[rid := r']> (s_regions st) ->
  (exists mg, s_metas st !! g = Some mg /\ exists mg', s_metas st1 = <[g := mg']> (s_metas st)
      /\ m_mem mg' = m_mem mg /\ m_next mg' = m_next mg) ->
  QM X st d -> QM X st1 d.
Proof.
  intros EC Hr K K' ER (mg & Hmg & mg' & EM & Emem & Enext) Q.
  assert (NC : ncarved st1 = ncarved st).
  { unfold ncarved. rewrite EM. unfold zlen. rewrite <- (insert_delete_eq (s_metas st) g mg').
    rewrite (Permutation_length (map_to_list_insert (delete g (s_metas st)) g mg' (lookup_delete_eq _ _))).
    rewrite (Permutation_length (mtl_delete (s_metas st) g mg Hmg)). reflexivity. }
  assert (AP : apages st1 = apages st).
  { rewrite !apages_msum, ER. rewrite (msum_insert_old (apF st1) (s_regions st) rid r' r Hr).
    assert (E0 : forall q, r_kind q = RKGroup -> forall stx k, apF stx (k, q) = 0) by (intros q Hq stx k; unfold apF, is_metakind_b; cbn; rewrite Hq; reflexivity).
    rewrite (E0 r' K'), (E0 r K). rewrite (msum_ext (apF st1) (apF st) (s_regions st)); [lia|].
    intros k v _. unfold apF, frontier. rewrite EC. reflexivity. }
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor.
  - intros m mr. rewrite EM. destruct (aptr_eq_dec m g) as [->|NE].
    + rewrite lookup_insert_eq. intros Hm Hmem. injection Hm as <-. rewrite Enext. apply (Q1 g mg Hmg). rewrite <- Emem. exact Hmem.
    + rewrite lookup_insert_ne by congruence. apply Q1.
  - rewrite AP, NC, EC. exact Q2.
  - intros rid' q. rewrite ER, NC. destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite lookup_insert_eq. intros Hq Kq. injection Hq as <-. rewrite K' in Kq. discriminate.
    + rewrite lookup_insert_ne by congruence. apply Q3.
  - intros rid' q. rewrite ER, EC. destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite lookup_insert_eq. intros Hq Kq. injection Hq as <-. rewrite K' in Kq. discriminate.
    + rewrite lookup_insert_ne by congruence. apply Q4.
  - intros rid1 rid2 r1 r2. rewrite ER.
    destruct (N.eq_dec rid1 rid) as [->|NE1]; [rewrite lookup_insert_eq; intros H1; injection H1 as <-; intros _ K1; rewrite K' in K1; discriminate|].
    rewrite lookup_insert_ne by congruence.
    destruct (N.eq_dec rid2 rid) as [->|NE2]; [rewrite lookup_insert_eq; intros _ H2; injection H2 as <-; intros _ K2; rewrite K' in K2; discriminate|].
    rewrite lookup_insert_ne by congruence. apply Q5.
  - rewrite EC, NC. exact Q6.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fqtree_conj_ftree {R} B (t : M R) : forall L P Q,
  ftree L t P -> fqtree B L t Q -> fqtree B L t (fun L' r => P L' r /\ Q L' r).
Proof.
  induction t as [r|e k IH]; intros L P Q HP HQ; cbn [ftree fqtree] in *; [split; assumption|].
  destruct e; try (destruct HP as [_ HkP]; destruct HQ as (He & HB & HkQ); split; [exact He|]; split; [exact HB|];
                   intros a; specialize (HkP a); specialize (HkQ a); case_ans; [apply IH; assumption| exact HkQ]).
  - intros v Hv. apply IH; [apply HP| apply HQ]; exact Hv.
  - exact HQ.
Qed.

Lemma fqtree_of_ftree_fbnd8 {R} B (t : M R) : forall L P, ftree L t P -> fbnd8 B L t -> fqtree B L t P.
Proof.
  induction t as [r|e k IH]; intros L P HP HB; cbn [ftree fqtree fbnd8] in *; [exact HP|].
  destruct e; try (destruct HP as [He Hk]; destruct HB as [HB1 HB2]; split; [exact He|]; split; [exact HB1|];
                   intros a; specialize (Hk a); case_ans; [apply IH; [exact Hk| apply HB2; assumption]| exact Hk]).
  - intros v Hv. apply IH; [apply HP; exact Hv| apply HB; exact Hv].
  - exact HP.
Qed.

Lemma xfqtree_conj_ftreeX {R} B (t : MX R) : forall L P Q,
  ftreeX L t P -> xfqtree B L t Q -> xfqtree B L t (fun L' r => P L' r /\ Q L' r).
Proof.
  induction t as [r|e k IH]; intros L P Q HP HQ; cbn [ftreeX xfqtree] in *; [split; assumption|].
  xev_cases e; try (destruct HP as [_ HkP]; destruct HQ as (He & HB & HkQ); split; [exact He|]; split; [exact HB|];
                     intros a; specialize (HkP a); specialize (HkQ a); xcase_ans; [apply IH; assumption| exact HkQ]).
  - intros v Hv. apply IH; [apply HP| apply HQ]; exact Hv.
  - exact HQ.
Qed.

Lemma xfqtree_xguard {R} B L tag (c : bool) (k bail : MX R) Post :
  c = true -> xfqtree B L k Post -> xfqtree B L (xguard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma xfqtree_vis {R} B L e (k : Z -> MX R) Post :
  xis_peek e = false -> xis_undef e = false ->
  xevent_pre L e -> XBOUND L e B ->
  (forall a, xanswer_ok L e a = true -> xfqtree B (xevent_post L e a) (k a) Post) ->
  (forall a, xanswer_ok L e a = false -> xrejects (k a)) ->
  xfqtree B L (SVis e k) Post.
Proof.
  intros Hp Hu He HB Hk Hr. xev_cases e; cbn in Hp, Hu; try discriminate; cbn [xfqtree]; split; auto; split; auto;
  intros a; xcase_ans; auto.
Qed.

(* [comment removed for export] *)
Lemma R63_remove BL (k : blk) : NoDup (map bslot BL) -> In k BL ->
  R63 BL = (if isbig k then round_up_pg (bsize k + IB + UNIT) + PGSZ else 0) + R63 (bl_remove (bslot k) BL).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn [map] in ND. apply list.NoDup_cons in ND as [N1 N2]. cbn [bl_remove].
  destruct Hin as [<-|Hin].
  - rewrite aptr_eqb_refl. unfold R63. cbn [map]. rewrite zsum_cons. reflexivity.
  - destruct (aptr_eqb_spec (bslot b) (bslot k)) as [E|NE].
    + exfalso. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin.
    + unfold R63 in *. cbn [map]. rewrite !zsum_cons. rewrite (IH N2 Hin). lia.
Qed.

Lemma ROOM_sub BL P n c : ROOM BL P n -> ROOM (bl_remove c BL) P n.
Proof.
  intros (R1 & R2 & R3). pose proof (LR_sub BL (size_to_class n) c). pose proof (n63_sub BL c).
  assert (zlen (bl_remove c BL) <= zlen BL).
  { unfold zlen. clear. induction BL as [|b BL IH]; cbn; [lia|]. destruct (aptr_eqb (bslot b) c); cbn; lia. }
  split; [| split]; [intros LT; specialize (R1 LT); lia| intros GE; specialize (R2 GE); lia| lia].
Qed.

Lemma bigb_le' n : 0 <= n -> 0 <= bigb n /\ (MMAP_THRESHOLD <= n -> bigb n = round_up_pg (n + IB + UNIT) + PGSZ).
Proof.
  intros Hn. unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); [| split; [lia| intros; lia]].
  pose proof (round_up_pg_spec (n + IB + UNIT)) as [[? ?] _]. unfold PGSZ, IB, UNIT in *. split; [lia| intros; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MPOSTQ (st : mstate) (L : mled) (BL : list blk) (P : Z -> Z) (n : Z) : mled -> mstate * optr -> Prop :=
  fun L' r =>
    ld_live L' = ld_live L /\ GP st (fst r) /\
    match snd r with
    | None => exists LS', INVL x0 (fst r) L' BL LS' /\ SINV x0 (fst r) BL /\ AQ (fst r) BL P
    | Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
        /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
        /\ SINV x0 (fst r) (((c, off), n) :: BL) /\ AQ (fst r) (((c, off), n) :: BL) P
    end.

Theorem malloc_fq st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
  fqtree B L (malloc st n) (MPOSTQ st L BL P n).
Proof.
  intros INV SI HAQ Hn HR HB. rewrite malloc_unfold.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply fqtree_bind.
  { apply fqtree_conj_ftree; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)|].
    exact (malloc_core_fq_proof st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB). }
  intros L1 [st1 r] [(LIVE & GP1 & RES) PQ]. cbn [fst snd] in RES, GP1, PQ |- *. unfold CORE_POSTQ in PQ. cbn [fst snd] in PQ.
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct r as [[g idx]|].
  - destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    apply fqtree_of_ftree_fbnd8; [| apply fbnd8_enframe_full; intros; apply fbnd8_ret].
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
    intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|].
    split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]]|].
    exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    split.
    + pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
      apply list.NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
    + destruct (PQ bg off Hg) as [S1 A1].
      split; [exact (SINV_ctrl x0 st1 st' _ CE S1)| exact (AQ_ctrl st1 st' _ P CE A1)].
  - destruct RES as (LS1 & INV1). cbn [fqtree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|].
    exists LS1. split; [exact INV1|]. exact PQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RPOSTQ (BL : list blk) (c : cptr) (n : Z) (P : Z -> Z) : mled -> mstate * optr -> Prop :=
  fun L' res =>
    match snd res with
    | None => exists LS', INVL x0 (fst res) L' BL LS' /\ SINV x0 (fst res) BL /\ AQ (fst res) BL P
    | Some p' => exists c' off' LS', p' = aadd c' (UNIT * off') /\ 0 <= off' <= 255
                 /\ INVL x0 (fst res) L' (((c', off'), n) :: bl_remove c BL) LS'
                 /\ SINV x0 (fst res) (((c', off'), n) :: bl_remove c BL) /\ AQ (fst res) (((c', off'), n) :: bl_remove c BL) P
    end.

Lemma RPOSTQ_RPOST BL c n P L' res : RPOSTQ BL c n P L' res -> RPOST BL c n L' res.
Proof.
  unfold RPOSTQ, RPOST. destruct (snd res); [| intros (LS' & I & _); exists LS'; exact I].
  intros (c' & off' & LS' & E & Ho & I & _). exists c', off', LS'. auto.
Qed.

Section REALLOC.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (c : cptr) (off n0 n : Z) (P : Z -> Z) (B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis Hn : 0 <= n.
Hypothesis OV : size_overflows n = false.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
(* [comment removed for export] *)
Hypothesis HROOM : ROOM BL P n.
Hypothesis HB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ.
Let st0 := set_tick (N.succ (s_tick st)) st.

Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st0 c off n0 m bm i ai a ar ka.
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (MR st0 m).
Let X1 := xpend x0 (Some c).
Let BL1 := bl_remove c BL.

Let INV0 : INVL x0 st0 L BL LS := m_INV0 st L BL LS INV.
Lemma r_SI0 : SINV x0 st0 BL. Proof. apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]. Qed.
Lemma r_AQ0 : AQ st0 BL P. Proof. apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]. Qed.
Lemma r_ND : NoDup (map bslot BL).
Proof. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0))))))). Qed.
Lemma r_slot : s_slots st0 !! c = Some (m, i). Proof. exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). Qed.

(* [comment removed for export] *)
Lemma realloc_move_fq :
  xfqtree B L (realloc_move st0 p n) (RPOSTQ BL c n P).
Proof.
  unfold realloc_move.
  eapply xfqtree_bind.
  { apply xfqtree_xlift. exact (malloc_fq st0 L BL LS P n B INV0 r_SI0 r_AQ0 Hn HROOM HB). }
  intros L1 [st1 r1] (LIVE1 & GP1 & RES). cbn [fst snd] in *.
  destruct r1 as [q|].
  - destruct RES as (c' & off' & LS1 & -> & Ho' & INV1 & NI & SI1 & AQ1).
    eapply xfqtree_bind.
    { apply xfqtree_xlift.
      apply (free_fq st1 L1 (((c', off'), n) :: BL) LS1 P c off n0 B INV1 SI1 AQ1); [right; exact Hk|].
      rewrite R63_cons. pose proof (proj1 (bigb_le' n Hn)). lia. }
    intros L2 st2 (LS2 & INV2 & SI2 & AQ2). cbn [xfqtree RPOSTQ fst snd].
    assert (E : bl_remove c (((c', off'), n) :: BL) = ((c', off'), n) :: bl_remove c BL).
    { apply bl_remove_cons_ne. cbn [bslot fst]. intros E. apply NI. rewrite E.
      change c with (bslot ((c, off), n0)). apply in_map. exact Hk. }
    rewrite E in INV2, SI2, AQ2. exists c', off', LS2. auto 10.
  - destruct RES as (LS1 & INV1 & SI1 & AQ1). cbn [xfqtree RPOSTQ fst snd]. exists LS1. auto.
Qed.

(* [comment removed for export] *)
Lemma round_up_pg_window x d : 0 <= d < PGSZ ->
  round_up_pg x <= round_up_pg (x + d) <= round_up_pg x + PGSZ.
Proof.
  intros Hd. pose proof (round_up_pg_spec x) as [[A1 A2] A3]. pose proof (round_up_pg_spec (x + d)) as [[B1 B2] B3].
  unfold PGSZ in *.
  pose proof (Z_div_mod_eq_full (round_up_pg x) 4096) as E1. rewrite A3 in E1.
  pose proof (Z_div_mod_eq_full (round_up_pg (x + d)) 4096) as E2. rewrite B3 in E2.
  split; nia.
Qed.

(* [comment removed for export] *)
Lemma inplace_SAQ : UNIT * off + n <= stride - IB -> n < MMAP_THRESHOLD ->
  m_sizeclass (MR st0 m) < 48 ->
  forall st', ctrl_eq st0 st' ->
  SINV x0 st' (((c, off), n) :: BL1) /\ AQ st' (((c, off), n) :: BL1) P.
Proof.
  intros FIT LT SC48 st' CE. split.
  - apply (SINV_ctrl x0 st0 st' _ CE). apply (SINV_reblock x0 st0 BL c off off n0 n r_SI0 Hk).
    exists m, i. split; [exact r_slot|]. split; [intros _; exact LT| intros; lia].
  - apply (AQ_ctrl st0 st' _ P CE). apply (AQ_reblock st0 BL P c off n r_AQ0 Hn). apply ROOM_sub. exact HROOM.
Qed.

(* [comment removed for export] *)
Lemma big_window : MMAP_THRESHOLD <= n ->
  let needed := round_up_pg (n + UNIT * off + UNIT + IB) in
  round_up_pg (n + IB + UNIT) <= needed <= round_up_pg (n + IB + UNIT) + PGSZ.
Proof.
  intros Hbig needed. subst needed. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  replace (n + UNIT * off + UNIT + IB) with ((n + IB + UNIT) + UNIT * off) by lia.
  apply round_up_pg_window. unfold UNIT, PGSZ. lia.
Qed.

Lemma bigsame_SAQ : m_sizeclass (MR st0 m) = 63 -> MMAP_THRESHOLD <= n ->
  m_maplen (MR st0 m) * 4096 = round_up_pg (n + UNIT * off + UNIT + IB) ->
  forall st', ctrl_eq st0 st' ->
  SINV x0 st' (((c, off), n) :: BL1) /\ AQ st' (((c, off), n) :: BL1) P.
Proof.
  intros SC63 GE EQN st' CE. split.
  - apply (SINV_ctrl x0 st0 st' _ CE). apply (SINV_reblock x0 st0 BL c off off n0 n r_SI0 Hk).
    exists m, i. split; [exact r_slot|]. split; [intros; lia|]. intros _. split; [exact GE|]. rewrite EQN. exact (big_window GE).
  - apply (AQ_ctrl st0 st' _ P CE). apply (AQ_reblock st0 BL P c off n r_AQ0 Hn). apply ROOM_sub. exact HROOM.
Qed.

(* [comment removed for export] *)
Section BIG.
Hypothesis SC63 : m_sizeclass (MR st0 m) = 63.
Let M63 := m63_facts st L BL LS c off n0 INV m bm i ai a ar ka BF SC63.
Let IR0 : inv_R x0 st0 L := proj1 INV0.
Let IM0 : inv_M x0 st0 LS := proj1 (proj2 (proj2 INV0)).
Let IG0 : inv_G x0 st0 LS := proj1 (proj2 (proj2 (proj2 (proj2 INV0)))).
Let IS0 : inv_S x0 st0 BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0))))).

Lemma r_n0_big : MMAP_THRESHOLD <= n0 /\ round_up_pg (n0 + IB + UNIT) <= m_maplen (MR st0 m) * 4096.
Proof.
  destruct (qb_cls _ _ _ r_SI0 _ Hk) as (m' & i' & Hs & _ & C63). cbn [bslot bsize fst snd] in Hs, C63.
  rewrite r_slot in Hs. injection Hs as <- <-. destruct (C63 SC63) as [A0 [B1 _]]. split; [exact A0| exact B1].
Qed.

(* [comment removed for export] *)
Lemma r_one : forall s i', s_slots st0 !! s = Some (m, i') -> s = c.
Proof.
  intros s i' Hs. destruct (is_valid _ _ _ IS0 _ _ _ Hs) as (_ & Hi' & ->).
  destruct M63 as (I0 & L0 & _). rewrite L0 in Hi'. assert (i' = 0) by lia. subst i'.
  rewrite <- (m_slot st L BL LS c off n0 INV m bm i ai a ar ka BF), I0. reflexivity.
Qed.

Lemma r_meta_some : s_metas st0 !! m = Some (MR st0 m).
Proof.
  destruct (hosts_ok x0 st0 LS IG0 _ _ (m_hosts st c off n0 m bm i ai a ar ka BF)) as (ai' & _ & GO).
  pose proof (g_present _ _ _ _ _ _ GO) as PR. unfold MR, get_meta_rec.
  destruct (s_metas st0 !! m) as [mr|] eqn:E; [reflexivity| exfalso; exact (PR eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma r_ledger : exists rg, s_regions st0 !! fst bm = Some rg /\ r_kind rg = RKGroup
  /\ m_maplen (MR st0 m) * 4096 = round_up_pg (r_len rg) /\ In (r_base rg, r_len rg) (ld_groups L)
  /\ gm L + BB L + 2 * PGSZ <= PHI P + R63 BL1 + round_up_pg (n0 + IB + UNIT).
Proof.
  destruct M63 as (I0 & L0 & B0 & ML & MLG & STR & (rg & Hrg & Hkrg & Hml) & EC & EP).
  exists rg. split; [exact Hrg|]. split; [exact Hkrg|]. split; [exact Hml|]. split.
  - assert (Hf : In (fst bm, rg) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st0)))).
    { apply filter_In. split; [apply In_map_to_list_regions; exact Hrg| cbn; rewrite Hkrg; reflexivity]. }
    pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hin. cbn [snd] in Hin.
    exact (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR0)) Hin).
  - pose proof (regions_bound x0 st0 L BL LS P INV0 r_SI0 r_AQ0 eq_refl) as RB. pose proof (ledger_bound x0 st0 L BL LS INV0) as LBd.
    unfold ORPH in RB. cbn [x_orph x0] in RB.
    pose proof (R63_remove BL ((c, off), n0) r_ND Hk) as R. cbn [bslot bsize fst snd] in R. fold BL1 in R.
    unfold isbig in R. cbn [bsize snd] in R. destruct r_n0_big as [GE0 _]. rewrite (proj2 (Z.leb_le _ _) GE0) in R.
    unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Lemma r_XBOUND needed rg :
  s_regions st0 !! fst bm = Some rg -> MMAP_THRESHOLD <= n ->
  needed = round_up_pg (n + UNIT * off + UNIT + IB) ->
  XBOUND L (XMremap (r_base rg) (m_maplen (MR st0 m) * 4096) needed MREMAP_MAYMOVE) B.
Proof.
  intros Hrg GE En z Hz. cbn [xevent_post].
  destruct r_ledger as (rg' & Hrg' & K & Hml & Hin & GB). rewrite Hrg in Hrg'. injection Hrg' as <-.
  pose proof (proj1 (bigb_le' n Hn)) as B0. pose proof (proj2 (bigb_le' n Hn) GE) as Bn.
  pose proof (big_window GE) as W. cbv zeta in W. rewrite <- En in W.
  destruct r_n0_big as [GE0 W0]. pose proof (round_up_pg_spec (n0 + IB + UNIT)) as [[RU0 _] _].
  pose proof (R63_remove BL ((c, off), n0) r_ND Hk) as R. cbn [bslot bsize fst snd] in R. fold BL1 in R.
  unfold isbig in R. cbn [bsize snd] in R. rewrite (proj2 (Z.leb_le _ _) GE0) in R.
  destruct (is_err z).
  - unfold PGSZ, IB, UNIT, MMAP_THRESHOLD in *. lia.
  - rewrite BB_set_groups.
    assert (ND : NoDup (map fst (ld_groups L))).
    { apply (groups_nodup x0 st0 L BL LS m m PGSZ INV0); [unfold PTRDIFF_MAX, PGSZ; lia| reflexivity]. }
    destruct (g_remove_split' (r_base rg) (r_len rg) (ld_groups L) Hin ND) as (l1 & l2 & EL & ER).
    assert (Egm : gm (KInv.set_groups ((z, needed) :: g_remove (r_base rg) (ld_groups L)) L) = gm L - mmap_len (r_len rg) + mmap_len needed).
    { unfold gm. cbn [ld_groups ld_metas KInv.set_groups]. rewrite ER.
      replace (fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L)))
         with (fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (l1 ++ (r_base rg, r_len rg) :: l2))) by (rewrite <- EL; reflexivity).
      cbn [map]. rewrite !map_app. cbn [map snd].
      assert (FA : forall l l' : list Z, fold_right Z.add 0 (l ++ l') = fold_right Z.add 0 l + fold_right Z.add 0 l').
      { intros l l'. induction l as [|x l IHl]; cbn; [lia| rewrite IHl; lia]. }
      cbn [fold_right]. rewrite !FA. cbn [fold_right]. lia. }
    rewrite Egm.
    assert (E1 : mmap_len (r_len rg) = round_up_pg (r_len rg)) by (unfold mmap_len; rewrite round_up_pg_eq; reflexivity).
    assert (E2 : mmap_len needed = needed).
    { pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[R1 _] R3]. rewrite <- En in R1, R3.
      apply mmap_len_of_aligned; [unfold MMAP_THRESHOLD, UNIT, IB in *; pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); lia| exact R3]. }
    rewrite E1, E2, <- Hml. unfold PGSZ, IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

(* [comment removed for export] *)
Section REMAPPED.
Variables (z needed : Z).
Hypothesis GE : MMAP_THRESHOLD <= n.
Hypothesis En : needed = round_up_pg (n + UNIT * off + UNIT + IB).
Let st_r := remap_region (fst bm) m z needed st0.

Lemma r_needed : 4096 <= needed /\ needed mod 4096 = 0 /\ needed / 4096 * 4096 = needed
  /\ Z.land (needed / 4096) (2 ^ 52 - 1) = needed / 4096.
Proof.
  pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[R1 R2] R3]. rewrite <- En in R1, R2, R3.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  assert (N1 : 4096 <= needed) by (unfold MMAP_THRESHOLD, UNIT, IB in *; lia).
  pose proof (Z.div_mod needed 4096 ltac:(lia)) as DM.
  split; [exact N1|]. split; [exact R3|]. split; [lia|].
  assert (0 <= needed / 4096 < 2 ^ 52).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    unfold size_overflows in OV. apply Z.leb_gt in OV. unfold UNIT, IB in *. lia. }
  change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma remap_SAQ rg : s_regions st0 !! fst bm = Some rg -> r_kind rg = RKGroup ->
  forall st', ctrl_eq st_r st' ->
  SINV x0 st' (((c, off), n) :: BL1) /\ AQ st' (((c, off), n) :: BL1) P.
Proof.
  intros Hrg Hkrg st' CE.
  destruct M63 as (I0 & L0 & B0 & ML & MLG & STR & _ & EC & EP).
  destruct r_needed as (N1 & N2 & N3 & N4).
  assert (Est : st_r = upd_meta m (m_set_maplen (needed / 4096))
                        (upd_shadow (fst bm) (shadow_trunc needed) (set_regions (<[fst bm := mkRegion RKGroup z needed]> (s_regions st0)) st0))).
  { unfold st_r, remap_region, upd_region, get_region. rewrite Hrg, Hkrg. reflexivity. }
  assert (EG : s_groups st_r = s_groups st0) by (rewrite Est; reflexivity).
  assert (ES : s_slots st_r = s_slots st0) by (rewrite Est; reflexivity).
  assert (EC0 : s_ctx st_r = s_ctx st0) by (rewrite Est; reflexivity).
  assert (MRg : MR st_r m = m_set_maplen (needed / 4096) (MR st0 m)).
  { rewrite Est. unfold MR. rewrite get_meta_rec_upd_same. reflexivity. }
  assert (MRo : forall m', m' <> m -> MR st_r m' = MR st0 m').
  { intros m' NE. rewrite Est. unfold MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity. }
  assert (ML' : m_maplen (MR st_r m) = needed / 4096) by (rewrite MRg; cbn; exact N4).
  assert (EREG : s_regions st_r = <[fst bm := mkRegion RKGroup z needed]> (s_regions st0)) by (rewrite Est; reflexivity).
  assert (EM : s_metas st_r = <[m := m_set_maplen (needed / 4096) (MR st0 m)]> (s_metas st0)) by (rewrite Est; reflexivity).
  assert (SV : forall s m' i', s_slots st0 !! s = Some (m', i') -> exists b, hosts st0 b m').
  { intros s m' i' Hs. destruct (is_valid _ _ _ IS0 _ _ _ Hs) as (LG & _). exact (live_hosts st0 _ LG). }
  assert (GEO : forall m', (exists b, hosts st0 b m') -> m' <> m -> geom (MR st_r m') = geom (MR st0 m')).
  { intros m' Hm' NE. unfold geom. rewrite (MRo m' NE). reflexivity. }
  assert (Hg : exists b, hosts st0 b m) by (exists bm; exact (m_hosts st c off n0 m bm i ai a ar ka BF)).
  assert (C63' : m_sizeclass (MR st_r m) = 63) by (rewrite MRg; cbn; exact SC63).
  assert (LI1 : m_last_idx (MR st_r m) = 0) by (rewrite MRg; cbn; exact L0).
  assert (ML1 : 1 <= m_maplen (MR st_r m)) by (rewrite ML'; apply Z.div_le_lower_bound; lia).
  assert (MM : m_mem (MR st_r m) = m_mem (MR st0 m)) by (rewrite MRg; reflexivity).
  assert (WIN : round_up_pg (n + IB + UNIT) <= m_maplen (MR st_r m) * 4096 <= round_up_pg (n + IB + UNIT) + PGSZ).
  { rewrite ML', N3, En. exact (big_window GE). }
  pose proof (SG_remap63_reblock st0 st_r BL m c off off n0 n i EG ES GEO SV Hg SC63 C63' LI1 ML1 MM r_ND Hk r_slot r_one GE WIN
                (proj1 (proj1 (SINV_split _ _ _) r_SI0))) as SGr.
  assert (QMr : QM x0 st_r 0).
  { apply (QM_regroup x0 st0 st_r 0 (fst bm) rg (mkRegion RKGroup z needed) m EC0 Hrg Hkrg eq_refl EREG).
    - exists (MR st0 m). split; [exact r_meta_some|]. exists (m_set_maplen (needed / 4096) (MR st0 m)). split; [exact EM|]. split; reflexivity.
    - exact (proj2 (proj1 (SINV_split _ _ _) r_SI0)). }
  split.
  - apply (SINV_ctrl x0 st_r st' _ CE). apply (proj2 (SINV_split _ _ _)). split; [exact SGr| exact QMr].
  - apply (AQ_ctrl st_r st' _ P CE). apply (AQ_reblock st_r BL P c off n); [| exact Hn| apply ROOM_sub; exact HROOM].
    destruct r_AQ0 as [A1 A2 A3 A4 A5 A6]. constructor; auto.
    + intros c' Hc'. replace (gcnt st_r c') with (gcnt st0 c'); [exact (A2 c' Hc')|].
      unfold gcnt. rewrite EG. apply zsum_map_ext. intros [b h] Hin. cbn [snd].
      destruct (g_meta h) as [m'|] eqn:Eh; [| reflexivity].
      destruct (aptr_eq_dec m' m) as [->|NE]; [rewrite MRg; cbn; rewrite SC63; reflexivity|].
      rewrite (MRo m' NE). reflexivity.
    + replace (ncarved st_r) with (ncarved st0); [exact A4|].
      symmetry. rewrite Est. rewrite ncarved_upd_meta_old; [reflexivity|]. cbn. rewrite r_meta_some. discriminate.
Qed.
End REMAPPED.
End BIG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem realloc_fq_main :
  xfqtree B L (realloc st (Some p) n) (RPOSTQ BL c n P).
Proof.
  pose proof INV0 as INV0'. pose proof (m_hosts st c off n0 m bm i ai a ar ka BF) as Hm. pose proof (m_c st c off n0 m bm i ai a ar ka BF) as Ec.
  pose proof INV0' as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM]. fold stride in S16, SM.
  unfold realloc. rewrite OV. fold st0. unfold p.
  rewrite (realloc_hdr_eq st0 c off n0 m bm i ai a ar ka BF). cbn [xlift sbind].
  fold (MR st0 m). rewrite (m_slot st L BL LS c off n0 INV m bm i ai a ar ka BF). fold stride.
  replace (snd (aadd c (stride - IB)) - snd (aadd c (UNIT * off))) with (stride - IB - UNIT * off) by (cbn [snd aadd]; lia).
  replace (snd (aadd c (UNIT * off)) - snd c) with (UNIT * off) by (cbn [snd aadd]; lia).
  destruct ((n <=? stride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st0 m) <=? size_to_class n + 1)) eqn:C1.
  { (* [comment removed for export] *)
    apply andb_prop in C1 as [C1 C13]. apply andb_prop in C1 as [C11 C12].
    apply Z.leb_le in C11. apply Z.ltb_lt in C12. apply Z.leb_le in C13.
    pose proof (size_to_class_ok n ltac:(lia)) as [SCR _].
    assert (SC48 : m_sizeclass (MR st0 m) < 48) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [[? _]| E63]; lia).
    cbn [xfqtree RPOSTQ fst snd].
    destruct (inplace_INVL st L BL LS c off n0 n INV Hk Hn m bm i ai a ar ka BF ltac:(fold st0; fold stride; lia) SC48) as [LS' INV'].
    destruct (inplace_SAQ ltac:(fold st0; fold stride; lia) C12 SC48 (havoc (aadd c (UNIT * off)) n (set_size (aadd c (UNIT * off)) (aadd c (stride - IB)) n i st0))
                (ctrl_eq_trans _ _ _ (ctrl_eq_set_size st0 _ _ _ _) (ctrl_eq_havoc _ _ _))) as [S' A'].
    exists c, off, LS'. auto 6. }
  destruct ((48 <=? m_sizeclass (MR st0 m)) && (MMAP_THRESHOLD <=? n)) eqn:C2.
  2:{ exact realloc_move_fq. }
  apply andb_prop in C2 as [C21 C22]. apply Z.leb_le in C21. apply Z.leb_le in C22.
  assert (SC63 : m_sizeclass (MR st0 m) = 63) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [[? ?]| E63]; lia).
  apply xfqtree_xguard; [apply Z.eqb_eq; exact SC63|].
  destruct (m63_facts st L BL LS c off n0 INV m bm i ai a ar ka BF SC63) as (I0 & L0 & B0 & ML & MLG & STR & (rg & Hrg & Hkrg & Hml) & EC & EP).
  fold st0 in L0, ML, MLG, STR, Hrg, Hml. fold stride in STR.
  change (default (0%N, 0) (m_mem (MR st0 m))) with (gbase (MR st0 m)). rewrite (m_gbase st L BL LS c off n0 INV m bm i ai a ar ka BF).
  set (needed := round_up_pg (n + UNIT * off + UNIT + IB)).
  pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [RU1 RU2]. fold needed in RU1, RU2.
  assert (N0 : 0 < needed) by (unfold UNIT, IB, MMAP_THRESHOLD in *; lia).
  destruct (Z.eqb_spec (m_maplen (MR st0 m) * 4096) needed) as [EQN|NEN].
  { (* [comment removed for export] *)
    cbn [xfqtree RPOSTQ fst snd].
    assert (FIT : UNIT * off + n <= stride - IB) by (rewrite STR; unfold UNIT, IB in *; lia).
    assert (RES32 : stride - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR; unfold UNIT, IB in *; lia).
    destruct (bigsame_INVL st L BL LS c off n0 n INV Hk Hn m bm i ai a ar ka BF SC63 FIT RES32) as [LS' INV']. exists c, off, LS'.
    assert (E1 : aadd bm (UNIT + UNIT * off) = aadd c (UNIT * off)) by (rewrite EC; unfold aadd; cbn [fst snd]; f_equal; lia).
    assert (E2 : aadd bm (needed - IB) = aadd c (stride - IB)) by (rewrite EC, STR, EQN; unfold aadd; cbn [fst snd]; f_equal; lia).
    unfold realloc_big_tail. rewrite E1, E2. cbn [fst snd]. split; [reflexivity|]. split; [exact Hoff|]. split; [exact INV'|].
    apply (bigsame_SAQ SC63 C22 EQN).
    exact (ctrl_eq_trans _ _ _ (ctrl_eq_wr8 st0 _ _) (ctrl_eq_trans _ _ _ (ctrl_eq_set_size _ _ _ _ _) (ctrl_eq_havoc _ _ _))). }
  destruct (Z.leb_spec PTRDIFF_MAX needed) as [BIG|SMALL].
  { exact realloc_move_fq. }
  (* [comment removed for export] *)
  assert (CONC : conc st0 bm = r_base rg) by (unfold conc, get_region; rewrite Hrg; lia).
  rewrite CONC.
  assert (OKEQ : forall z, mremap_answer_ok (lranges L) (r_base rg) (m_maplen (MR st0 m) * 4096) needed z
                         = mremap_answer_ok (live_ranges st0) (r_base rg) (m_maplen (MR st0 m) * 4096) needed z).
  { intros z. unfold mremap_answer_ok. rewrite !(ranges_free_eq x0 st0 L IR). reflexivity. }
  apply xfqtree_vis; [reflexivity| reflexivity| | | |].
  - (* [comment removed for export] *)
    cbn [xevent_pre]. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split.
    + exists (r_len rg). split; [| exact Hml]. destruct (r_ledger SC63) as (rg' & Hrg' & _ & _ & Hin & _). rewrite Hrg in Hrg'. injection Hrg' as <-. exact Hin.
    + unfold LEN_MAX, PTRDIFF_MAX, MMAP_THRESHOLD, PGSZ, UNIT, IB in *. repeat split; try lia.
  - (* [comment removed for export] *)
    exact (r_XBOUND SC63 needed rg Hrg C22 eq_refl).
  - (* [comment removed for export] *)
    intros z Hz. cbn [xanswer_ok xevent_post] in Hz |- *. rewrite OKEQ in Hz. rewrite Hz. cbn [negb].
    destruct (is_err z) eqn:EZ.
    + exact realloc_move_fq.
    + cbn [xfqtree RPOSTQ fst snd].
      pose proof (m_INV1 st L BL LS c off n0 INV Hk) as INV1. fold st0 X1 BL1 in INV1.
      assert (HO : x_orph X1 = None) by reflexivity.
      assert (HPc : x_pend X1 = Some (fst bm, sstart (MR st0 m) 0)) by (unfold X1; cbn; rewrite Ec, I0; reflexivity).
      assert (OLD : r_base (default (mkRegion RKGroup 0 0) (s_regions st0 !! fst bm)) = r_base rg) by (rewrite Hrg; reflexivity).
      destruct (remap_INVL X1 st0 L BL1 LS m bm z needed INV1 Hm SC63 HPc HO) as (INVr & Hmr & MRr & KN & SEC & REGS & REG & TWr).
      { rewrite OLD. exact Hz. }
      { exact EZ. }
      { unfold PTRDIFF_MAX, MMAP_THRESHOLD, UNIT, IB in *. lia. }
      { unfold PGSZ. exact RU2. }
      { lia. }
      { exact (m_TF0 st L BL LS INV). }
      rewrite OLD in INVr.
      set (str := wr8 (fst bm, needed - IB) 0 (remap_region (fst bm) m z needed st0)) in *.
      assert (ML' : m_maplen (MR str m) = needed / 4096).
      { rewrite MRr. cbn. pose proof (Z.div_pos needed 4096 ltac:(lia) ltac:(lia)).
        assert (needed / 4096 < 2 ^ 52) by (apply Z.div_lt_upper_bound; unfold PTRDIFF_MAX in *; lia).
        change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ND : needed / 4096 * 4096 = needed).
      { pose proof (Z.div_mod needed 4096 ltac:(lia)). unfold PGSZ in *. lia. }
      assert (STR' : get_stride (MR str m) = needed - UNIT).
      { unfold get_stride. rewrite ML'. replace (m_last_idx (MR str m)) with 0 by (rewrite MRr; cbn; lia).
        cbn [Z.eqb andb negb]. destruct (Z.eqb_spec (needed / 4096) 0) as [E0|NE0]; [exfalso; lia|]. cbn [negb andb]. lia. }
      assert (SS' : sstart (MR str m) 0 = UNIT).
      { unfold sstart. replace (gbase (MR str m)) with (gbase (MR st0 m)) by (rewrite MRr; reflexivity). rewrite (m_gbase st L BL LS c off n0 INV m bm i ai a ar ka BF), B0, STR'. lia. }
      assert (Hi' : 0 <= 0 <= m_last_idx (MR str m)) by (rewrite MRr; cbn; lia).
      assert (FIT' : UNIT * off + n <= get_stride (MR str m) - IB) by (rewrite STR'; unfold UNIT, IB in *; lia).
      assert (RES32' : get_stride (MR str m) - IB - UNIT * off - n < 2 ^ 32) by (rewrite STR'; unfold UNIT, IB in *; lia).
      pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
      rewrite (m_gbase st L BL LS c off n0 INV m bm i ai a ar ka BF) in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _). rewrite EC in K4, K2, K1, Q. cbn [fst snd] in K4, K2, K1, Q. rewrite B0 in K4, K2, K1, Q.
      assert (HPr : x_pend X1 = Some (fst bm, sstart (MR str m) 0)) by (rewrite SS', HPc; unfold sstart; rewrite (m_gbase st L BL LS c off n0 INV m bm i ai a ar ka BF), B0; f_equal; f_equal; lia).
      destruct (resize_INVL X1 str _ BL1 LS m bm 0 off n INVr Hmr Hi' HPr Hoff Hn FIT' RES32') as (INV2 & CE2 & _).
      * rewrite SS'. cbn [fst snd aadd]. apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 4) with (0 + UNIT + UNIT * off - 4) by lia. exact K4.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 2) with (0 + UNIT + UNIT * off - 2) by lia. exact K2.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia).
        apply KN; [unfold UNIT, IB in *; lia|]. replace (UNIT + UNIT * off - 1) with (0 + UNIT + UNIT * off - 1) by lia. exact K1.
      * rewrite SS', B0. cbn [fst snd aadd]. replace ((UNIT + UNIT * off - (0 + UNIT)) / UNIT) with ((0 + UNIT + UNIT * off - 0 - UNIT) / UNIT) by (f_equal; lia). exact Q.
      * eapply TW_mono; [| exact TWr]. intros q ->. cbn [fst snd aadd]. rewrite SS'. unfold UNIT, IB in *. lia.
      * exists c, off, LS. split; [| split; [exact Hoff|]].
        -- rewrite EC, B0. unfold aadd. cbn [fst snd]. f_equal. lia.
        -- split.
           ++ unfold realloc_big_tail. cbn [fst].
              unfold stf2 in INV2, CE2. rewrite <- (rs_set_size str m bm 0 off n) in INV2, CE2. rewrite SS', STR' in INV2, CE2.
              unfold BL1 in INV2. unfold aadd in INV2, CE2 |- *. cbn [fst snd] in INV2, CE2 |- *.
              rewrite EC, B0 in INV2 |- *. rewrite I0. rewrite !Z.add_0_l in INV2 |- *. cbn [fst snd] in INV2 |- *.
              replace (UNIT + (needed - UNIT - IB)) with (needed - IB) in INV2 by lia.
              first [exact INV2 | match goal with |- INVL _ ?S _ ?B _ => idtac "GOAL" S B end; match type of INV2 with INVL _ ?S _ ?B _ => idtac "INV2" S B end; fail].
           ++ (* [comment removed for export] *)
              unfold realloc_big_tail. cbn [fst].
              apply (remap_SAQ SC63 z needed C22 eq_refl rg Hrg Hkrg).
              eapply ctrl_eq_trans; [apply ctrl_eq_wr8|]. eapply ctrl_eq_trans; [apply ctrl_eq_set_size|]. apply ctrl_eq_havoc.
  - (* [comment removed for export] *)
    intros z Hz. cbn [xanswer_ok] in Hz. rewrite OKEQ in Hz. rewrite Hz. exact I.
Qed.

End REALLOC.

End RC__.
