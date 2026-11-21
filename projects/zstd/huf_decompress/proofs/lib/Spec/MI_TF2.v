(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (TF0_TW, TF0_TF, TW_mono and 19 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Shadow MI_WFree2 MI_WGroup.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_TF2 () := "C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes8list_indC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldc59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec6MI_TF22TWC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec6MI_TF22PSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF26TF0_TWC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec9MI_WGroup2TFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup3TKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3sndC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC35stdpp4base6insertC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic7f_equalC35stdpp4base5emptyC35stdpp8fin_maps<lookup_emptyC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec9MI_WGroup3wrsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib4Spec6MI_TF27TW_wr8'C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib4Spec6MI_TF29geom_keptC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF27PS_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF27TW_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF27TW_monoC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec9MI_WFree2Awr8_shadow_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF2?wr8_cells_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8hosts_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8sep_hdr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom6sep_h3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroupEget_shadow_cells_someC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_TF2?PS_not_interiorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib4Spec6MI_TF2:sstart_resC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

(* [comment removed for export] *)
Definition PS (st : mstate) (q : aptr) : Prop :=
  exists b m, hosts st b m /\ fst b = fst q /\
    ((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
     \/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 st : TF0 st -> TF2 st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_TF2 ()) [] "h02stp;1p;2g00cmj11Tg00d`j20Tg00ZhR0f0R1%11'0X00P1O1W0o"). Qed.
Lemma TF0_TF st : TF0 st -> TF st.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.

Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

(* [comment removed for export] *)
Definition geom_kept (st st' : mstate) : Prop :=
  forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
                              /\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

Lemma geom_kept_refl st : geom_kept st st.
Proof. intros b m H. auto. Qed.
Lemma geom_kept_trans a b c : geom_kept a b -> geom_kept b c -> geom_kept a c.
Proof.
  intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
  split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.

Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
  intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
  exists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

(* [comment removed for export] *)
Lemma geom_kept_of st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall b m, hosts st b m -> MR st' m = MR st m) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

(* [comment removed for export] *)
Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
  r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other l : forall st rid o, ~ In (rid, o) (map fst l) ->
  r_cells (get_shadow (wrs l st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma PS_not_interior q :
  PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
  intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    + (* [comment removed for export] *)
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  - (* [comment removed for export] *)
    destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
    destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_interior_old :
  TF2 st -> forall o v t, r_cells (get_shadow st (fst bg)) !! o = Some (v, t) ->
  sstart (MR st g) idx <= o < sstart (MR st g) (idx + 1) - IB -> (t < s_tick st)%N.
Proof.
  intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

(* [comment removed for export] *)
Lemma TF2_ghdr_old (p : aptr) :
  TF2 st -> snd p mod 16 = 0 ->
  forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
  intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_TF : TF2 st -> TF st.
Proof.
  intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.
