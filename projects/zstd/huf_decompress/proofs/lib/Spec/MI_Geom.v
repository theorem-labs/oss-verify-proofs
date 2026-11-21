(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (34 recorded proofs replaced by written proofs (hosts_gbase, hosts_mem, hosts_inj and 31 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Geom () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6im_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transI59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_InvBslot_start'_sstartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec7MI_Geom8hosts_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec7MI_Geom<stride_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Arith@size_class_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib4Spec6MI_Inv8g_maplenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=add_le_mono_lK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lK46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib4Spec7MI_Geom;sstart_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib4Spec7MI_Geom5childC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegi59OSSVerify5KrLib4Spec7MI_Geom3anc00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom;child_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom7sstart0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom7gend_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib4Spec7MI_Geom7anc_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom9anc_factsC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec7MI_Geom3anc02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom9hosts_funC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revk59OSSVerify5KrLib4Spec7MI_Geom3anc01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom9anc_transC1?~~~~~~~~~~~~~~~C46Stdlib5Arith6Wf_nat9lt_wf_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib4Spec6MI_Inv5g_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom7top_at0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom<child_uniqueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom9top_chainC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom:top_uniqueC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec7MI_Geom9sstart_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom?last_idx_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom6sst_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom<anc_hostslotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib4Spec7MI_Geom9dichotomyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom:sep_no_ancC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom7anc_boxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Geom7gend_geC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Section GEOM.
Variable X : extras.
Variable st : mstate.
Variable L : mled.
Variable BL : list blk.
Variable LS : lhead -> list aptr.
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Local Notation R := (MR st).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hosts_gbase b m : hosts st b m -> gbase (R m) = b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
  unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

Lemma hosts_mem b m : hosts st b m -> m_mem (R m) = Some b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

Lemma hosts_inj b1 b2 m : hosts st b1 m -> hosts st b2 m -> b1 = b2.
Proof. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Lemma hosts_ok b m : hosts st b m -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

Lemma live_hosts m : live_group st m -> exists b, hosts st b m.
Proof. intros H. exact H. Qed.

Lemma slot_start'_eq m b i : hosts st b m -> slot_start' (R m) i = (fst b, sstart (R m) i).
Proof. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

Lemma stride_cases b m : hosts st b m ->
  get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) /\ 0 <= m_sizeclass (R m) < 48
  \/ get_stride (R m) = m_maplen (R m) * 4096 - UNIT /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0.
Proof.
  intros H. destruct (hosts_ok _ _ H) as (ai & Hg & GO). unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (R m)) 0) as [E|NE]; cbn.
  - destruct (Z.eqb_spec (m_maplen (R m)) 0) as [E2|NE2]; cbn.
    + left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
    + right. auto.
  - left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
Qed.

Lemma stride_ge b m : hosts st b m -> UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0.
Proof.
  intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
  - pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
    replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstart_mono b m i j : hosts st b m -> i <= j -> sstart (R m) i <= sstart (R m) j.
Proof. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

Lemma sstart_succ m i : sstart (R m) (i + 1) = sstart (R m) i + get_stride (R m).
Proof. unfold sstart. lia. Qed.

Lemma sstart_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + get_stride (R m) <= sstart (R m) j.
Proof. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.

Lemma sstart0 b m : hosts st b m -> sstart (R m) 0 = snd b + UNIT.
Proof. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.

Lemma gend_eq m : gend (R m) = sstart (R m) (m_last_idx (R m) + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition child (c p : aptr) (i : Z) : Prop :=
  exists b, hosts st b c /\ m_maplen (R c) = 0 /\ s_slots st !! b = Some (p, i).

Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.

Lemma child_facts c p i : child c p i ->
  exists bc bp, hosts st bc c /\ hosts st bp p /\ fst bc = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ bc = (fst bp, sstart (R p) i)
    /\ sstart (R p) i = snd bc /\ gend (R c) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R c) < m_sizeclass (R p) < 48.
Proof.
  intros (bc & Hc & Hml & Hsl).
  destruct (is_valid _ _ _ IS _ _ _ Hsl) as (Hlive & Hi & Hs).
  destruct Hlive as [bp Hp].
  destruct (hosts_ok _ _ Hc) as (ai & Hg & GO).
  destruct (g_nest _ _ _ _ _ _ GO Hml) as (p' & i' & Hsl' & Hfst & Hend & Hsc & Hstr).
  rewrite Hsl in Hsl'. inversion Hsl'; subst p' i'.
  exists bc, bp. rewrite (slot_start'_eq _ _ _ Hp) in Hs.
  repeat split; auto; try lia.
  - rewrite Hs. reflexivity.
  - rewrite Hs. reflexivity.
  - rewrite sstart_succ. exact Hend.
Qed.

Lemma anc_facts m p i c : anc m p i c ->
  exists bm bp, hosts st bm m /\ hosts st bp p /\ fst bm = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ child c p i /\ (m = c \/ exists j c', anc m c j c')
    /\ sstart (R p) i <= snd bm /\ gend (R m) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R m) < m_sizeclass (R p) < 48.
Proof.
  induction 1 as [c p i Hch|m c j c' p i Ha IH Hch].
  - destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & Hs & Hend & Hsc).
    exists bc, bp. repeat split; auto; lia.
  - destruct IH as (bm & bc & Hm & Hc & Hfst & Hj & Hch' & _ & Hs & Hend & Hsc).
    destruct (child_facts _ _ _ Hch) as (bc' & bp & Hc' & Hp & Hfst' & Hi & Hbc & Hs' & Hend' & Hsc').
    pose proof (hosts_inj _ _ _ Hc Hc') as E.
    pose proof (sstart0 _ _ Hc). pose proof (sstart_mono _ _ 0 j Hc ltac:(lia)).
    pose proof (sstart_mono _ _ (j + 1) (m_last_idx (R c) + 1) Hc ltac:(lia)). rewrite <- gend_eq in *.
    subst bc bc'. cbn [fst snd] in *.
    exists bm, bp. split; [exact Hm|]. split; [exact Hp|]. split; [congruence|]. split; [exact Hi|].
    split; [exact Hch|]. split; [right; eauto|].
    unfold UNIT in *. repeat split; lia.
Qed.

Lemma anc_irrefl m i c : anc m m i c -> False.
Proof. intros H. destruct (anc_facts _ _ _ _ H) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). lia. Qed.

Lemma anc_trans m q j c' p i c : anc m q j c' -> anc q p i c -> anc m p i c.
Proof.
  intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
  - eapply anc_step; eauto.
  - eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.

(* [comment removed for export] *)
Lemma child_unique c1 c2 p i : child c1 p i -> child c2 p i -> c1 = c2.
Proof.
  intros H1 H2.
  destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
  destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.

(* [comment removed for export] *)
Lemma top_chain m bm : hosts st bm m -> m_maplen (R m) = 0 ->
  exists t i c bt, anc m t i c /\ hosts st bt t /\ m_maplen (R t) <> 0 /\ fst bt = fst bm.
Proof.
  intros Hm Hml.
  remember (Z.to_nat (48 - m_sizeclass (R m))) as n eqn:En.
  revert m bm Hm Hml En. induction n as [n IH] using lt_wf_ind; intros m bm Hm Hml En.
  assert (Hch : exists p i, child m p i).
  { destruct (hosts_ok _ _ Hm) as (ai & Hg & GO). destruct (g_nest _ _ _ _ _ _ GO Hml) as (p & i & Hsl & _). exists p, i. exists bm. auto. }
  destruct Hch as (p & i & Hch).
  destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & _ & _ & Hsc).
  pose proof (hosts_inj _ _ _ Hm Hc). subst bc bm. cbn [fst snd] in *.
  destruct (Z.eq_dec (m_maplen (R p)) 0) as [Hml'|Hml'].
  - destruct (IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl) as (t & j & c & bt & Ha & Ht & Htop & Hfst').
    exists t, j, c, bt. split; [| repeat split; auto; congruence]. eapply anc_trans; [apply anc_child; exact Hch| exact Ha].
  - exists p, i, m, bp. repeat split; auto. apply anc_child. exact Hch.
Qed.

(* [comment removed for export] *)
Lemma top_at0 t bt : hosts st bt t -> m_maplen (R t) <> 0 -> snd bt = 0.
Proof. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

Lemma top_unique t1 t2 b1 b2 : hosts st b1 t1 -> hosts st b2 t2 -> m_maplen (R t1) <> 0 -> m_maplen (R t2) <> 0 ->
  fst b1 = fst b2 -> t1 = t2.
Proof.
  intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
  assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

(* [comment removed for export] *)
Lemma anc_not_top m p i c bm : anc m p i c -> hosts st bm m -> 0 < snd bm.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & Hi & _ & _ & Hs & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
  destruct (hosts_ok _ _ Hp) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [H0 _].
  pose proof (sstart0 _ _ Hp). pose proof (sstart_mono _ _ 0 i Hp ltac:(lia)). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma dichotomy m1 m2 b1 b2 : hosts st b1 m1 -> hosts st b2 m2 -> fst b1 = fst b2 -> m1 <> m2 ->
  (exists i c, anc m1 m2 i c) \/ (exists i c, anc m2 m1 i c)
  \/ (exists p i1 i2 c1 c2, i1 <> i2 /\ anc m1 p i1 c1 /\ anc m2 p i2 c2).
Proof.
  remember (Z.to_nat (48 - m_sizeclass (R m1)) + Z.to_nat (48 - m_sizeclass (R m2)))%nat as n eqn:En.
  revert m1 m2 b1 b2 En. induction n as [n IH] using lt_wf_ind; intros m1 m2 b1 b2 En H1 H2 Hf NE.
  destruct (Z.eq_dec (m_maplen (R m1)) 0) as [M1|M1]; destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
  - (* [comment removed for export] *)
    destruct (hosts_ok _ _ H1) as (a1 & _ & G1). destruct (g_nest _ _ _ _ _ _ G1 M1) as (p1 & i1 & S1 & _).
    destruct (hosts_ok _ _ H2) as (a2 & _ & G2). destruct (g_nest _ _ _ _ _ _ G2 M2) as (p2 & i2 & S2 & _).
    assert (C1 : child m1 p1 i1) by (exists b1; auto). assert (C2 : child m2 p2 i2) by (exists b2; auto).
    destruct (child_facts _ _ _ C1) as (bc1 & bp1 & Hc1 & Hp1 & Hf1 & Hi1 & Hb1 & _ & _ & Hsc1).
    destruct (child_facts _ _ _ C2) as (bc2 & bp2 & Hc2 & Hp2 & Hf2 & Hi2 & Hb2 & _ & _ & Hsc2).
    pose proof (hosts_inj _ _ _ H1 Hc1); subst bc1. pose proof (hosts_inj _ _ _ H2 Hc2); subst bc2.
    destruct (aptr_eq_dec p1 m2) as [->|N1]; [left; exists i1, m1; apply anc_child; exact C1|].
    destruct (aptr_eq_dec p2 m1) as [->|N2]; [right; left; exists i2, m2; apply anc_child; exact C2|].
    destruct (aptr_eq_dec p1 p2) as [->|N3].
    + pose proof (hosts_inj _ _ _ Hp1 Hp2); subst bp2.
      destruct (Z.eq_dec i1 i2) as [->|Ni].
      * exfalso. apply NE. exact (child_unique _ _ _ _ C1 C2).
      * right; right. exists p2, i1, i2, m1, m2. split; [exact Ni|]. split; apply anc_child; assumption.
    + assert (Hf' : fst bp1 = fst bp2) by congruence.
      destruct (IH (Z.to_nat (48 - m_sizeclass (R p1)) + Z.to_nat (48 - m_sizeclass (R p2)))%nat ltac:(lia) p1 p2 bp1 bp2 eq_refl Hp1 Hp2 Hf' N3)
        as [(j & c & Ha)|[(j & c & Ha)|(p & j1 & j2 & c1 & c2 & Nj & Ha1 & Ha2)]].
      * (* [comment removed for export] *)
        destruct (Z.eq_dec j i2) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C2); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [contradiction|].
           left. exists j', c'. eapply anc_trans; [apply anc_child; exact C1| exact Ha'].
        -- right; right. exists p2, j, i2, c, m2. split; [exact Nj|]. split; [| apply anc_child; exact C2].
           eapply anc_trans; [apply anc_child; exact C1| exact Ha].
      * destruct (Z.eq_dec j i1) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C1); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [congruence|].
           right; left. exists j', c'. eapply anc_trans; [apply anc_child; exact C2| exact Ha'].
        -- right; right. exists p1, i1, j, m1, c. split; [congruence|]. split; [apply anc_child; exact C1|].
           eapply anc_trans; [apply anc_child; exact C2| exact Ha].
      * right; right. exists p, j1, j2, c1, c2. split; [exact Nj|]. split.
        -- eapply anc_trans; [apply anc_child; exact C1| exact Ha1].
        -- eapply anc_trans; [apply anc_child; exact C2| exact Ha2].
  - (* [comment removed for export] *)
    destruct (top_chain _ _ H1 M1) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m2) by (eapply top_unique; eauto; congruence). subst t. left. exists i, c. exact Ha.
  - destruct (top_chain _ _ H2 M2) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m1) by (eapply top_unique; eauto; congruence). subst t. right; left. exists i, c. exact Ha.
  - exfalso. apply NE. eapply top_unique; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma last_idx_nonneg b m : hosts st b m -> 0 <= m_last_idx (R m).
Proof. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

(* [comment removed for export] *)
Lemma anc_box m p j c bm : anc m p j c -> hosts st bm m ->
  sstart (R p) j <= snd bm /\ gend (R m) <= sstart (R p) (j + 1)
  /\ sstart (R p) j + 16 <= sstart (R m) 0.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma anc_hostslot m p j c : anc m p j c -> exists bp, hosts st bp p /\ s_groups st !! (fst bp, sstart (R p) j) <> None.
Proof.
  intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
  destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
  rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.

Lemma sst_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + 16 <= sstart (R m) j.
Proof. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.

Lemma gend_ge b m : hosts st b m -> snd b + 32 <= gend (R m).
Proof.
  intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
  unfold UNIT in *. lia.
Qed.

Section SEP.
  Variables (m : aptr) (bm : aptr) (i : Z).
  Hypothesis Hm : hosts st bm m.
  Hypothesis Hi : 0 <= i <= m_last_idx (R m).
  Hypothesis NH : s_groups st !! (fst bm, sstart (R m) i) = None.

  (* [comment removed for export] *)
  Lemma sep_no_anc m2 c : anc m2 m i c -> False.
  Proof. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

  (* [comment removed for export] *)
  Let S0m := sstart0 _ _ Hm.
  Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).

  (* [comment removed for export] *)
  Lemma sep_hdr0 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) + 1 ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sep_h3 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sst_lt _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sep_ghdr m2 b2 : hosts st b2 m2 -> fst b2 = fst bm ->
    snd b2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= snd b2 + 4.
  Proof.
    intros H2 Hf. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - left. pose proof (hosts_inj _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ H2) as G2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + left. destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
        pose proof (sstart_mono _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sep_ext m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) -> s_groups st !! (fst b2, sstart (R m2) i2) = None ->
    sstart (R m2) (i2 + 1) <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE NH2. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (Z.eq_dec j i2) as [->|Nj].
        { exfalso. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ H2 Hp); subst bp. exact (Hne NH2). }
        destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (i2 + 1) j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.
End SEP.

End GEOM.
