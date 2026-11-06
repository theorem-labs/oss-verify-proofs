(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  intros [ai H]. (first [ pose proof ((im_hdr _ _ _ IM _ _ H)) as dR_1; dex1 dR_1 as m'; dand3 dR_1 as Hm Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ H)) as dR_1; dand4 dR_1 as m' Hm Hmem _ | destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _) ]). cbn in Hm. inversion Hm; subst.
  unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

Lemma hosts_mem b m : hosts st b m -> m_mem (R m) = Some b.
Proof.
  intros [ai H]. (first [ pose proof ((im_hdr _ _ _ IM _ _ H)) as dR_2; dex1 dR_2 as m'; dand3 dR_2 as Hm Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ H)) as dR_2; dand4 dR_2 as m' Hm Hmem _ | destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _) ]). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

Lemma hosts_inj b1 b2 m : hosts st b1 m -> hosts st b2 m -> b1 = b2.
Proof. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Lemma hosts_ok b m : hosts st b m -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

(* [comment removed for export] *)

Lemma slot_start'_eq m b i : hosts st b m -> slot_start' (R m) i = (fst b, sstart (R m) i).
Proof. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

Lemma stride_cases b m : hosts st b m ->
  get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) /\ 0 <= m_sizeclass (R m) < 48
  \/ get_stride (R m) = m_maplen (R m) * 4096 - UNIT /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0.
Proof.
  intros H. (first [ pose proof ((hosts_ok _ _ H)) as dR_3; dex1 dR_3 as ai; destruct dR_3 as [Hg GO] | pose proof ((hosts_ok _ _ H)) as dR_3; dand3 dR_3 as ai Hg GO | destruct (hosts_ok _ _ H) as (ai & Hg & GO) ]). unfold get_stride.
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
  - (first [ pose proof ((hosts_ok _ _ H)) as dR_4; dex1 dR_4 as ai; destruct dR_4 as [_ GO] | pose proof ((hosts_ok _ _ H)) as dR_4; dand3 dR_4 as ai _ GO | destruct (hosts_ok _ _ H) as (ai & _ & GO) ]). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
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
  ((first [ intro dR_65; dex1 dR_65 as bc; dand3 dR_65 as Hc Hml Hsl | intro dR_65; dand4 dR_65 as bc Hc Hml Hsl | intros (bc & Hc & Hml & Hsl) ])).
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hsl)) as dR_5; dand3 dR_5 as Hlive Hi Hs | destruct (is_valid _ _ _ IS _ _ _ Hsl) as (Hlive & Hi & Hs) ]).
  destruct Hlive as [bp Hp].
  (first [ pose proof ((hosts_ok _ _ Hc)) as dR_6; dex1 dR_6 as ai; destruct dR_6 as [Hg GO] | pose proof ((hosts_ok _ _ Hc)) as dR_6; dand3 dR_6 as ai Hg GO | destruct (hosts_ok _ _ Hc) as (ai & Hg & GO) ]).
  (first [ pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_7; dex2 dR_7 as p' i'; dand5 dR_7 as Hsl' Hfst Hend Hsc Hstr | pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_7; dand7 dR_7 as p' i' Hsl' Hfst Hend Hsc Hstr | destruct (g_nest _ _ _ _ _ _ GO Hml) as (p' & i' & Hsl' & Hfst & Hend & Hsc & Hstr) ]).
  rewrite Hsl in Hsl'. inversion Hsl'; subst p' i'.
  exists bc, bp. rewrite (slot_start'_eq _ _ _ Hp) in Hs.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try lia.
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
  - (first [ pose proof ((child_facts _ _ _ Hch)) as dR_8; dex2 dR_8 as bc bp; dand8 dR_8 as Hc Hp Hfst Hi Hbc Hs Hend Hsc | pose proof ((child_facts _ _ _ Hch)) as dR_8; dand10 dR_8 as bc bp Hc Hp Hfst Hi Hbc Hs Hend Hsc | destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & Hs & Hend & Hsc) ]).
    exists bc, bp. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
  - (first [ dex2 IH as bm bc; dand9 IH as Hm Hc Hfst Hj Hch' _ Hs Hend Hsc | dand11 IH as bm bc Hm Hc Hfst Hj Hch' _ Hs Hend Hsc | destruct IH as (bm & bc & Hm & Hc & Hfst & Hj & Hch' & _ & Hs & Hend & Hsc) ]).
    (first [ pose proof ((child_facts _ _ _ Hch)) as dR_10; dex2 dR_10 as bc' bp; dand8 dR_10 as Hc' Hp Hfst' Hi Hbc Hs' Hend' Hsc' | pose proof ((child_facts _ _ _ Hch)) as dR_10; dand10 dR_10 as bc' bp Hc' Hp Hfst' Hi Hbc Hs' Hend' Hsc' | destruct (child_facts _ _ _ Hch) as (bc' & bp & Hc' & Hp & Hfst' & Hi & Hbc & Hs' & Hend' & Hsc') ]).
    pose proof (hosts_inj _ _ _ Hc Hc') as E.
    pose proof (sstart0 _ _ Hc). pose proof (sstart_mono _ _ 0 j Hc ltac:(lia)).
    pose proof (sstart_mono _ _ (j + 1) (m_last_idx (R c) + 1) Hc ltac:(lia)). rewrite <- gend_eq in *.
    subst bc bc'. cbn [fst snd] in *.
    exists bm, bp. split; [exact Hm|]. split; [exact Hp|]. split; [congruence|]. split; [exact Hi|].
    split; [exact Hch|]. split; [right; eauto|].
    unfold UNIT in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

(* [comment removed for export] *)

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
  (first [ pose proof ((child_facts _ _ _ H1)) as dR_11; dex2 dR_11 as b1 bp; dand6 dR_11 as Hc1 Hp _ _ Hb1 _ | pose proof ((child_facts _ _ _ H1)) as dR_11; dand8 dR_11 as b1 bp Hc1 Hp _ _ Hb1 _ | destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _) ]).
  (first [ pose proof ((child_facts _ _ _ H2)) as dR_12; dex2 dR_12 as b2 bp'; dand6 dR_12 as Hc2 Hp' _ _ Hb2 _ | pose proof ((child_facts _ _ _ H2)) as dR_12; dand8 dR_12 as b2 bp' Hc2 Hp' _ _ Hb2 _ | destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _) ]).
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
  { (first [ pose proof ((hosts_ok _ _ Hm)) as dR_13; dex1 dR_13 as ai; destruct dR_13 as [Hg GO] | pose proof ((hosts_ok _ _ Hm)) as dR_13; dand3 dR_13 as ai Hg GO | destruct (hosts_ok _ _ Hm) as (ai & Hg & GO) ]). (first [ pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_14; dex2 dR_14 as p i; destruct dR_14 as [Hsl _] | pose proof ((g_nest _ _ _ _ _ _ GO Hml)) as dR_14; dand4 dR_14 as p i Hsl _ | destruct (g_nest _ _ _ _ _ _ GO Hml) as (p & i & Hsl & _) ]). exists p, i. exists bm. auto. }
  (first [ dex2 Hch as p i | dand3 Hch as p i Hch | destruct Hch as (p & i & Hch) ]).
  (first [ pose proof ((child_facts _ _ _ Hch)) as dR_16; dex2 dR_16 as bc bp; dand8 dR_16 as Hc Hp Hfst Hi Hbc _ _ Hsc | pose proof ((child_facts _ _ _ Hch)) as dR_16; dand10 dR_16 as bc bp Hc Hp Hfst Hi Hbc _ _ Hsc | destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & _ & _ & Hsc) ]).
  pose proof (hosts_inj _ _ _ Hm Hc). subst bc bm. cbn [fst snd] in *.
  destruct (Z.eq_dec (m_maplen (R p)) 0) as [Hml'|Hml'].
  - (first [ pose proof ((IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl)) as dR_17; dex4 dR_17 as t j c bt; dand4 dR_17 as Ha Ht Htop Hfst' | pose proof ((IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl)) as dR_17; dand8 dR_17 as t j c bt Ha Ht Htop Hfst' | destruct (IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl) as (t & j & c & bt & Ha & Ht & Htop & Hfst') ]).
    exists t, j, c, bt. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; congruence]. eapply anc_trans; [apply anc_child; exact Hch| exact Ha].
  - exists p, i, m, bp. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. apply anc_child. exact Hch.
Qed.

(* [comment removed for export] *)
Lemma top_at0 t bt : hosts st bt t -> m_maplen (R t) <> 0 -> snd bt = 0.
Proof. intros Ht Hml. (first [ pose proof ((hosts_ok _ _ Ht)) as dR_18; dex1 dR_18 as ai; destruct dR_18 as [_ GO] | pose proof ((hosts_ok _ _ Ht)) as dR_18; dand3 dR_18 as ai _ GO | destruct (hosts_ok _ _ Ht) as (ai & _ & GO) ]). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

Lemma top_unique t1 t2 b1 b2 : hosts st b1 t1 -> hosts st b2 t2 -> m_maplen (R t1) <> 0 -> m_maplen (R t2) <> 0 ->
  fst b1 = fst b2 -> t1 = t2.
Proof.
  intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
  assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dichotomy m1 m2 b1 b2 : hosts st b1 m1 -> hosts st b2 m2 -> fst b1 = fst b2 -> m1 <> m2 ->
  (exists i c, anc m1 m2 i c) \/ (exists i c, anc m2 m1 i c)
  \/ (exists p i1 i2 c1 c2, i1 <> i2 /\ anc m1 p i1 c1 /\ anc m2 p i2 c2).
Proof.
  remember (Z.to_nat (48 - m_sizeclass (R m1)) + Z.to_nat (48 - m_sizeclass (R m2)))%nat as n eqn:En.
  revert m1 m2 b1 b2 En. induction n as [n IH] using lt_wf_ind; intros m1 m2 b1 b2 En H1 H2 Hf NE.
  destruct (Z.eq_dec (m_maplen (R m1)) 0) as [M1|M1]; destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
  - (* [comment removed for export] *)
    (first [ pose proof ((hosts_ok _ _ H1)) as dR_21; dex1 dR_21 as a1; destruct dR_21 as [_ G1] | pose proof ((hosts_ok _ _ H1)) as dR_21; dand3 dR_21 as a1 _ G1 | destruct (hosts_ok _ _ H1) as (a1 & _ & G1) ]). (first [ pose proof ((g_nest _ _ _ _ _ _ G1 M1)) as dR_22; dex2 dR_22 as p1 i1; destruct dR_22 as [S1 _] | pose proof ((g_nest _ _ _ _ _ _ G1 M1)) as dR_22; dand4 dR_22 as p1 i1 S1 _ | destruct (g_nest _ _ _ _ _ _ G1 M1) as (p1 & i1 & S1 & _) ]).
    (first [ pose proof ((hosts_ok _ _ H2)) as dR_23; dex1 dR_23 as a2; destruct dR_23 as [_ G2] | pose proof ((hosts_ok _ _ H2)) as dR_23; dand3 dR_23 as a2 _ G2 | destruct (hosts_ok _ _ H2) as (a2 & _ & G2) ]). (first [ pose proof ((g_nest _ _ _ _ _ _ G2 M2)) as dR_24; dex2 dR_24 as p2 i2; destruct dR_24 as [S2 _] | pose proof ((g_nest _ _ _ _ _ _ G2 M2)) as dR_24; dand4 dR_24 as p2 i2 S2 _ | destruct (g_nest _ _ _ _ _ _ G2 M2) as (p2 & i2 & S2 & _) ]).
    assert (C1 : child m1 p1 i1) by (exists b1; auto). assert (C2 : child m2 p2 i2) by (exists b2; auto).
    (first [ pose proof ((child_facts _ _ _ C1)) as dR_25; dex2 dR_25 as bc1 bp1; dand8 dR_25 as Hc1 Hp1 Hf1 Hi1 Hb1 _ _ Hsc1 | pose proof ((child_facts _ _ _ C1)) as dR_25; dand10 dR_25 as bc1 bp1 Hc1 Hp1 Hf1 Hi1 Hb1 _ _ Hsc1 | destruct (child_facts _ _ _ C1) as (bc1 & bp1 & Hc1 & Hp1 & Hf1 & Hi1 & Hb1 & _ & _ & Hsc1) ]).
    (first [ pose proof ((child_facts _ _ _ C2)) as dR_26; dex2 dR_26 as bc2 bp2; dand8 dR_26 as Hc2 Hp2 Hf2 Hi2 Hb2 _ _ Hsc2 | pose proof ((child_facts _ _ _ C2)) as dR_26; dand10 dR_26 as bc2 bp2 Hc2 Hp2 Hf2 Hi2 Hb2 _ _ Hsc2 | destruct (child_facts _ _ _ C2) as (bc2 & bp2 & Hc2 & Hp2 & Hf2 & Hi2 & Hb2 & _ & _ & Hsc2) ]).
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
        -- (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_27; dand9 dR_27 as _ _ _ _ _ _ Cc Hor _ | destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _) ]).
           pose proof (child_unique _ _ _ _ Cc C2); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [contradiction|].
           left. exists j', c'. eapply anc_trans; [apply anc_child; exact C1| exact Ha'].
        -- right; right. exists p2, j, i2, c, m2. split; [exact Nj|]. split; [| apply anc_child; exact C2].
           eapply anc_trans; [apply anc_child; exact C1| exact Ha].
      * destruct (Z.eq_dec j i1) as [->|Nj].
        -- (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_28; dand9 dR_28 as _ _ _ _ _ _ Cc Hor _ | destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _) ]).
           pose proof (child_unique _ _ _ _ Cc C1); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [congruence|].
           right; left. exists j', c'. eapply anc_trans; [apply anc_child; exact C2| exact Ha'].
        -- right; right. exists p1, i1, j, m1, c. split; [congruence|]. split; [apply anc_child; exact C1|].
           eapply anc_trans; [apply anc_child; exact C2| exact Ha].
      * right; right. exists p, j1, j2, c1, c2. split; [exact Nj|]. split.
        -- eapply anc_trans; [apply anc_child; exact C1| exact Ha1].
        -- eapply anc_trans; [apply anc_child; exact C2| exact Ha2].
  - (* [comment removed for export] *)
    (first [ pose proof ((top_chain _ _ H1 M1)) as dR_29; dex4 dR_29 as t i c bt; dand4 dR_29 as Ha Ht Mt Hft | pose proof ((top_chain _ _ H1 M1)) as dR_29; dand8 dR_29 as t i c bt Ha Ht Mt Hft | destruct (top_chain _ _ H1 M1) as (t & i & c & bt & Ha & Ht & Mt & Hft) ]).
    assert (t = m2) by (eapply top_unique; eauto; congruence). subst t. left. exists i, c. exact Ha.
  - (first [ pose proof ((top_chain _ _ H2 M2)) as dR_30; dex4 dR_30 as t i c bt; dand4 dR_30 as Ha Ht Mt Hft | pose proof ((top_chain _ _ H2 M2)) as dR_30; dand8 dR_30 as t i c bt Ha Ht Mt Hft | destruct (top_chain _ _ H2 M2) as (t & i & c & bt & Ha & Ht & Mt & Hft) ]).
    assert (t = m1) by (eapply top_unique; eauto; congruence). subst t. right; left. exists i, c. exact Ha.
  - exfalso. apply NE. eapply top_unique; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma last_idx_nonneg b m : hosts st b m -> 0 <= m_last_idx (R m).
Proof. intros H. (first [ pose proof ((hosts_ok _ _ H)) as dR_31; dex1 dR_31 as ai; destruct dR_31 as [_ GO] | pose proof ((hosts_ok _ _ H)) as dR_31; dand3 dR_31 as ai _ GO | destruct (hosts_ok _ _ H) as (ai & _ & GO) ]). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

(* [comment removed for export] *)
Lemma anc_box m p j c bm : anc m p j c -> hosts st bm m ->
  sstart (R p) j <= snd bm /\ gend (R m) <= sstart (R p) (j + 1)
  /\ sstart (R p) j + 16 <= sstart (R m) 0.
Proof.
  intros Ha Hm. (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_32; dex2 dR_32 as bm' bp; dand9 dR_32 as Hm' Hp _ _ _ _ Hs He _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_32; dand11 dR_32 as bm' bp Hm' Hp _ _ _ _ Hs He _ | destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _) ]).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma anc_hostslot m p j c : anc m p j c -> exists bp, hosts st bp p /\ s_groups st !! (fst bp, sstart (R p) j) <> None.
Proof.
  intros Ha. (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_33; dex2 dR_33 as bm bp; dand6 dR_33 as Hm Hp _ _ Hch _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_33; dand8 dR_33 as bm bp Hm Hp _ _ Hch _ | destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _) ]).
  (first [ pose proof ((child_facts _ _ _ Hch)) as dR_34; dex2 dR_34 as bc bp'; dand6 dR_34 as Hc Hp' _ _ Hbc _ | pose proof ((child_facts _ _ _ Hch)) as dR_34; dand8 dR_34 as bc bp' Hc Hp' _ _ Hbc _ | destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _) ]).
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
  Proof. intros Ha. (first [ pose proof ((anc_hostslot _ _ _ _ Ha)) as dR_35; dex1 dR_35 as bp; destruct dR_35 as [Hp Hne] | pose proof ((anc_hostslot _ _ _ _ Ha)) as dR_35; dand3 dR_35 as bp Hp Hne | destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne) ]). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

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
        (first [ pose proof ((anc_box _ _ _ _ _ Ha H2)) as dR_36; dand3 dR_36 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_37; dex2 dR_37 as bm' b2'; dand5 dR_37 as Hm' H2' _ Hj _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_37; dand7 dR_37 as bm' b2' Hm' H2' _ Hj _ | destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha Hm)) as dR_38; dand3 dR_38 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha1)) as dR_39; dex2 dR_39 as bm' bp; dand5 dR_39 as Hm' Hp _ Hj1 _ | pose proof ((anc_facts _ _ _ _ Ha1)) as dR_39; dand7 dR_39 as bm' bp Hm' Hp _ Hj1 _ | destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        (first [ pose proof ((anc_facts _ _ _ _ Ha2)) as dR_40; dex2 dR_40 as b2' bp'; dand5 dR_40 as H2' Hp' _ Hj2 _ | pose proof ((anc_facts _ _ _ _ Ha2)) as dR_40; dand7 dR_40 as b2' bp' H2' Hp' _ Hj2 _ | destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _) ]).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha1 Hm)) as dR_41; dand3 dR_41 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3) ]).
        (first [ pose proof ((anc_box _ _ _ _ _ Ha2 H2)) as dR_42; dand3 dR_42 as B1 B2 B3 | destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3) ]). rewrite gend_eq in A2, B2.
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
        (first [ pose proof ((anc_box _ _ _ _ _ Ha H2)) as dR_43; dand3 dR_43 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_44; dex2 dR_44 as bm' b2'; dand5 dR_44 as Hm' H2' _ Hj _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_44; dand7 dR_44 as bm' b2' Hm' H2' _ Hj _ | destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha Hm)) as dR_45; dand3 dR_45 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha1)) as dR_46; dex2 dR_46 as bm' bp; dand5 dR_46 as Hm' Hp _ Hj1 _ | pose proof ((anc_facts _ _ _ _ Ha1)) as dR_46; dand7 dR_46 as bm' bp Hm' Hp _ Hj1 _ | destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        (first [ pose proof ((anc_facts _ _ _ _ Ha2)) as dR_47; dex2 dR_47 as b2' bp'; dand5 dR_47 as H2' Hp' _ Hj2 _ | pose proof ((anc_facts _ _ _ _ Ha2)) as dR_47; dand7 dR_47 as b2' bp' H2' Hp' _ Hj2 _ | destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _) ]).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha1 Hm)) as dR_48; dand3 dR_48 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3) ]).
        (first [ pose proof ((anc_box _ _ _ _ _ Ha2 H2)) as dR_49; dand3 dR_49 as B1 B2 B3 | destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3) ]). rewrite gend_eq in A2, B2.
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
        (first [ pose proof ((anc_box _ _ _ _ _ Ha H2)) as dR_50; dand3 dR_50 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3) ]).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + left. (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_51; dex2 dR_51 as bm' b2'; dand5 dR_51 as Hm' H2' _ Hj _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_51; dand7 dR_51 as bm' b2' Hm' H2' _ Hj _ | destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha Hm)) as dR_52; dand3 dR_52 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3) ]).
        pose proof (sstart_mono _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha1)) as dR_53; dex2 dR_53 as bm' bp; dand5 dR_53 as Hm' Hp _ Hj1 _ | pose proof ((anc_facts _ _ _ _ Ha1)) as dR_53; dand7 dR_53 as bm' bp Hm' Hp _ Hj1 _ | destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        (first [ pose proof ((anc_facts _ _ _ _ Ha2)) as dR_54; dex2 dR_54 as b2' bp'; dand5 dR_54 as H2' Hp' _ Hj2 _ | pose proof ((anc_facts _ _ _ _ Ha2)) as dR_54; dand7 dR_54 as b2' bp' H2' Hp' _ Hj2 _ | destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _) ]).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha1 Hm)) as dR_55; dand3 dR_55 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3) ]).
        (first [ pose proof ((anc_box _ _ _ _ _ Ha2 H2)) as dR_56; dand3 dR_56 as B1 B2 B3 | destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3) ]). rewrite gend_eq in A2.
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
        (first [ pose proof ((anc_box _ _ _ _ _ Ha H2)) as dR_57; dand3 dR_57 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (Z.eq_dec j i2) as [->|Nj].
        { exfalso. (first [ pose proof ((anc_hostslot _ _ _ _ Ha)) as dR_58; dex1 dR_58 as bp; destruct dR_58 as [Hp Hne] | pose proof ((anc_hostslot _ _ _ _ Ha)) as dR_58; dand3 dR_58 as bp Hp Hne | destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne) ]). pose proof (hosts_inj _ _ _ H2 Hp); subst bp. exact (Hne NH2). }
        (first [ pose proof ((anc_facts _ _ _ _ Ha)) as dR_59; dex2 dR_59 as bm' b2'; dand5 dR_59 as Hm' H2' _ Hj _ | pose proof ((anc_facts _ _ _ _ Ha)) as dR_59; dand7 dR_59 as bm' b2' Hm' H2' _ Hj _ | destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha Hm)) as dR_60; dand3 dR_60 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3) ]). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (i2 + 1) j H2 ltac:(lia)). lia.
      + (first [ pose proof ((anc_facts _ _ _ _ Ha1)) as dR_61; dex2 dR_61 as bm' bp; dand5 dR_61 as Hm' Hp _ Hj1 _ | pose proof ((anc_facts _ _ _ _ Ha1)) as dR_61; dand7 dR_61 as bm' bp Hm' Hp _ Hj1 _ | destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _) ]).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        (first [ pose proof ((anc_facts _ _ _ _ Ha2)) as dR_62; dex2 dR_62 as b2' bp'; dand5 dR_62 as H2' Hp' _ Hj2 _ | pose proof ((anc_facts _ _ _ _ Ha2)) as dR_62; dand7 dR_62 as b2' bp' H2' Hp' _ Hj2 _ | destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _) ]).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        (first [ pose proof ((anc_box _ _ _ _ _ Ha1 Hm)) as dR_63; dand3 dR_63 as A1 A2 A3 | destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3) ]).
        (first [ pose proof ((anc_box _ _ _ _ _ Ha2 H2)) as dR_64; dand3 dR_64 as B1 B2 B3 | destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3) ]). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.
End SEP.

End GEOM.
