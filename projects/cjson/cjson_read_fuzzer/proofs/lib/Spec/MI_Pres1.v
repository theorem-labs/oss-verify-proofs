(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From Stdlib Require Wf_nat.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Module MI_Geom.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Arith.Wf_nat.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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


End CeilWrap.
End MI_Geom.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
Import MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 :
  hosts st b1 m1 -> hosts st b2 m2 -> 0 <= i1 <= m_last_idx (MR st m1) -> 0 <= i2 <= m_last_idx (MR st m2) ->
  slot_start' (MR st m1) i1 = slot_start' (MR st m2) i2 -> m1 = m2 /\ i1 = i2.
Proof.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

(* [comment removed for export] *)
Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
  unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : 0 <= A' /\ 0 <= F'
  /\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
  /\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
  /\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
  let s := slot_start' (R g) i in
  one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).
(* [comment removed for export] *)
Hypothesis C_pend : pend' = x_pend X \/
  ((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
   /\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.

Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fR_mem : m_mem (f (R g)) = m_mem (R g). Proof. reflexivity. Qed.
Lemma fR_prev : m_prev (f (R g)) = m_prev (R g). Proof. reflexivity. Qed.
Lemma fR_next : m_next (f (R g)) = m_next (R g). Proof. reflexivity. Qed.
Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
Lemma fR_gbase : gbase (f (R g)) = gbase (R g). Proof. reflexivity. Qed.
Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i. Proof. reflexivity. Qed.
Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i. Proof. reflexivity. Qed.
Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.
Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_stride x : get_stride (R' x) = get_stride (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gend x : gend (R' x) = gend (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x). Proof. intros; rewrite R'_other; auto. Qed.

Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma st'_shadow : s_shadow st' = s_shadow st. Proof. reflexivity. Qed.
Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      * (* [comment removed for export] *)
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-G" g end.
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-O" g end.
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      * (* [comment removed for export] *)
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.


End CeilWrap.
