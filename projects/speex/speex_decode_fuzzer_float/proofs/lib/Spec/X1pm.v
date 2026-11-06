(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1og X1po X1pv X1pf.
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

#[using="X LS IM"] Lemma hosts_gbase b m : hosts st b m -> gbase (R m) = b.
Proof.
intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

#[using="X LS IM"] Lemma hosts_mem b m : hosts st b m -> m_mem (R m) = Some b.
Proof.
intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

#[using="X LS IM"] Lemma hosts_inj b1 b2 m : hosts st b1 m -> hosts st b2 m -> b1 = b2.
Proof. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

#[using="Type"] Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

#[using="IG"] Lemma hosts_ok b m : hosts st b m -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

#[using="Type"] Lemma live_hosts m : live_group st m -> exists b, hosts st b m.
Proof. intros H. exact H. Qed.

#[using="X LS IM"] Lemma slot_start'_eq m b i : hosts st b m -> slot_start' (R m) i = (fst b, sstart (R m) i).
Proof. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

#[using="X LS IG"] Lemma stride_cases b m : hosts st b m ->
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

#[using="X LS IG"] Lemma stride_ge b m : hosts st b m -> UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0.
Proof.
intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
- pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.

#[using="X LS IG"] Lemma sstart_mono b m i j : hosts st b m -> i <= j -> sstart (R m) i <= sstart (R m) j.
Proof. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

#[using="Type"] Lemma sstart_succ m i : sstart (R m) (i + 1) = sstart (R m) i + get_stride (R m).
Proof. unfold sstart. lia. Qed.

#[using="X LS IG"] Lemma sstart_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + get_stride (R m) <= sstart (R m) j.
Proof. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.

#[using="X LS IM"] Lemma sstart0 b m : hosts st b m -> sstart (R m) 0 = snd b + UNIT.
Proof. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.

#[using="Type"] Lemma gend_eq m : gend (R m) = sstart (R m) (m_last_idx (R m) + 1).
Proof. reflexivity. Qed.

Definition child (c p : aptr) (i : Z) : Prop :=
exists b, hosts st b c /\ m_maplen (R c) = 0 /\ s_slots st !! b = Some (p, i).

Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.

#[using="X BL LS IM IG IS"] Lemma child_facts c p i : child c p i ->
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

#[using="X BL LS IM IG IS"] Lemma anc_facts m p i c : anc m p i c ->
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

#[using="X BL LS IM IG IS"] Lemma anc_irrefl m i c : anc m m i c -> False.
Proof. intros H. destruct (anc_facts _ _ _ _ H) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). lia. Qed.

#[using="Type"] Lemma anc_trans m q j c' p i c : anc m q j c' -> anc q p i c -> anc m p i c.
Proof.
intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
- eapply anc_step; eauto.
- eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.

#[using="X BL LS IM IG IS"] Lemma child_unique c1 c2 p i : child c1 p i -> child c2 p i -> c1 = c2.
Proof.
intros H1 H2.
destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.

#[using="X BL LS IM IG IS"] Lemma top_chain m bm : hosts st bm m -> m_maplen (R m) = 0 ->
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

#[using="X LS IG"] Lemma top_at0 t bt : hosts st bt t -> m_maplen (R t) <> 0 -> snd bt = 0.
Proof. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

#[using="X LS IG"] Lemma top_unique t1 t2 b1 b2 : hosts st b1 t1 -> hosts st b2 t2 -> m_maplen (R t1) <> 0 -> m_maplen (R t2) <> 0 ->
fst b1 = fst b2 -> t1 = t2.
Proof.
intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

#[using="X BL LS IM IG IS"] Lemma anc_not_top m p i c bm : anc m p i c -> hosts st bm m -> 0 < snd bm.
Proof.
intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & Hi & _ & _ & Hs & _).
pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
destruct (hosts_ok _ _ Hp) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [H0 _].
pose proof (sstart0 _ _ Hp). pose proof (sstart_mono _ _ 0 i Hp ltac:(lia)). unfold UNIT in *. lia.
Qed.

#[using="X BL LS IM IG IS"] Lemma dichotomy m1 m2 b1 b2 : hosts st b1 m1 -> hosts st b2 m2 -> fst b1 = fst b2 -> m1 <> m2 ->
(exists i c, anc m1 m2 i c) \/ (exists i c, anc m2 m1 i c)
\/ (exists p i1 i2 c1 c2, i1 <> i2 /\ anc m1 p i1 c1 /\ anc m2 p i2 c2).
Proof.
remember (Z.to_nat (48 - m_sizeclass (R m1)) + Z.to_nat (48 - m_sizeclass (R m2)))%nat as n eqn:En.
revert m1 m2 b1 b2 En. induction n as [n IH] using lt_wf_ind; intros m1 m2 b1 b2 En H1 H2 Hf NE.
destruct (Z.eq_dec (m_maplen (R m1)) 0) as [M1|M1]; destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
-
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
*
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
-
destruct (top_chain _ _ H1 M1) as (t & i & c & bt & Ha & Ht & Mt & Hft).
assert (t = m2) by (eapply top_unique; eauto; congruence). subst t. left. exists i, c. exact Ha.
- destruct (top_chain _ _ H2 M2) as (t & i & c & bt & Ha & Ht & Mt & Hft).
assert (t = m1) by (eapply top_unique; eauto; congruence). subst t. right; left. exists i, c. exact Ha.
- exfalso. apply NE. eapply top_unique; eauto.
Qed.

#[using="X LS IG"] Lemma last_idx_nonneg b m : hosts st b m -> 0 <= m_last_idx (R m).
Proof. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

#[using="X BL LS IM IG IS"] Lemma anc_box m p j c bm : anc m p j c -> hosts st bm m ->
sstart (R p) j <= snd bm /\ gend (R m) <= sstart (R p) (j + 1)
/\ sstart (R p) j + 16 <= sstart (R m) 0.
Proof.
intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

#[using="X BL LS IM IG IS"] Lemma anc_hostslot m p j c : anc m p j c -> exists bp, hosts st bp p /\ s_groups st !! (fst bp, sstart (R p) j) <> None.
Proof.
intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.

#[using="X LS IG"] Lemma sst_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + 16 <= sstart (R m) j.
Proof. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.

#[using="X LS IM IG"] Lemma gend_ge b m : hosts st b m -> snd b + 32 <= gend (R m).
Proof.
intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
unfold UNIT in *. lia.
Qed.

Section SEP.
Variables (m : aptr) (bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (R m).
Hypothesis NH : s_groups st !! (fst bm, sstart (R m) i) = None.

#[using="X BL LS IM IG IS bm Hm NH"] Lemma sep_no_anc m2 c : anc m2 m i c -> False.
Proof. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

Let S0m := sstart0 _ _ Hm.
Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).

#[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_hdr0 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) + 1 ->
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

#[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_h3 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
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

#[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_ghdr m2 b2 : hosts st b2 m2 -> fst b2 = fst bm ->
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

#[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_ext m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
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
