(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr37Corelib4Init5Logick42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~ld2MRld5gbaseld5hosts37Corelib4Init9Datatypesr04Some05m_mem04optr37Corelib7Numbers7BinNumstc1Z04ghdrtc1N35stdpp7numbers1Nhg36eq_dec35stdpp7numbers1Zhhe6eq_dec25stdpp9countablehj9bN_countablehj9bZ_countablehj9eprod_countable25stdpp9decidablehnabprod_eq_decr06optionk43andk42exld8group_ok06mkGhdr08s_groups25stdpp4basehsb6lookup25stdpp4gmaphu14gmaphu1bgmap_lookupr03fstr04pairld6sstart0bslot_start'0bm_sizeclass04UNIT0aget_stride08m_maplen46Stdlib6ZArith6BinInt1Zil03mulk43notk42or0am_last_idx0asize_classil02leil02ltil03subil06moduloil03addr03sndld4gendr04prod07s_slots89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Geom4GEOM~~~~~~it35childit33ancr04Nonek45Falseld6extras06mstater04listld3blk05lheadld5inv_Mld5inv_Gld5inv_S" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section GEOM.
Variable X : ltac2:(zQ "10!jj6$0").
Variable st : ltac2:(zQ "10!jjf$0").
Variable L : mled.
Variable BL : ltac2:(zQ "20!jk7!jke@1$0$1").
Variable LS : ltac2:(zQ "30!jk7!je!jl4>0$2@1$0$1").
Hypothesis IM : ltac2:(zQ "10!jlb@3$0?1X?2st?2LS").
Hypothesis IG : ltac2:(zQ "10!jm3@3$0?1X?2st?2LS").
Hypothesis IS : ltac2:(zQ "10!jmb@3$0?1X?2st?2BL").
Local Notation R := (MR st).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hosts_gbase : ltac2:(zQ "50!je!l8!pb!q0!q8>1b$0>1m$0>0@3$4?2st^2^1@3$1$0@1$3@2$2?2st^2^3").
Proof. intros b m.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
  unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

Lemma hosts_mem : ltac2:(zQ "70!je!s8!l8!pb!q8!sf!t6>1b$0>1m$0>0@3$4?2st^2^1@3$2$6@1$5@2$3?2st^2@2$1$0^3").
Proof. intros b m.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

Lemma hosts_inj : ltac2:(zQ "30!je!q8!l8>2b1$0>2b2$0>1m$0>0@3$1?2st^3^1>0@3$1?2st^3^2@3$2$0^5^4").
Proof. intros b1 b2 m. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

Lemma hosts_fun : ltac2:(zQ "30!je!q8!l8>1b$0>2m1$0>2m2$0>0@3$1?2st^3^2>0@3$1?2st^4^2@3$2$0^4^3").
Proof. intros b m1 m2. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Lemma hosts_ok : ltac2:(zQ "h60!v5!je!v9!vf!hh4!hif!s8!hka!hl9!hm8!hob!hpa!hq3!l8!hq9!hqe!q8!hr9!hs1!ht7!hud!hv5>1b$1>1m$1>0@3$h0?2st^2^1@2$e$0\2ai$0@2$c@3$d@1$b$2@6$h3$1$2@4$h4$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2@4$h5$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2^4@1$h2?2st@2$6$2@2$h1@2$6$1^3^1@6$f?1X?2st?2LS^3^4^1").
Proof. intros b m. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

Lemma slot_start'_eq : ltac2:(zQ "a0!v5!je!vf!pb!ig4!iga!l8!q8!ih1!iha>1m$1>1b$1>1i$0>0@3$7?2st^2^3@3$6$1@2$9@2$3?2st^4^2@4$5$2$0@3$4$2$0^3@2$8@2$3?2st^4^2").
Proof. intros m b i. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

Lemma stride_cases : ltac2:(zQ "h20!pb!hq3!l8!v5!ii7!ij4!je!ija!ik6!im8!imf!in5!q8!ina!io6!ip2!ip8!ipe>1b$6>1m$6>0@3$c?2st^2^1@2$b@2$1@3$2$3@1$7@2$0?2st^2@2$9$5@1$e@1$4@2$0?2st^2@2$1@2$fZ@1$4@2$0?2st^2@2$h0@1$4@2$0?2st^2+j0@2$1@3$2$3@1$7@2$0?2st^2@2$h1@2$9@1$8@2$0?2st^2+hgg0$5@2$1@3$2$3@1$d@2$0?2st^2Z@1$a@3$2$3@1$8@2$0?2st^2Z").
Proof. intros b m.
  intros H. destruct (hosts_ok _ _ H) as (ai & Hg & GO). unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (R m)) 0) as [E|NE]; cbn.
  - destruct (Z.eqb_spec (m_maplen (R m)) 0) as [E2|NE2]; cbn.
    + left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
    + right. auto.
  - left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
Qed.

Lemma stride_ge : ltac2:(zQ "a0!pb!ij4!je!ija!hq3!l8!v5!q8!ip2!iq5>1b$2>1m$2>0@3$7?2st^2^1@2$4@2$8$1@1$3@2$0?2st^2@3$5$6@2$9@1$3@2$0?2st^2$1Z").
Proof. intros b m.
  intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
  - pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
    replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstart_mono : ltac2:(zQ "60!v5!pb!ih1!je!ip2!q8>1b$3>1m$3>1i$0>1j$0>0@3$5?2st^4^3>0@2$4^3^2@2$4@2$2@2$1?2st^5^4@2$2@2$1?2st^5^3").
Proof. intros b m i j. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

Lemma sstart_succ : ltac2:(zQ "70!pb!v5!ih1!iqf!l8!je!ija>1m$5>1i$1@3$4$1@2$2@2$0?2st^2@2$3^1+1@2$3@2$2@2$0?2st^2^1@1$6@2$0?2st^2").
Proof. intros m i. unfold sstart. lia. Qed.

Lemma sstart_lt : ltac2:(zQ "90!pb!v5!ih1!je!q8!ija!iqf!ip2!ip8>1b$3>1m$3>1i$1>1j$1>0@3$4?2st^4^3>0@2$8^3^2@2$7@2$6@2$2@2$0?2st^5^4@1$5@2$0?2st^5@2$2@2$0?2st^5^3").
Proof. intros b m i j. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.

Lemma sstart0 : ltac2:(zQ "a0!v5!je!ir6!l8!vf!pb!q8!ih1!ij4!iqf>1b$1>1m$1>0@3$6?2st^2^1@3$3$0@2$7@2$5?2st^2Z@2$9@3$2$4$0^3$8").
Proof. intros b m. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.

Lemma gend_eq : ltac2:(zQ "80!pb!l8!v5!irc!ih1!je!ina!iqf>1m$5@3$1$2@1$3@2$0?2st^1@2$4@2$0?2st^1@2$7@1$6@2$0?2st^1+1").
Proof. intros m. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition child : ltac2:(zQ "20!je!v5>1c$0>1p$0>1i$1P") := ltac2:(zQ "h70!je!v5!is3!vf!hh4!hif!hq3!l8!hka!hl9!hm8!hob!s8!hpa!iga!hq9!pb!q8!ik6!isa!ht7!hud!hv5\1c$0\1p$0\1i$1@2$f$0\1b$0@2$6@3$h1?2st^1^4@2$6@3$7$1@1$h2@2$h0?2st^4Z@3$7@1$d@2$2$0$1@6$h4$0@2$2$0$1@4$h5$0@4$b$3$4$1$5@6$a$3$4$8$1$5$9@2$2$0$1@4$h6$0@4$b$3$4$1$5@6$a$3$4$8$1$5$9@2$2$0$1^1@1$h3?2st@2$c@2$2$0$1@4$e$0$1^3^2").

Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.

Lemma child_facts : ltac2:(zQ "h30!hq3!pb!v5!je!vf!ig4!l8!ih1!ii7!ip2!hq9!q8!ip8!iga!ir6!jh7!irc!ina!iqf>1c$3>1p$3>1i$2>0@3$f^3^2^1@2$a$3\2bc$3@2$a$3\2bp$3@2$0@3$b?2st^2^6@2$0@3$b?2st^1^5@2$0@3$6$4@3$5$4$2^2@3$5$4$2^1@2$0@2$0@2$9Z^4@2$9^4@1$h1@2$1?2st^5@2$0@3$6$3^2@4$d$4$2@3$5$4$2^1@2$7@2$1?2st^5^4@2$0@3$6$2@2$7@2$1?2st^5^4@3$e$4$2^2@2$0@2$9@1$h0@2$1?2st^6@2$7@2$1?2st^5@2$h2^4+1@2$0@2$c@1$8@2$1?2st^6@1$8@2$1?2st^5@2$c@1$8@2$1?2st^5+j0").
Proof. intros c p i.
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

Lemma anc_facts : ltac2:(zQ "h40!hq3!je!pb!v5!hq9!vf!ip2!ii7!ig4!l8!ji0!q8!ih1!ip8!ir6!in5!jh7!irc!ina!iqf>1m$1>1p$1>1i$3>1c$1>0@4$a^4^3^2^1@2$4$1\2bm$1@2$4$1\2bp$1@2$0@3$b?2st^2^7@2$0@3$b?2st^1^6@2$0@3$9$5@3$8$5$3^2@3$8$5$3^1@2$0@2$0@2$6Z^5@2$6^5@1$h2@2$2?2st^6@2$0@3$h0^4^6^5@2$0@2$f@3$9$1^7^4@2$4$3\1j$3@2$4$1\2c'$1@4$a^9^6^2^1@2$0@2$6@2$c@2$2?2st^6^5@3$e$5$3^2@2$0@2$6@1$h1@2$2?2st^7@2$c@2$2?2st^6@2$h3^5+1@2$0@2$d@1$7@2$2?2st^7@1$7@2$2?2st^6@2$d@1$7@2$2?2st^6+j0").
Proof. intros m p i c.
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

Lemma anc_trans : ltac2:(zQ "30!je!ji0!v5>1m$0>1q$0>1j$2>2c'$0>1p$0>1i$2>1c$0>0@4$1^7^6^5^4>0@4$1^7^4^3^2@4$1^9^5^4^3").
Proof. intros m q j c' p i c.
  intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
  - eapply anc_step; eauto.
  - eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.

(* [comment removed for export] *)
Lemma child_unique : ltac2:(zQ "40!je!jh7!l8!v5>2c1$0>2c2$0>1p$0>1i$3>0@3$1^4^2^1>0@3$1^4^3^2@3$2$0^6^5").
Proof. intros c1 c2 p i.
  intros H1 H2.
  destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
  destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.

(* [comment removed for export] *)
Lemma top_chain : ltac2:(zQ "c0!je!v5!hq9!hq3!l8!vf!ig4!pb!q8!ik6!imf!ji0>1m$0>2bm$0>0@3$8?2st^1^2>0@3$4$1@1$9@2$7?2st^3Z@2$2$0\1t$0@2$2$1\1i$1@2$2$0\1c$0@2$2$0\2bt$0@2$3@4$b^8^4^3^2@2$3@3$8?2st^1^4@2$3@1$a@3$4$1@1$9@2$7?2st^4Z@3$4$5@3$6$5$1^1@3$6$5$1^7").
Proof. intros m bm.
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
Lemma top_at0 : ltac2:(zQ "90!v5!l8!je!ir6!imf!vf!pb!q8!ik6>1t$2>2bt$2>0@3$7?2st^1^2>0@1$4@3$1$0@1$8@2$6?2st^3Z@3$1$0@3$3$5$0^3Z").
Proof. intros t bt. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

Lemma top_unique : ltac2:(zQ "91!je!l8!v5!vf!ig4!imf!pb!q8!ik6&@1$5@3$1$2@1$8@2$6?2st^6Z>2t1$0>2t2$0>2b1$0>2b2$0>0@3$7?2st^2^4>0@3$7?2st^2^4>0~0>0~0>0@3$1$3@3$4$3$2^6@3$4$3$2^5@3$1$0^9^8").
Proof. intros t1 t2 b1 b2.
  intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
  assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dichotomy : ltac2:(zQ "b0!je!v5!hq9!ji0!l8!vf!ig4!hq3!imf!in5!q8>2m1$0>2m2$0>2b1$0>2b2$0>0@3$a?2st^2^4>0@3$a?2st^2^4>0@3$4$5@3$6$5$1^4@3$6$5$1^3>0@1$8@3$4$0^7^6@2$9@2$2$1\1i$1@2$2$0\1c$0@4$3^a^9^2^1@2$9@2$2$1\1i$1@2$2$0\1c$0@4$3^9^a^2^1@2$2$0\1p$0@2$2$1\2i1$1@2$2$1\2i2$1@2$2$0\2c1$0@2$2$0\2c2$0@2$7@1$8@3$4$1^4^3@2$7@4$3^d^5^4^2@4$3^c^5^3^1").
Proof. intros m1 m2 b1 b2.
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

Lemma last_idx_nonneg : ltac2:(zQ "50!je!pb!q8!ina!ip2>1b$0>1m$0>0@3$2?2st^2^1@2$4Z@1$3@2$1?2st^2").
Proof. intros b m. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

(* [comment removed for export] *)
Lemma anc_box : ltac2:(zQ "c0!pb!ih1!je!ip2!hq3!v5!iqf!ir6!vf!ji0!irc!q8>1m$2>1p$2>1j$5>1c$2>2bm$2>0@4$9^5^4^3^2>0@3$b?2st^2^6@2$4@2$3@2$1@2$0?2st^6^5@3$7$8$5^3@2$4@2$3@1$a@2$0?2st^7@2$1@2$0?2st^6@2$6^5+1@2$3@2$6@2$1@2$0?2st^6^5+h0@2$1@2$0?2st^7Z").
Proof. intros m p j c bm.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma anc_hostslot : ltac2:(zQ "hb0!v5!vf!je!v9!hh4!hif!hka!hl9!hm8!hob!ji7!ig4!hpa!iga!is3!hq3!l8!hq9!imf!ji0!pb!q8!ih1!hs1!ht7!hud!hv5>1m$2>1p$2>1j$0>1c$2>0@4$h3^4^3^2^1@2$h1$2\2bp$2@2$f@3$h5?2st^1^5@1$h2@3$h0@1$c$3@6$h8@2$e$1$0$3@4$h9$2@4$9$1$4$0$5@6$8$1$4$6$0$5$7$3@4$ha$2@4$9$1$4$0$5@6$8$1$4$6$0$5$7$3@4$d$1$0@3$b$1$0^1@2$h6@2$h4?2st^5^4@1$h7?2st@1$a$3").
Proof. intros m p j c.
  intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
  destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
  rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.

Lemma sst_lt : ltac2:(zQ "80!v5!pb!ih1!je!q8!iqf!ip2!ip8>1b$3>1m$3>1i$0>1j$0>0@3$4?2st^4^3>0@2$7^3^2@2$6@2$5@2$2@2$1?2st^5^4+h0@2$2@2$1?2st^5^3").
Proof. intros b m i j. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.

Lemma gend_ge : ltac2:(zQ "90!je!ir6!vf!v5!pb!irc!q8!iqf!ip2>1b$0>1m$0>0@3$6?2st^2^1@2$8@2$7@3$1$2$3^3+i0@1$5@2$4?2st^2").
Proof. intros b m.
  intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
  unfold UNIT in *. lia.
Qed.

Section SEP.
  Variables (m : aptr) (bm : aptr) (i : Z).
  Hypothesis Hm : ltac2:(zQ "10!q8@3$0?2st?2bm?1m").
  Hypothesis Hi : ltac2:(zQ "40!ip2!hq3!pb!ina@2$1@2$0Z?1i@2$0?1i@1$3@2$2?2st?1m").
  Hypothesis NH : ltac2:(zQ "h60!vf!v5!v9!hh4!hif!je!hka!hl9!hm8!hob!ji7!ig4!hpa!iga!is3!l8!pb!ih1!hs1!ht7!hud!hv5@3$f@1$c$2@6$h3@2$e$0$1$2@4$h4$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2@4$h5$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2@4$d$0$1@3$b$0$1?2bm@2$h1@2$h0?2st?1m?1i@1$h2?2st@1$a$2").

  (* [comment removed for export] *)
  Lemma sep_no_anc : ltac2:(zQ "30!je!jie!ji0>2m2$0>1c$0>0@4$2^2?1m?1i^1$1").
  Proof. intros m2 c. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

  (* [comment removed for export] *)
  Let S0m := sstart0 _ _ Hm.
  Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).

  (* [comment removed for export] *)
  Lemma sep_hdr0 : ltac2:(zQ "e0!pb!v5!ih1!ip2!l8!vf!je!ig4!imf!in5!iqf!hq3!q8!ina>2m2$6>2b2$6>2i2$1>0@3$c?2st^2^3>0@3$4$5@3$7$5$1^3@3$7$5$1?2bm>0@2$b@2$3Z^3@2$3^3@2$a@1$d@2$0?2st^5+1>0@2$9@1$8@3$4$6^6?1m@1$8@3$4$1^4?1i@2$9@2$3@2$2@2$0?2st^7^5@2$2@2$0?2st?1m?1i@2$3@2$2@2$0?2st?1m@2$a?1i+1@2$2@2$0?2st^7^5").
  Proof. intros m2 b2 i2.
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
  Lemma sep_h3 : ltac2:(zQ "e0!pb!v5!ih1!ip2!l8!vf!je!ig4!imf!in5!iqf!hq3!q8!ina>2m2$6>2b2$6>2i2$1>0@3$c?2st^2^3>0@3$4$5@3$7$5$1^3@3$7$5$1?2bm>0@2$b@2$3Z^3@2$3^3@1$d@2$0?2st^5>0@2$9@1$8@3$4$6^6?1m@1$8@3$4$1^4?1i@2$9@2$3@2$a@2$2@2$0?2st^7^5+h0@2$2@2$0?2st?1m?1i@2$3@2$2@2$0?2st?1m@2$a?1i+1@2$2@2$0?2st^7^5").
  Proof. intros m2 b2 i2.
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
  Lemma sep_ghdr : ltac2:(zQ "c0!vf!v5!iqf!ig4!ir6!pb!ih1!je!ip2!l8!in5!q8>2m2$7>2b2$7>0@3$b?2st^1^2>0@3$9$0@3$3$0$1^2@3$3$0$1?2bm@2$a@2$8@2$2@3$4$0$1^3+h0@2$6@2$5?2st?1m?1i@2$8@2$6@2$5?2st?1m@2$2?1i+1@2$2@3$4$0$1^3+4").
  Proof. intros m2 b2.
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
  Lemma sep_ext : ltac2:(zQ "hd0!v5!vf!pb!ih1!je!v9!l8!ip2!hh4!hif!ig4!imf!in5!iqf!hka!hl9!hm8!hob!ji7!hpa!iga!is3!hq3!q8!ina!hs1!ht7!hud!hv5>2m2$4>2b2$4>2i2$0>0@3$h7?2st^2^3>0@3$6$1@3$a$1$0^3@3$a$1$0?2bm>0@2$h6@2$7Z^3@2$7^3@1$h8@2$2?2st^5>0@2$c@1$b@3$6$4^6?1m@1$b@3$6$0^4?1i>0@3$6@1$h3$5@6$ha@2$h5$1$0$5@4$hb$4@4$h1$1$8$0$9@6$h0$1$8$e$0$9$f$5@4$hc$4@4$h1$1$8$0$9@6$h0$1$8$e$0$9$f$5@4$h4$1$0@3$a$1$0^6@2$3@2$2?2st^7^5@1$h9?2st@1$h2$5@2$c@2$7@2$3@2$2?2st^8@2$d^6+1@2$3@2$2?2st?1m?1i@2$7@2$3@2$2?2st?1m@2$d?1i+1@2$3@2$2?2st^8^6").
  Proof. intros m2 b2 i2.
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
(* [comment removed for export] *)
