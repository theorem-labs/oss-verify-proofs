(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Geom () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Geom.CEIL_WRAP_1.GEOM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1fst"; "1option"; "1pair"; "1prod"; "1snd"; "2False"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3N"; "3Z"; "0LS"]; ["4anc"; "4child"; "5MR"; "5gbase"; "5gend"; "5group_ok"; "5hosts"; "5live_group"; "5sstart"; "6UNIT"; "6aptr"; "6get_stride"; "6ghdr"; "6m_last_idx"; "6m_maplen"; "6m_mem"]; ["6m_sizeclass"; "6mkGhdr"; "6optr"; "6s_groups"; "6size_class"; "6slot_start'"; "7add"; "7le"; "7lt"; "7modulo"; "7mul"; "7sub"; "0X"; "0ai"; "0b"; "0b1"]; ["0b2"; "0bc"; "0bm"; "0bp"; "0bt"; "0c"; "0c'"; "0c1"; "0c2"; "0i"; "0i1"; "0i2"; "0j"; "0m"; "0m1"; "0m2"]; ["0p"; "0q"; "0st"; "8lookup"; "9N_countable"; "9Z_countable"; "9prod_countable"; ":prod_eq_dec"; ";gmap"; ";gmap_lookup"; "<eq_dec"; "=eq_dec"; "0t"; "0t1"; "0t2"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
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
Lemma hosts_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "@&J&FvR2r2r1%43321'9&C&B%1276%311r3%63<21p081pSL>1pRN?1").
Proof. intros b m.
intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.
Lemma hosts_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "C&J&FvR2r2r1%43321'9&Q2&O&B%1287%311(1r3%22>1%93841p0;1pSLA1pRNB1").
Proof. intros b m.
intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.
Lemma hosts_inj : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "A&J&FvR2r3r1%43321r2%63541'9r5r4%33;21p051p081pSL>1pS2?1pS0@1").
Proof. intros b1 b2 m. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.
Lemma hosts_fun : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "?&J&FvR2r3r2%43321r4%63513'9%13936p031p061pT0<1pSN=1pRN>1").
Proof. intros b m1 m2. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.
Lemma hosts_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "Q@&J&FvR2r2r1%43321':'>'8'9'3'L%211&R3'R8&R7'=&R:&R;%4432<1&R6&R4&R5%36762@51%:4H51=&R9%14J73?r4&Q3%11K%A6NC6431(1(Q1r3%32Q21%321O%52I1%L3I71'EvQ<v?%362Q718>Q5%Q2251qRLQ41%Q62Q51p0Q81pSLQ>1pRNQ?1").
Proof. intros b m. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.
Lemma live_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "=&J&GvR2r1%3221':&Fr3%23651qRN91%52:1p071pSL<1").
Proof. intros m. intros H. exact H. Qed.
Lemma slot_start'_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "I&J'>&FvR2r2r3%43321'9&Q5&Br4%2281%4218(4'=&2%132?;&H%127>%645B31%=3D81p0?1pSDE1pRNG1pSLH1").
Proof. intros m b i. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.
Lemma stride_cases : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "QA&J&FvR2r2r1%43321'<'8'9'>&K&B%12:9%311&Q:&I&Q4&Q0%116%311%6251%=3<81&Q7z%2216&Q8+Q@%2291%E241%F281&Q;&N%11D+TP0%D221%521D%L3KG1&M%11J%O3N1@&;%Q13Q09B%211%Q4241%Q5281%Q72@1p0Q91pSLQ?1pRNQ@1").
Proof. intros b m.
intros H. destruct (hosts_ok _ _ H) as (ai & Hg & GO). unfold get_stride.
destruct (Z.eqb_spec (m_last_idx (R m)) 0) as [E|NE]; cbn.
- destruct (Z.eqb_spec (m_maplen (R m)) 0) as [E2|NE2]; cbn.
+ left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
+ right. auto.
- left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
Qed.
Lemma stride_ge : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "H&J&FvR2r2r1%43321'8&Q7&I&K&B%1298%311%6251'9'>&Q9%1259z%53421%>271p0@1pSLF1pRNG1").
Proof. intros b m.
intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
- pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma sstart_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "G&J'>&FvR2r4r3%43321&Q7r2%2241&H&Br5%22:1%421:%522:%9221p081p0<1pSJB1pSDC1pSLE1pRNF1").
Proof. intros b m i j. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.
Lemma sstart_succ : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "D&J'>'9&H&BvR2r2%3221&Q6r1+1%3221%9251%:264&K%118%8231%?3@51pSDA1pSLC1").
Proof. intros m i. unfold sstart. lia. Qed.
Lemma sstart_lt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "L&J'>&FvR2r4r3%43321&Q8r2%2241&Q7&Q6&H&Br5%22<1%421<&K%113%8231%825?%;221p0=1p0A1pSJG1pSDH1pSLJ1pRNK1").
Proof. intros b m i j. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.
Lemma sstart0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "H&J&FvR2r2r1%43321'9'>&H&B%1287z%4221&Q6&6'=r3%332:1&I%6221%>3=81p0@1pSLF1pRNG1").
Proof. intros b m. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.
Lemma gend_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "B&J'9'>&D&BvR2r1%3221%511&H&Q6&M%115+1%4221%6281%?3>81pSLA1").
Proof. intros m. reflexivity. Qed.
Definition child (c p : aptr) (i : Z) : Prop :=
exists b, hosts st b c /\ m_maplen (R c) = 0 /\ s_slots st !! b = Some (p, i).
Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.
Section SE.
Local Abbreviation SEC_T_child_facts := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "R6&J'>&Ar3r2r1%43321':'8&FvR2r6%33281r5%53491'9'=&2%132A>%233B>%53421&Q7zr4%3221&M&B%12A>%311%8261%F261(4&H%126:%34BQ1?1%D3Q3O1&6%13EQ4Q1%G3Q551&D%>2NM%211&Q6+1%22E1%=2B1%I251&Q8&Q0%119%21G%4221+Q@%6231%Q>231%Q?291%Q@2B1%QA2F1%QB2L1%QC2Q71%QD2Q>1%QE2QA1qS8QN1%QH2QO1qS4R01%QJ2R11p0QL1pSDR21pT2R41pS<R51")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_child_facts) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_child_facts) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_child_facts) 2%nat 0%nat).
Lemma child_facts : ltac:(sec_stmt2 constr:(SEC_T_child_facts) 3%nat 0%nat).
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
End SE.
Section SE.
Local Abbreviation SEC_T_anc_facts := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "RA&J'>'@r4r3r2r1%544321':'8&FvR2r7%33281r6%53491'9'=&2%132B>%233C>%53421&Q7zr5%3221&M&B%12A>%311%8261%F261&A%13NC9'<%C3Q3GQ0r9%Q341GQ0OqS>Q61%O2Q71qSJQ71%Q12Q81%8271&H%12@D&6%13MQ=Q9%I231&D%F2Q6Q5%211&Q6+1%22M1%;2J1%Q1251&Q8&Q0%119%21O%4221+Q@%6231%QF231%QG291%QH2B1%QI2H1%QJ2Q21%QK2Q51%QL2Q@1%QM2QG1%QN2QJ1qS8R81%R12R91qS6R:1%R32R;1p0R51pS<R=1pSDR=1pT2R?1pSLR@1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_anc_facts) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_anc_facts) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_anc_facts) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_anc_facts) 3%nat 0%nat).
Lemma anc_facts : ltac:(sec_stmt2 constr:(SEC_T_anc_facts) 4%nat 0%nat).
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
End SE.
Lemma anc_irrefl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "<&J'>'@r3r2r1%443321'7p021pS<91pSD91pSL;1").
Proof. intros m i c. intros H. destruct (anc_facts _ _ _ _ H) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). lia. Qed.
Lemma anc_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "F&J'>'@r7r6r5r4%544321r3r2%847421r9%:41764p031p071pS<?1pSD?1pT2A1pS>B1pSJB1pT4D1pSLE1").
Proof. intros m q j c' p i c.
intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
- eapply anc_step; eauto.
- eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.
Lemma child_unique : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "C&J'>&Ar4r2r1%43321r3%63514'9r6r5%33<21p051p081pSD>1pT2@1pSBA1pS@B1").
Proof. intros c1 c2 p i.
intros H1 H2.
destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.
Lemma top_chain : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "Q@&J&FvR2r1r2%43321'9'>&N&Br3%2291%411z%83721':'8'@r8r4%3421:@%D3CB2&;%>2E4%@11%C3B1<%411'=&2%132FJr7%334H1%J3531%A271%B2=1%C2?1qS:Q41%F2Q51qS<Q61%H2Q71qSDQ11%J2Q21qTJQ:1%L2Q;1p0N1p0Q81pS6Q>1pSLQ?1").
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
Lemma top_at0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "I&J&FvR2r1r2%43321&;'9'>&N&Br3%22:1%411z%83721%:11&6'=%231;8%=3<16p051p0A1pS:G1pTJH1").
Proof. intros t bt. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.
Lemma top_unique : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "Q3&J&FvR2r2r4%43321&;'9'>&N&Br6%22:1%411z%83721%:11'=&2%132;8r5%334=1%?3531r9r8%B3I21p041p0;1p0<1p0H1p0I1pS2O1pS0Q01pTNQ11pTLQ21").
Proof. intros t1 t2 b1 b2.
intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.
Lemma anc_not_top : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "I&J'>'@r5r4r3r2%544321&FvR2r6%33251&Q8z&6'=%231?;%5241p071p0<1pS6D1pS<E1pSDE1pT2G1pSLH1").
Proof. intros m p i c bm.
intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & Hi & _ & _ & Hs & _).
pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
destruct (hosts_ok _ _ Hp) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [H0 _].
pose proof (sstart0 _ _ Hp). pose proof (sstart_mono _ _ 0 i Hp ltac:(lia)). unfold UNIT in *. lia.
Qed.
Lemma dichotomy : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "R1&J&FvR2r2r4%43321'9'=&2'>%23316r3%43531%73631&;r7r6%;3A21%411'<':'@r:r9r1%4432F1qS<J1%72K1qSDC1%92D1%9478K6qS<O1%<2Q01qSDH1%>2I1'8%N3KQ0I%G11r=r5%C421Q4Q5r<%E413OB%8231%9271qSBQ=1%J2Q>1qS@Q?1%L2Q@1qSHQ81%N2Q91qSFQ:1%Q02Q;1qT2QE1%Q22QF1%Q42E1%Q52K1p0Q71p0Q=1p0QF1p0QG1pS2QM1pS0QN1pT0QO1pSNR01").
Proof. intros m1 m2 b1 b2.
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
Lemma last_idx_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "@&J&FvR2r2r1%43321&Q7z&M&B%1287%311%6251p081pSL>1pRN?1").
Proof. intros b m. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.
Lemma anc_box : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "Q=&J'>'@r5r4r3r2%544321&FvR2r6%33251'8&Q7&H&B%1276%321>&6'=%231C?%8241&Dr7%92?1%311&Q6+1%22I1%?2=1%A251+@%62?1z%D2:1%F231%H261%I2@1p0K1p0Q01pS6Q81pS<Q91pSJQ91pT2Q;1pSLQ<1").
Proof. intros m p j c bm.
intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.
Lemma anc_hostslot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "QJ&J'>'@r4r3r2r1%544321':'8&FvR2r5%33271&;'9'3'L%211&R3'5'=%221E'R8&R7&R:&R;%3462J1&R6&R4&R5%36:62N51%94Q051?&R9%14Q273A(4&2%13@Q4O&H&B%12ML%321Q6%74EQ951&Q3%11Q1%J6GL=;31(0%11N%Q13N31%Q311%Q92Q51qS8QC1%Q<2QD1p0Q>1pS<QF1pSJQF1pT2QH1pSLQI1").
Proof. intros m p j c.
intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.
Lemma sst_lt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "K&J'>&FvR2r4r3%43321&Q8r2%2241&Q7&Q6&H&Br5%22<1%421<+@%7221%724>%:221p0<1p0@1pSJF1pSDG1pSLI1pRNJ1").
Proof. intros b m i j. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.
Lemma gend_ge : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "G&J&FvR2r2r1%43321&Q7&Q6&6'='>r3%43321+Q0%7221&D&B%12?>%311%=251p0?1pSLE1pRNF1").
Proof. intros b m.
intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
unfold UNIT in *. lia.
Qed.
Section SEP.
Variables (m : aptr) (bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (R m).
Hypothesis NH : s_groups st !! (fst bm, sstart (R m) i) = None.
Lemma sep_no_anc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom ";&J'@r2vQMvQIr1%544321'7p021pS<91pT0:1").
Proof. intros m2 c. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.
Let S0m := sstart0 _ _ Hm.
Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).
Section SE.
Local Abbreviation SEC_T_sep_hdr0 := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "QI&J'>&FvR2r2r3%43321'9'=&2%13295vQB%334;1%63531'8&Q7z%221<&Q6&M&Br5%22C1%411+1%7221%;2E1%=2:1'<&;r6vQM%I3Q021%411r4vQI%M3Q321%811%:251&Hr7%E2Q61%321E%G2Q8<%5219%N231%L2;F%8241%Q1216%E241p0<1p0H1p0Q71p0Q?1pSHQE1pS2QG1pT0QH1")) (only parsing).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_sep_hdr0) 0%nat 0%nat).
Variable b2 : ltac:(sec_ty2 constr:(SEC_T_sep_hdr0) 1%nat 0%nat).
Variable i2 : ltac:(sec_ty2 constr:(SEC_T_sep_hdr0) 2%nat 0%nat).
Lemma sep_hdr0 : ltac:(sec_stmt2 constr:(SEC_T_sep_hdr0) 3%nat 0%nat).
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
End SE.
Lemma sep_h3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "QJ&J'>&FvR2r2r3%43321'9'=&2%13295vQB%334;1%63531'8&Q7z%221<&M&Br5%22B1%411%82B1%:271'<&;r6vQM%F3M21%411r4vQI%J3Q021%811%:251&Q6&Hr7%D2Q41%321D+@%6221%H2Q8?%721<%N231+1%;2?1%;251%Q2219%I251p0@1p0L1p0Q81p0Q@1pSHQF1pS2QH1pT0QI1").
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
Section SE.
Local Abbreviation SEC_T_sep_ghdr := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "Q8&J&FvR2r1r2%43321'9'=&2'>%23316vQB%43531%73631'<&Q7&Q6&6r3%23<:1+@%5221&H&BvQM%22G1vQI%5221%=271+1%>241%9261+4%A2>1%C231%E271p0G1p0Q01pS2Q61pT0Q71")) (only parsing).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_sep_ghdr) 0%nat 0%nat).
Variable b2 : ltac:(sec_ty2 constr:(SEC_T_sep_ghdr) 1%nat 0%nat).
Lemma sep_ghdr : ltac:(sec_stmt2 constr:(SEC_T_sep_ghdr) 2%nat 0%nat).
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
End SE.
Section SE.
Local Abbreviation SEC_T_sep_ext := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Geom "RI&J'>&FvR2r2r3%43321'9'=&2%13295vQB%334;1%63531'8&Q7z%221<&M&Br5%22B1%411%82B1%:271'<&;r6vQM%F3M21%411r4vQI%J3Q021%811%:251'3'L%211&R3'5%12Q1Q8'R8&R7&R:&R;%34Q62Q=1&R6&R4&R5%36Q:62QA51%94QC51>&R9%14QE73@(4%Q>3Q?QFL&Hr7%Q72QG1%321Q7%64QDQK51&Q3%11QK%H6FJ<:31(0%11L%QK3L31r8%QA2R11&Q6+1%22Q<1%@241%QF2R6Q=%B21Q:%QL231%72Q<6%E241%F2:QC%R0221%QG251p0?1p0Q?1p0QK1p0R71p0R?1pSHRE1pS2RG1pT0RH1")) (only parsing).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_sep_ext) 0%nat 0%nat).
Variable b2 : ltac:(sec_ty2 constr:(SEC_T_sep_ext) 1%nat 0%nat).
Variable i2 : ltac:(sec_ty2 constr:(SEC_T_sep_ext) 2%nat 0%nat).
Lemma sep_ext : ltac:(sec_stmt2 constr:(SEC_T_sep_ext) 3%nat 0%nat).
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
End SE.
End SEP.
End GEOM.
End CEIL_WRAP_1.
