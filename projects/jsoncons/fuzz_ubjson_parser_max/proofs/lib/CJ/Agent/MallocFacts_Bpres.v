(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocTree MallocBlocks MallocKit_B MallocFacts_B MallocModel_B.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocFacts_Bpres () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_Bpres."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_Bpres.CEIL_WRAP_3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_Bpres.CEIL_WRAP_4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."; "stdpp.option."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1id"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1reflect"; "1snd"; "1true"; "2and"]; ["2eq"; "2ex"; "2iff"; "2not"; "2or"; "3Forall"; "4N"; "4Z"; "0LB"; "5blk_slot"; "5block"; "6CINV"; "6blk_ok"; "6ci_gmeta"; "6ci_heads_t"; "6ci_homog"]; ["6ci_links_t"; "6ci_slots"; "6gmeta_ok"; "6hdr_known"; "6hosts"; "6is_gm"; "6slot_free"; "6sstart_of"; "8KINV"; "8LG"; "8LPRE"; "8amc"; "8geom_eq"; "8kctx"; "8ntf_frame"; "8same_but_links"]; ["8usage_ok"; "9ZINV"; "7KINV"; "7LPRE"; "7data_of"; "7same_but_links"; ":fm_st"; ":queue_st"; ";act_of"; ";act_st"; ";aor_st"; ";deq_mid"; ";fg_usage_st"; ";grp_del"; ";pd_st"; "<meta_slot"]; ["=LActive"; "=UNIT"; "=aadd"; "=active"; "=aptr"; "=aptr_eqb"; "=area"; "=bit"; "=brkstate"; "=c_brk"; "=c_free_meta_head"; "=c_secret"; "=c_seq"; "=conc"; "=cptr"; "=ctx"]; ["=del_slots"; "=dequeue"; "=get_head"; "=get_meta_rec"; "=get_shadow"; "=get_stride"; "=ghdr"; "=lhead"; "=m_avail"; "=m_freeable"; "=m_freed"; "=m_last_idx"; "=m_maplen"; "=m_mem"; "=m_next"; "=m_prev"]; ["=m_set_next"; "=m_set_prev"; "=m_sizeclass"; "=mask_upto"; "=mctx"; "=meta"; "=meta0"; "=mstate"; "=optr"; "=put_meta"; "=record_seq"; "=region"; "=s_areas"; "=s_ctx"; "=s_groups"; "=s_metas"]; ["=s_regions"; "=s_reserved"; "=s_shadow"; "=s_slots"; "=s_tick"; "=set_active"; "=set_head"; "=set_usage"; "=shadow"; "=slot_start'"; "=step_seq"; "=upd_ctx"; "=upd_meta"; ">incl"; "?add"; "?eqb"]; ["?land"; "?ldiff"; "?le"; "?leb"; "?lor"; "?lt"; "?mul"; "?pow"; "?testbit"; "0X"; "0Zs"; "0Zs'"; "0a"; "0act"; "0an"; "0avail"]; ["0b"; "0b1"; "0blk"; "0c"; "0c'"; "0cnt"; "0f"; "0freed"; "0g"; "0gh"; "0h"; "0hd"; "0i"; "0i1"; "0j"; "0li"]; ["0m"; "0n"; "0nx"; "0p"; "0pv"; "0q"; "0r"; "0r'"; "0rid"; "0s"; "0sc"; "0sc'"; "0st"; "0st'"; "0st0"; "0st1"]; ["0stA"; "0stB"; "@delete"; "@lookup"; "AN_countable"; "AZ_countable"; "Aprod_countable"; "Bprod_eq_dec"; "Cmap_delete"; "Dgmap"; "Dgmap_lookup"; "Dgmap_partial_alter"; "Eeq_dec"; "Feq_dec"; "Gfrom_option"; "0stride"]; ["0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).
End CEIL_WRAP_1.
Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
data_of meta0] in *.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma aptr_eqb_spec' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";&R4'<'@r2r1%33521&R5%1243%7231pY291pXJ:1").
Proof. intros a b.
destruct (aptr_eqb a b) eqn:E; constructor.
- apply aptr_eqb_eq. exact E.
- intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.
End CEIL_WRAP_2.
Ltac case_ptr x y := destruct (aptr_eqb_spec' x y) as [?EQ|?NE]; [subst x|].
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Lemma rec_upd st g f x :
get_meta_rec (upd_meta g f st) x = if aptr_eqb x g then f (get_meta_rec st g) else get_meta_rec st x.
Proof. apply get_meta_rec_upd. Qed.
Lemma rec_put st g mr x :
get_meta_rec (put_meta g mr st) x = if aptr_eqb x g then mr else get_meta_rec st x.
Proof. apply get_meta_rec_put. Qed.
Lemma data_of_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QA'S5&B'@&QDr2%211r1%411%63831'?&S8&RM%118%217%<3421'G&RH%11=%21<%A3421&RJ%11A%21@%E3821&RK%11E%21D%I3<21&RI%11I%21H%M3@21&S2%11M%21L%Q13D21&RL%11Q1%21Q0%Q53H21%O251%Q02:1%Q12?1%Q22D1%Q32I1%Q42O1%Q=2Q61pZ@Q?1pZ>Q@1").
Proof. intros r r'.
destruct r, r'; unfold data_of; msimp; split.
- intros H. inversion H. repeat split; reflexivity.
- intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.
Lemma get_stride_data : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S5'@&QDr2%211r1%411%63731'G&REr3%211%319%<3521p071pZ@?1pZ>@1").
Proof. intros r r'. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.
Lemma slot_start'_data : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S5'G'@&QDr3%211r2%411%63831&R4&SIr4%2216%3297%<3521p071pYJ?1pZ@A1pZ>B1").
Proof. intros r r' i. intros H. unfold slot_start'. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
Lemma sstart_of_data : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "B'S5'G'@&QDr3%211r2%411%63831&Q7r4%2215%3286%;3<21p061pYJ>1pZ@@1pZ>A1").
Proof. intros r r' i. intros H. unfold sstart_of. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
Lemma slot_free_data : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S5'G'@&QDr3%211r2%411%63831&B&Q6r4%2216%3297%5221p071pYJ?1pZ@A1pZ>B1").
Proof. intros r r' i. intros H. apply data_of_eq in H. unfold slot_free. destruct H as (_ & -> & -> & _). tauto. Qed.
Definition kctx (st : mstate) : Prop :=
0 <= c_seq (ctx st) < 256
/\ (forall i, 0 <= bounces st i < 256) /\ (forall i, 0 <= unmap_seq st i < 256)
/\ 0 <= c_secret (ctx st) < 2^64.
Definition usage_ok (st : mstate) (c : Z) : Prop := forall sc, c <= sc -> 0 <= usage st sc < 2^64.
Record KINV (st : mstate) (LB : list block) (c : Z) : Prop := mkKI {
ki_links : ci_links_t st;
ki_heads : ci_heads_t st;
ki_hom : ci_homog st;
ki_gmetas : ci_gmeta st;
ki_grps : ci_groups st;
ki_ginj : ci_group_inj st;
ki_slts : ci_slots st;
ki_sltt : ci_slots_total st;
ki_unk : ci_ghdr_unk st;
ki_h0 : ci_hdr0 st;
ki_blks : Forall (blk_ok st) LB;
ki_nodup : List.NoDup (map blk_slot LB);
ki_cx : kctx st;
ki_usage : usage_ok st c;
ki_bk : ci_brk st;
ki_ticks : ticks_ok st
}.
Lemma KINV_of_CINV : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S7'7&J%211'Kr2r1%3221'Q8r3z%33261p051pQB:1pZJ>1").
Proof. intros st LB.
intros C. pose proof (ci_cx _ _ C) as (S1 & S2 & S3 & S4 & S5).
constructor; try (destruct C; assumption).
- unfold kctx. repeat split; try apply S1; try apply S2; try apply S3; try apply S5.
- intros sc _. apply S4.
Qed.
Lemma KINV_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'S7'7&J%211'G'Q8r4r3r2%43321&T2%1243r6r5%93217p041p071pY:=1pY8>1pQB@1pZJD1").
Proof. intros st LB c c'. intros K Hc. pose proof (ki_usage _ _ _ K) as U. destruct K; constructor; auto. intros sc Hsc. apply U. lia. Qed.
Section EXT.
Variables st st' : mstate.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis ES : s_shadow st' = s_shadow st.
Lemma meta_slot_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ":&R4&B&QOvU<r1%3221vU=%5213%7231pYB91").
Proof. intros g. unfold meta_slot. rewrite EA. tauto. Qed.
Lemma get_shadow_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";'F'@'SH&RDvU=r1%3221vU<%5213%83731pZB:1").
Proof. intros rid. unfold get_shadow. rewrite ES. reflexivity. Qed.
Lemma conc_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";&R4'@'G&R=vU=r1%3221vU<%5213%83731pZ<:1").
Proof. intros q. unfold conc, get_region. rewrite ER. reflexivity. Qed.
Hypothesis EL : forall x, m_next (get_meta_rec st' x) = m_next (get_meta_rec st x) /\ m_prev (get_meta_rec st' x) = m_prev (get_meta_rec st x).
Lemma links_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "6'Q0vU<%211vU=%411p031").
Proof.
intros [N P NN SF]. constructor.
- intros m nx H. destruct (EL m) as [E1 _]. rewrite E1 in H. destruct (N m nx H) as [H1 H2].
destruct (EL nx) as [_ E2]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
- intros m pv H. destruct (EL m) as [_ E1]. rewrite E1 in H. destruct (P m pv H) as [H1 H2].
destruct (EL pv) as [E2 _]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
- intros m. destruct (EL m) as [E1 E2]. rewrite E1, E2. apply NN.
- intros m H. destruct (EL m) as [E1 _]. rewrite E1 in H. apply meta_slot_ext. apply SF. exact H.
Qed.
End EXT.
Lemma hosts_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q2'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'RF%<4>621&S>r3%211r4%411%C3631&B&Q4r2%23681r5%431:3%6231p081pYBM1pY2N1pZLQ01pZJQ11").
Proof. intros st st' b g. intros E. unfold hosts. rewrite E. tauto. Qed.
Lemma is_gm_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q0'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'RF%<4>621&S>r2%211r3%411%C3631&B&Q5%1257r4%3219%5231p071pYBL1pZLN1pZJO1").
Proof. intros st st' g. intros E. unfold is_gm. split; intros [b H]; exists b; [rewrite <- (hosts_ext st st')|rewrite (hosts_ext st st')]; auto. Qed.
Record LPRE (st : mstate) (LB : list block) (c : Z) (g p : aptr) (i : Z) : Prop := mkLP {
lp_hosts : hosts st p g;
lp_i : 0 <= i <= m_last_idx (get_meta_rec st g);
lp_nonfree : ~ slot_free (get_meta_rec st g) i;
lp_nogroup : (s_groups st) !! (slot_start' (get_meta_rec st g) i) = None;
lp_noblock : Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) i) LB;
lp_class : c <= m_sizeclass (get_meta_rec st g)
}.
Lemma lpre_gmeta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'S7'7&J%211'G&R4'Q8r6r5r4%43321'Q:r7r3r2%46387621'Q2r8%231:9p041p0:1pYJA1pZ8A1pYBB1pY8D1pQBF1pZJJ1").
Proof. intros st LB c g p i. intros K L. apply (ki_gmetas _ _ _ K). apply (lp_hosts _ _ _ _ _ _ L). Qed.
Lemma kinv_next : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R5'S7'7&J%211'G&R4'Q8r5r4r3%43321'@&S8&RN&RCr6%2217%411(1r2%22?1%:3941'?&QOr7%221@&RO%=23B%211%;2HE%C3B21&C%C15(0%11M%H3G31%511'Ar8%I21Q0%>11r1%H2Q51%Q03O31%E263%O274%Q111%M2Q:Q8%Q53Q421%Q63Q<Q9Q:%C11%Q83Q>Q0Q4%E11p031%Q0261%Q12;1%Q22=1qZ:QD1%E2QE1%Q52G1%Q62N1%Q72Q41p0Q91p0QE1pZ6QK1pYBQL1pY8QN1pQBR01pZJR41").
Proof. intros st LB c g nx.
intros K NX. pose proof (ki_links _ _ _ K) as [N P NN SF].
destruct (N g nx NX) as [P1 S1]. split; [exact S1|]. split; [exact P1|]. split.
{ intros E. apply (proj1 (NN nx)) in E. rewrite E in P1. discriminate. }
destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV.
2:{ apply (proj2 (NN g)) in PV. rewrite PV in NX. discriminate. }
destruct (P g pv PV) as [N2 S2]. exists pv. repeat split; auto.
intros NE ->. rewrite N2 in NX. inversion NX. subst. apply NE. reflexivity.
Qed.
Lemma kinv_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R:'S7'7&J%211'G&R4'Q8r5r4r3%43321'@&S8&R3r6%2216(1r2%22=1%83741'?&T2z%221?&T5+Q@%22B1%7241&QOr7%221E&C&RN&RC%125I%311(0%11Q0%K3J31%811&Q5%12<Q0&S2%119%Q13Q81Q4'A&ROr8%?21Q8%311r1%Q32Q>1%Q93Q831%I263%E274%G11%Q82QCQ@%Q>3Q=21%Q6251%Q7271qZ:QG1%@2QH1%Q:2B1%Q;2F1%Q<2I1%Q=2Q31%Q>2Q71p0Q@1p0QJ1pXJR01pZFR21pY8R31pQBR51pZJR91").
Proof. intros st LB c sc a.
intros K HA. pose proof (ki_heads _ _ _ K) as [_ CA]. destruct (CA sc a HA) as (SC & NX & GM & SCa).
pose proof (ki_links _ _ _ K) as [N P NN SF].
split; [exact SC|]. split; [apply SF; exact NX|]. split; [exact NX|]. split; [exact GM|]. split; [exact SCa|].
destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:PV.
2:{ apply (proj2 (NN a)) in PV. exfalso. exact (NX PV). }
exists pv. destruct (P a pv PV) as [N2 S2]. auto.
Qed.
Lemma kinv_free_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QO'S7'7&J%211'G&R4'Q8r4r3r2%43321'@&S8&R:&R?r5%211%411(1%12>:%93831'?&QOr6%221@&C&RN&RC%125D%311(0%11J%E3D31%811&Q5%12<K%;11'A&ROr7%=21Q1%311r1%I2Q61%Q13Q031%G263%C274%E11%N2Q;Q9%Q63Q521%M251%N271qZ:Q?1%@2Q@1%Q12B1%Q22F1%Q32Q01p0Q51p0Q@1pYFQF1pY8QH1pQBQJ1pZJQN1").
Proof. intros st LB c h.
intros K HF. pose proof (ki_heads _ _ _ K) as [CF _]. destruct (CF h HF) as (NX & MM).
pose proof (ki_links _ _ _ K) as [N P NN SF].
split; [apply SF; exact NX|]. split; [exact NX|]. split.
{ intros [b [ai Hb]]. pose proof (go_mem _ _ _ (ki_gmetas _ _ _ K b h (ex_intro _ ai Hb))) as MEM. congruence. }
destruct (m_prev (get_meta_rec st h)) as [pv|] eqn:PV.
2:{ apply (proj2 (NN h)) in PV. exfalso. exact (NX PV). }
exists pv. destruct (P h pv PV) as [N2 S2]. auto.
Qed.
Lemma kinv_fm_facts_raw : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QM'S7'7&J%211'G&R4'Q8r4r3r2%43321'@&S8&RN&RCr5%2217%411(0%11>%93831&R:&R?r7%211%411(1r1%22G1%B3A41'?&C%E3KGA%211&QOr8%221K'A&ROr9%J21Q0%311%O3N1>r6%Q13Q7A1%>11%<27C%A221%B261qZ:Q<1%=2Q=1%E2?1%F2C1p0H1pYFQA1p0Q31p0Q>1pYBQD1pY8QF1pQBQH1pZJQL1").
Proof. intros st LB c g.
intros K GN h HF. destruct (kinv_free_head st LB c h K HF) as (S1 & N1 & _ & pv & P1 & S2 & N2).
split; [congruence|]. split; [exact S1|]. exists pv. repeat split; auto. congruence.
Qed.
Lemma hosts_is_gm : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ">'S7&R4&Q4r3r2r1%43321&Q5r4%2215p041pYB:1pY2;1pZJ=1").
Proof. intros st b g. intros H. exists b. exact H. Qed.
Definition LG (st : mstate) (q : aptr) : Prop := m_next (get_meta_rec st q) <> None \/ is_gm st q.
Definition amc (c : mctx) :=
(c_avail_meta c, c_meta_area_head c, c_meta_area_tail c, c_avail_meta_areas c, c_init_done c,
c_mmap_counter c, c_avail_meta_count c, c_avail_meta_area_count c, c_meta_alloc_shift c).
Record ntf_frame (st st' : mstate) : Prop := mkNF {
nf_amc : amc (ctx st') = amc (ctx st);
nf_regions : s_regions st' = s_regions st;
nf_shadow : s_shadow st' = s_shadow st;
nf_areas : s_areas st' = s_areas st;
nf_reserved : s_reserved st' = s_reserved st;
nf_tick : s_tick st' = s_tick st;
nf_brk : c_brk (ctx st') = c_brk (ctx st);
nf_secret : c_secret (ctx st') = c_secret (ctx st);
nf_groups : forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh;
nf_slots : forall s x, (s_slots st') !! s = Some x -> (s_slots st) !! s = Some x;
nf_linked : forall q, m_next (get_meta_rec st' q) <> None -> LG st q;
nf_metas : forall q, ~ LG st q -> get_meta_rec st' q = get_meta_rec st q
}.
Lemma frame_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "5'S7'Q>r1%2211pZJ41").
Proof. intros st. constructor; auto. intros q H. left. exact H. Qed.
Lemma LG_frame : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S7&R4'Q>r3r2%3221&Q9%1243r5%3216p031p061pZ<;1p[2=1pZJ>1").
Proof. intros st stA q.
intros FR [H|[b [ai Hb]]]. { apply (nf_linked _ _ FR). exact H. }
right. exists b, ai. apply (nf_groups _ _ FR). exact Hb.
Qed.
Lemma frame_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'S7&R4'S5p011'Q>r4r3%3221&Q9r5%2214r6&SL%13874%:231p051p091pY>>1pZ<A1p[2C1pZJD1").
Proof. intros st stA q f.
intros FR Hq. destruct FR. constructor; auto.
- intros q' H. rewrite rec_upd in H. destruct (aptr_eqb_spec' q' q); [subst; exact Hq| auto].
- intros q' H. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; tauto| auto].
Qed.
Lemma frame_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7&R4'S5'Q>r4r3%3221&Q9r5%2214r6&S9%13874%:231p051p091pZ>>1pZ<@1p[2B1pZJC1").
Proof. intros st stA q r. intros. rewrite <- (upd_meta_put stA q (fun _ => r)). apply frame_upd_meta; auto. Qed.
Lemma frame_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QE'S7'S4p\411'Q>r3r2%3221'@'R8&R9&S=%117%711%411%513%83721'G&R;r4%911%@11%411%513%@3721';&S8%2211%3212%4213%521=%621>%721?%821@%921A&Q;r5%J11%C11%411%513%Q13721r7&SKr6%2291%Q:241p061p0H1p0Q11p0Q;1pY>Q@1p[2QC1pZJQD1").
Proof. intros st stA f.
intros FR E1 E2 E3. destruct FR. constructor; auto.
- unfold ctx in *. cbn. congruence.
- unfold ctx in *. cbn. congruence.
- unfold ctx in *. cbn. congruence.
Qed.
Lemma frame_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'G&S8'Q>r4r3%3221r5&SEr2%23516%8241p061p\2;1pZF=1p[2?1pZJ@1").
Proof. intros st stA sc v. intros FR. unfold set_active. apply frame_ctx; auto; reflexivity. Qed.
Lemma frame_set_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'RG&S8'Q>r4r3%3221r5&SFr2%23516%8241p061p\2;1pYF=1p[2?1pZJ@1").
Proof. intros st stA h v. intros FR. destruct h; cbn; [apply frame_set_active| apply frame_ctx]; auto; reflexivity. Qed.
Lemma frame_grp_del : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S7&R4'Q>r4r3%3221r5&QMr2%23651%8241p061pZ8;1pYB<1p[2>1pZJ?1").
Proof. intros st stA g p.
intros FR. destruct FR. unfold grp_del, del_slots, del_group. constructor; cbn; auto.
- intros b gh Hb. apply nf_groups0. apply lookup_delete_Some in Hb. tauto.
- intros s x Hs. apply nf_slots0.
revert Hs. generalize (s_slots stA). intros tb.
match goal with |- context [Z.iter ?n ?F (0, tb)] => set (f := F) end.
assert (GEN : forall acc, (snd (Z.iter (m_last_idx (get_meta_rec stA g) + 1) f acc)) !! s = Some x -> (snd acc) !! s = Some x).
{ intros acc. unfold Z.iter. destruct (m_last_idx (get_meta_rec stA g) + 1); cbn; auto.
revert acc. induction p0 using Pos.peano_ind; intros acc.
- cbn. unfold f at 1. destruct acc as [j t]. cbn. rewrite lookup_delete_Some. tauto.
- rewrite Pos.iter_succ. unfold f at 1. destruct (Pos.iter f acc p0) as [j t] eqn:E. cbn.
rewrite lookup_delete_Some. intros [_ H]. apply IHp0. rewrite E. exact H. }
apply (GEN (0, tb)).
Qed.
Lemma frame_aor : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7&R4'G'Q>r4r3%3221&Q9r5%2214r6&QJ%13487%:231p051p091pYJ>1pYB@1p[2B1pZJC1").
Proof. intros st stA g i. intros. unfold aor_st. apply frame_upd_meta; auto. Qed.
Lemma frame_act : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7&R4'G'Q>r4r3%3221&Q9r5%2214r6&QI%13487%:231p051p091pXL>1pXJ@1p[2B1pZJC1").
Proof. intros st stA a act. intros. unfold act_st. apply frame_upd_meta; auto. Qed.
Lemma frame_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'S7'RG&R4'Q>r4r3%3221'Q0%114&Q9r6%2216r7&RAr5%231;5%=241p061p0:1p0=1pYBB1pYFD1p[2F1pZJG1").
Proof. intros st stA h g.
intros FR CL Hg. unfold dequeue.
apply frame_upd_meta; [|exact Hg].
destruct (negb (optr_eqb (m_next (get_meta_rec stA g)) (Some g))); [|apply frame_set_head; exact FR].
set (st1 := match m_prev (get_meta_rec stA g) with Some pv => _ | None => stA end).
assert (F1 : ntf_frame st st1).
{ subst st1. destruct (m_prev (get_meta_rec stA g)) as [pv|] eqn:PV; [|exact FR].
apply frame_upd_meta; [exact FR|]. apply (LG_frame st stA pv FR). left.
destruct (cl_prev _ CL g pv PV) as [N _]. rewrite N. discriminate. }
set (st2 := match m_next (get_meta_rec stA g) with Some nx => _ | None => st1 end).
assert (F2 : ntf_frame st st2).
{ subst st2. destruct (m_next (get_meta_rec stA g)) as [nx|] eqn:NX; [|exact F1].
apply frame_upd_meta; [exact F1|]. apply (LG_frame st stA nx FR). left.
destruct (cl_next _ CL g nx NX) as [P _]. intros E. apply (proj1 (cl_none _ CL nx)) in E. rewrite E in P. discriminate. }
destruct (optr_eqb (get_head st2 h) (Some g)); [apply frame_set_head|]; exact F2.
Qed.
Lemma frame_queue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q>'S7'RG&R4'Q>r4r3%3221'Q0%114'@&S8&RBr6r5%3221(1r1%22?1%93841&C&RN&RCr7r2%3221%511(0%11I%C3B31%:11p0<1pYHM1&Q9%12;Mr8&QG%13HG>%Q2231p051p081p0Q01p0Q31pYBQ81pYFQ:1p[2Q<1pZJQ=1").
Proof. intros st stA h g.
intros FR CL HH Hg. unfold queue_st, fm_link, fm_single.
destruct (get_head stA h) as [hd|] eqn:HD.
- specialize (HH hd eq_refl).
apply frame_upd_meta.
+ destruct (m_prev (get_meta_rec stA hd)) as [pv|] eqn:PV.
* apply frame_upd_meta; [apply frame_upd_meta; [exact FR| exact Hg]|].
apply (LG_frame st stA pv FR). left. destruct (cl_prev _ CL hd pv PV) as [N _]. rewrite N. discriminate.
* apply frame_upd_meta; [exact FR| exact Hg].
+ apply (LG_frame st stA hd FR). left. exact HH.
- apply frame_set_head. apply frame_upd_meta; [exact FR| exact Hg].
Qed.
Lemma frame_fm : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QA'S7&R4'Q>r3r2%3221'Q0&S9&S6%23516%411'@&S8&R:&R?r5%211%411(1r1%22C1%:3941&C&RN&RCr6%C3;B1%321G%511(0%11M%D3C31%:11p0<1pYHQ11&Q9r4%22<1r7&QF%12?I%Q7231p051p091p0Q21p0Q81pYBQ=1p[2Q?1pZJQ@1").
Proof. intros st stA g.
intros FR CL HH Hg. unfold fm_st. apply frame_queue; auto. apply frame_put_meta; auto.
Qed.
Lemma frame_seq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S7'G'Q>r3r2%3221r4&S:&SJ%116%3261%9251p071pZF<1p[2>1pZJ?1").
Proof. intros st stA sc.
intros FR.
assert (F1 : ntf_frame st (step_seq stA)).
{ unfold step_seq. destruct (c_seq (ctx stA) =? 255); apply frame_ctx; auto; reflexivity. }
unfold record_seq. destruct (sc_in_seq_range sc); [apply frame_ctx; auto; reflexivity| exact F1].
Qed.
Lemma frame_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ">'S7&R4'Q>r3r2%3221r4&QL%1254%7231p051pYB:1p[2<1pZJ=1").
Proof. intros st stA g. intros FR. unfold fg_usage_st. destruct (m_sizeclass _ <? 48); [unfold set_usage; apply frame_ctx|]; auto; reflexivity. Qed.
Record same_but_links (st st' : mstate) : Prop := mkSBL {
sbl_data : forall q, data_of (get_meta_rec st' q) = data_of (get_meta_rec st q);
sbl_regions : s_regions st' = s_regions st;
sbl_shadow : s_shadow st' = s_shadow st;
sbl_areas : s_areas st' = s_areas st;
sbl_groups : s_groups st' = s_groups st;
sbl_slots : s_slots st' = s_slots st;
sbl_tick : s_tick st' = s_tick st;
sbl_reserved : s_reserved st' = s_reserved st;
sbl_brk : c_brk (ctx st') = c_brk (ctx st);
sbl_secret : c_secret (ctx st') = c_secret (ctx st);
sbl_seq : c_seq (ctx st') = c_seq (ctx st);
sbl_usage : forall sc, usage st' sc = usage st sc;
sbl_bounces : forall j, bounces st' j = bounces st j;
sbl_unmap : forall j, unmap_seq st' j = unmap_seq st j;
sbl_fmh_or : True
}.
Lemma sbl_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "5'S7'Q?r1%2211pZJ41").
Proof. intros st. constructor; auto. Qed.
Lemma sbl_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "<'S7'Q?r3r2%3221r5%5214p031p041pY891pY2:1pXJ;1").
Proof. intros a b c. intros [] []; constructor; intros; try congruence. Qed.
Lemma data_of_links : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S5p\411'@&QDr3r1%211%411%513%73921pZ>:1r2%811%:11%;13%=3?21p061pZ>A1pY>A1").
Proof. intros f r. auto. Qed.
Lemma sbl_upd_links : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "G'S7&R4'S5p\411'@&QDr2r1%211%411%513%73921pZ>:1'Q?r4&SLr3%231;3%5241p071pY>A1pZ<D1pZJF1").
Proof. intros st q f.
intros Hf. constructor; try reflexivity.
intros q'. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; apply Hf| reflexivity].
Qed.
Lemma sbl_set_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "='S7'RG&S8'Q?r3&SFr2r1%33214%6251p\281pYF:1pZJ<1").
Proof. intros st h v. destruct h; cbn; constructor; try reflexivity. Qed.
Lemma data_set_prev : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "=&S8'S5'@&QD&S1r2r1%3221%511%613%83921pZ>:1p\2<1"). Proof. intros v r. reflexivity. Qed.
Lemma data_set_next : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "=&S8'S5'@&QD&S0r2r1%3221%511%613%83921pZ>:1p\2<1"). Proof. intros v r. reflexivity. Qed.
Lemma sbl_upd_links'' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'S7&R4'S5p\411'Q?r3r4%3221'@&QDr1%611%311%413%63<21pZ>=1r5&SLr6%23=>1%@241p061p0?1pY>D1pZ<G1pZNI1pZJJ1").
Proof. intros st st0 q f. intros S Hf. eapply sbl_trans; [exact S| apply sbl_upd_links; exact Hf]. Qed.
Lemma sbl_set_head'' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'RG&S8'Q?r3r4%3221&SFr2r5%33621%8261p061p\2;1pYF=1pZN?1pZJ@1").
Proof. intros st st0 h v. intros S. eapply sbl_trans; [exact S| apply sbl_set_head]. Qed.
Lemma sbl_queue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "='S7'RG&R4'Q?r3&QGr2r1%33214%6251pYB81pYF:1pZJ<1").
Proof. intros st h g.
unfold queue_st, fm_link, fm_single.
destruct (get_head st h) as [hd|]; [destruct (m_prev (get_meta_rec st hd)) as [pv|]|];
repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.
Lemma sbl_deq_mid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "='S7'RG&R4'Q?r3&QKr2r1%33214%6251pYB81pYF:1pZJ<1").
Proof. intros st h g.
unfold deq_mid.
destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| apply sbl_set_head].
destruct (m_prev (get_meta_rec st g)) as [pv|]; destruct (m_next (get_meta_rec st g)) as [nx|];
match goal with |- same_but_links st (if ?c then _ else _) => destruct c end;
repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.
Lemma sbl_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "='S7'RG&R4'Q?r3&RAr2r1%33214%6251pYB81pYF:1pZJ<1").
Proof. intros st h g.
rewrite dequeue_mid. apply sbl_upd_links''; [apply sbl_deq_mid|]. intros; reflexivity.
Qed.
Lemma data_of_fields : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QJ'S7&R4'@'S5&QD&RCr2r1%3221%511r3%6214%811%;3:41'?&S8&RM%<27;%211r4%?21>%511%D3741'G&RH%118%216%I3421&RJ%11<%21:%M3821&RK%11@%21>%Q13<21&RI%11D%21B%Q53@21&S2%11H%21F%Q93D21&RL%11L%21J%Q=3H21%Q2251%Q32:1%Q42?1%Q52D1%Q62I1%Q72O1p0Q91pZ<QF1pZLQH1pZJQI1").
Proof. intros st st' q. intros H. apply data_of_eq. exact H. Qed.
Lemma LPRE_sbl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'S7'7&J%211'G&R4'Q?r7r6%3221'Q:r8r5r4r3r2%66584321%766:9543p021p0:1pYJ@1pZ8@1pYBA1pY8C1pQBE1pZLI1pZJJ1").
Proof. intros st st' LB c g p i.
intros S L. pose proof (sbl_data _ _ S g) as D. destruct L. constructor.
- unfold hosts in *. rewrite (sbl_groups _ _ S). exact lp_hosts0.
- rewrite (proj1 (proj2 (proj2 (proj2 (data_of_fields st st' g D))))). exact lp_i0.
- rewrite (slot_free_data _ _ i D). exact lp_nonfree0.
- rewrite (sbl_groups _ _ S), (slot_start'_data _ _ i D). exact lp_nogroup0.
- rewrite (slot_start'_data _ _ i D). exact lp_noblock0.
- destruct (data_of_fields st st' g D) as (_ & _ & _ & _ & _ & -> & _). exact lp_class0.
Qed.
Lemma meta_slot_sbl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S7&R4'Q?r3r2%3221&QOr4%2214%3226p021p061pZ<;1pZL=1pZJ>1").
Proof. intros st st' q. intros S H. eapply meta_slot_same_areas; [apply (sbl_areas _ _ S)| exact H]. Qed.
Lemma frame_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "<'S7'Q>r3r2%3221r5%5214p031p041p[491p[2:1pZJ;1").
Proof. intros st stA stB.
intros F1 F2. pose proof (LG_frame st stA) as LGF.
destruct F1, F2; constructor; try congruence; auto.
- intros q H. apply LGF; [constructor; auto|]. apply nf_linked1. exact H.
- intros q H. rewrite nf_metas1; [apply nf_metas0; exact H|]. intros H'. apply H. apply LGF; [constructor; auto| exact H'].
Qed.
Lemma LPRE_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'S7'S4p011'7&J%211'G&R4'Q:r7r5r4r3r2r1%76654321&SKr8%2291r6%<621:987p061pYJ@1pZ8@1pYBA1pY8C1pQBE1pY>I1pZJL1").
Proof. intros st f LB c g p i. intros L. destruct L; constructor; auto. Qed.
Lemma LPRE_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "I'S7'7&J%211'G&R4'Q:r6r5r4r3r2r1%76654321&QLr7%2217%;61:9876p051pYJ?1pZ8?1pYB@1pY8B1pQBD1pZJH1").
Proof. intros st LB c g p i. intros L. unfold fg_usage_st. destruct (_ <? 48); [apply LPRE_ctx|]; exact L. Qed.
Lemma LPRE_upd_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q4'S7&R4'S5p011'7&J%211'G&C'@r7r3%33;21%511'Q:r9r6r5r4r2%66543291&SLr8r:%33921%;61?987>p061p0>1pYJE1pZ8L1pYBM1pY8H1pQBJ1pY>N1pZ<Q11pZJQ31").
Proof. intros st q f LB c g p i.
intros NE L. destruct L; constructor; auto; rewrite ?rec_upd, ?(aptr_eqb_neq g q) by congruence; auto.
Qed.
Lemma LPRE_mono_c : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'S7'7&J%211'G&R4'Q:r7r6r5r3r2r1%76654321&T2%1267r9r8r4%=632;:19p051p081pYJB1pZ8B1pYBC1pY:E1pY8F1pQBH1pZJL1").
Proof. intros st LB c c' g p i. intros L Hc. destruct L; constructor; auto. lia. Qed.
Lemma grp_del_groups : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q2'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'RF%<4>621&S>&QMr3r2r1%43321%611&UB&UH&UK%14IA=<%34J=<1%<1:%65L>291%L3?81pZ8N1pYBO1pZJQ11"). Proof. intros st g p. reflexivity. Qed.
Lemma grp_del_rec : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "B'S7&R4'@'S5&RC&QMr4r3r2%43321r1%7221%8262%;3:21pZ<=1pZ8>1pYB?1pZJA1"). Proof. intros st g p q. reflexivity. Qed.
Lemma grp_del_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'S7&R4'@'UI'F&UL&UD'S;%544321&S@&QMr3r2r1%43321%611%715%?3921pZ8A1pYBB1pZJD1"). Proof. intros st g p. reflexivity. Qed.
Lemma grp_del_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'S7&R4'@'UI'F&UL&UD'SH%544321&SB&QMr3r2r1%43321%611%715%?3921pZ8A1pYBB1pZJD1"). Proof. intros st g p. reflexivity. Qed.
Lemma grp_del_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "L'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'R6%<4>621&S<&QMr3r2r1%43321%611%715%F3921pZ8H1pYBI1pZJK1"). Proof. intros st g p. reflexivity. Qed.
Lemma grp_del_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S7&R4'@'S4&S=&QMr3r2r1%43321%611%715%:3921pZ8<1pYB=1pZJ?1"). Proof. intros st g p. reflexivity. Qed.
Lemma conc_grp_del : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "B'S7&R4'@'G&R=&QMr4r3r2%43321r1%7221%8262%;3:21pZ<=1pZ8>1pYB?1pZJA1"). Proof. intros st g p q. reflexivity. Qed.
Lemma fg_usage_rec : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S7&R4'@'S5&RC&QLr3r2%3221r1%6221%7252%:3921pZ<<1pYB=1pZJ?1").
Proof. intros st g q. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_groups : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "J'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'RF%<4>621&S>&QLr2r1%3221%511%614%E3821pYBG1pZJI1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S7&R4'@'UI'F&UL&UD'S;%544321&S@&QLr2r1%3221%511%614%>3821pYB@1pZJB1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S7&R4'@'UI'F&UL&UD'SH%544321&SB&QLr2r1%3221%511%614%>3821pYB@1pZJB1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "J'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'R6%<4>621&S<&QLr2r1%3221%511%614%E3821pYBG1pZJI1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fg_usage_slots : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'S7&R4'@'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651';%12>8%=4?731&SC&QLr2r1%3221%511%614%F3821pYBH1pZJJ1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma conc_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S7&R4'@'G&R=&QLr3r2%3221r1%6221%7252%:3921pZ<<1pYB=1pZJ?1").
Proof. intros st g q. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma fmh_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'@&S8&R:&R?&QLr2r1%3221%511%711%715%911%<3;31pYB>1pZJ@1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma seq_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'@'G&R<&R?&QLr2r1%3221%511%711%715%911%<3;31pYB>1pZJ@1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma brk_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'@'R8&R9&R?&QLr2r1%3221%511%711%715%911%<3;31pYB>1pZJ@1").
Proof. intros st g. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
Lemma hosts_grp_del : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "I'S7&R4&B&Q4&QMr5r4r3%43321r2r1%83321'?&C'@%13>68%311%>3<87%6221%A281pZ<C1pY2D1pZ8E1pYBF1pZJH1").
Proof. intros st g p b q.
unfold hosts. rewrite grp_del_groups. split.
- intros [ai H]. apply lookup_delete_Some in H. destruct H as [NE H]. split; [congruence| exists ai; exact H].
- intros [NE [ai H]]. exists ai. apply lookup_delete_Some. split; [congruence| exact H].
Qed.
Lemma links_put_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'S7&R4'Q0r2%211'@&S8&RN&RCr3%2217%411(0%11<%93831&S9&S6r4%33921%A11p061p0A1pYBE1pZJG1").
Proof. intros st g.
intros [N P NN SF] GN. pose proof (proj1 (NN g) GN) as GP.
constructor.
- intros m nx H. rewrite rec_put in H. rewrite rec_put.
destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
destruct (N m nx H) as [H1 H2]. destruct (aptr_eqb_spec' nx g); [subst; rewrite GP in H1; discriminate|].
split; [exact H1|]. unfold meta_slot in *. exact H2.
- intros m pv H. rewrite rec_put in H. rewrite rec_put.
destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
destruct (P m pv H) as [H1 H2]. destruct (aptr_eqb_spec' pv g); [subst; rewrite GN in H1; discriminate|].
split; [exact H1|]. exact H2.
- intros m. rewrite rec_put. destruct (aptr_eqb_spec' m g); [subst; cbn; tauto| apply NN].
- intros m H. rewrite rec_put in H. destruct (aptr_eqb_spec' m g); [subst; cbn in H; congruence|]. apply SF. exact H.
Qed.
Lemma seq_shape : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "RB'S7'G&S:r1&SJr2%211%5241'?'@'UI'F&UL&UD'S;%544321&S@%11>r3%311%;3531'SH%<4;:91&SB%11E%217%A3421&R4&UG&UM%24CBM1&UF&UE%26FEDQ041'RF%I48521&S>%11Q2%21D%N3421';%12>Q8%Q04?<91&SC%11Q9%21K%Q53421'R6%Q64EB?1&S<%11Q?%21Q1%Q;3421'S5%Q<4KHE1&S?%11QE%21Q7%QA3421'R8&R9&R?%11QK%311%31Q>%511%QI3731&S8&R:%117%216%QN3421%R0261%R12?1%R22F1%R32M1%R42Q51%R52QC1%R62QJ1tZLR?R81pZFR?1pXDRA1").
Proof. intros X sc.
unfold record_seq, step_seq. destruct (c_seq (ctx X) =? 255); destruct (sc_in_seq_range sc); cbn; repeat split; reflexivity.
Qed.
Lemma fm_shape : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R3'S7&R4&QFr2r1%3221'?'@'UI'F&UL&UD'S;%544321&S@%11;r3%311%;3531'SH%<4;:91&SB%11B%217%A3421&UG'G&UM%34CB21&UF&UE%26FED541'RF%I4Q0521&S>%11O%21D%N3421';%12Q6=%Q04Q7<91&SC%11Q6%21K%Q53421'R6%Q64Q=B?1&S<%11Q<%21Q1%Q;3421'R8&R9&R?%11QB%311%31Q8%511%QC3731%QE291%QF2@1%QG2H1%QH2Q61%QI2Q=1tZLR0QK1pYBR01pXDR21").
Proof. intros X g.
pose proof (sbl_queue (put_meta g meta0 X) LFree g) as S. unfold fm_st. cbn zeta.
rewrite (sbl_regions _ _ S), (sbl_shadow _ _ S), (sbl_groups _ _ S), (sbl_slots _ _ S), (sbl_areas _ _ S), (sbl_brk _ _ S).
repeat split; reflexivity.
Qed.
Lemma deq_mid_shape : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "='S7'RG&R4'Q?r3&QKr2r1%33214%6251pYB81pYF:1pZJ<1").
Proof. intros st h g. apply sbl_deq_mid. Qed.
Lemma conc_sbl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'Q?r3r2%3221'@'G&R=%1265r4%3217%63531p081pZ<=1pZL?1pZJ@1").
Proof. intros st st' q. intros S. unfold conc, get_region. rewrite (sbl_regions _ _ S). reflexivity. Qed.
Lemma pd_st_cases : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q5'2'S7'G'D'@&QNr3r2r1%43321%63913'A&R4'?r4(>%<3@21&S8&R3%12=<(1%129=%B3531%B39A@&QI&QH%12DB%33EC1%H3K51%@271%A2>1qXJC1%E2D1%N2G1pZFQ01p[0Q21pXNQ41").
Proof. intros an st1 sc.
unfold pd_st. destruct an; [|left; reflexivity]. destruct (active st1 sc) as [a|]; [right; exists a; auto| left; reflexivity].
Qed.
Lemma act_st_rec_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'S7&R4'G&C'@r1r3%33621%511'S5&RC&QIr5r4%33218r2%6221%7252%>3921p0;1pZ<C1pXLC1pXJE1pZJG1").
Proof. intros st a act q. intros NE. unfold act_st. rewrite rec_upd, (aptr_eqb_neq q a NE). reflexivity. Qed.
Lemma act_st_groups : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "L'S7&R4'G'@'UI&UG'F&UL&UM%443271&UF&UD&UE%36762;51'RF%;4>621&S>&QIr3r2r1%43321%611%715%E3921pXLG1pXJI1pZJK1"). Proof. intros st a act. reflexivity. Qed.
Lemma act_st_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "F'S7&R4'G'@'UI'F&UL&UD'S;%544321&S@&QIr3r2r1%43321%611%715%?3921pXLA1pXJC1pZJE1"). Proof. intros st a act. reflexivity. Qed.
Lemma act_st_shadow : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "F'S7&R4'G'@'UI'F&UL&UD'SH%544321&SB&QIr3r2r1%43321%611%715%?3921pXLA1pXJC1pZJE1"). Proof. intros st a act. reflexivity. Qed.
Lemma act_st_areas : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "L'S7&R4'G'@'UI&UG'F&UL&UM%443271&UF&UD&UE%36762;51'R6%;4>621&S<&QIr3r2r1%43321%611%715%E3921pXLG1pXJI1pZJK1"). Proof. intros st a act. reflexivity. Qed.
Lemma act_st_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'G'@'S4&S=&QIr3r2r1%43321%611%715%:3921pXL<1pXJ>1pZJ@1"). Proof. intros st a act. reflexivity. Qed.
Lemma act_of_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";'S7&R4&T2z&QHr2r1%3221%6251pXJ81pZJ:1").
Proof. intros st a.
unfold act_of. destruct (m_mem (get_meta_rec st a)) as [b|]; [|lia]. cbn [default id].
unfold mask_upto.
assert (H : 0 <= group_active_idx st b).
{ unfold group_active_idx. destruct (get_group st b); [apply Z.land_nonneg; right; lia| lia]. }
assert (0 < 2 ^ (group_active_idx st b + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.
Lemma slot_start'_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'S5'G'@&R4&SIr2r1%3221(:'F&5&UN';%124<&6%112wz%:49A21&RM%11?%:588631%<3=E1&Q7%12CB%A4@H31%H3GC1pYJJ1pZ>L1").
Proof. intros r i. unfold slot_start', sstart_of, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.
Lemma bits_lt_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "J'G'?&T2zr2%3221&T5&T7+2r3%3221%5271%;271r4%<21:'@'2&T8%1259(4%53421p071p0:1pZ2G1pXJH1pZ4I1").
Proof. intros n a m.
intros Ha Hm. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
apply (proj1 (Z.bounded_iff_bits_nonneg n a Hn ltac:(lia))); lia.
Qed.
Lemma lt_pow2_bits : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'G&T2zr2%3221r5r1%6221'@'2&T8%1268(4%53421p071pZ2?1&T5r4&T7+2%221?%5241p071p0C1p0D1pXJI1pZ4J1").
Proof. intros n a. intros Hn Ha H. apply (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha)). exact H. Qed.
Lemma lor_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'G'?&T2zr2%3221&T5&T7+2r3%3221%5271%;271r4%7261%92;1%?2;1&T4%1259%A2@1r5%>2=1%@241%F241p081p0=1pY2J1pXJK1pZ4L1").
Proof. intros n a b.
intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
split; [apply Z.lor_nonneg; lia|].
apply lt_pow2_bits; [lia| apply Z.lor_nonneg; lia|]. intros m Hm. rewrite Z.lor_spec, (bits_lt_pow2 n a m), (bits_lt_pow2 n b m) by lia. reflexivity.
Qed.
Lemma land_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "J'G'?&T2zr2%3221&T5&T7+2r3%3221%5271%;271&T0r4%2216%>2=1r5%;2:1%=241%C241p0@1p0:1pY2G1pXJH1pZ4I1").
Proof. intros n a b.
intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
split; [apply Z.land_nonneg; lia|].
apply lt_pow2_bits; [lia| apply Z.land_nonneg; lia|]. intros m Hm. rewrite Z.land_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
Lemma ldiff_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'G'?&T2zr2%3221&T5&T7+2r3%3221%5271%;271&T1%125:%=2<1r4%:291%<241%B241p081pY2E1pXJF1pZ4G1").
Proof. intros n a b.
intros Ha. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
assert (H0 : 0 <= Z.ldiff a b) by (apply (proj2 (Z.ldiff_nonneg a b)); lia).
split; [exact H0|].
apply lt_pow2_bits; [lia| exact H0|]. intros m Hm. rewrite Z.ldiff_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
Lemma bit_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "F'G'?&T2zr1%3221+O%5231%7231&R7r2%211%:291&T5&T7+2+Q0%3221%5271%B271p0<1pYJE1").
Proof. intros i. intros Hi. unfold bit. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]. Qed.
Lemma testbit_bit : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "B'G&T2zr2%3221'@'2&T8&R7r3%211%4218&SO%124:%93831p0;1pYN@1pYJA1").
Proof. intros i j. intros. unfold bit. apply Z.pow2_bits_eqb. lia. Qed.
Lemma testbit_mask_upto : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'G&T2zr2%3221'@'2&T8&S3r4%211r3%5221&T3%1235%:3931p0<1p0=1pYNB1pZ0C1").
Proof. intros li j.
intros. unfold mask_upto. replace (2 ^ (li + 1) - 1) with (Z.ones (li + 1)).
2:{ unfold Z.ones. rewrite Z.shiftl_1_l. lia. }
rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec j (li + 1)); destruct (Z.leb_spec j li); try reflexivity; lia.
Qed.
Lemma all_free_of_mask : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R8'G'?&T2zr4%3221&T5&T7+2+Q0%3221%5271%;271r3%<2:1%>2:1+O%?2=1'@'2&T8r8r6%3221(4%73621r7%7261%:3914&SN&T4r:r9%3221&R7%11>%7231&S3%11<%E3Q731r1%Q72Q61%Q822:%Q:221&Cr2r;%M3Q?21%411'Dr>%O21Q6(>%Q33Q221r=%Q321Q:%Q63Q514%8241p0:1p0@1pYNQL1p0F1p0Q21p0Q61p0Q?1p0QB1p0QF1p0QG1pZ0R41pYJR51pY0R61pY@R71").
Proof.
intros freed avail i li HF HA Hi Hli Fi Ai HM j Hj NE.
assert (L0 : Z.land (Z.lor freed avail) (bit i) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.testbit_0_l by lia.
destruct (Z.eqb_spec i n); [subst; rewrite Fi, Ai; reflexivity| apply andb_false_r]. }
rewrite (Z.add_nocarry_lxor _ _ L0), (Z.lxor_lor _ _ L0) in HM.
assert (T : Z.testbit (Z.lor (Z.lor freed avail) (bit i)) j = true).
{ rewrite HM, testbit_mask_upto by lia. apply Z.leb_le. lia. }
rewrite !Z.lor_spec, testbit_bit in T by lia.
destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in T.
destruct (Z.testbit freed j); [left; reflexivity|]. destruct (Z.testbit avail j); [right; reflexivity|]. discriminate.
Qed.
Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
P 0 x -> (forall n y, 0 <= n -> P n y -> P (n + 1) (f y)) ->
forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
induction (Z.abs_nat n) as [|k IH]; [exact H0|].
cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.
Lemma del_slots_lookup : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R8&R4'G'S7';%1243&T2zr4%3221&B'@'9%118&UC'UI&UG'F&UL&UM%4432B1&UF&UD&UE%36762F51%:4H51D&UJ%14J73Fr3&SC&R@r7r6r5%44321J%611%F6Q3O;981(1r2%22Q21%M3K41'?%=1Q2%M6Q:Q6B@?1%Q13O15r1%Q82Q71&T5%123@%8231&C&R2r9&SN&R1&T6r8%221C%5241%8271%QA3QKK1%;11p0=1pYJQM1%G2D1%QG2I1p0QI1p\4QN1pZDR31pZJR21pY<R41p\0R51pZ8R71").
Proof. intros p stride cnt st s x.
intros Hc. unfold del_slots. cbn [s_slots].
match goal with |- context [Z.iter cnt ?f ?x0] =>
enough (IND : fst (Z.iter cnt f x0) = cnt /\ forall s' x', snd (Z.iter cnt f x0) !! s' = Some x' <->
((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < cnt -> s' <> aadd p (UNIT + stride * i)))
by (apply (proj2 IND));
apply (Z_iter_ind f (fun n acc => fst acc = n /\ forall s' x', snd acc !! s' = Some x' <->
((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < n -> s' <> aadd p (UNIT + stride * i)))); [| | exact Hc]
end.
- split; [reflexivity|]. intros s' x'. cbn [snd]. split; [intros H; split; [exact H| intros; lia]| intros [H _]; exact H].
- intros n [i tb] Hn [Hi IH]. cbn [fst snd] in Hi, IH |- *. subst i. split; [reflexivity|].
intros s' x'. rewrite lookup_delete_Some, IH. split.
+ intros [NE [H1 H2]]. split; [exact H1|]. intros j Hj.
destruct (Z.eq_dec j n) as [->|]; [congruence| apply H2; lia].
+ intros [H1 H2]. split; [| split; [exact H1| intros j Hj; apply H2; lia]].
intros E. apply (H2 n); [lia| congruence].
Qed.
Lemma del_slots_lookup_None : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "QA&R4'G'S7&T2zr3%3221'@'9';%12:9%311&UC'UI&UG'F&UL&UM%4432A1&UF&UD&UE%36762E51%:4G51=&UJ%14I73?r2&SC%11G%A6MC6431(0%11E%I3E31&R@r7r6r5r4%544321%<11%L6Q8NA?Q31%Q23N1:p0:1p0Q51pZDQ<1pZJQ;1pY<Q=1p\0Q>1pZ8Q@1").
Proof. intros p stride cnt st s.
intros Hc H. destruct (s_slots (del_slots p stride cnt st) !! s) as [x|] eqn:E; [|reflexivity].
apply (del_slots_lookup p stride cnt st s x Hc) in E. destruct E as [E _]. congruence.
Qed.
Lemma slot_start'_mem : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'S5&R4'G'@&S8&RMr3%211(1r2%2291%83741&SIr4%2215&R2&SN&R1&T6&RE%117%321<%6251%82A1%E3G:1p0>1pYNH1pZ8J1pZ>L1").
Proof. intros r p j. intros H. unfold slot_start'. rewrite H. reflexivity. Qed.
Definition geom_eq (r r' : meta) : Prop :=
m_mem r' = m_mem r /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r
/\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.
Lemma geom_eq_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "5'S5&Q<r1%2211pZ>41"). Proof. intros r. repeat split; reflexivity. Qed.
Lemma geom_of_data : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ">'S5'@&QDr1%211r2%411%63731&Q<r3%2215p041pZ@<1pZ>=1").
Proof. intros r r'. intros H. apply data_of_eq in H. destruct H as (A1 & _ & _ & A4 & A5 & A6 & A7). repeat split; auto. Qed.
Lemma get_stride_geom : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S5&Q<r2r1%3221'@'G&RE%116r3%311%63531p081pZ@=1pZ>>1").
Proof. intros r r'. intros (A1 & A2 & A3 & A4 & A5). unfold get_stride. rewrite A2, A4, A5. reflexivity. Qed.
Lemma slot_start'_geom : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S5'G&Q<r3r2%3221'@&R4&SI%1265r4%3217%63531p081pYJ=1pZ@?1pZ>@1").
Proof. intros r r' i. intros G. unfold slot_start'. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.
Lemma sstart_of_geom : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "@'S5'G&Q<r3r2%3221'@&Q7%1254r4%3216%53:31p071pYJ<1pZ@>1pZ>?1").
Proof. intros r r' i. intros G. unfold sstart_of. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.
Section XFER.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis ET : s_tick st' = s_tick st.
Hypothesis EB : c_brk (ctx st') = c_brk (ctx st).
Hypothesis GEO : forall q, is_gm st q -> geom_eq (get_meta_rec st q) (get_meta_rec st' q).
Hypothesis MASK : forall q b, hosts st b q ->
0 <= m_avail (get_meta_rec st' q) < 2^32 /\ 0 <= m_freed (get_meta_rec st' q) < 2^32
/\ forall i, 0 <= i ->
(Z.testbit (m_avail (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q))
/\ (Z.testbit (m_freed (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q)).
Hypothesis NF : forall q b j, hosts st b q -> 0 <= j <= m_last_idx (get_meta_rec st q) ->
~ slot_free (get_meta_rec st q) j -> slot_free (get_meta_rec st' q) j ->
(s_groups st) !! (slot_start' (get_meta_rec st q) j) = None
/\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st q) j) LB.
Lemma hosts_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "<&R4&B&Q4vU=r2r1%43321vU<%63143%8231pZ<:1pY2;1").
Proof. intros b q. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ":&R4&B&Q5vU=r1%3221vU<%5213%7231pZ<91").
Proof. intros q. unfold is_gm. split; intros [b H]; exists b; apply hosts_x; exact H. Qed.
Lemma meta_slot_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ":&R4&B&QOvU=r1%3221vU<%5213%7231pZ<91").
Proof. intros q. unfold meta_slot. rewrite EA. tauto. Qed.
Lemma get_shadow_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";'F'@'SH&RDvU=r1%3221vU<%5213%83731pZB:1").
Proof. intros rid. unfold get_shadow. rewrite ES. reflexivity. Qed.
Lemma conc_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ";&R4'@'G&R=vU=r1%3221vU<%5213%83731pZ<:1").
Proof. intros q. unfold conc, get_region. rewrite ER. reflexivity. Qed.
Lemma hdr_known_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?&R4'G&Q3vU<r3r2r1%544321vU=r4%842165p041pYL;1pY4=1pZ8>1").
Proof. intros p b1 i1. unfold hdr_known. rewrite !get_shadow_x. exact (fun H => H). Qed.
Section SE.
Local Abbreviation SEC_T_gmeta_x := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C&R4&Q1vU<%211&M%113&Q4r4r3%33721'Q2vU=r5%33261p051p0:1p0=1pYBA1pY2B1")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_gmeta_x) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_gmeta_x) 1%nat 0%nat).
Lemma gmeta_x : ltac:(sec_stmt2 constr:(SEC_T_gmeta_x) 2%nat 0%nat).
Proof.
intros CS CG HB. pose proof (CG b g HB) as GO. pose proof (GEO g (ex_intro _ b HB)) as Gg.
pose proof Gg as (M1 & M2 & M3 & M4 & M5).
destruct (MASK g b HB) as (RA & RF & BITS).
constructor.
- apply meta_slot_x. exact (go_slot _ _ _ GO).
- exact RA.
- exact RF.
- rewrite M2. exact (go_li _ _ _ GO).
- rewrite M3. exact (go_freeable _ _ _ GO).
- rewrite M4, M2, M5. exact (go_sc _ _ _ GO).
- rewrite M5. exact (go_maplen _ _ _ GO).
- intros i Hi. rewrite M2. exact (BITS i Hi).
- rewrite M1. exact (go_mem _ _ _ GO).
- destruct (go_region _ _ _ GO) as (r & Hr & Kr & S0 & S16 & SP & TOP). exists r.
rewrite ER, (sstart_of_geom _ _ _ Gg), M2, M5. repeat split; auto; apply TOP; auto.
- rewrite (get_stride_geom _ _ Gg). exact (go_stride _ _ _ GO).
- intros ML. rewrite M5 in ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
pose proof (GEO g1 (ex_intro _ b1 HB1)) as G1. pose proof G1 as (N1 & N2 & N3 & N4 & N5).
exists g1, i1, b1. rewrite ESL, (slot_start'_geom _ _ _ G1), N2, N4, M4.
split; [exact SL|]. split; [apply hosts_x; exact HB1|]. split; [exact FB|]. split; [exact EQB|]. split; [exact I1|].
split.
{ intros FR'. destruct (NF g1 b1 i1 HB1 I1 NF1 FR') as [NG _]. rewrite <- EQB in NG.
destruct HB as [ai Hai]. rewrite Hai in NG. discriminate. }
split; [exact LT|]. apply hdr_known_x. exact HK.
Qed.
End SE.
Lemma blks_x : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres ">&Q1vU<%211'E&J'L%115vH%53421vU=%511%83714p041p0;1").
Proof.
intros CS H. apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) H blk Hin) as BK.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
pose proof (GEO g (ex_intro _ b HB)) as Gg. pose proof Gg as (M1 & M2 & M3 & M4 & M5).
constructor.
- exists g, i, b. rewrite ESL, M2, (get_stride_geom _ _ Gg), get_shadow_x, conc_x.
split; [exact SL|]. split; [apply hosts_x; exact HB|]. split; [exact FB|]. split; [exact I|]. split.
+ intros FR'. destruct (NF g b i HB I NFR FR') as [_ NB].
pose proof (proj1 (Forall_forall _ _) NB blk Hin) as NE. apply NE.
destruct (CS _ _ _ SL) as (_ & E & _). exact E.
+ exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split; [exact OK|]. apply hdr_known_x. exact HK.
- rewrite EG. exact NG.
- exact SZ.
Qed.
Lemma KINV_xfer : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "L'G'Q8vU<vHr2%43321'Q0vU=%211'N%113&O%115&Q=%117&Q@r6%22:1r7%B3<@1p031p071p0:1p0=1p0@1p0D1pY:J1pY8K1").
Proof. intros c c'.
intros K L H HO KC US.
pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_gmetas _ _ _ K) as CG.
constructor; auto.
- intros b g HB. apply gmeta_x; auto. apply hosts_x. exact HB.
- intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. split; [exact Hg|].
assert (HB : hosts st b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
destruct (GEO g (ex_intro _ b HB)) as (_ & -> & _). exact Hai.
- intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_x; auto.
- intros s g i Hs. rewrite ESL in Hs. destruct (CS s g i Hs) as (GM & E & I).
pose proof (GEO g GM) as Gg. rewrite (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & -> & _).
split; [apply is_gm_x; exact GM| auto].
- intros b g i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
rewrite ESL, (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
- intros b gh o Hb Ho. rewrite EG in Hb. rewrite get_shadow_x. exact (ki_unk _ _ _ K b gh o Hb Ho).
- intros g b i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
rewrite get_shadow_x, (sstart_of_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_h0 _ _ _ K g b i HB Hi).
- apply blks_x; auto. exact (ki_blks _ _ _ K).
- exact (ki_nodup _ _ _ K).
- intros rid off Hb. rewrite EB in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
- pose proof (ki_ticks _ _ _ K) as [T1 T2]. split; intros until 0; rewrite ES, ET; [apply T1| apply T2].
Qed.
End XFER.
Section LINKX.
Variables (st st' : mstate).
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis EL : forall q, m_next (get_meta_rec st' q) = m_next (get_meta_rec st q) /\ m_prev (get_meta_rec st' q) = m_prev (get_meta_rec st q).
Hypothesis EH : forall sc, active st' sc = active st sc.
Hypothesis EF : c_free_meta_head (ctx st') = c_free_meta_head (ctx st).
Hypothesis ED : forall q, m_next (get_meta_rec st q) <> None ->
m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q) /\ m_sizeclass (get_meta_rec st' q) = m_sizeclass (get_meta_rec st q).
Lemma heads_lx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "6'NvU<%211vU=%411p031").
Proof.
intros [CF CA]. constructor.
- intros h Hh. rewrite EF in Hh. destruct (CF h Hh) as [N M]. destruct (EL h) as [E1 _]. rewrite E1.
destruct (ED h N) as [-> _]. auto.
- intros sc a Ha. rewrite EH in Ha. destruct (CA sc a Ha) as (SC & N & GM & SCa). destruct (EL a) as [E1 _]. rewrite E1.
destruct (ED a N) as [_ ->]. pose proof (proj2 (is_gm_ext st st' a EG) GM). auto.
Qed.
Lemma homog_lx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "9'Q0vU<%211&O%113vU=%311p031p061").
Proof.
intros [LN LP LNN LS] HO m nx Hn. destruct (EL m) as [E1 _]. rewrite E1 in Hn. destruct (HO m nx Hn) as [H1 H2].
assert (Nm : m_next (get_meta_rec st m) <> None) by congruence.
assert (Nx : m_next (get_meta_rec st nx) <> None).
{ intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. congruence. }
destruct (ED m Nm) as [_ ->]. destruct (ED nx Nx) as [_ ->].
pose proof (is_gm_ext st st' m EG). pose proof (is_gm_ext st st' nx EG). tauto.
Qed.
End LINKX.
Lemma KINV_xfer_recs : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "SN'S7'7&J%211'G'@'UI'F&UL&UD'S;%544321&S@r4%211r5%411%<3631'SH%=4<;:1&SB%116r6%311%C3531&R4&UG&UM%24EDH1&UF&UE%26HGFK41'R6%K48521&S<%11=r7%311%Q13531'RF%Q24?<91&S>%116r8%311%Q83531';%12FQ;%Q:4GDA1&SC%117r9%311%Q@3531&SD%114r:%311%QE3QC31%=2QGQG%QK11&SA%116r;%311%QL3531'R8&R9&R?%116%311r<%411%611%R53841'S5&RCr=r1%3221r>%5213%R=3731pZ<QJ1&S8&R3%1268r?%321:%RD3531pZFRF1&R:%H1<%211%J17%411%RK3<31'Q8r@%231CF&Q=%113&Q@rA%221HrB%9313Cp031p071p0:1p0>1p0E1p0M1p0Q71p0QA1p0QI1p0QO1p0R81p0R@1p0RO1p0S71pY:SE1pY8SF1pQBSH1pZLSL1pZJSM1").
Proof. intros st st' LB c c'.
intros ER ES EA EG ESL ET ERS EB EM EH EF K KC US.
eapply (KINV_xfer st st' LB ER ES EA EG ESL ET EB); try exact K; try exact KC; try exact US.
- intros q _. rewrite EM. apply geom_eq_refl.
- intros q b HB. rewrite EM. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
- intros q b j _ _ NFR FR. rewrite EM in FR. tauto.
- apply (links_ext st st' EA); [| exact (ki_links _ _ _ K)]. intros q. rewrite EM. auto.
- apply (heads_lx st st' EG); [intros q; rewrite EM; auto | exact EH | exact EF | intros q _; rewrite EM; auto | exact (ki_heads _ _ _ K)].
- apply (homog_lx st st' EG); [intros q; rewrite EM; auto | intros q _; rewrite EM; auto | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
Qed.
Lemma KINV_xfer_sbl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q0'S7'7&J%211'G'Q?r4r3%3221'Q8r5r2%33251'Q0%114'Nr6%211&Or7%211r8%=3136p031p071p0;1p0>1p0C1pY8H1pQBJ1pZLN1pZJO1").
Proof. intros st st' LB c.
intros S K L H HO.
eapply (KINV_xfer st st' LB (sbl_regions _ _ S) (sbl_shadow _ _ S) (sbl_areas _ _ S) (sbl_groups _ _ S) (sbl_slots _ _ S)
(sbl_tick _ _ S) (sbl_brk _ _ S)); try exact K; try exact L; try exact H; try exact HO.
- intros q _. apply geom_of_data. apply (sbl_data _ _ S).
- intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (_ & -> & -> & _).
split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
- intros q b j _ _ NFR FR. exfalso. apply NFR. apply (proj1 (slot_free_data _ _ j (sbl_data _ _ S q))). exact FR.
- pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4). unfold kctx.
rewrite (sbl_seq _ _ S), (sbl_secret _ _ S). split; [exact X1|]. split; [intros i; rewrite (sbl_bounces _ _ S); apply X2|].
split; [intros i; rewrite (sbl_unmap _ _ S); apply X3| exact X4].
- intros sc Hsc. rewrite (sbl_usage _ _ S). exact (ki_usage _ _ _ K sc Hsc).
Qed.
Lemma rec_set_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7'RG&S8&R4'@'S5&RC&SFr3r2r4%43321r1%7221%8242%;3:21pZ<=1p\2?1pYFA1pZJC1").
Proof. intros st h v q. destruct h; reflexivity. Qed.
Lemma active_set_active_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S7'G&S8'@&R3&SEr2r1r3%43321%6214%83914p\2:1pZF<1pZJ>1").
Proof. intros st sc v.
unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
destruct v as [p|]; [apply lookup_insert_eq| apply lookup_delete_eq].
Qed.
Lemma active_set_active_ne : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "F'S7'G&S8&C'@r2r3%33621%511&R3&SEr4r5%33281%5218%6239%<3>21p091p\2@1pZHB1pZFC1pZJE1").
Proof. intros st sc sc' v.
intros NE. unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
destruct v as [p|]; [rewrite lookup_insert_ne by lia| rewrite lookup_delete_ne by lia]; reflexivity.
Qed.
Lemma get_head_set_head : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "?'S7'RG&S8'@&RB&SFr2r1r3%43321%6214%83914p\2:1pYF<1pZJ>1").
Proof. intros st h v. destruct h as [sc|]; cbn [get_head set_head]; [apply active_set_active_eq| reflexivity]. Qed.
End CEIL_WRAP_3.
Ltac crush_ptr :=
repeat (match goal with |- context [aptr_eqb ?x ?y] => destruct (aptr_eqb_spec' x y); try subst end);
cbn [m_next m_prev m_set_prev m_set_next]; try reflexivity; try congruence.
Section CEIL_WRAP_4.
Context {RUNp : RunP}.
Lemma fm_single_next st h g q :
m_next (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
Lemma fm_single_prev st h g q :
m_prev (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
Lemma fm_link_next st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
m_next (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.
Lemma fm_link_prev st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
m_prev (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.
Lemma queue_ctx_some : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "J'S7'RG&R4'@&S8&RBr4r3%3221(1r1%2291%93841'S4&R?&QGr5%23;:1%411%513%A3721p091pYHD1pYBE1pYFG1pZJI1").
Proof. intros st h g hd. intros H. unfold queue_st. rewrite H. unfold fm_link. destruct (m_prev (get_meta_rec st hd)); reflexivity. Qed.
Lemma queue_head_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "G'S7'RG&R4'@&S8&RBr3r2%3221(0%118%83731&QGr4%23871%:219(1%12?:%?3>31p081pYBB1pYFD1pZJF1").
Proof. intros st h g. intros H. unfold queue_st. rewrite H. unfold fm_single. apply get_head_set_head. Qed.
Lemma queue_active_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q1'S7'RG&R4'G'@&S8&RBr4r3%3221(0%119%83731&C(R0r2%211%=3@:1%511&R3&QGr5r6%332@1%521@%623A%F3E21p091p0@1pZFJ1pYBL1pYFN1pZJQ01").
Proof. intros st h g sc.
intros H NE. unfold queue_st. rewrite H. unfold fm_single. destruct h as [sc0|]; cbn [set_head].
- rewrite active_set_active_ne by congruence. reflexivity.
- reflexivity.
Qed.
Lemma queue_fmh_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "M'S7'G&R4'@&S8&RBr3(R0r2%211%5241(0%11:%:3931&R:&R?&QG%:1;r4%332;1%511%711%714%911%E3D31p0<1pYBH1pZFJ1pZJL1").
Proof. intros st sc g. intros H. unfold queue_st. rewrite H. reflexivity. Qed.
Lemma dequeue_next_self st h g q : m_next (get_meta_rec st g) = Some g ->
m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_next (get_meta_rec st q).
Proof.
intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
Lemma dequeue_prev_self st h g q : m_next (get_meta_rec st g) = Some g ->
m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q).
Proof.
intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
Lemma dequeue_next st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q).
Proof.
intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
rewrite rec_upd.
match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.
Lemma dequeue_prev st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q).
Proof.
intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
rewrite rec_upd.
match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.
Lemma dequeue_active st sc g nx pv sc' : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
active (dequeue (LActive sc) g st) sc' =
if sc' =? sc then (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
else active st sc'.
Proof.
intros NX PV. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb].
change (active (upd_meta g ?f ?s) sc') with (active s sc').
destruct (aptr_eqb_spec' nx g).
- cbn [negb set_head]. destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| apply active_set_active_ne; exact NE].
- cbn [negb get_head set_head].
change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc) with (active st sc).
destruct (active st sc) as [a|] eqn:HA; cbn [optr_eqb].
+ destruct (aptr_eqb_spec' a g).
* destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| rewrite active_set_active_ne by exact NE; reflexivity].
* change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
+ change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
Qed.
Lemma dequeue_fmh : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "F'S7'G&R4'@&S8&R:&R?&RA(R0r2%211r1r3%63321%811%:11%:14%<11%?3>31pYBA1pZFC1pZJE1").
Proof. intros st sc g.
unfold dequeue. lazy zeta.
destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| reflexivity].
destruct (m_prev (get_meta_rec st g)); destruct (m_next (get_meta_rec st g));
match goal with |- context [if ?c then set_head _ _ _ else _] => destruct c end; reflexivity.
Qed.
Lemma dequeue_shape : forall st g sc nx pv,
m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
let st' := dequeue (LActive sc) g st in
(forall x, data_of (get_meta_rec st' x) = data_of (get_meta_rec st x))
/\ m_next (get_meta_rec st' g) = None /\ m_prev (get_meta_rec st' g) = None
/\ s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_areas st' = s_areas st
/\ s_groups st' = s_groups st /\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_reserved st' = s_reserved st
/\ active st' sc = (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
/\ (forall sc', sc' <> sc -> active st' sc' = active st sc')
/\ c_free_meta_head (ctx st') = c_free_meta_head (ctx st)
/\ (forall sc', usage st' sc' = usage st sc') /\ (forall j, bounces st' j = bounces st j) /\ (forall j, unmap_seq st' j = unmap_seq st j)
/\ c_seq (ctx st') = c_seq (ctx st) /\ c_brk (ctx st') = c_brk (ctx st) /\ c_secret (ctx st') = c_secret (ctx st).
Proof.
intros st g sc nx pv NX PV. pose proof (sbl_dequeue st (LActive sc) g) as S. cbn zeta.
split; [exact (sbl_data _ _ S)|].
split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
split; [exact (sbl_regions _ _ S)|]. split; [exact (sbl_shadow _ _ S)|]. split; [exact (sbl_areas _ _ S)|].
split; [exact (sbl_groups _ _ S)|]. split; [exact (sbl_slots _ _ S)|]. split; [exact (sbl_tick _ _ S)|]. split; [exact (sbl_reserved _ _ S)|].
split. { rewrite (dequeue_active st sc g nx pv sc NX PV), Z.eqb_refl. reflexivity. }
split. { intros sc' NE. rewrite (dequeue_active st sc g nx pv sc' NX PV). destruct (Z.eqb_spec sc' sc); [lia| reflexivity]. }
split; [apply dequeue_fmh|].
split; [exact (sbl_usage _ _ S)|]. split; [exact (sbl_bounces _ _ S)|]. split; [exact (sbl_unmap _ _ S)|].
split; [exact (sbl_seq _ _ S)|]. split; [exact (sbl_brk _ _ S)| exact (sbl_secret _ _ S)].
Qed.
Lemma KINV_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "K'S7'7&J%211'G'QBr5r4r3%43321&T2%1243&SGr7%23761r6&SN+1%22;1%>3541p091p0<1p\2B1pZFC1pY8D1pQBF1pZJJ1").
Proof.
intros st LB c sc v K Hc.
apply (KINV_xfer_recs st (set_usage sc v st) LB c); try reflexivity; try exact K.
- exact (ki_cx _ _ _ K).
- intros sc' Hsc'. unfold usage, set_usage, upd_ctx, ctx. cbn [s_ctx c_usage set_usage_map].
rewrite lookup_insert_ne by lia. exact (ki_usage _ _ _ K sc' ltac:(lia)).
Qed.
Lemma KINV_seq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'S7'7&J%211'G'QBr4r3r2%43321&S:&SJr5%211%4261%:3198p071pZF=1pY8>1pQB@1pZJD1").
Proof.
intros st LB c sc K. pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4).
apply (KINV_xfer_recs st _ LB c); try exact K;
try (unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity).
- unfold kctx, bounces, unmap_seq in *. unfold record_seq, step_seq, upd_ctx, ctx in *.
destruct (Z.eqb_spec (c_seq (s_ctx st)) 255) as [E|NE]; destruct (sc_in_seq_range sc);
cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map]; unfold ctx; cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map].
all: split; [lia|]; split; [exact X2|]; split; [| exact X4].
all: intros i.
+ destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; rewrite lookup_empty; cbn; lia].
+ rewrite lookup_empty; cbn; lia.
+ destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; apply X3].
+ apply X3.
- intros sc0 Hsc0. unfold usage. replace (c_usage (ctx (record_seq sc (step_seq st)))) with (c_usage (ctx st)).
+ exact (ki_usage _ _ _ K sc0 Hsc0).
+ unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity.
Qed.
Lemma KINV_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q3'S7'7&J%211'G&R4'QBr6r5r4%43321'QCr7r3r2%46387621&QLr8%221:&SN&S2&RC%125>%311+1%6221%D38>1p0<1p0B1pYJI1pZ8I1pYBJ1pY8L1pQBN1pZJQ21").
Proof. intros st LB c g p i.
intros K L. unfold fg_usage_st. destruct (_ <? 48).
- apply (KINV_set_usage st LB c); [exact K| exact (lp_class _ _ _ _ _ _ L)].
- eapply KINV_mono; [exact K|]. pose proof (lp_class _ _ _ _ _ _ L). lia.
Qed.
Lemma KINV_aor : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "L'S7'7&J%211'G&R4'QBr6r5r4%43321'QCr7r3r2%46387621&QJr8%231:5%=317<p051p0;1pYJB1pZ8B1pYBC1pY8E1pQBG1pZJK1").
Proof.
intros st LB c g p i K L. pose proof (lpre_gmeta _ _ _ _ _ _ K L) as GO.
pose proof (lp_i _ _ _ _ _ _ L) as Hi. pose proof (go_li _ _ _ GO) as LI.
assert (RQ : forall q, get_meta_rec (aor_st st g i) q =
if aptr_eqb q g then m_set_freed (Z.lor (m_freed (get_meta_rec st g)) (bit i)) (get_meta_rec st g) else get_meta_rec st q).
{ intros q. unfold aor_st. rewrite rec_upd. reflexivity. }
apply (KINV_xfer st (aor_st st g i) LB) with (c := c); try reflexivity.
- intros q _. rewrite RQ. case_ptr q g; [| apply geom_eq_refl]. repeat split; reflexivity.
- intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ. case_ptr q g.
+ cbn [m_avail m_freed m_set_freed].
split; [exact (go_avail _ _ _ GQ)|].
split; [apply (lor_range 32); [exact (go_freed _ _ _ GQ)| apply bit_range; lia]|].
intros k Hk. split; [intros T; exact (proj1 (go_bits _ _ _ GQ k Hk) T)|].
rewrite Z.lor_spec, testbit_bit by lia. intros T. apply orb_true_iff in T.
destruct T as [T|T]; [exact (proj2 (go_bits _ _ _ GQ k Hk) T)| apply Z.eqb_eq in T; lia].
+ exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
- intros q b j HB Hj NFR FR. rewrite RQ in FR. case_ptr q g; [| tauto].
assert (b = p) as -> by (exact (ki_ginj _ _ _ K b p g HB (lp_hosts _ _ _ _ _ _ L))).
unfold slot_free in NFR, FR. cbn [m_freed m_avail m_set_freed] in FR. rewrite Z.lor_spec, testbit_bit in FR by lia.
assert (j = i) as ->.
{ destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in FR. tauto. }
split; [exact (lp_nogroup _ _ _ _ _ _ L)| exact (lp_noblock _ _ _ _ _ _ L)].
- exact K.
- apply (links_ext st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K)].
- apply (heads_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_heads _ _ _ K)].
- apply (homog_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
- exact (ki_cx _ _ _ K).
- exact (ki_usage _ _ _ K).
Qed.
Lemma KINV_act : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q6'S7'7&J%211'G&R4'QBr5r4r3%43321&Q5r6%2214'@&RH&RCr7%221:%411z%73A21&T2%123?&QIr9%231>Cr8%F321;p061p091p0B1p0F1pXLM1pXJM1pY8O1pQBQ11pZJQ51").
Proof.
intros st LB c a act K GM AV Hact. destruct GM as [b HB]. pose proof (ki_gmetas _ _ _ K b a HB) as GO.
assert (RQ : forall q, get_meta_rec (act_st st a act) q =
if aptr_eqb q a then m_set_avail (Z.land (m_freed (get_meta_rec st a)) act) (m_set_freed (Z.ldiff (m_freed (get_meta_rec st a)) act) (get_meta_rec st a)) else get_meta_rec st q).
{ intros q. unfold act_st. rewrite rec_upd. reflexivity. }
apply (KINV_xfer st (act_st st a act) LB) with (c := c); try reflexivity.
- intros q _. rewrite RQ. case_ptr q a; [| apply geom_eq_refl]. repeat split; reflexivity.
- intros q b' HB'. pose proof (ki_gmetas _ _ _ K b' q HB') as GQ. rewrite RQ. case_ptr q a.
+ cbn [m_avail m_freed m_set_freed m_set_avail].
split; [apply (land_range 32); [exact (go_freed _ _ _ GQ)| exact Hact]|].
split; [apply (ldiff_range 32); exact (go_freed _ _ _ GQ)|].
intros k Hk. rewrite Z.land_spec, Z.ldiff_spec.
split; intros T; apply andb_true_iff in T; destruct T as [T _]; exact (proj2 (go_bits _ _ _ GQ k Hk) T).
+ exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
- intros q b' j HB' Hj NFR FR. exfalso. apply NFR. rewrite RQ in FR. case_ptr q a; [| exact FR].
unfold slot_free in FR |- *. cbn [m_avail m_freed m_set_freed m_set_avail] in FR. rewrite Z.land_spec, Z.ldiff_spec in FR.
left. destruct FR as [T|T]; apply andb_true_iff in T; tauto.
- exact K.
- apply (links_ext st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K)].
- apply (heads_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_heads _ _ _ K)].
- apply (homog_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
- exact (ki_cx _ _ _ K).
- exact (ki_usage _ _ _ K).
Qed.
Definition hkind (st : mstate) (h : lhead) (x : aptr) : Prop :=
match h with
| LActive sc => is_gm st x /\ m_sizeclass (get_meta_rec st x) = sc
| LFree => ~ is_gm st x
end.
Lemma free_head_not_gm : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q0'S7'7&J%211'G&R4'QBr4r3r2%43321'@&S8&R:&R?r5%211%411(1%12>:%93831&C&Q5r6%221@%411p061p0A1pYFG1pY8I1pQBK1pZJO1").
Proof. intros st LB c h. intros K H. exact (proj1 (proj2 (proj2 (kinv_free_head st LB c h K H)))). Qed.
Lemma KINV_queue_gen st LB c g h :
KINV st LB c -> meta_slot st g ->
m_next (get_meta_rec st g) = None -> m_prev (get_meta_rec st g) = None ->
match h with
| LActive sc => is_gm st g /\ m_sizeclass (get_meta_rec st g) = sc /\ 0 <= sc < 48
| LFree => ~ is_gm st g /\ m_mem (get_meta_rec st g) = None
end ->
KINV (queue_st h g st) LB c.
Proof.
intros K MSg N0 P0 HH.
pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
pose proof (sbl_queue st h g) as S. set (st' := queue_st h g st) in *.
assert (GK : hkind st h g) by (destruct h; cbn; tauto).
assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
{ intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
{ intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).
assert (HD : forall hd, get_head st h = Some hd ->
m_next (get_meta_rec st hd) <> None /\ hd <> g /\ hkind st h hd /\
exists pv, m_prev (get_meta_rec st hd) = Some pv /\ pv <> g /\ m_next (get_meta_rec st pv) = Some hd /\ hkind st h pv).
{ intros hd Hhd.
assert (N : m_next (get_meta_rec st hd) <> None /\ hkind st h hd).
{ destruct h as [sc|]; cbn in Hhd |- *.
- destruct (CA _ _ Hhd) as (_ & N & GM & SC). auto.
- split; [exact (proj1 (CF _ Hhd))| exact (free_head_not_gm st LB c hd K Hhd)]. }
destruct N as [N HK]. split; [exact N|]. split; [congruence|]. split; [exact HK|].
destruct (m_prev (get_meta_rec st hd)) as [pv|] eqn:PV; [| exfalso; apply N; apply (proj2 (LNN hd)); exact PV].
exists pv. destruct (LP hd pv PV) as [NP _]. split; [reflexivity|]. split; [congruence|]. split; [exact NP|].
destruct (HO pv hd NP) as [G1 G2]. destruct h as [sc|]; cbn in HK |- *.
- destruct HK as [GMh SCh]. assert (GMp : is_gm st pv) by tauto. split; [exact GMp|]. rewrite <- (G2 GMp). exact SCh.
- tauto. }
apply (KINV_xfer_sbl st st' LB c S K).
-
destruct (get_head st h) as [hd|] eqn:Hhd.
+ destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q)).
{ intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_next. exact PV. }
assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q)).
{ intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_prev. exact PV. }
constructor.
* intros m nx Hn. rewrite FN in Hn. rewrite FP.
destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
-- assert (nx = g) as -> by congruence. rewrite (aptr_eqb_neq g hd) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
-- assert (nx = hd) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; exact Nhd].
-- destruct (LN m nx Hn) as [P1 S1].
destruct (aptr_eqb_spec' nx hd); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; tauto|].
destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|].
split; [exact P1| apply MSx; exact S1].
* intros m pv0 Hp. rewrite FP in Hp. rewrite FN.
destruct (aptr_eqb_spec' m hd) as [->|NEmh]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
-- assert (pv0 = g) as -> by congruence. rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
-- assert (pv0 = pv) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; congruence].
-- destruct (LP m pv0 Hp) as [N1 S1].
destruct (aptr_eqb_spec' pv0 pv); [subst; exfalso; rewrite Npv in N1; assert (m = hd) by congruence; tauto|].
destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|].
split; [exact N1| apply MSx; exact S1].
* intros m. rewrite FN, FP.
destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m g); [subst|]].
-- destruct (aptr_eqb_spec' pv hd); [split; discriminate|]. rewrite (aptr_eqb_neq pv g) by congruence.
assert (m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
split; [discriminate| intros E; exfalso; exact (H E)].
-- rewrite (aptr_eqb_neq g hd) by congruence. split; discriminate.
-- destruct (aptr_eqb_spec' m hd); [subst; split; [intros E; exfalso; exact (Nhd E)| discriminate]| apply LNN].
* intros m Hn. rewrite FN in Hn. apply MSx.
destruct (aptr_eqb_spec' m pv); [subst; apply LS; congruence|]. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
+ assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q)).
{ intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_next. }
assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q)).
{ intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_prev. }
constructor.
* intros m nx Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [->|NEmg].
-- assert (nx = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
-- destruct (LN m nx Hn) as [P1 S1]. destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|]. split; [exact P1| apply MSx; exact S1].
* intros m pv0 Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [->|NEmg].
-- assert (pv0 = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
-- destruct (LP m pv0 Hp) as [N1 S1]. destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|]. split; [exact N1| apply MSx; exact S1].
* intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [split; discriminate| apply LNN].
* intros m Hn. rewrite FN in Hn. apply MSx. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
-
assert (NXT : forall x, m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
{ intros x Hx. unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
- destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & _). rewrite (fm_link_next st g hd pv x PV).
destruct (aptr_eqb x pv); [discriminate|]. destruct (aptr_eqb x g); [discriminate| exact Hx].
- rewrite fm_single_next. destruct (aptr_eqb x g); [discriminate| exact Hx]. }
assert (NXg : m_next (get_meta_rec st' g) <> None).
{ unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
- destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & NEpv & _). rewrite (fm_link_next st g hd pv g PV).
rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. discriminate.
- rewrite fm_single_next, aptr_eqb_refl. discriminate. }
constructor.
+ intros h0 Hh0.
destruct (get_head st h) as [hd|] eqn:Hhd.
* unfold st' in Hh0. rewrite (queue_ctx_some st h g hd Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
* destruct h as [sc|].
-- unfold st' in Hh0. rewrite (queue_fmh_none st sc g Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
-- pose proof (queue_head_none st LFree g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Hh0. assert (h0 = g) as -> by congruence.
rewrite EMM. split; [exact NXg| exact (proj2 HH)].
+ intros sc a Ha.
assert (OLD : active st sc = Some a -> 0 <= sc < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st' a) = sc).
{ intros Ho. destruct (CA sc a Ho) as (R & N & GM & SC). rewrite ESC. split; [exact R|]. split; [apply NXT; exact N|]. split; [apply EGM; exact GM| exact SC]. }
destruct (get_head st h) as [hd|] eqn:Hhd.
* apply OLD. unfold st' in Ha. unfold active in Ha |- *. rewrite (queue_ctx_some st h g hd Hhd) in Ha. exact Ha.
* destruct h as [sc0|].
-- destruct (Z.eq_dec sc sc0) as [->|NE].
++ pose proof (queue_head_none st (LActive sc0) g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Ha. assert (a = g) as -> by congruence.
destruct HH as (GM & SC & R). rewrite ESC. split; [exact R|]. split; [exact NXg|]. split; [apply EGM; exact GM| exact SC].
++ apply OLD. unfold st' in Ha. rewrite (queue_active_none st (LActive sc0) g sc Hhd) in Ha by congruence. exact Ha.
-- apply OLD. unfold st' in Ha. rewrite (queue_active_none st LFree g sc Hhd) in Ha by congruence. exact Ha.
-
assert (HKx : forall x y, hkind st h x -> hkind st h y -> (is_gm st x <-> is_gm st y) /\ (is_gm st x -> m_sizeclass (get_meta_rec st y) = m_sizeclass (get_meta_rec st x))).
{ intros x y Hx Hy. destruct h as [sc|]; cbn in Hx, Hy; [| tauto]. destruct Hx as [Gx Sx], Hy as [Gy Sy]. split; [tauto| intros _; congruence]. }
intros m nx Hn. rewrite !EGM, !ESC.
destruct (get_head st h) as [hd|] eqn:Hhd.
+ destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
unfold st', queue_st in Hn. rewrite Hhd, (fm_link_next st g hd pv m PV) in Hn.
destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [assert (nx = g) as -> by congruence; apply HKx; auto|].
destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = hd) as -> by congruence; apply HKx; auto|].
exact (HO m nx Hn).
+ unfold st', queue_st in Hn. rewrite Hhd, fm_single_next in Hn.
destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = g) as -> by congruence; split; [tauto| reflexivity]|].
exact (HO m nx Hn).
Qed.
Lemma KINV_queue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R7'S7'7&J%211'G&R4'QBr6r5r4%43321&Q4r7r3%33215'@&S2&RCr8%221;%411%63A81'?&T2z%221@&T5+Q@%22C1%7241&S8&RNr:%@21E%311(0%11O%F3731&ROr;%G21F%311%K3<16&C&R3r<%221Q2(1r9%22Q<1%Q33D41%811&QG(R0%11Q4r=%432H1%QC31<Bp071p0A1p0G1p0Q01p0Q91p0QA1p0QF1pZFQM1pZ8QM1pYBQN1pY8R01pQBR21pZJR61").
Proof.
intros st LB c g p sc K HB SC R N0 P0 _.
apply (KINV_queue_gen st LB c g (LActive sc) K (go_slot _ _ _ (ki_gmetas _ _ _ K p g HB)) N0 P0).
split; [exists p; exact HB|]. split; [symmetry; exact SC| exact R].
Qed.
Lemma KINV_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q?'S7'7&J%211'G&R4'QBr7r6r5%43321&Q4r8r4%33215'@&S2&RCr9%221;%411%63A81&S8&RNr:%821B%311(1%12G?%>3731&RA(R0%11Hr;%432F1%M31;Ap071p0@1p0H1p0M1pZ6Q31pZFQ51pZ8Q51pYBQ61pY8Q81pQBQ:1pZJQ>1").
Proof.
intros st LB c g p sc nx K HB SC NX.
pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
pose proof (ki_gmetas _ _ _ K p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM.
assert (GMg : is_gm st g) by (exists p; exact HB).
pose proof (sbl_dequeue st (LActive sc) g) as S. set (st' := dequeue (LActive sc) g st) in *.
assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
{ intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
{ intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).
destruct (LN g nx NX) as [Pnx Snx].
destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV; [| apply (proj2 (LNN g)) in PV; congruence].
destruct (LP g pv PV) as [Npv Spv].
pose proof (dequeue_fmh st sc g) as EF. fold st' in EF.
pose proof (fun sc' => dequeue_active st sc g nx pv sc' NX PV) as EH. fold st' in EH.
assert (NEfree : forall h0, c_free_meta_head (ctx st) = Some h0 -> h0 <> g).
{ intros h0 Hh0 ->. destruct (CF g Hh0) as [_ M]. congruence. }
destruct (aptr_eqb_spec' nx g) as [Enx|NEnx].
-
subst nx. assert (pv = g) as -> by congruence.
assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else m_next (get_meta_rec st q)).
{ intros q. unfold st'. apply dequeue_next_self. exact NX. }
assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q)).
{ intros q. unfold st'. apply dequeue_prev_self. exact NX. }
assert (NXo : forall m x, m_next (get_meta_rec st m) = Some x -> m <> g -> x <> g).
{ intros m x Hm NE ->. destruct (LN m g Hm) as [P1 _]. congruence. }
assert (PVo : forall m x, m_prev (get_meta_rec st m) = Some x -> m <> g -> x <> g).
{ intros m x Hm NE ->. destruct (LP m g Hm) as [P1 _]. congruence. }
apply (KINV_xfer_sbl st st' LB c S K).
+ constructor.
* intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
rewrite (aptr_eqb_neq x g) by (exact (NXo m x Hn NEmg)). destruct (LN m x Hn) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
* intros m x Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
rewrite (aptr_eqb_neq x g) by (exact (PVo m x Hp NEmg)). destruct (LP m x Hp) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
* intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [tauto| apply LNN].
* intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx. apply LS. exact Hn.
+ constructor.
* intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite FN, EMM, (aptr_eqb_neq h0 g) by (exact (NEfree h0 Hh0)). auto.
* intros sc' a Ha. rewrite EH in Ha. rewrite ?aptr_eqb_refl in Ha.
destruct (Z.eqb_spec sc' sc); [discriminate|].
destruct (CA sc' a Ha) as (R & N & GM & SCa).
assert (NEa : a <> g) by (intros ->; apply n; rewrite SC; symmetry; exact SCa).
rewrite FN, ESC, (aptr_eqb_neq a g NEa). split; [exact R|]. split; [exact N|]. split; [apply EGM; exact GM| exact SCa].
+ intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [discriminate|]. exact (HO m x Hn).
-
assert (NEpv : pv <> g) by (intros ->; rewrite Npv in NX; apply NEnx; congruence).
assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q)).
{ intros q. unfold st'. apply dequeue_next; assumption. }
assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q)).
{ intros q. unfold st'. apply dequeue_prev; assumption. }
assert (Nnx : m_next (get_meta_rec st nx) <> None) by (intros E; apply (proj1 (LNN nx)) in E; congruence).
assert (Ppv : m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
assert (NXT : forall x, x <> g -> m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
{ intros x NE Hx. rewrite FN, (aptr_eqb_neq x g NE). destruct (aptr_eqb x pv); [discriminate| exact Hx]. }
apply (KINV_xfer_sbl st st' LB c S K).
+ constructor.
* intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
destruct (aptr_eqb_spec' m pv) as [->|NEmp].
-- assert (x = nx) as -> by congruence. rewrite (aptr_eqb_neq nx g NEnx), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Snx].
-- destruct (LN m x Hn) as [P1 S1].
destruct (aptr_eqb_spec' x g); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; tauto|].
destruct (aptr_eqb_spec' x nx); [subst; exfalso; rewrite Pnx in P1; assert (m = g) by congruence; tauto|].
split; [exact P1| apply MSx; exact S1].
* intros m y Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
destruct (aptr_eqb_spec' m nx) as [->|NEmn].
-- assert (y = pv) as -> by congruence. rewrite (aptr_eqb_neq pv g NEpv), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Spv].
-- destruct (LP m y Hp) as [N1 S1].
destruct (aptr_eqb_spec' y g); [subst; exfalso; rewrite NX in N1; assert (m = nx) by congruence; tauto|].
destruct (aptr_eqb_spec' y pv); [subst; exfalso; rewrite Npv in N1; assert (m = g) by congruence; tauto|].
split; [exact N1| apply MSx; exact S1].
* intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [tauto|].
destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m nx); [subst|]].
-- destruct (aptr_eqb_spec' pv nx); [split; discriminate|]. split; [discriminate| intros E; exfalso; exact (Ppv E)].
-- split; [intros E; exfalso; exact (Nnx E)| discriminate].
-- apply LNN.
* intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx.
destruct (aptr_eqb_spec' m pv); [subst; exact Spv| apply LS; exact Hn].
+ constructor.
* intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; [exact (NEfree h0 Hh0)| exact N]| exact M].
* intros sc' a Ha. rewrite EH, ?(aptr_eqb_neq nx g NEnx) in Ha. rewrite ESC.
assert (OLD : active st sc' = Some a -> a <> g -> 0 <= sc' < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st a) = sc').
{ intros Ho NE. destruct (CA sc' a Ho) as (R & N & GM & SCa). split; [exact R|]. split; [apply NXT; auto|]. split; [apply EGM; exact GM| exact SCa]. }
destruct (Z.eqb_spec sc' sc).
-- subst sc'. destruct (active st sc) as [a0|] eqn:A0; cbn [optr_eqb] in Ha; [|discriminate].
destruct (aptr_eqb_spec' a0 g).
++ assert (a = nx) as -> by congruence. destruct (CA _ _ A0) as (R & _ & _ & _). destruct (HO g nx NX) as [G1 G2].
split; [exact R|]. split; [apply NXT; [exact NEnx| exact Nnx]|]. split; [apply EGM; tauto| rewrite (G2 GMg); symmetry; exact SC].
++ apply OLD; [exact Ha| congruence].
-- apply OLD; [exact Ha|]. intros ->. destruct (CA sc' g Ha) as (_ & _ & _ & SCg). apply n. rewrite SC. symmetry. exact SCg.
+ intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
destruct (aptr_eqb_spec' m pv) as [->|NEmp].
* assert (x = nx) as -> by congruence. destruct (HO pv g Npv) as [A1 A2]. destruct (HO g nx NX) as [B1 B2].
split; [tauto|]. intros Gp. rewrite (B2 GMg). exact (A2 Gp).
* exact (HO m x Hn).
Qed.
Section SE.
Local Abbreviation SEC_T_KINV_grp_del := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "S@'S7'7&J%211'G&R4'QBr5r4r3%43321&Q4r6r2%33215'@&S8&RN&RCr7%221<%411(0%11B%93831'?&T2zr1%3221&RKr9%>21D%311%8261%:261'9'RF%211&UC'UI&UG'F&UL&UM%4432Q91&UF&UD&UE%36762Q=51%:4Q=51=&UJ%14Q?73?&SIr:%Q521Q4%321Q;&S>%114%D6QFF9731%Q61G%Q>3G21'E&C&R>&I%11Q6r;r8%QC221%A21QM%QH3751%911qY6R71%<3R81Q;%QB2>1p0Q91pYNR91&QM%13Q@R3R8%R:31<QM&Q5%123R6%D11';%12R@RA%QB11%Q?4RBQ:Q62%Q54RCQ;Q73&SC%<3GFR7%211%QE6RG754R?1(1(:%14RJRKKR3%32;1%RB3;51%Q311pYNRO1pZDRO1%R<2B1%R=2F1p0J1p0R@1p0RK1p0S01pZ8S61pYBS71pY8S91pQBS;1pZJS?1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_KINV_grp_del) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_KINV_grp_del) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_KINV_grp_del) 2%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_KINV_grp_del) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_KINV_grp_del) 4%nat 0%nat).
Lemma KINV_grp_del : ltac:(sec_stmt2 constr:(SEC_T_KINV_grp_del) 5%nat 0%nat).
Proof.
intros K HB GN CLR.
pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
pose proof (ki_heads _ _ _ K) as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM. pose proof (go_li _ _ _ GO) as LI.
pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_sltt _ _ _ K) as CT. pose proof (ki_ginj _ _ _ K) as GI.
set (st' := grp_del st g p).
assert (CNT : 0 <= m_last_idx (get_meta_rec st g) + 1) by lia.
assert (SL : forall s x, (s_slots st') !! s = Some x <->
(s_slots st) !! s = Some x /\ forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
{ intros s x. unfold st', grp_del. rewrite (del_slots_lookup p _ _ (del_group p st) s x CNT). cbn [s_slots del_group set_groups].
split; intros [H1 H2]; split; auto; intros j Hj; rewrite ?(slot_start'_mem _ p j MEM); [apply H2; lia|].
rewrite <- (slot_start'_mem _ p j MEM). apply H2. lia. }
assert (GR : forall b gh, (s_groups st') !! b = Some gh <-> b <> p /\ (s_groups st) !! b = Some gh).
{ intros b gh. unfold st'. rewrite grp_del_groups, lookup_delete_Some. split; intros [A B]; split; auto; congruence. }
assert (HX : forall b q, hosts st' b q <-> b <> p /\ hosts st b q) by (intros; apply hosts_grp_del).
assert (Hg : forall b, hosts st b g -> b = p) by (intros b Hb; exact (GI b p g Hb HB)).
assert (Hp : forall q, hosts st p q -> q = g).
{ intros q [ai Hq]. destruct HB as [ai' Hb']. rewrite Hb' in Hq. congruence. }
assert (GMX : forall q, q <> g -> (is_gm st' q <-> is_gm st q)).
{ intros q NE. split; intros [b Hb]; exists b; [apply HX in Hb; tauto|]. apply HX. split; [| exact Hb]. intros ->. apply NE. apply Hp. exact Hb. }
assert (NGM : ~ is_gm st' g).
{ intros [b Hb]. apply HX in Hb. destruct Hb as [NE Hb]. apply NE. apply Hg. exact Hb. }
assert (KEEP : forall s, (exists gh, (s_groups st) !! s = Some gh) \/ (exists blk, blk ∈ LB /\ blk_slot blk = s) ->
forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
{ intros s Hs j Hj ->. destruct (CLR j Hj) as [C1 C2]. destruct Hs as [[gh Hgh]|[blk [Hin Hbs]]]; [rewrite C1 in Hgh; discriminate|].
exact (proj1 (Forall_forall _ _) C2 blk Hin Hbs). }
assert (LINKED_NE : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
split; [| split; [exact NGM|]].
2:{ intros s j Hs. apply SL in Hs. destruct Hs as [H1 H2]. destruct (CS _ _ _ H1) as (_ & E & J). exact (H2 j J E). }
constructor.
- apply (links_ext st st'); [reflexivity| intros; split; reflexivity| exact L].
- constructor.
+ intros h Hh. exact (CF h Hh).
+ intros sc a Ha. destruct (CA sc a Ha) as (R & N & GM & SC). split; [exact R|]. split; [exact N|]. split; [apply GMX; [apply LINKED_NE; exact N| exact GM]| exact SC].
- intros m nx Hn. change (get_meta_rec st' m) with (get_meta_rec st m) in Hn.
change (m_sizeclass (get_meta_rec st' nx)) with (m_sizeclass (get_meta_rec st nx)).
change (m_sizeclass (get_meta_rec st' m)) with (m_sizeclass (get_meta_rec st m)).
destruct (HO m nx Hn) as [A B].
assert (NEm : m <> g) by (apply LINKED_NE; rewrite Hn; discriminate).
assert (NEn : nx <> g).
{ apply LINKED_NE. intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. rewrite E in P. discriminate. }
pose proof (GMX m NEm). pose proof (GMX nx NEn). tauto.
- intros b q HBq. apply HX in HBq. destruct HBq as [NEb HBq].
assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
pose proof (CG b q HBq) as GQ.
constructor; try (change (get_meta_rec st' ?x) with (get_meta_rec st x)); try exact (go_avail _ _ _ GQ); try exact (go_freed _ _ _ GQ);
try exact (go_li _ _ _ GQ); try exact (go_freeable _ _ _ GQ); try exact (go_sc _ _ _ GQ); try exact (go_maplen _ _ _ GQ);
try exact (go_bits _ _ _ GQ); try exact (go_mem _ _ _ GQ); try exact (go_region _ _ _ GQ); try exact (go_stride _ _ _ GQ).
+ exact (go_slot _ _ _ GQ).
+ intros ML. destruct (go_nest _ _ _ GQ ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & LT & HK).
exists g1, i1, b1. change (get_meta_rec st' ?x) with (get_meta_rec st x).
split. { apply SL. split; [exact S1|]. apply KEEP. left. destruct HBq as [ai Hai]. eexists; exact Hai. }
split. { apply HX. split; [| exact HB1]. intros ->. pose proof (Hp g1 HB1) as ->.
destruct (CLR i1 I1) as [C1 _]. rewrite <- EQB in C1. destruct HBq as [ai Hai]. rewrite C1 in Hai. discriminate. }
change (get_meta_rec st' g1) with (get_meta_rec st g1). change (get_meta_rec st' q) with (get_meta_rec st q).
split; [exact FB|]. split; [exact EQB|]. split; [exact I1|]. split; [exact NF1|]. split; [exact LT|]. exact HK.
- intros b gh Hb. apply GR in Hb. destruct Hb as [_ Hb]. exact (ki_grps _ _ _ K b gh Hb).
- intros b1 b2 q H1 H2. apply HX in H1. apply HX in H2. exact (GI b1 b2 q (proj2 H1) (proj2 H2)).
- intros s q i Hs. apply SL in Hs. destruct Hs as [Hs NK]. destruct (CS s q i Hs) as (GM & E & I).
change (get_meta_rec st' q) with (get_meta_rec st q).
assert (NEq : q <> g) by (intros ->; exact (NK i I E)).
split; [apply GMX; auto| auto].
- intros b q i HBq Hi. change (get_meta_rec st' q) with (get_meta_rec st q) in Hi |- *.
apply HX in HBq. destruct HBq as [NEb HBq].
assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
apply SL. split; [exact (CT b q i HBq Hi)|].
intros j Hj E. pose proof (CT p g j HB Hj) as Tg. rewrite <- E, (CT b q i HBq Hi) in Tg. exfalso. apply NEq. congruence.
- intros b gh o Hb Ho. apply GR in Hb. exact (ki_unk _ _ _ K b gh o (proj2 Hb) Ho).
- intros q b i HBq Hi. apply HX in HBq. exact (ki_h0 _ _ _ K q b i (proj2 HBq) Hi).
- apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & REST) NG SZ].
constructor; [| unfold st'; rewrite grp_del_groups, lookup_delete_None; right; exact NG | exact SZ].
exists q, i, b. change (get_meta_rec st' ?x) with (get_meta_rec st x). change (conc st' ?x) with (conc st x). change (get_shadow st' ?x) with (get_shadow st x).
split. { apply SL. split; [exact S1|]. apply KEEP. right. exists blk. auto. }
split. { apply HX. split; [| exact HBq]. intros ->. pose proof (Hp q HBq) as ->.
destruct (CS _ _ _ S1) as (_ & E & _). exact (KEEP (blk_slot blk) (or_intror (ex_intro _ blk (conj Hin eq_refl))) i I E). }
split; [exact FB|]. split; [exact I|]. split; [exact NFR|]. exact REST.
- exact (ki_nodup _ _ _ K).
- exact (ki_cx _ _ _ K).
- exact (ki_usage _ _ _ K).
- exact (ki_bk _ _ _ K).
- exact (ki_ticks _ _ _ K).
Qed.
End SE.
Lemma KINV_put_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R7'S7'7&J%211'G&R4'QBr4r3r2%43321&C&Q5r5%2215%411'@&S8&RN&RCr6%221=%411(0%11C%93831'9';%12GH%311&UC'UI&UG'F&UL&UM%4432Q01&UF&UD&UE%36762Q451%:4Q451=&UJ%14Q673?&SCr9%211%A6Q:C64Q61(1(:r1%24Q>Q?O1%42H1%Q53H61%Q;11pYNQC1pZDQC1&S9&S6r8%33Q?21r7%QH321Q:p071p0Q71p0QB1p0QH1pYBQN1pY8R01pQBR21pZJR61").
Proof. intros st LB c g.
intros K NGM GN NS.
pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS]. pose proof (proj1 (LNN g) GN) as GP.
assert (RQ : forall q, get_meta_rec (put_meta g meta0 st) q = if aptr_eqb q g then meta0 else get_meta_rec st q) by (intros q; apply rec_put).
assert (GMne : forall q, is_gm st q -> q <> g) by (intros q Hq ->; exact (NGM Hq)).
assert (LKne : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
apply (KINV_xfer st (put_meta g meta0 st) LB) with (c := c); try reflexivity.
- intros q Hq. rewrite RQ, (aptr_eqb_neq q g (GMne q Hq)). apply geom_eq_refl.
- intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))).
exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
- intros q b j HB _ NFR FR. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))) in FR. tauto.
- exact K.
- apply links_put_meta0; [exact L| exact GN].
- apply (heads_lx st (put_meta g meta0 st)); [reflexivity | | intros sc; reflexivity | reflexivity | | exact (ki_heads _ _ _ K)].
+ intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
+ intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
- apply (homog_lx st (put_meta g meta0 st)); [reflexivity | | | exact L | exact (ki_hom _ _ _ K)].
+ intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
+ intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
- exact (ki_cx _ _ _ K).
- exact (ki_usage _ _ _ K).
Qed.
Lemma KINV_fm : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "R:'S7'7&J%211'G&R4'QBr4r3r2%43321&QOr5%2214&C&Q5r6%2219%411'@&S8&RN&RCr7%221A%411(0%11F%93831'9';%12JK%311&UC'UI&UG'F&UL&UM%4432Q31&UF&UD&UE%36762Q751%:4Q751=&UJ%14Q973?&SCr:%211%A6Q=C64Q91(1(:r1%24QAQBO1%42H1%Q53H61%Q;11pYNQF1pZDQF1&QFr9%221Q>r8%QJ321Q9p061p0Q61p0QA1p0QG1p0QK1pYBR11pY8R31pQBR51pZJR91").
Proof.
intros st LB c g K MSg NGM GN NS. unfold fm_st.
apply (KINV_queue_gen (put_meta g meta0 st) LB c g LFree).
- apply KINV_put_meta0; assumption.
- exact MSg.
- rewrite rec_put, aptr_eqb_refl. reflexivity.
- rewrite rec_put, aptr_eqb_refl. reflexivity.
- cbn. split; [| rewrite rec_put, aptr_eqb_refl; reflexivity]. intros [b [ai Hb]]. apply NGM. exists b, ai. exact Hb.
Qed.
Lemma snd_slot_start' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "O'S7&R4'G'Q2r4r3r2%43321&T2z%2214&SN&='F%231<:+@%5221&SI&RCr6r5%3221%521A%;3:E1%@281p0?1p0C1pYNI1pZ8K1pYBL1pZJN1").
Proof. intros st g p j.
intros GO Hj. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). cbn [aadd snd].
pose proof (go_stride _ _ _ GO) as [S16 _]. unfold UNIT in *.
assert (0 <= get_stride (get_meta_rec st g) * j) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma fst_slot_start' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'S7&R4'G'Q2r4r3r2%43321'@'F&5&SI&RCr5%221:%4219%637>1%738?<%:3921p0<1pYNB1pZ8D1pYBE1pZJG1").
Proof. intros st g p j. intros GO. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_free_slot_clear := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "RB'S7'7&J%211'G&R4'QBr6r5r4%43321&Q4r7r3%33215'?&T2z%2215&RK&RCr8%221>%411%82;1%:271&Q6r9%821E%321D'@'9'RF%211&UC'UI&UG'F&UL&UM%4432Q41&UF&UD&UE%36762Q851%:4Q851=&UJ%14Q:73?&SIr:%N21Q6%321Q;&S>%114%D6QAF9731(0%11H%K3H31'E&C&R>&Ir1%211r;%Q=21Q<%B21QK%Q53741%911qY6R31%<3R41Q;%QH2>1p0Q;1p0Q@1p0QL1p0R11pYNR81pZ8R81pYBR91pY8R;1pQBR=1pZJRA1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 2%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 4%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_free_slot_clear) 5%nat 0%nat).
Lemma free_slot_clear : ltac:(sec_stmt2 constr:(SEC_T_free_slot_clear) 6%nat 0%nat).
Proof.
intros K HB Hj FR.
pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (ki_sltt _ _ _ K p g j HB Hj) as Tj.
set (s := slot_start' (get_meta_rec st g) j) in *.
split.
- destruct (s_groups st !! s) as [gh|] eqn:Hs; [| reflexivity]. exfalso.
destruct (ki_grps _ _ _ K s gh Hs) as (g' & Hg' & _).
assert (HB' : hosts st s g') by (exists (g_active_idx gh); rewrite Hs; destruct gh; cbn in Hg' |- *; subst; reflexivity).
pose proof (CG s g' HB') as GO'.
destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML|ML].
+ destruct (go_nest _ _ _ GO' ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
rewrite Tj in S1. assert (g1 = g) as -> by congruence. assert (i1 = j) as -> by congruence. exact (NF1 FR).
+ destruct (go_region _ _ _ GO') as (r & _ & _ & _ & _ & _ & TOP). destruct (TOP ML) as [S0 _].
destruct (go_region _ _ _ GO) as (r0 & _ & _ & P0 & _).
pose proof (snd_slot_start' st g p j GO ltac:(lia)) as LE. fold s in LE. lia.
- apply Forall_forall. intros blk Hin E.
pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & _) _ _].
rewrite E, Tj in S1. assert (q = g) as -> by congruence. assert (i = j) as -> by congruence. exact (NFR FR).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_top_region_clear := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "RJ'S7'7&J%211'G&R4'QBr6r5r4%43321'QCr7r3r2%46387621&C'@&RL&RCr8%221=%411z%73D21%911'?&T2r1%2261&RKr:%=21D%311%7261%9261%C3Q0FM%E11&Q6r<r9%F221%421Mp061p091pYNQ91';'F%221Q<'RF'9%112&UC'UI&UG&UL&UM%34:2QE1&UF&UD&UE%36>62QI51%94QI51=&UJ%14QK73?&S>%11K%?6CB53QE1(1%12DQ9%QE3C31&5%13IR4QK%23JR5Q1%QI3K21%QJ3KR2Q<p021p071pYDM1pY2O1p0Q31p0QH1p0R31p0R91pYJR@1pZ8R@1pYBRA1pY8RC1pQBRE1pZJRI1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 2%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 4%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_top_region_clear) 5%nat 0%nat).
Lemma top_region_clear : ltac:(sec_stmt2 constr:(SEC_T_top_region_clear) 6%nat 0%nat).
Proof.
intros K L ML ALLF.
pose proof (ki_gmetas _ _ _ K) as CG. pose proof (lp_hosts _ _ _ _ _ _ L) as HB. pose proof (CG p g HB) as GO.
destruct (go_region _ _ _ GO) as (r & Hr & _ & _ & _ & _ & TOP). destruct (TOP ML) as [P0 _].
assert (REC : forall n, forall b gh, 0 <= snd b < Z.of_nat n -> (s_groups st) !! b = Some gh -> fst b = fst p -> b = p).
{ induction n as [|n IH]; intros b gh Hn Hb Hf; [lia|].
destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
pose proof (CG b g' HB') as GO'.
destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML'|ML'].
- destruct (go_nest _ _ _ GO' ML') as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
pose proof (CG b1 g1 HB1) as GO1.
destruct (go_region _ _ _ GO1) as (r1 & _ & _ & B10 & _).
pose proof (snd_slot_start' st g1 b1 i1 GO1 ltac:(lia)) as LE. rewrite <- EQB in LE.
assert (E1 : b1 = p).
{ destruct HB1 as [ai1 Hb1]. apply (IH b1 _ ltac:(lia) Hb1). rewrite FB. exact Hf. }
subst b1. assert (g1 = g) as ->.
{ destruct HB1 as [ai1 Hb1]. destruct HB as [ai Hb0]. rewrite Hb0 in Hb1. congruence. }
exfalso. destruct (Z.eq_dec i1 i) as [->|NE].
+ pose proof (lp_nogroup _ _ _ _ _ _ L) as NG. rewrite <- EQB in NG. rewrite NG in Hb. discriminate.
+ exact (NF1 (ALLF i1 I1 NE)).
- destruct (go_region _ _ _ GO') as (r' & _ & _ & _ & _ & _ & TOP'). destruct (TOP' ML') as [B0 _].
apply injective_projections; [exact Hf| rewrite B0, P0; reflexivity]. }
intros b gh Hb Hf.
destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
destruct (go_region _ _ _ (CG b g' HB')) as (rb & _ & _ & B0 & _).
apply (REC (S (Z.to_nat (snd b))) b gh); [| exact Hb| exact Hf]. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.
End SE.
Definition ZINV (st : mstate) (Zs : list aptr) : Prop :=
forall q b, m_mem (get_meta_rec st q) = Some b -> hosts st b q \/ In q Zs.
Lemma ZINV_of_CINV : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'7&J%211'Kr2r1%3221&QAr3(8&R4%211%5241p071pQB<1pZJ@1").
Proof. intros st LB. intros C q b H. left. exact (ci_memh _ _ C q b H). Qed.
Lemma ZINV_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "Q<'S7'7&R4%211'@&S8&RM&RCr3r1%3221%511r4%6214%811%;3:41pZ<>1'UI&UG'F&UL'G&UM%544321&UF&UD&UE%36872651'RF%<4K621&S>%11G%21D%M3421&QAr5%221L%322Ip021p061p0H1pXFQ61pZLQ:1pZJQ;1").
Proof. intros st st' Zs.
intros EM EG Z q b H. rewrite EM in H. destruct (Z q b H) as [HB|HI]; [left| right; exact HI].
unfold hosts in *. rewrite EG. exact HB.
Qed.
Lemma ZINV_sbl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'7&R4%211'QEr3r2%3221&QAr4%2214%3226p021p061pXF;1pZL?1pZJ@1").
Proof. intros st st' Zs.
intros S. apply ZINV_ext; [| exact (sbl_groups _ _ S)].
intros q. destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (E & _). exact E.
Qed.
Lemma ZINV_aor : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7&R4'G'7%113&QAr4r1%3221&QJr5r3%33261r2%9221p071pXF<1pYJ?1pYBA1pZJC1").
Proof. intros st g i Zs. apply ZINV_ext; [| reflexivity]. intros q. unfold aor_st. rewrite rec_upd. destruct (aptr_eqb_spec' q g); [subst; reflexivity| reflexivity]. Qed.
Lemma ZINV_act : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7&R4'G'7%113&QAr4r1%3221&QIr5r3%33261r2%9221p071pXF<1pXL?1pXJA1pZJC1").
Proof. intros st a act Zs. apply ZINV_ext; [| reflexivity]. intros q. unfold act_st. rewrite rec_upd. destruct (aptr_eqb_spec' q a); [subst; reflexivity| reflexivity]. Qed.
Lemma ZINV_pd : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "E'2'S7'G'7&R4%211&QAr3r1%3221&QNr5r4%33216r2%9221p071pXF<1pZF@1pZJB1pXND1").
Proof. intros an st sc Zs. intros Z. destruct (pd_st_cases an st sc) as [-> | (a & _ & _ & ->)]; [exact Z| apply ZINV_act; exact Z]. Qed.
Lemma ZINV_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S7'S4p011'7&R4%211&QAr3r1%3221&SKr4%2251r2%8221p061pXF;1pY>?1pZJB1").
Proof. intros st f Zs. apply ZINV_ext; reflexivity. Qed.
Lemma ZINV_fg_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7&R4'7%112&QAr3r1%3221&QLr4%2215r2%8221p061pXF;1pYB>1pZJ@1").
Proof. intros st g Zs. intros Z. unfold fg_usage_st. destruct (_ <? 48); [apply ZINV_ctx|]; exact Z. Qed.
Lemma ZINV_seq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7'G'7&R4%211&QAr3r1%3221&S:&SJr4%211%4271r2%:221p081pXF=1pZFA1pZJC1").
Proof. intros st sc Zs.
intros Z. unfold record_seq, step_seq.
destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); repeat apply ZINV_ctx; exact Z.
Qed.
Lemma ZINV_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7'RG&R4'7%112&QAr4r1%3221&RAr3r5%33621r2%9221p071pXF<1pYB?1pYFA1pZJC1").
Proof. intros st h g Zs. apply ZINV_sbl. apply sbl_dequeue. Qed.
Lemma ZINV_queue : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "D'S7'RG&R4'7%112&QAr4r1%3221&QGr3r5%33621r2%9221p071pXF<1pYB?1pYFA1pZJC1").
Proof. intros st h g Zs. apply ZINV_sbl. apply sbl_queue. Qed.
Lemma ZINV_grp_del : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "H'S7&R4'7%112&QAr4r1%3221&Q4r5r3%33216&QMr6%23159(3%13?76%=231p071p0<1pXFA1pZ8D1pYBE1pZJG1").
Proof. intros st g p Zs.
intros Z HB q b H. change (get_meta_rec (grp_del st g p) q) with (get_meta_rec st q) in H.
destruct (Z q b H) as [Hq|HI]; [| right; right; exact HI].
destruct (aptr_eqb_spec' b p).
- subst. right. left. destruct Hq as [ai Hq]. destruct HB as [ai' HB]. rewrite HB in Hq. congruence.
- left. apply hosts_grp_del. split; [exact n| exact Hq].
Qed.
Lemma ZINV_fm : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "C'S7&R4'7%112&QAr3(3r2r1%33821%6251&QFr4%2218%:217p051pXF=1pYB@1pZJB1").
Proof. intros st g Zs.
intros Z. unfold fm_st. apply ZINV_queue.
intros q b H. rewrite rec_put in H. destruct (aptr_eqb_spec' q g); [subst; cbn in H; discriminate|].
destruct (Z q b H) as [Hq|[E|HI]]; [left; exact Hq| exfalso; exact (n (eq_sym E))| right; exact HI].
Qed.
Lemma ZINV_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_Bpres "A'S7'7&R4%211&QAr3r2%3221&SM%13743r5%7216p031p061pXH;1pXF<1pZJ@1").
Proof. intros st Zs Zs'. intros Z HI q b H. destruct (Z q b H) as [Hq|Hin]; [left; exact Hq| right; exact (HI _ Hin)]. Qed.
End CEIL_WRAP_4.
