(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_WFree
MI_Pres4 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_inv.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocFacts_inv2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1bool"; "1fst"; "1length"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3Forall"; "3map"; "4N"; "4Z"; "0K"; "0LB"; "0LS"; "0N"; "0RUNp"; "5blk_addr"; "5blk_size"; "5blk_slot"; "5block"; "6block_ok"; "6fact_active"]; ["6fact_avail_clear"; "6fact_blk_unknown"; "6fact_blocks_disjoint"; "6fact_cell_ticks"; "6fact_ctx"; "6fact_free_clear"; "6fact_gmeta"; "6fact_hdr0"; "6fact_hdr_clear"; "6fact_maplen"; "6fact_masks"; "6fact_ptrs"; "6fact_slots"; "6fact_slots_complete"; "6fact_usage"; "6sstart_of"]; ["7ticks_ok"; "8alloc_ceiling"; "9MR"; "9blk"; "9bslot"; "9gcnt"; "9gend"; "9group_ok"; "9hosts"; "9sstart"; "9zsum"; ":IB"; ":RKGroup"; ":UNIT"; ":aptr"; ":area"]; [":conc"; ":cptr"; ":get_stride"; ":ghdr"; ":lhead"; ":m_avail"; ":m_freed"; ":m_last_idx"; ":m_mem"; ":meta"; ":meta0"; ":mkGhdr"; ":optr"; ":r_base"; ":r_kind"; ":r_len"]; [":region"; ":rkind"; ":round_up_pg"; ":s_areas"; ":s_groups"; ":s_metas"; ":s_next_rid"; ":s_regions"; ":strip"; ";In"; ";NoDup"; "<lt"; "=add"; "=le"; "=lt"; "=mul"]; ["=of_nat"; "=pow"; "=sub"; "=testbit"; "0X"; "0a"; "0ai"; "0ar"; "0b"; "0b1"; "0b2"; "0blk"; "0bm"; "0c"; "0g"; "0gh"]; ["0h"; "0i"; "0l"; "0m"; "0m1"; "0m2"; "0n"; "0off"; "0r"; "0rid"; "0sc"; "0st"; ">lookup"; "?N_countable"; "?Z_countable"; "?prod_countable"]; ["@prod_eq_dec"; "Amap_to_list"; "Bgmap"; "Bgmap_fold"; "Bgmap_lookup"; "Ceq_dec"; "Deq_dec"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
(forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
induction l as [|a l IH]; intros Hinj ND; cbn; [constructor|].
inversion ND; subst. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy).
rewrite (Hinj a y ltac:(now left) ltac:(now right) (eq_sym Ey)) in H1. exact (H1 Hy).
- apply IH; [| assumption]. intros x y Hx Hy. apply Hinj; now right.
Qed.
Lemma NoDup_Z_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q0'6'D%211&RMzr1%3221'RJr3%2281&RIr5%23;71'<r2%<2;1&RN%1236%5231p071pX@C1&S0&5%12F<%311r4%G221p071p0C1p0G1pQBM1pW6M1").
Proof. intros l N.
intros Hn ND HB.
assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
{ intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (HB x Hx). split; [lia|]. apply in_seq. lia. }
pose proof (NoDup_incl_length ND INCL) as Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.
Lemma zsum_bound : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "N'6'D%211&RIr1r3%33521'<&RMzr2%3221%4227%6221p081pX@>1&QJ%11<%:291&RO&S0&5%12EA%311%52>1%A281%C281p0<1pQ<K1pW6K1").
Proof. intros l K.
induction l as [|a l IH]; intros HB; cbn -[Z.of_nat]; [lia|].
pose proof (HB a ltac:(now left)). specialize (IH ltac:(intros x Hx; apply HB; now right)).
unfold zsum in IH. rewrite Nat2Z.inj_succ. lia.
Qed.
Section MF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Lemma mem_hosts : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "C&QN'=&R<&R8&QBvSKr2%3221%511(2r1%22;1%;3:41&QHr3%23:91p041pVBA1pVNB1").
Proof. intros g b. intros H. destruct (im_group _ _ _ IM g b H) as [Hh|Hz]; [exact Hh|]. rewrite ZB in Hz. destruct Hz. Qed.
Lemma hosts_GO : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q@&QN&QHvSKr2r1%43321'>'D'<'='7'R3%211&SL'T2&T0'C&T5&T6%4432<1&SO&SM&SN%36762@51%:4H51=&T4%14J73?r4&RD%11K%A6NC6431(2(R;r3%32Q21%321O%52I1%L3I71'QGvS4vG%362Q718>Q5%Q2251qV>Q41%Q62Q51p0Q81pVNQ>1pVBQ?1").
Proof. intros b g. intros H. exact (hosts_ok _ _ _ IG _ _ H). Qed.
Lemma sstart_of_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "<'R9'D'=&Q?r2r1%3221&QI%1243%73831pW491pWB;1").
Proof. intros r i. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_group_in_region := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "QJ&QN&QHvSKr2r1%43321'>'R@'<'='7%114&SL'C'T2&T5&SM%34421:&T4%14643<&4'Dr4%33:21&RG%11G%>6=C9731(2%12EH%D3B31'RA&R>%11L(QL%I3421&RMz&:%13IA@%4231&QF&QBr3%22Q91%411&RB&R?%11Q;%311%>251%Q:2;1%Q;2A1%Q<2G1qWBQ>1%Q@2Q?1p0QB1pW8QH1pVBQI1")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_group_in_region) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_group_in_region) 1%nat 0%nat).
Lemma group_in_region : ltac:(sec_stmt2 constr:(SEC_T_group_in_region) 2%nat 0%nat).
Proof.
intros Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ].
- destruct (top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & i & c & bt & Ha & Ht & Htl & Hf).
destruct (anc_box _ _ _ _ IM IG IS m t i c b Ha Hm) as (B1 & B2 & B3).
destruct (anc_facts _ _ _ _ IM IG IS m t i c Ha) as (bm & bp & Hm' & Hp' & _ & Hi & _).
pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hp'); subst bp.
destruct (hosts_GO _ _ Ht) as (ait & Hbt & GOt).
destruct (g_top _ _ _ _ _ _ GOt Htl) as (S0 & r & Hr & Kr & ML & GE).
rewrite <- Hf. exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|].
pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st t) + 1) Ht ltac:(lia)) as SM. rewrite <- gend_eq in SM. lia.
- destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE). exists r. repeat split; auto. lia.
Qed.
End SE.
Lemma conc_group : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "QO&QN&QHvSKr2r1%43321'>'R@'<'='7%114&SL'C'T2&T5&SM%34421:&T4%14643<&4'Dr4%33:21&RG%11G%>6=C9731(2%12EH%D3B31'RA&R>%11L(QL%I3421&R0%12Q2>&RL&R=%11Q3&:%13LDC%5231%Q23F71&RM%1269+Q0%:2;1&RB&R?%11Q>%311%?2=1%9261%Q>291%Q?2<1%Q@2F1%QA2L1qWBQC1%QE2QD1p0QG1pW8QM1pVBQN1").
Proof. intros b m.
intros Hm. destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). pose proof (gend_ge _ _ _ IM IG _ _ Hm) as G32.
exists r. unfold conc, get_region. rewrite Hr. repeat split; auto; lia.
Qed.
Lemma f_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q4&RHvSK%211%411").
Proof.
pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
unfold fact_ctx. rewrite ctx_strip. unfold ctx.
split; [exact C1|]. split; [destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia|].
split; [destruct S2 as [(E & _)|[E _]]; rewrite E; auto|]. split; [exact C2|].
split.
- intros i. unfold bounces, ctx. cbn. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)).
- intros i. unfold unmap_seq, ctx. cbn. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)).
Qed.
Lemma f_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&O&RHvSK%211%411").
Proof.
intros sc g H. rewrite active_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
destruct (il_active _ _ IL sc g Hin) as (Hsc & [b Hb] & Esc). split; [exact Hsc|]. split; [exact Esc|].
rewrite (hosts_mem _ _ _ IM _ _ Hb). discriminate.
Qed.
Lemma f_masks : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q:&RHvSK%211%411").
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
destruct (hosts_GO _ _ (mem_hosts _ _ H)) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
split; [intros i Hi Ha; pose proof (M3 i Hi Ha); lia|]. split; [exact M4|].
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.testbit (m_avail (MR st g)) i) eqn:Ea; destruct (Z.testbit (m_freed (MR st g)) i) eqn:Ef; try reflexivity.
exfalso. exact (M5 i Hi Ea Ef).
Qed.
Lemma f_maplen : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q9&RHvSK%211%411").
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE).
destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). pose_ceil. lia.
Qed.
Lemma f_slots : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q<&RHvSK%211%411").
Proof.
intros p g idx H. rewrite s_slots_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
destruct (is_valid _ _ _ IS _ _ _ H) as ([b Hb] & Hi & Ep). exists b. split; [exact (hosts_mem _ _ _ IM _ _ Hb)|].
rewrite (slot_start'_eq _ _ _ IM _ _ idx Hb) in Ep. rewrite Ep. cbn. rewrite sstart_of_eq. auto.
Qed.
Lemma f_slots_complete : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q=&RHvSK%211%411").
Proof.
intros g b i H Hi. rewrite s_slots_strip. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_hosts _ _ H) as Hm. rewrite sstart_of_eq, <- (slot_start'_eq _ _ _ IM _ _ i Hm). exact (is_total _ _ _ IS _ _ _ Hm Hi).
Qed.
Lemma f_hdr0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "3&Q7vSK%211").
Proof.
intros g b i H Hi. fold (MR st g) in *. rewrite sstart_of_eq. exact (ish_hdr0 _ _ ISH b g i (mem_hosts _ _ H) ltac:(unfold cnt_of; lia)).
Qed.
Lemma f_cell_ticks : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "3&Q3vSK%211").
Proof. intros rid sh o v t Hs Hc. exact (proj2 (proj1 (ish_ticks _ _ ISH rid sh Hs) o v t Hc)). Qed.
Lemma f_ticks : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "3&Q@vSK%211").
Proof.
split.
- intros rid sh u hl ch Hs Hu Hin. exact (proj1 (proj2 (ish_ticks _ _ ISH rid sh Hs)) u hl ch Hu Hin).
- intros rid sh pg t Hs Hp. exact (proj2 (proj2 (ish_ticks _ _ ISH rid sh Hs)) pg t Hp).
Qed.
Lemma f_gmeta : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q6&RHvSK%211%411").
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
pose proof (g_li _ _ _ _ _ _ GO) as LI.
assert (AV : m_avail (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
assert (FR : m_freed (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
split.
{ pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. rewrite s_areas_strip. split; [exact Ha|]. split; [exact Hka|]. exact Emk. }
split; [lia|]. split; [lia|]. split; [exact LI|]. split; [exact (g_freeable _ _ _ _ _ _ GO)|].
pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
split. { destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia]. }
split; [exact ML|].
split. { exists ai. rewrite s_groups_strip. split; [exact Hb|]. split; [exact AI|]. exact M3. }
split. { destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). exists r. rewrite s_regions_strip.
pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|]. rewrite sstart_of_eq. rewrite gend_eq in GE. exact GE. }
pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
split; [exact SG|]. split; [exact SM|].
pose proof (g_stride _ _ _ _ _ _ GO) as GS.
split. { intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. nia. }
split. { intros Hsc i Hi Ht. destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| lia].
exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 _]. rewrite A0 in Ht. rewrite Z.bits_0 in Ht. discriminate. }
intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. lia.
Qed.
Lemma bit_slot_nonH : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "RK&QN'9'C'D%3221'='7'R3%211&SL'T2&T0&T5&T6%34<2;1&SO&SM&SN%36@62?51%94C51<&T4%14E73>r3&RDvSK%211%A6FC7541(2(R;r4%32N1r2%4221%62J1%M3J81'<&RMz%2217&R7&QBr5%22B1%411%82=1%:271'@'3&S3&R5r6%;2K1%311%521O(;%QB3821&R6%116%:21Q4%QF3<15%>251(8&4%13QMQL=&QIr7%J2Q:1%321Q6%74R2R151%QL6R1QNQBQ@1Q<(1%11R0%R33R031&?&RI&B&QC&R1&QDv0%544321%73R==1%911%Q@2;1p0H1p0Q81p0QD1pW4RD1pV>RE1pVBRE1pVNRJ1").
Proof. intros g b ai i.
intros Hb Hil Hbits. assert (Hm : hosts st b g) by (exists ai; exact Hb).
pose proof (is_part _ _ _ IS b g ai i Hb Hil) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm) in P.
unfold one5, tbit in P. destruct P as (_ & nAB & nAC & nAD & _ & nBC & nBD & _).
split.
- destruct (s_groups st !! (fst b, sstart (MR st g) i)) eqn:E; [| reflexivity]. exfalso.
destruct Hbits as [A|F]; [apply nAD| apply nBD]; split; auto; intros Y; rewrite Y in E; discriminate E.
- intros C. destruct Hbits as [A|F]; [apply nAC| apply nBC]; split; auto.
Qed.
Lemma hdr_hosts : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q6&QN'R3'='7%113&SL'T2&T0'C&T5'D&T6%544321&SO&SM&SN%36872651%;4A51@&T4%14C73Br2&RDvSK%211%C6HG7541(2r1%22J1%J3H41'>&QHr4%23:16qW8Q11%52Q21p071pW0Q31pVBQ51").
Proof. intros b gh.
intros Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _). exists m. destruct gh as [gm gai]; cbn in Eg; subst gm. exists gai. exact Hb.
Qed.
Variable LB : list block.
Hypothesis CR : CORR st LB BL.
Lemma LB_blk : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "QA&M&RIr1vF%33421'>&R1'D'<'9%1243%2214(8r3r2%349821%44691>v0%A3721'=&Lr5%211%43A1:&K%114%73C1H&J%117&RL&R0vSK%221C&RO&QM%221E%7241%B3N91%N2<1%O2@1%Q02F1qW>Q21%Q52Q31qW@Q41%Q72Q51qVLQ71%Q92Q81p0Q;1pVHQ@1").
Proof. intros blk.
intros Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)). destruct k as [[c off] n].
exists c, off, n. cbn [bslot boff bsize fst snd] in C1, C2, C3. auto.
Qed.
Section SE.
Local Abbreviation SEC_T_LB_geo := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "T8&M&RIr1vF%33421'>&R1'D&QN'R@'<'9%1265%2216(8r7r6%34;:21r5%547<21v0%D3821'=&Lr9%211%43D1;&K%114%73F1;&QHvSKr3r4%43321&RMzr2%3221&R7&QB%12:8%311%8261%Q2261'C&4%132Q8?&QI%128<%Q445Q;31%M3Q=Q41'7'R3%211&SL'T2&T0&T5&T6%34?2QE1&SO&SM&SN%36C62QI51%94QI51<&T4%14QK73>&RD%11Q6%?6R0A53QG1(1%11C%QC3C31%F1R1%C4NA=R2%:4OB>R3&RG%11Q?%H6Q2R643Q01(2%12R8R?%QL3831'RA&R>%11RC(QL%R13421&J%11R1&RL&R=%11RJ%321Q<&RO&QM%221R@%7241%R<3RK91%R02QORC%R12R0RB%;25RC&S2&R2%11QO&QK%4221%R8261%S2281%S32:1%S42<1%S52H1%S62N1%S72Q81%S82QO1%S92R71%S:2RB1%S;2RH1%S<2RL1%S=2S21qWBS?1%SD2S@1qW4SC1%SF2SD1qVJSD1%SH2SE1qW8SF1%SJ2SG1qW>SI1%SL2SJ1qW@SK1%SN2SL1qVLSN1%T02SO1p0T21pVHT71")) (only parsing).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_LB_geo) 0%nat 0%nat).
Lemma LB_geo : ltac:(sec_stmt2 constr:(SEC_T_LB_geo) 1%nat 0%nat).
Proof.
intros Hb. destruct (LB_blk _ Hb) as (c & off & n & Hk & C1 & C2 & C3).
destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh. assert (Hm : hosts st bm m) by (exists ai; exact Hh).
destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr).
exists c, off, n, m, bm, i, r.
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hf.
repeat split; auto; try lia.
rewrite C3, Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. lia.
Qed.
End SE.
Lemma f_free_clear : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "6&Q5&RHvSK%211vF%5221").
Proof.
change (fact_free_clear st LB). intros g b i H Hi Hbits. fold (MR st g) in *. cbn zeta. rewrite !sstart_of_eq.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Hil : 0 <= i <= m_last_idx (MR st g)). { destruct Hbits as [A|F]; [pose proof (M3 i Hi A); lia | pose proof (M4 i Hi F); lia]. }
destruct (bit_slot_nonH _ _ _ _ Hb Hil Hbits) as [NH NB].
pose proof (sstart_succ st g i) as SS.
split.
- intros b' gh Hb' Hf. destruct (hdr_hosts _ _ Hb') as [m' Hm'].
destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hm Hil NH m' b' Hm' Hf) as [A|A]; unfold IB; lia.
- intros blk Hblk Hf. destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr & Kr & Ea & Ho & Hn & Fit).
rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr. exists r. split; [reflexivity|].
rewrite Ea, C2. pose proof (sstart_succ st m2 i2) as SS2.
assert (NE : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NB. rewrite <- Hf, <- Ec, <- C1.
destruct (Forall2_In_l _ _ _ _ CR Hblk) as (k & HkB & (Ek & _)). rewrite Ek. apply in_map. exact HkB. }
destruct (sep_ext _ _ _ _ IM IG IS g b i Hm Hil NH m2 b2 i2 Hm2 Hf Hi2 NE ltac:(rewrite Ec in NH2; exact NH2)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
Lemma f_avail_clear : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "6&Q0&RHvSK%211vF%5221").
Proof. intros g b i H Hi Ha. exact (f_free_clear g b i H Hi (or_introl Ha)). Qed.
Lemma f_hdr_clear : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "6&Q8&RHvSK%211vF%5221").
Proof.
change (fact_hdr_clear st LB). intros b gh blk r Hb Hblk Hf Hr.
destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r' & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr' & Kr & Ea & Ho & Hn & Fit).
rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr' in Hr. inversion Hr; subst r'.
destruct (hdr_hosts _ _ Hb) as [m' Hm']. rewrite Ea, C2. pose proof (sstart_succ st m2 i2).
rewrite Ec in NH2. destruct (sep_ghdr _ _ _ _ IM IG IS m2 b2 i2 Hm2 Hi2 NH2 m' b Hm' (eq_sym Hf)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
Lemma f_blk_unknown : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "4&Q1vSKvF%3221").
Proof.
intros blk r Hblk Hr a Ha. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _). cbn [bslot fst snd] in Hs.
pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U). cbn [bslot boff bsize fst snd] in U.
rewrite C1 in Hr |- *. rewrite C3, C2 in Ha. unfold conc, get_region in Ha. rewrite Hr in Ha.
destruct (U (a - r_base r) ltac:(lia)) as [h Hh]. exists h. exact Hh.
Qed.
Lemma f_blocks_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "4&Q2vSKvF%3221").
Proof.
intros b1 b2 H1 H2 Hf NE.
destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1).
destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
rewrite E1 in N1. rewrite E2 in N2.
destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
Lemma LB_blocks_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "7'A&M'NvSK%211vF%63521").
Proof.
apply List.Forall_forall. intros blk Hblk. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
constructor.
- exists m, i. rewrite C1. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. fold (MR st m).
split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|].
split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|].
exists off. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). rewrite C2, C3. repeat split; lia.
- rewrite C1. destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr). rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. exists r. auto.
- rewrite C2. exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
Qed.
Lemma LB_nodup : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "8'RJ&R1&B&M&LvF%443521%7261").
Proof.
rewrite (Forall2_map_eq (corr1 st) blk_slot bslot LB BL CR ltac:(intros a b (E & _); exact E)).
apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
Qed.
Lemma region_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "M'C'R@'='7%113&SL'T2&T5&SM%349218&T4%14;43:r2&RGvSK%211%;6@?7541(2r1%22B1%B3@41&RKr3&RF%11:%4231p061pWBJ1pWDL1").
Proof. intros rid r. exact (ir_ids _ _ _ IR rid r). Qed.
Lemma area_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q9'9'C'D%3221'QO'='7%113&SL'T2&QN&T0&T5&T6%34=2<1&SO&SM&SN%36A62@51%:4951?&T4%14;73Ar2&RCvSK%211%B6GF7541(2r1%22I1%I3G41&RK&4r3%23Q1Q01&RF%11<%6231p081pV@Q31pV<Q51").
Proof. intros a ar. intros Ha. destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & _) & _). exact (region_rid _ _ Hr). Qed.
Lemma area_rid' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q9'9'C'D%3221&?'='7'QO%211&SL'T2&QN&T0&T5&T6%34>2=1&SO&SM&SN%36B62A51%:4951=&T4%14;73?r1&RCvSK%211%B6HD7541(1%11F%I3F31%K11&RK&4r2%23Q2Q11&RF%11<%6231p081pV<Q51").
Proof. intros a. intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [exact (area_rid _ _ E)| congruence]. Qed.
Lemma present_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q9'9'C'D%3221&?'='7'R9%211&SL'T2&QN&T0&T5&T6%34>2=1&SO&SM&SN%36B62A51%:4951=&T4%14;73?r1&REvSK%211%B6HD7541(1%11F%I3F31%K11&RK&4r2%23Q2Q11&RF%11<%6231p081pW8Q51").
Proof. intros m.
intros Hm. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). unfold mslot, aadd. cbn [fst]. exact (area_rid _ _ Ha).
Qed.
Lemma nonzero_present : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q6&QN&?'='R9&QBvSKr1%3221&R:%73621%911'7%119&SL'T2&T0'C&T5'D&T6%544321&SO&SM&SN%36872651%;4I51F&T4%14K73Hr2&RE%11I%B6OL6431(1%11N%Q03F31%Q211p0J1pW8Q51").
Proof. intros m. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; congruence. Qed.
Lemma listed_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "E&QN'R4&RIr2vGr1%211%53741&RK&4'C'Dr3%43321&RFvSK%211%9241p0;1pW2B1pW8D1").
Proof. intros m h. intros H. apply present_rid. exact (listed_present _ _ _ _ _ INV m h H). Qed.
Lemma hosts_rid : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "B&QN&QHvSKr2r1%43321&RK&4'C'Dr3%43321&RF%11;%8231p0:1pW8@1pVBA1").
Proof. intros b m. intros [ai Hb]. destruct (ig_region _ _ _ IG _ _ Hb) as (r & Hr & _). exact (region_rid _ _ Hr). Qed.
Lemma f_ptrs : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "3&Q;vSK%211").
Proof.
split.
- unfold ptrs_in. cbn zeta.
assert (HD : forall h, optr_in (fun rid => (rid < s_next_rid st)%N) (get_head st h)).
{ intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (listed_rid _ _ (head_listed _ _ _ _ _ INV h a E)). }
split; [exact (HD LFree)|].
split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & _). exact (region_rid _ _ Hr). }
split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_head _ IA q E)). }
split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_tail _ IA q E)). }
split. { destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:E; cbn; [| exact I].
destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & _). exact (region_rid _ _ Hr). }
split; [intros sc; exact (HD (LActive sc))|].
split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |rid off]; try exact I.
destruct BR as (_ & r & Hr & _). exact (region_rid _ _ Hr). }
split.
{ intros g. fold (MR st g). pose proof (il_link _ _ IL g) as [[L1 L2] L3].
assert (NX : forall x, m_next (MR st g) = Some x -> (fst x < s_next_rid st)%N).
{ intros x Hx. destruct (L2 ltac:(rewrite Hx; discriminate)) as [h Hh]. exact (listed_rid _ _ (next_listed _ _ _ _ _ INV h g x Hh Hx)). }
split. { destruct (m_prev (MR st g)) as [p|] eqn:Ep; cbn; [| exact I].
destruct (m_next (MR st g)) as [x|] eqn:Ex; [| discriminate (L3 eq_refl)].
destruct (L2 ltac:(discriminate)) as [h Hh]. exact (listed_rid _ _ (prev_listed _ _ _ _ _ INV h g p Hh Ep)). }
split. { destruct (m_next (MR st g)) as [x|] eqn:Ex; cbn; [| exact I]. exact (NX x eq_refl). }
destruct (m_mem (MR st g)) as [b|] eqn:Eb; cbn; [| exact I]. exact (hosts_rid _ _ (mem_hosts _ _ Eb)). }
split.
{ intros a ar Ha. split; [exact (area_rid _ _ Ha)|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_rid' _ (NXT a' E)). }
intros b gh Hb. destruct (hdr_hosts _ _ Hb) as [m Hm]. split; [exact (hosts_rid _ _ Hm)|].
destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _). rewrite Eg. cbn. apply present_rid. apply nonzero_present. intros E. rewrite E in Hmem. cbn in Hmem. discriminate.
- intros rid Hrid. split.
+ destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. pose proof (region_rid _ _ E). lia.
+ destruct (s_shadow st !! rid) as [sh|] eqn:E; [| reflexivity]. destruct (ish_dom _ _ ISH _ _ E) as (r & Hr & _). pose proof (region_rid _ _ Hr). lia.
Qed.
Lemma conc_group_inj : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "G&QN&QHvSKr4r2%43321'='D&R0r6%2281r5%42:1%73631r7%93?16p031p0<1p0=1pW<C1pW:D1pVFE1pVDF1").
Proof. intros b1 b2 m1 m2.
intros H1 H2 E.
destruct (conc_group _ _ H1) as (r1 & R1 & K1 & C1 & LO1 & HI1). destruct (conc_group _ _ H2) as (r2 & R2 & K2 & C2 & LO2 & HI2).
destruct (N.eq_dec (fst b1) (fst b2)) as [Ef|NEf].
- rewrite Ef, R2 in R1. inversion R1; subst r1. apply injective_projections; [exact Ef| lia].
- exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NEf) as D. unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.
Lemma groups_count : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "Q0&RM&S0&5'9&QN'R3%3221&T1'T2&T0'C&T5'D&T6%544321&SO&SM&SN%36872651%;4?51>&T3%14A73@&RDvSK%211%B5ED641%H2D1%J11&QAvI%211%O241").
Proof.
rewrite <- (length_map (fun bh : aptr * ghdr => conc st (fst bh))).
assert (HIN : forall bh, In bh (map_to_list (s_groups st)) -> s_groups st !! (fst bh) = Some (snd bh)).
{ intros [b h] Hin. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
apply NoDup_Z_length; [pose_ceil; lia| |].
- apply NoDup_map_on.
+ intros [b1 h1] [b2 h2] I1 I2 E. cbn in E. pose proof (HIN _ I1) as G1. pose proof (HIN _ I2) as G2. cbn in G1, G2.
destruct (hdr_hosts _ _ G1) as [m1 Hm1]. destruct (hdr_hosts _ _ G2) as [m2 Hm2].
pose proof (conc_group_inj _ _ _ _ Hm1 Hm2 E) as Eb. subst b2. rewrite G1 in G2. inversion G2. reflexivity.
+ pose proof (NoDup_fst_map_to_list (s_groups st)) as ND. apply NoDup_ListNoDup in ND.
apply (NoDup_map_inv fst). exact ND.
- intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn. pose proof (HIN _ Hin) as G. cbn in G.
destruct (hdr_hosts _ _ G) as [m Hm]. destruct (conc_group _ _ Hm) as (r & Hr & Kr & C & LO & HI).
destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CE & _). lia.
Qed.
Lemma gcnt_bound : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "A'D'<&RMz&QEvSKr1%3221%6251&RN&S1+2+QL%3221%5271%>271pWF@1").
Proof. intros sc.
unfold gcnt.
pose proof (zsum_bound (map (fun bh : aptr * ghdr => match g_meta (snd bh) with
| Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0 | None => 0 end) (map_to_list (s_groups st))) 32) as ZS.
rewrite length_map in ZS. pose proof groups_count as GC. pose_ceil.
eassert (H : _); [| specialize (ZS H); lia].
intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn.
assert (G : s_groups st !! b = Some h). { apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
destruct (im_hdr _ _ _ IM _ _ G) as (m & Eg & Hmem & AI). rewrite Eg.
destruct (hosts_GO _ _ (mem_hosts _ _ Hmem)) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of.
destruct (m_sizeclass (MR st m) =? sc); lia.
Qed.
Lemma f_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_inv2 "5&Q>&RHvSK%211%411").
Proof.
intros i. rewrite usage_strip. destruct (c_usage (s_ctx st) !! i) as [v|] eqn:E.
- pose proof (ia_usage_keys _ IA i v E) as Hi. rewrite (ia_usage _ IA i Hi). apply gcnt_bound.
- unfold usage, ctx. rewrite E. cbn. lia.
Qed.
End MF.
End CEIL_WRAP_1.
Local Ltac inst f INV CR :=
first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
| exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Theorem areach_facts_proof : forall {resv} st LB, AREACH_from resv st LB -> @MFACTS_g resv st LB.
Proof.
intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
constructor.
- inst LB_blocks_ok INV CR.
- inst LB_nodup INV CR.
- inst f_ticks INV CR.
- rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
- inst f_ctx INV CR.
- inst f_active INV CR.
- inst f_gmeta INV CR.
- inst f_avail_clear INV CR.
- inst f_hdr0 INV CR.
- inst f_free_clear INV CR.
- inst f_hdr_clear INV CR.
- inst f_usage INV CR.
- inst f_masks INV CR.
- inst f_maplen INV CR.
- inst f_slots INV CR.
- inst f_slots_complete INV CR.
- inst f_ptrs INV CR.
- inst f_blk_unknown INV CR.
- inst f_blocks_disjoint INV CR.
- inst f_cell_ticks INV CR.
Qed.
End CEIL_WRAP_2.
