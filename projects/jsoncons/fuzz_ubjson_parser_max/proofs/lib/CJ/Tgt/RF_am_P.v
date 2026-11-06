(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocFacts_AM.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export F_am_P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_am_P () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_E."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_P."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3N"; "3Z"; "0P"]; ["0RUNp"; "4am_took"; "5am_init_st"; "6carve_st"; "7AMI"; "7ctx_core_eq"; "8AMpre_g"; "9clr_links"; ":meta_slot"; ";am_rel"; ";ptrs_in"; "<AREA_HDR"; "<BrkDead"; "<BrkLive"; "<LFree"; "<META_SIZE"]; ["<NSLOTS"; "<RKGroup"; "<aadd"; "<aptr"; "<area"; "<brkstate"; "<c_active"; "<c_avail_meta"; "<c_avail_meta_areas"; "<c_avail_meta_count"; "<c_bounces"; "<c_brk"; "<c_free_meta_head"; "<c_meta_area_tail"; "<c_mmap_counter"; "<c_secret"]; ["<c_seq"; "<c_unmap_seq"; "<c_usage"; "<conc"; "<ctx"; "<dequeue"; "<get_meta_rec"; "<ghdr"; "<m_mem"; "<m_next"; "<m_prev"; "<mctx"; "<meta"; "<meta0"; "<mkRegion"; "<mstate"]; ["<new_region"; "<optr"; "<r_base"; "<r_kind"; "<r_len"; "<region"; "<rkind"; "<s_areas"; "<s_groups"; "<s_metas"; "<s_next_rid"; "<s_regions"; "<s_reserved"; "<s_shadow"; "<s_slots"; "<s_tick"]; ["<set_regions"; "<shadow"; "<upd_ctx"; "=ref_reserved"; ">add"; ">le"; ">lt"; ">mul"; ">pow"; ">sub"; "0a"; "0base"; "0f"; "0g"; "0h"; "0k"]; ["0len"; "0m"; "0mo"; "0nx"; "0off"; "0p"; "0pv"; "0q"; "0r"; "0rid"; "0st"; "0st'"; "0st1"; "0stI"; "0stX"; "?insert"]; ["?is_Some"; "?lookup"; "@N_countable"; "@Z_countable"; "@prod_countable"; "Aprod_eq_dec"; "Bmap_insert"; "Cgmap"; "Cgmap_lookup"; "Cgmap_partial_alter"; "Deq_dec"; "Eeq_dec"; "0tl"; "0x"]]).
Notation RAMpre := (@AMpre_g _ ref_reserved).
Notation ram_pre := (am_pre_g ref_reserved).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.
Lemma rAMpre_init : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "7'Fv@&RC&BvS:%211%63541").
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
- rewrite A3. pose_secret. lia.
- right; reflexivity.
- destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.
Lemma ram_init_regions : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P ">'8'SG'=&SJ&SB'R5%544321&R;&BvS:%211%411%513%=3721").
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_brk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "<'8'Q5&Q;&QD&BvS:%211%411%611%614%811%;3:31").
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_conc : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "<&Q3'8'>&QC&BvS:%211r1%5221%6242%93821pV@;1").
Proof. intros q. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.
Lemma rAMI_init : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "5'DvS:&B%112%4231").
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
(split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| intros rid r Hr; exists r; repeat split; auto; lia
| intros rid r' H1 H2; cbn in H1; congruence
| cbn; lia
| intros P _ HP; exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
| intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
| exact (amp_rpos st AMP) ]).
- cbn. rewrite (amp_s_secret st AMP). pose_secret. lia.
- exact (amp_secret st AMP).
Qed.
Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E6.
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.
Section SE.
Local Abbreviation SEC_T_ram_rel_final := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "VF'QO'4&Q3%211'DvS:r3%3221'8'SG'>&SK&SC%44321;&Q6&QD%11:%311r4%411%611%=3841%=4<;:<&QB%115r5%;11%411%D3641&QA%114r6%A11%411%J3<41&Q:%114r7%G11%411%Q03B41&Q@%114r8%M11%411%Q63Q441&Q>%114r9%Q311%411%Q<3Q:41&SE'=&SJ%3421Q>Q=&SD&SB%26541QAQ@Q?'QG%QD4QK521&R8%11>r:%311%QJ3531'6%12R2QJ%QL4R3=:1&R>%117r;%311%R23531'RA%R34FEB1&R=%116r<%311%R93531&R?%114r=%311%R>3Q031'3%E2R>R>%211&R<%117r>%311%RF3531'R5%RG4Q:Q9Q61&R;%116r?%311%RM3531&R:%114r@%311%S23QD31&S@'Q4&SA%S54S<QFQC2&SH%14S>QHQE4r1&R7rB%211%86SC97541%;2:1r2%;6SF<:814%>2=1p041pUFSI1&;(1%12SL=rA%SH3SM21%511'<&R1&QH&QF%12T1?%311(0%11T7%T23731%?11&QI%117%T63;15%=241'QLrD%=21T<rE%?21T>%T=3531p071p0F1pULTF1%TA3TFQ6K'7%F2:Q4&QM%TE3=21&H%12>Q8%6231p081pV4U01!p0S>1%U41R6%QG4S@S?S<R7rG%R711%QL6SCR:R93QB1%Q=2R;QI%U33621'R6&R3%11QG(Q1%U83421%QE11%TI1U0p021p091pVBRF1pVDT01&JrF%22R21%32UD2p021p061pQ0I1'IrC%23UKQ?1p041p0Q01p0Q;1p0R91p0RK1p0S11p0S91p0SB1p0SH1p0T01p0T91p0TH1p0TO1p0U61p0U=1p0UD1p0UL1p0V;1pV6V@1pVJVD1pVNVE1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_ram_rel_final) 0%nat 0%nat).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_ram_rel_final) 1%nat 0%nat).
Variable mo : ltac:(sec_ty2 constr:(SEC_T_ram_rel_final) 2%nat 0%nat).
Lemma ram_rel_final : ltac:(sec_stmt2 constr:(SEC_T_ram_rel_final) 3%nat 0%nat).
Proof.
intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split.
- intros sc. unfold active. rewrite E1, C7. reflexivity.
- intros sc. unfold usage. rewrite E2, C8. reflexivity.
- intros i. unfold bounces. rewrite E4, C10. reflexivity.
- intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
- rewrite E5, C11. reflexivity.
- rewrite E6, C1. reflexivity.
- rewrite EG, XG. reflexivity.
- rewrite ESl, XS. reflexivity.
- rewrite ESh, XSH. reflexivity.
- rewrite ET, XT. reflexivity.
- rewrite ERs, XR. reflexivity.
- intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
- exact HR.
- intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
- intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
- rewrite EN. exact XNX.
- intros a Ha. apply HA. rewrite XA. exact Ha.
- intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
- intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.
End SE.
Lemma ram_rel_none : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "='QO'DvS:r1%3221'Ir2(0&Q3%211%53841p071pVN<1").
Proof. intros stX.
intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
- intros m Hm. discriminate.
Qed.
Section SE.
Local Abbreviation SEC_T_ram_rel_take := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "QN'QO&Q3'DvS:r2%3221'8&R1&Q7&QD%117%311(1%12<9%83731'4'QL%211&SA'SG&SE'=&SJ'>&SK%544321&SD&SB&SC%36872651%;4M51>&SH%14O73@r3&R9%11Q0%B6Q3D6431(0%11F%Q13F31&Hr4%22Q71'I&Ar6r5&RI&Q9%Q814%211+1%5221%93871%Q:2QE8%<3QD21p0>1p0B1p0Q<1p0QF1pV@QK1pVNQM1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_ram_rel_take) 0%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_ram_rel_take) 1%nat 0%nat).
Lemma ram_rel_take : ltac:(sec_stmt2 constr:(SEC_T_ram_rel_take) 2%nat 0%nat).
Proof.
intros AI AVM MQ MSq. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
unfold am_took. rewrite upd_meta_put.
eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
- intros a Ha. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
+ apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
- intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta.
+ cbn. exact I.
+ cbn. exact I.
+ unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
+ pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
try assumption; try reflexivity.
cbn. rewrite C3, AVM in H2. exact H2.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_ram_rel_carve := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "SF'QO'6'='>%3221'R5'DvS:r3%3221'8'4%117&SA'SG&SJ&SB%34?21<&SH%14A43>&2%13CB=&R;r4%211%<6GD8641(1r2%22G1%C3A41&;'R6&R3%11I(Q1%I3421%611'Q4%K11&Q3&SE&SK%24Q8KQ71&SD&SC%26Q;NMQ:41%Q047419%M4852:r5&R7r6%211%Q76Q@?6541(0%11A%Q=3A31'7&REzr1%3221&RF&Q0%2241%8241'QL%QG11%QE4LIF2%QB4MJG3&Q2r8&RD&K&RG&O%221Q@%5241%8271&R9r9%211%R46Q:@>=41%M1A%R93A21p0D1pV0RB1&R1&Q=&QD%11:%311%R12QDQ0%RB3621&S@r:%Q>11%RC6QIQKQBQAR51%42QL1p061pWJQL1'I&A&C%12HQ1%Q32Q2Q0+S4%53321%RA2R43%83S521p0:1p0I1p0QH1p0R<1p0RD1p0S91pVBS>1pV<S@1pVNSE1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_ram_rel_carve) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_ram_rel_carve) 1%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_ram_rel_carve) 2%nat 0%nat).
Lemma ram_rel_carve : ltac:(sec_stmt2 constr:(SEC_T_ram_rel_carve) 3%nat 0%nat).
Proof.
intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
{ replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }
assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
/\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
/\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
/\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
/\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
/\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
/\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
{ destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
- destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
+ intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct H0 as (H1 & _). exact H1.
* destruct H0 as (_ & H2 & _). exact H2.
* destruct H0 as (_ & _ & H3 & _). exact H3.
* exact HP.
* exact HP.
* destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
{ apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
split; [exact Q8|]. split; [| exact Q10].
intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
- rewrite (carve_st_none stX p HT ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. exact Ha.
+ intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
rewrite EC. unfold am_took. rewrite upd_meta_put.
set (stD := set_areas _ stC).
eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
- intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
+ apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
- intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
+ unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
+ apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct (RP P HPp HP0) as (H1 & _). exact H1.
* exact HPp.
* destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
* destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
split; [exact H8|]. split; [| exact H10].
intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_ram_rel_deq := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "RH'QO&Q3'DvS:r4%3221'8&R1&Q<&QD%117%311(1%12<9%83731r6%711%911r5%72B1%>3=31&QI&QF%12D8%311%C3B16&QJr7%62I1%311%H3G1;&:r8%K3Q061%L3Q1C2%4221&Hr9%22Q31'QL&Gr:%D2Q71%311&QM%Q73621&QH%115(0%11Q@%Q<3Q;31&;r;%O2QB1%Q111%QA3Q@16%511%;14%QD3QC19r<%Q62QI1%Q811%QH3QG1=%<11'I&QE(Nr?r@%43321%QJ2R53%73R421p091p0?1p0B1p0I1p0O1p0Q71p0Q;1p0QA1p0QG1p0QM1p0R41p0R>1pV>RC1pV8RD1pUNRE1pVLRG1")) (only parsing).
Variable stI : ltac:(sec_ty2 constr:(SEC_T_ram_rel_deq) 0%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_ram_rel_deq) 1%nat 0%nat).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_ram_rel_deq) 2%nat 0%nat).
Variable pv : ltac:(sec_ty2 constr:(SEC_T_ram_rel_deq) 3%nat 0%nat).
Lemma ram_rel_deq : ltac:(sec_stmt2 constr:(SEC_T_ram_rel_deq) 4%nat 0%nat).
Proof.
intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
destruct (aptr_eqb nx h) eqn:E.
-
apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
* change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
* pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
-
assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
{ change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
rewrite !get_meta_rec_put_other by congruence. apply GM. }
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
rewrite !get_meta_rec_put_other by assumption. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same, R3. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
assert (P1 : ptrs_in P st1).
{ unfold st1. apply MallocKit_A2.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
- destruct (H8 pv) as (X & _ & _). exact X.
- destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P2 : ptrs_in P st2).
{ unfold st2. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P3 : ptrs_in P st3).
{ unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
apply rptrs_in_upd_ctx; cbn; try reflexivity.
- exact Q2.
- change (ctx st2) with (ctx stI). exact H2.
- change (ctx st2) with (ctx stI). exact H3.
- change (ctx st2) with (ctx stI). exact H4.
- change (ctx st2) with (ctx stI). exact H5.
- change (ctx st2) with (ctx stI). exact H7.
- exact P2. }
apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
rewrite R3. rewrite <- GM. exact Q3.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rAMI_ctx := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "SK'QO'QKpWL11'DvS:r2%3221&E&QDr3%211%611%5221'7&REz&Q?r4%:11%:11%411%7261&RF&RH+2+R0%3221%5271%?271'<'8&R1&Q8r5%J11%B11%411%513%83721'9&Q3'R5r6r7%Q411%311%>11(1%128Q;%C3B31'4%11:&SA'='SG&SJ&SB%34421@&SH%14643B&2'>%2391QI&R;%11E%=6<H8631r1%D2J1%Q63A31&;'R6&R3%116(Q1%Q<3421%611%QO281%R02L1qVBQ51%Q82Q61qV@Q81%Q:2Q91%QE2Q<1'Q5&Q;%R=1Q;%QE11%311%413%QK3621(L%QM3841r8r9%RF11%311%<11(M%12RIRM%R53@31%Q517%QA6Q@QLQ<Q:RL1%R83QC1Q3%RJ21L%RK251qVBR01%R32R11qV:Q>1%R52Q?1qVDQH1%R72QI1%RB2D1%RC2G1&RB%12R8R7%S@2S?1p041p0Q31p0RJ1p0S;1p0SB1pUJSG1pVNSJ1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_rAMI_ctx) 0%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_rAMI_ctx) 1%nat 0%nat).
Lemma rAMI_ctx : ltac:(sec_stmt2 constr:(SEC_T_rAMI_ctx) 2%nat 0%nat).
Proof.
intros AI CE SR HA HB. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split; cbn; try assumption.
- destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
- intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
+ destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
+ destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
+ exact (XP P HPn HP0).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_rAMI_new_region := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "RC'QO'R6'>'DvS:r4%3221&;'8(Q1%23951%411&RFzr3%3221'7&2'=&R0r6r5r7%4432B1%73H61%F2E1'4'R5%211&SA'SG&SJ&SB%34?216&SH%14A438&R:%11?&R;%11?%;6F=7531(1(QN%13GFQ6%32A1%Q53A51'6%12MQ=r1%Q03OQ?1r8%?11%Q<3Q231%Q>11&QCr9%Q546Q2Q41%Q83QIQ71r2%5221%6252%QE3QK21p091pV@@1%Q=4Q:Q<Q;>%Q@3R1Q?1(5%14QAR1@C%>231&RD%12QBF%QO3R531pV:R61%QI2:1%QJ2M1%QK2QB1p0QM1p0R21p0R81pV2R=1pUHR>1pV0R@1pVNRB1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_rAMI_new_region) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_rAMI_new_region) 1%nat 0%nat).
Variable base : ltac:(sec_ty2 constr:(SEC_T_rAMI_new_region) 2%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_rAMI_new_region) 3%nat 0%nat).
Lemma rAMI_new_region : ltac:(sec_stmt2 constr:(SEC_T_rAMI_new_region) 4%nat 0%nat).
Proof.
intros AI NK LEN. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
unfold new_region. cbn [fst].
set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
split; [| split; [| split]].
- split; cbn -[insert]; try assumption.
+ intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
+ intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
+ unfold rid. lia.
+ intros P HPn HP0. apply (MallocKit_A2.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
+ intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
+ intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
- rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
- intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
- intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.
End SE.
Lemma rAMI_grow : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_am_P "RF'QO'='R5'>'DvS:r4%3221'8'4%118&SA'SG&SJ&SB%34>21=&SH%14@43?&R;r5%211%:6DC64?1(1r3%22F1%A3?41&;'R6&R3%11G(Q1%G3421%611&R4%11?%K3Q01M&R@&S?&SF&SI%14Q7KJQ6%34Q8Q7J1r7(QNr6%A11&R2%113&RD+TP0%22O1%83641r8%Q311%A7QEQDQ7=<31%C213'7r1%QF2QE1&Q3&QCr2%2215r:%4217%QI3QN31pV@71%QA1:%QI6R3R2QEQC@1%Q91K%H1L%G2KF%M3321%QC2R71%R23R061%C291%D2B1tVHR=F1p0Q;1p0Q?1p0QG1p0R:1pV:R?1pVBRA1pVDRC1pVNRE1").
Proof. intros stX rid r off.
intros AI Hr NK LEN st'. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
assert (CQ : forall q, conc st' q = conc stX q).
{ intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
split; cbn -[insert]; try assumption.
- intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
destruct (decide (q = rid)) as [->|NE].
+ rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
intros HG. exfalso. apply NK. rewrite K'. exact HG.
+ exists r'. auto.
- intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
- intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
destruct (decide (q = rid)) as [->|NE].
+ apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
+ apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
- intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
+ destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
+ apply XF. exact Hq.
- intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.
End CEIL_WRAP_1.
