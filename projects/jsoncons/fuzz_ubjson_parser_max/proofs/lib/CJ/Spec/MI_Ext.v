(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Ext () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Ext.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.NArith.BinNat.N."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1fst"; "1list"; "1nat"; "1prod"; "2eq"; "2iff"; "3N"; "3Z"; "0L"; "0LS"; "0RUNp"; "4mled"; "5ctrl_eq"; "6INVL"; "6MR"]; ["6blk"; "6dll"; "6extras"; "6frontier"; "6gbase"; "6gcnt"; "6group_ok"; "6hosts"; "6inv_A"; "6inv_G"; "6inv_L"; "6inv_M"; "6inv_R"; "6inv_S"; "6inv_SH"; "6known"]; ["6linked"; "6live_group"; "6unknown"; "7active"; "7aptr"; "7c_active"; "7c_avail_meta_areas"; "7c_usage"; "7enframe_at"; "7get_head"; "7get_shadow"; "7get_stride"; "7ghdr"; "7havoc"; "7hdr_havoc"; "7lhead"]; ["7m_last_idx"; "7m_maplen"; "7mctx"; "7meta"; "7mstate"; "7nest_layout"; "7optr"; "7region"; "7s_ctx"; "7s_groups"; "7s_metas"; "7s_regions"; "7s_shadow"; "7s_slots"; "7s_tick"; "7set_size"]; ["7set_tick"; "7shadow"; "7strip"; "7upd_shadow"; "7usage"; "7wr16"; "7wr32"; "7wr8"; "7zero_hdrs"; "8le"; "0X"; "0a"; "0ai"; "0b"; "0c"; "0cnt"]; ["0e"; "0f"; "0g"; "0h"; "0i"; "0idx"; "0j"; "0l"; "0m"; "0n"; "0off"; "0p"; "0r"; "0rid"; "0sc"; "0size"]; ["0st"; "0st'"; "9N_countable"; "9Z_countable"; "9prod_countable"; ":prod_eq_dec"; ";gmap"; "<eq_dec"; "=eq_dec"; "0t"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Record ctrl_eq (st st' : mstate) : Prop := mkCE {
ce_ctx : s_ctx st' = s_ctx st;
ce_regions : s_regions st' = s_regions st;
ce_next_rid : s_next_rid st' = s_next_rid st;
ce_metas : s_metas st' = s_metas st;
ce_areas : s_areas st' = s_areas st;
ce_groups : s_groups st' = s_groups st;
ce_slots : s_slots st' = s_slots st;
ce_secret : s_secret st' = s_secret st;
ce_reserved : s_reserved st' = s_reserved st
}.
Lemma ctrl_eq_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "5'QD'=r1%2211pV241").
Proof. intros st. constructor; reflexivity. Qed.
Lemma ctrl_eq_sym : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext ":'QD'=r2r1%3221r3%5241p031pV481pV291").
Proof. intros st st'. intros []; constructor; symmetry; assumption. Qed.
Lemma ctrl_eq_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "<'QD'=r3r2%3221r5%5214p031p041pTN91pTL:1pTH;1").
Proof. intros a b c. intros [] []; constructor; congruence. Qed.
Section SE.
Local Abbreviation SEC_T_ctrl_eq_strip := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext ">'QD'5&R2r1%211r2%411%63731'=r3%2215p041pV4<1pV2=1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ctrl_eq_strip) 0%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SEC_T_ctrl_eq_strip) 1%nat 0%nat).
Lemma ctrl_eq_strip : ltac:(sec_stmt2 constr:(SEC_T_ctrl_eq_strip) 2%nat 0%nat).
Proof.
intros H. pose proof (strip_fields st) as A. pose proof (strip_fields st') as B. constructor; intuition congruence. Qed.
End SE.
Lemma ctrl_eq_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext ":'QD'7'=r2&R0r1%2213%5241pVD71pV291"). Proof. intros st t. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "='QD&Q4'8'=r3&R7r2r1%33214%6251pVF81pUH:1pV2<1"). Proof. intros st p v. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "='QD&Q4'8'=r3&R5r2r1%33214%6251pVF81pUH:1pV2<1"). Proof. intros st p v. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr32 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "='QD&Q4'8'=r3&R6r2r1%33214%6251pVF81pUH:1pV2<1"). Proof. intros st p v. constructor; reflexivity. Qed.
Lemma ctrl_eq_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "='QD&Q4'8'=r3&Q=r2r1%33214%6251pUD81pUH:1pV2<1"). Proof. intros st p n. apply ctrl_eq_strip. apply strip_havoc. Qed.
Lemma ctrl_eq_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext ":'QD&Q4'=r2&Q>r1%2213%5241pTL71pV291"). Proof. intros st b. constructor; reflexivity. Qed.
Lemma ctrl_eq_upd_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext ">'QD'7'R1p011'=r3&R3r2r1%33214%6251pU481pUL;1pV2=1"). Proof. intros st rid f. constructor; reflexivity. Qed.
Lemma ctrl_eq_zero_hdrs : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "B'QD&Q4'8'3'=r5&R8r4r3r2r1%5543216%8271pU0:1pU:<1pV0=1pUH?1pV2A1"). Proof. intros st p size i cnt. apply ctrl_eq_strip. apply strip_zero_hdrs. Qed.
Lemma ctrl_eq_set_size : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "A'QD&Q4'8'=r5&QOr4r3r2r1%5543216%8271pTL:1pUD;1pU2=1pUH>1pV2@1"). Proof. intros st p e n b. apply ctrl_eq_strip. apply strip_set_size. Qed.
Lemma ctrl_eq_enframe_at : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "C'QD&Q4'8'=r5&1&Q8r4r3r2r1%5574321%73<;1%:291pUF<1pUD=1pU<>1pU6@1pV2B1"). Proof. intros st g idx n off. apply ctrl_eq_strip. apply strip_enframe_at. Qed.
Lemma ctrl_eq_nest_layout : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "C'QD&Q4'8'=r6&QEr5r4r3r2r1%66754321%9281pU0;1pV0<1pU>=1pU<>1pU6@1pV2B1"). Proof. intros st g idx j size cnt. apply ctrl_eq_strip. apply strip_nest_layout. Qed.
Section VIEWS.
Variables st st' : mstate.
Lemma MR_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "L'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'QC%=4<621&QJvS1%211vS0%411%D3631&?r1%2271%3262%I3<21pVHH1p071").
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
Lemma hosts_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "O'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'Q<%=4<621&QIvS1%211vS0%411%D3631&6&Gr2r1%33921%43832%6221pUBJ1pTLK1p0:1").
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
Lemma live_group_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "M'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'Q<%=4<621&QIvS1%211vS0%411%D3631&6&Q1r1%2281%3272%5221pUBI1p081").
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
Lemma frontier_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "G'5&QF&Q6&QHvS1%211%411vS0%511%711%:3941'7'QG'8&Cr2r1%33=21%43;32%C3621pUJ81pUL:1p0<1").
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
Lemma gcnt_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "Q3'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'Q<%=4<621&QIvS1%211vS0%411%D3631'QC%E4D>:1&QJ%118%217%J3421&Er1%22=1%32<2%O3I21pUNJ1p071p0>1").
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
Lemma get_head_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "A'5'QB&QHvS1%211vS0%411%73631'Q?&QF&Q9r1%2291%3282%>3521pU871p091").
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.
Lemma active_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "H'5'S6'8&S8&S3&Q4%544321&Q5&QHvS1%211%411vS0%511%711%?3941&QF&Q3r1%22:1%3282%E3521pUND1p081").
Proof. intros H sc. unfold active, ctx. rewrite H. reflexivity. Qed.
Lemma usage_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "F'5'S6'8&S8&S3%443213&Q7&QHvS1%211%411vS0%511%711%>3941&R4r1%2291%3272%C3A21pUNB1p071").
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.
Lemma get_shadow_ext' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "D'5'S6'7&S7&S2'R1%544321&QLvS1%211vS0%411%<3631&Q:r1%2271%3262%A3<21pUL@1p071").
Proof. intros H rid. apply get_shadow_ext. exact H. Qed.
Lemma known_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "I'5'S6'7&S7&S2'R1%544321&QLvS1%211vS0%411%<3631&Q4'8&6&Or2r1%33;21%43:32%6221pVF81pUH:1p0<1").
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma unknown_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "F'5'S6'7&S7&S2'R1%544321&QLvS1%211vS0%411%<3631&Q4&6&Q2r1%2291%3282%5221pUH71p091").
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma linked_ext_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "O'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'QC%=4<621&QJvS1%211vS0%411%D3631'2%11D&Q0r1%2271r2%42;1p031pU@71p0:1").
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
Lemma dll_ext_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "O'5'S6&Q4&S5'7&S7'8&S8%544321&S4&S2&S3%36872651'QC%=4<621&QJvS1%211vS0%411%D3631'2%11D&Ar1%2271r2%42;1p031pU@71p0:1").
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.
Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.
Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE.
Lemma inv_R_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "9'Lv;vR:vS0v9%544321vS1%746513p031").
Proof.
intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HC, ?HG; try assumption.
-
eapply Permutation_trans; [exact ir_metas|].
erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
- intros rid r H1 H2. rewrite FR. eauto.
- intros rid r H1 H2. rewrite FR. eauto.
Qed.
Lemma inv_A_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "6'HvS0%211vS1%411p031").
Proof.
intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
- intros a ar H. destruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
- intros sc Hsc. rewrite US, GC. auto.
Qed.
Lemma inv_M_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "8'KvR:vS0v:%43321vS1%63513p031").
Proof.
intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [M1 M2 M3 M4 M5]; constructor.
- intros m Hm. rewrite !ME in *. apply M1. exact Hm.
- intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
- intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
- intros m Hm. rewrite HM. apply M4. exact Hm.
- intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.
Lemma inv_L_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "7'JvS0v:%3221vS1%5213p031").
Proof.
intros I. pose proof (MR_ext st st' HM) as ME. pose proof (get_head_ext st st' HC) as HE.
destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
- intros h. rewrite HE. apply L1.
- intros h. apply (dll_ext_metas st st' HM). apply L2.
- exact L3.
- exact L4.
- intros m. rewrite !ME. apply L5.
- intros m Hm. rewrite !ME. apply L6. exact Hm.
- intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
- exact L9.
Qed.
Lemma group_ok_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "A&Q4'8'FvR:vS0v:r3r2r1%76654321vS1r4%:6927165p041pTJ=1pTL?1pUB@1").
Proof. intros m b ai.
intros I. pose proof (MR_ext st st' HM) as ME.
destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
- intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.
Lemma inv_G_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "8'IvR:vS0v:%43321vS1%63513p031").
Proof.
intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [G1 G2 G3 G4 G5]; constructor.
- intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
- intros b ai H. rewrite HG in H. eapply G2. exact H.
- intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
- intros rid r H1 H2 H3. rewrite HR in H1. destruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
- intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
Qed.
Lemma inv_S_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "8'MvR:vS0v0%43321vS1%63513p031").
Proof.
intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
- intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
- intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
- intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
- intros c Hc. rewrite HS. apply S4. exact Hc.
- exact S5.
- intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End CTRL.
Lemma inv_SH_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "G'QD'2&@%211'7&R9&QNr3%211r1%5221'Nr4%2216&R0r5%2291%6215p051p091pVD@1p2B1pV2F1").
Proof. intros st BL t.
intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
intros rid sh H. destruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
- intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
- intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
- intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_inv_SH_ctrl := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "Q4'QD'2&@%211'=r3r2%3221'5'S6'7&S7&S2'R1%544321&QL%11;r4%311%;3531&QN%114r5%311%@3>31'Nr6%221:%3226p021p061p0<1p0I1p2N1pV4Q21pV2Q31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_inv_SH_ctrl) 0%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SEC_T_inv_SH_ctrl) 1%nat 0%nat).
Variable BL : ltac:(sec_ty2 constr:(SEC_T_inv_SH_ctrl) 2%nat 0%nat).
Lemma inv_SH_ctrl : ltac:(sec_stmt2 constr:(SEC_T_inv_SH_ctrl) 3%nat 0%nat).
Proof.
intros CE SH TK I.
pose proof (MR_ext st st' (ce_metas _ _ CE)) as ME. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
- intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
- intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
- intros b m i Hb Hi. rewrite ME in Hi |- *. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
- intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
- intros b m p i Hb Hml Hs. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
- intros k m i Hk Hs. rewrite HS in Hs. rewrite !ME.
destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
split; [exact A5|]. split.
+ intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
+ split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_inv_SH_view := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "S4'QD'2&@%211'5'S6'7&S7&S2'R1%544321&QLr2%211r3%411%<3631&QN%114r4%311%A3?31'QG%B4A@?1&QK%116r5%311%H3531&Q4&S5'8&S8%34KJ21&S4&S3%26NML541'Q<%Q149521&QI%11>r6%311%Q73531'4%12@>%Q94A=:1&QM%117r7%311%Q?3531&D&?r8r1%3221%511r9%6214%811%QI3Q041pVHQ11&Q;%115r:%=21;%411%R03Q541pVHQ81&Q@%115r;%D21B%411%R73Q<41pVHQ?1&QA%115r<%K21I%411%R>3QC41pVHQF1'N%126D%227>p021p051p0=1p0E1p0M1p0Q91p0QB1p0R21p0R:1p0R@1p2RN1pV4S21pV2S31")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_inv_SH_view) 0%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SEC_T_inv_SH_view) 1%nat 0%nat).
Variable BL : ltac:(sec_ty2 constr:(SEC_T_inv_SH_view) 2%nat 0%nat).
Lemma inv_SH_view : ltac:(sec_stmt2 constr:(SEC_T_inv_SH_view) 3%nat 0%nat).
Proof.
intros SH TK HR HG HS VB VS VL VM I.
assert (VSS : forall x i, sstart (MR st' x) i = sstart (MR st x) i) by (intros; unfold sstart; rewrite VB, VS; reflexivity).
assert (VC : forall x, cnt_of (MR st' x) = cnt_of (MR st x)) by (intros; unfold cnt_of; rewrite VL; reflexivity).
pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
- intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
- intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
- intros b m i Hb Hi. rewrite VC in Hi. rewrite VSS. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
- intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
- intros b m p i Hb Hml Hs. rewrite VM in Hml. rewrite HS in Hs. rewrite !VB.
destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
- intros k m i Hk Hs. rewrite HS in Hs. rewrite !VS, !VB.
destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
split; [exact A5|]. split.
+ intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
+ split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.
End SE.
Lemma INVL_ctrl_same : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ext "Q@'B'QD'<'2&@%211'Q?&Q4%511p031'=r5r4%3221'5'S6'7&S7&S2'R1%544321&QL%11;r6%311%;3531&QN%114r7%311%@3>31&>v;r9r8%46321<HGr:%665139>Jp031p091p0?1p0L1pFQ11p2Q61pDQ:1pV4Q<1pV2Q=1pTFQ?1").
Proof. intros X st st' L BL LS.
intros CE SH TK (IR & IA & IM & IL & IG & IS & ISH).
split; [apply (inv_R_ctrl X st st'); assumption|].
split; [apply (inv_A_ctrl st st'); assumption|].
split; [apply (inv_M_ctrl X st st'); assumption|].
split; [apply (inv_L_ctrl st st'); assumption|].
split; [apply (inv_G_ctrl X st st'); assumption|].
split; [apply (inv_S_ctrl X st st'); assumption|].
apply (inv_SH_ctrl st st'); assumption.
Qed.
End CEIL_WRAP_1.
