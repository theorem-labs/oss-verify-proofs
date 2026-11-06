(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Pres4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_List."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Pres4.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1app"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3N"]; ["3Z"; "0L"; "0LS"; "0LS'"; "0RUNp"; "4mled"; "5INVL"; "5MR"; "5blk"; "5cnt_of"; "5extras"; "5frontier"; "5gbase"; "5gcnt"; "5gend"; "5group_ok"]; ["5head_of"; "5hosts"; "5in_list"; "5inv_L"; "5live_group"; "5sstart"; "5x_fresh"; "5x_idle"; "5x_zomb"; "6data_of"; "6fupd"; "6lists_ok"; "6queue_st"; "7ctx_but_heads"; "7xfresh"; "8LActive"]; ["8LFree"; "8UNIT"; "8aptr"; "8area"; "8c_active"; "8dequeue"; "8get_head"; "8get_stride"; "8ghdr"; "8lhead"; "8m_avail"; "8m_freeable"; "8m_freed"; "8m_last_idx"; "8m_maplen"; "8m_mem"]; ["8m_next"; "8m_prev"; "8m_sizeclass"; "8mctx"; "8meta"; "8meta0"; "8mkGhdr"; "8mkMeta"; "8mstate"; "8optr"; "8region"; "8s_areas"; "8s_ctx"; "8s_groups"; "8s_metas"; "8s_next_rid"]; ["8s_regions"; "8s_reserved"; "8s_secret"; "8s_shadow"; "8s_slots"; "8s_tick"; "8set_head"; "8shadow"; "8size_class"; "8slot_start'"; "8upd_meta"; "8usage"; "9In"; ":le"; ":lt"; ":mul"]; ["0X"; "0X'"; "0a"; "0ai"; "0b"; "0c"; "0f"; "0g"; "0h"; "0h'"; "0i"; "0l"; "0m"; "0r"; "0rid"; "0sc"]; ["0st"; "0st'"; ";lookup"; "<N_countable"; "<Z_countable"; "<prod_countable"; "=prod_eq_dec"; ">gmap"; ">gmap_lookup"; "?eq_dec"; "@eq_dec"; "0v"; "0x"; "0z"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition xfresh (X : extras) (f : option aptr) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) f.
Lemma data0_shape : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "F'R4&<':&Q9r1%211&R5%411%63831(R7&R1%117&R0%119(1&QB%211z%99752111111%A3C?1%C2<1pVLE1").
Proof. intros r.
destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.
Lemma data0_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "B'R4':&Q9r1%211&R5%411%63731&R9&QOr2%211(1&QB%211%>3741p091pVLA1").
Proof. intros r. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.
Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Lemma de_fields : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q>&QB'9':&R9&QO&GvSAr1%3221%511vS@%6214%811%;3:41'@&QJ%118%216%@3421&QL%11<%21:%D3821&QM%11@%21>%H3<21&QK%11D%21B%L3@21&R2%11H%21F%Q03D21&QN%11L%21J%Q43H21%Q6251%Q72:1%Q82?1%Q92D1%Q:2I1%Q;2O1pWJQ=1").
Proof. intros x. apply data_of_eq. apply DE. Qed.
Lemma de_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':&R9&QO&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_avail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QJ&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_freed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QL&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_last : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QM&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_freeable : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QK&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_sc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&R2&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_maplen : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QN&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply de_fields. Qed.
Lemma de_stride : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&QG&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. apply get_stride_data. apply DE. Qed.
Lemma de_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "=&QB':&L&GvSAr1%3221%511vS@%6214%811%:3;41pWJ<1"). Proof. intros x. unfold gbase. rewrite de_mem. reflexivity. Qed.
Lemma de_sstart : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "@&QB'@':&Q5&GvSAr2%3221r1%6221vS@%7215%9214%;3<41pVF=1pWJ?1"). Proof. intros x i. unfold sstart. rewrite de_gbase, de_stride. reflexivity. Qed.
Lemma de_slot_start' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "@&QB'@':&RI&GvSAr2%3221r1%6221vS@%7215%9214%;3=41pVF=1pWJ?1").
Proof. intros x i. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
Lemma de_cnt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&I&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. unfold cnt_of. rewrite de_last. reflexivity. Qed.
Lemma de_gend : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">&QB':'@&N&GvSAr1%3221%511vS@%6214%811%;3:41pWJ=1"). Proof. intros x. unfold gend. rewrite de_sstart, de_cnt. reflexivity. Qed.
End DEXT.
Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
cb_secret : c_secret c' = c_secret c;
cb_init : c_init_done c' = c_init_done c;
cb_mc : c_mmap_counter c' = c_mmap_counter c;
cb_am : c_avail_meta c' = c_avail_meta c;
cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
cb_mah : c_meta_area_head c' = c_meta_area_head c;
cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
cb_usage : c_usage c' = c_usage c;
cb_unmap : c_unmap_seq c' = c_unmap_seq c;
cb_bounces : c_bounces c' = c_bounces c;
cb_seq : c_seq c' = c_seq c;
cb_brk : c_brk c' = c_brk c
}.
Lemma cbh_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "5'R3'Q=r1%2211pV<41"). Proof. intros c. constructor; reflexivity. Qed.
Lemma cbh_trans : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "<'R3'Q=r3r2%3221r5%5214p031p041pV<91pV::1pV6;1").
Proof. intros a b c. intros [] []; constructor; congruence. Qed.
Lemma cbh_set_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "@'R8'QI&R9'Q=&R<r3%211&RFr2r1%33215%711%9261pWH;1pVB=1pW2?1").
Proof. intros st h v. destruct h; constructor; reflexivity. Qed.
Lemma cbh_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "A'R8&QB'R4p011'Q=&R<r3%211&RJr2r1%33215%711%9261pV>;1pVJ>1pW2@1").
Proof. intros st m f. constructor; reflexivity. Qed.
Lemma inv_L_lists : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "@'R8'QI'5&QB%211p041'Q3r2r1%3221'Q;r3%2215p041pQ691pW2?1").
Proof. intros st LS. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.
Lemma head_of_app : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "G'5&QB%211&=':r2(6%116%43631%611&R9&Q0&3r3(4%13>:8%43?31%611%715%?3921p0;1pV@D1pVHD1").
Proof. intros l g. destruct l; cbn; congruence. Qed.
Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Hypothesis KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None.
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
(HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
(HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st).
Hypothesis HC : ctx_but_heads (s_ctx st) (s_ctx st').
Hypothesis XE : x_pend X' = x_pend X /\ x_orph X' = x_orph X /\ x_zomb X' = x_zomb X.
Hypothesis LO' : lists_ok st' LS'.
Hypothesis H_free : forall m, In m (LS' LFree) -> data_of (MR st m) = data_of meta0.
Hypothesis H_active : forall sc m, In m (LS' (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Hypothesis H_keys : forall sc, LS' (LActive sc) <> [] -> 0 <= sc < 48.
Hypothesis H_actkeys : forall sc g, c_active (s_ctx st') !! sc = Some g -> 0 <= sc < 48.
Hypothesis H_idle : forall m, In m (x_idle X') -> s_metas st' !! m = Some meta0 /\ ~ in_list LS' m.
Hypothesis H_zomb : forall z, In z (x_zomb X) -> m_next (MR st' z) = None /\ m_prev (MR st' z) = None /\ ~ in_list LS' z.
Hypothesis H_groups : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
(x_fresh X' <> Some m -> ai < m_last_idx (MR st m) -> In m (LS' (LActive (m_sizeclass (MR st m)))))
/\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> ~ in_list LS' m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0)
/\ (x_fresh X' <> Some m -> forall sc, In m (LS' (LActive sc)) -> Some m <> head_of (LS' (LActive sc)) ->
m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0)
/\ (m_sizeclass (MR st m) = 63 -> ~ in_list LS' m)
/\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < UNIT * size_class (m_sizeclass (MR st m)) ->
m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0).
Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.
Lemma rl_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "<&QB&<&Q1vSAr2r1%43321vS@%63143%8231pVJ:1pV:;1"). Proof. intros b m. apply hosts_ext. exact HG. Qed.
Lemma rl_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ":&QB&<&Q4vSAr1%3221vS@%5213%7231pVJ91"). Proof. intros m. apply live_group_ext. exact HG. Qed.
Lemma rl_frontier : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ">'?'R:':'@&KvSAr2r1%43321vS@%63143%93831pVL;1pVN=1").
Proof. intros rid r. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
Lemma rl_usage : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ":'@':&RKvSAr1%3221vS@%5213%73831pW091").
Proof. intros sc. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
Lemma rl_gcnt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ":'@':&MvSAr1%3221vS@%5213%73831pW091").
Proof. intros sc.
apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.
Theorem INVL_relink : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "8&FvDvS1vSAvAv0vC%76654321").
Proof.
destruct XE as (XP & XO & XZ).
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
+ intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
- destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
+ intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
+ intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
- destruct IM as [M1 M2 M3 M4 M5]; constructor.
+ intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
+ intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
+ intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
+ exact H_idle.
+ intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
- destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
+ intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
+ intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
+ intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
- destruct IG as [G1 G2 G3 G4 G5]; constructor.
+ intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
* apply KEYS. exact g_present.
* destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
* intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
+ intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
+ intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
+ intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
- destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
+ intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
+ intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
+ intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
+ intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
- apply (inv_SH_view st st'); auto.
Qed.
End RELINK.
Lemma present_MR : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q:'R8&QB&=':'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4B51>&SH%14D73@r1&R>r2%211%C6IE7541(1%11G%J3G31%L11r3%911%J6Q0L><91(2&G%125<%32Q01%Q33Q051p091pWJQ71pW2Q91").
Proof. intros st x. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.
Lemma fupd_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q1'QI'5&QB%211p041&<&RLr1&Q:r5r4r3r2%544321%83<71'>'9':%13B68%=3A<8%4221&=%114%>1;%B3FA1%9231%;261%F2=1pVJJ1pVDM1pVHK1pVBO1pQ6L1").
Proof. intros LS h l h' m.
unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.
Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Lemma old_lists : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "4'Q;vS@vB%3221"). Proof. apply inv_L_lists. exact (proj1 (proj2 (proj2 (proj2 INV)))). Qed.
Lemma old_free : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "D&QB&RLr1vB(Q@%211%53641':'R4&Q9&GvS@r2%3221%511&R5%711%:3931p0<1pVJC1").
Proof. intros m. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
Lemma old_active : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q1'@&QB&RLr1vB(Q?r2%211%411%73861'9&RMzr3%3221&RN+Q@%2241%8241&Q4vS@%221?':&R2&G%125C%311%53K1>%B271%C2;1p0E1pVJN1pW0Q01").
Proof. intros sc m. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
Lemma old_keys : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "J'@&=':'5&QB%211vB(Q?r1%211%411(6%118%;3831%=11'9&RMzr2%3221&RN+Q@%2241%8241p0:1pW0I1").
Proof. intros sc. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
Lemma old_actkeys : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q3'@&QB':'7%113&SB'SG&SJ&SD%349218&SH%14;43:r2&QD&R<vS@%211%411%=6BA9761(2r1%22D1%D3B41'9&RMzr3%3221&RN+Q@%2241%8241p0:1pV@Q01pW0Q21").
Proof. intros sc g. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
Lemma old_idle : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q<&QB&RLr1&Q7vS0%211%53641'9':'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4H51>&SH%14J73@r2&R>vS@%211%C6OE7541(2&R5%22H1%K3H41&=&Q2vB%221<%411%Q2261p0Q41pVJQ;1").
Proof. intros m. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
Lemma old_zomb : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "R2&QB&RLr1&Q8vS0%211%53641'9':&R9&R0&GvS@r2%3221%511(1%11A%:3931&R1%116%=3<14&=&Q2vB%221<%411';&QOr3%C2B1%311(2%12Q1O%J3I31'7'QH%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4QB51>&SH%14QD73@&R=%11Q:%A6QGC53QE1%Q81D%QA3D21%QC2H1qV:QK1%Q12QL1%QF2Q31%QG2Q91%QH2Q=1p0QJ1pWLR11").
Proof. intros z. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
Lemma old_group : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q:&QB'@':'7'QH%211&SB'SG&SF'?&SI&SJ%4432;1&SE&SC&SD%36762?51%:4A51=&SH%14C73?r2&R=vS@%211%B6HD7541(2(R6r3%32L1r1%4221%62K1%N3K81'OvS0vBr4%463?21:Ap061pV8Q61pV:Q81pVJQ91").
Proof. intros m b ai. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
Lemma old_63 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "QC&QB'@':'7'QH%211&SB'SG&SF'?&SI&SJ%4432;1&SE&SC&SD%36762?51%:4A51=&SH%14C73?r2&R=vS@%211%B6HD7541(2(R6r3%32L1r1%4221%62K1%N3K81&R2&Gr4%22>1%411+QO%Q53Q621&=&Q2vBr5%3221%511p071p0?1pV8Q?1pV:QA1pVJQB1").
Proof. intros m b ai. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.
Lemma listed_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "H&QB'QI&RLr2vBr1%211%53741&=':&R9&R0&GvS@r3%3221%511(1%11B%:3931%<11p0>1pVBE1pVJG1").
Proof. intros m h. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
Lemma listed_present : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q8&QB'QI&RLr2vBr1%211%53741&=':'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4I51>&SH%14K73@r3&R>vS@%211%C6Q0E7541(1%11G%J3G31%L11p0N1pVBQ51pVJQ71").
Proof. intros m h. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
Lemma head_listed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "D'QI&QB':&R9&QFvS@r2%3221(2r1%2291%93841&RLvBr3%211%43?:1p061pV6A1pVBC1").
Proof. intros h a. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
Lemma prev_listed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "J'QI&QB&RLr2vBr3%211%53641':&R9&R1&GvS@%2218%411(2%12?=%93831r5%?11%B3C?1p041p0?1pWJF1pV6G1pVBI1").
Proof. intros h a x. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
Lemma next_listed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "J'QI&QB&RLr2vBr3%211%53641':&R9&R0&GvS@%2218%411(2%12?=%93831r5%?11%B3C?1p041p0?1pWJF1pV6G1pVBI1").
Proof. intros h a x. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
Lemma idle_unlisted : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "A&QB'QI&RLr2&Q7vS0%211%53741&=r3vB%118%:3<31%511p071pVB>1pVJ@1").
Proof. intros m h. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
Lemma zomb_unlisted : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "A&QB'QI&RLr2&Q8vS0%211%53741&=r3vB%118%:3<31%511p071pVB>1pWL@1").
Proof. intros z h. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
Lemma idle_not_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB&RLr1&Q7vS0%211%53641&=&Q4vS@r2%3221%511p071pVJ>1").
Proof. intros m.
intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
Lemma zomb_not_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB&RLr1&Q8vS0%211%53641&=&Q4vS@r2%3221%511p071pWL>1").
Proof. intros z.
intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
Lemma free_not_live : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB&RLr1vB(Q@%211%53641&=&Q4vS@r2%3221%511p071pVJ>1").
Proof. intros m.
intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.
Lemma INVL_set_fresh : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q7'J'R8'E'5&H%211'QI&QB%511p031'7%114&FvDr6r5r4r3r2%76654321':&Q6r7%211(1%11B%63?31&Q>r8%221<%B6A18@?>p051p0=1pV>F1pQ6I1p2N1pQ4Q21pW2Q41pV2Q61").
Proof. intros X st L BL LS f.
intros INV HF.
refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
(old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
(old_actkeys _ _ _ _ _ INV) _ _ _).
- cbn. auto.
- cbn. apply (old_idle _ _ _ _ _ INV).
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
split; [| split; [| split; [| split]]].
+ intros _. exact (g_partial _ _ _ _ _ _ GO NF).
+ intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
+ intros _. exact (g_rest _ _ _ _ _ _ GO NF).
+ exact (old_63 _ _ _ _ _ INV m b ai Hb).
+ intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.
Lemma INVL_clear_fresh : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "T?'J'R8'E'5&H%211'QI&QB%511p031&FvDr6r5r4r3r2%76654321':'7%11=&Q6r7%211(2%12B9%83631'@'QH%:11&SB'SG&SF'?&SI&SJ%443291&SE&SC&SD%36762=51%:4Q251=&SH%14Q473?&R=r9%211%A6Q8C64O1(R6%I2Q:Q4r1%3221%L2H1%Q33H61'9&RN&QM&Gr:%221Q?%411%62Q=1&RLr8(Q?&R2r;%:21Q=%311%511%711%93R0QA1p0;1%81>+Q@%D221&=&Q2%12?QH%311&QJr<%I21C%311z%R33QJ21&QL%115%R63QM14%Q3241p0;1p0@1%L1Q:%N11%Q03RGR81%R72RHQ0&Q0%Q11RA%QE11%311%RB3R@51%I11r=%Q>21QJ%H11%RG3R>1E%D13%RI3R@1G%Q011%QG241p091p0A1pW0RE1&QG%11Q?&RO&QA&RH%11QB%4231%R1261p01Q0p0Q?1%R52;1%R62Q11%R72QE1p0R91pV8S41pV:SI1&Q>(1%11SL%32RG1%SK6SJ1R6S?SISHp061p0S=1p0SG1pV@T21pQ6T11p2T61pQ4T:1pW2T<1pV2T>1").
Proof. intros X st L BL LS g.
intros INV HF OB.
refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
(old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
(old_actkeys _ _ _ _ _ INV) _ _ _).
- cbn. auto.
- cbn. apply (old_idle _ _ _ _ _ INV).
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
destruct (aptr_eq_dec m g) as [->|NE].
+ destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
+ assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
split; [| split; [| split; [| split]]].
* intros _. exact (g_partial _ _ _ _ _ _ GO NF).
* intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
* intros _. exact (g_rest _ _ _ _ _ _ GO NF).
* exact (old_63 _ _ _ _ _ INV m b ai Hb).
* intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.
Lemma queue_frame : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "RI'QI&QB'R8&Q<r3r2r1%43321'9':'SG'?&SI&SC'R:%544321&R@%11;%21=%:3421'RG%;4:981&RC%11A%21C%@3421&R?%11E%21G%D3B21&SF'@&SJ%34FE21&SE&SD%26IHG541'QC%L4Q5521&R;%11Q2%21Q4%Q13421'QH%Q24Q;;81&R=%11Q8%21Q:%Q73421'8%12QAC%Q94QBB?1&RD%11Q?%21QA%Q>3421&RE%11QC%21QE%QB3Q@21&RB%11QG%21QI%QF3Q021'5%@2Q2Q2%211&RA%11QN%21R0%QM3421'Q=&R<%11R4%21R4%4221%R4261%R52>1%R62C1%R72H1%R82Q01%R92Q71%R:2QE1%R;2QJ1%R<2R11tW4RCR>1pW2RD1pV@RF1pVBRH1").
Proof. intros h g st.
unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
repeat split; try reflexivity; constructor; reflexivity.
Qed.
Lemma queue_metas_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "R0'QI&QB'R8&=':r1r3%33621%511&R9&QFr4r6%3221(2%12>:%<3731'9r2%?3B81%A11&R1&Gr5%2216%411%<2I?%G3B21%I11%<291p0>1pV6N1'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4Q>51>&SH%14Q@73@&R>&Q<%13Q8MQ9%311%C6QEE75Q@1%51Q<%E6QGG97QB1%QE3G31p0K1p0QC1pWJQK1pW2QK1pV@QM1pVBQO1").
Proof. intros h g st x.
intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
- destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
- rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma dequeue_frame : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "RI'QI&QB'R8&QEr3r2r1%43321'9':'SG'?&SI&SC'R:%544321&R@%11;%21=%:3421'RG%;4:981&RC%11A%21C%@3421&R?%11E%21G%D3B21&SF'@&SJ%34FE21&SE&SD%26IHG541'QC%L4Q5521&R;%11Q2%21Q4%Q13421'QH%Q24Q;;81&R=%11Q8%21Q:%Q73421'8%12QAC%Q94QBB?1&RD%11Q?%21QA%Q>3421&RE%11QC%21QE%QB3Q@21&RB%11QG%21QI%QF3Q021'5%@2Q2Q2%211&RA%11QN%21R0%QM3421'Q=&R<%11R4%21R4%4221%R4261%R52>1%R62C1%R72H1%R82Q01%R92Q71%R:2QE1%R;2QJ1%R<2R11tW4RCR>1pW2RD1pVJRF1pVBRH1").
Proof. intros h m st.
unfold dequeue.
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
repeat split; try reflexivity; constructor; reflexivity.
Qed.
Lemma dequeue_metas_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "QN'QI&QB'R8&=':r1r3%33621%511&R9&R1&Gr4%2271%411(2r2%22@1%>3941%@11&R0r5%;2:1%311%92GB%E3@21%G11'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4Q951>&SH%14Q;73@&R>&QEr7r6%3321L%511%E6QBG97Q71%71O%G6QDI;9Q91%QB3I31p0M1p0Q51p0QA1pWJQI1pW2QI1pVJQK1pVBQM1").
Proof. intros h m st x.
intros NE NP NN. unfold dequeue, MR in *.
rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
repeat match goal with |- context [if ?c then _ else _] => destruct c end;
rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.
Lemma get_head_active : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "J'R8'@':&R9&QFr2(Q?r1%211%5241&SB&QB'SG&SJ&SD%34>214&SH%14@436&QD&R<%11?%311%<6E;75?1%E3D>1pW0G1pW2I1").
Proof. intros st sc. reflexivity. Qed.
Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis PRES : s_metas st !! g <> None.
Hypothesis HQ : match h with
| LActive sc => 0 <= sc < 48 /\ live_group st g /\ m_sizeclass (MR st g) = sc /\ x_fresh X = Some g
| LFree => data_of (MR st g) = data_of meta0 /\ ~ In g (x_idle X) /\ ~ In g (x_zomb X)
end.
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).
Lemma q_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "H&QB'QI&<&RLr2vCr1%211%53841'>vB%115%93<81'9':vS8%23?:1vS7%43B>1%6231%;281%C2=1pVDE1pVJG1").
Proof. intros m h'.
unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
Lemma q_in_list : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB&<&Q2vCr1%3221'>vB%6214':vS7%23;71%6241%<281pVJ>1").
Proof. intros m.
unfold in_list. split.
- intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
- intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
Lemma g_unlisted_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ";'QI&=&RL&QBvS7vBr1%211%63541%811pVD:1").
Proof. intros h'. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h'). Qed.
Lemma g_not_idle : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "9&=&RL&QBvS7&Q7vS0%211%63541%811").
Proof.
destruct h as [sc|]; [| exact (proj1 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hi. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
Qed.
Lemma g_not_zomb : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "9&=&RL&QBvS7&Q8vS0%211%63541%811").
Proof.
destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
Lemma untouched : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q=&QB'QI&=&RLr2vBr1%211%53841%711pVD91':vS7%23=91%<11'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4N51>&SH%14Q073@r3&R>vSA%211%C6Q5E7541vS@%511%F6Q8H:871%N3H41p0L1p0Q11pWJQ<1").
Proof. intros x.
intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
- intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
- intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.
Theorem INVL_queue : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "8&FvDvS0vSAvAv0vC%76654321").
Proof.
destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
refine (INVL_relink X X st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
- intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
+ exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
+ exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
- auto.
- apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
- intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
- intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
- intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
+ subst h. exact (proj1 HQ).
+ unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
- intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
- intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm)).
split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
rewrite q_in_list. tauto.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
assert (E : MR st' z = MR st z).
{ unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
rewrite E, q_in_list. repeat split; auto. tauto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
5:{ exact (g_under _ _ _ _ _ _ GO). }
+ intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
+ intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
+ intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
* apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
-- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
-- rewrite fupd_ne in Hh by exact NE. exact Hh.
* exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
+ intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
destruct h as [sc|].
* destruct HQ as (A & _ & C & _). lia.
* pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
Qed.
End QUEUE.
Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS h = l1 ++ m :: l2.
Hypothesis HX : (exists sc, h = LActive sc /\ x_fresh X = None /\ X' = xfresh X (Some m)) \/ (h = LFree /\ X' = xidle X (m :: x_idle X)).
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).
Lemma m_listed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "7&RL&QBvS<vBvS8%211%63541"). Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma d_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB'QI&RLr2vCr1%211%53741r3vB%117%93;31p051pVD<1pWJ>1").
Proof. intros x h'.
unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
Lemma d_in_rev : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "F&QB'QI&RLr2vBr1%211%53741&=':r3vS<%33<21%511r4vC%116%?3A31p051p0<1pVDC1pWJE1").
Proof. intros x h'.
intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
- left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
- right. auto.
Qed.
Lemma d_in_list : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ":&QB&Q2vCr1%3221vBr2%6221p041pWJ91").
Proof. intros x. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
Lemma m_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "6&=&Q2vCvS<%3221%511").
Proof.
intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
- pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
- apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
Lemma untouched_d : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "Q8&QB'QI&=&RLr2vBr1%211%53841%711pVD91':'7'R4%211&SB'SG&SF'?&SI'@&SJ%544321&SE&SC&SD%36872651%;4K51>&SH%14M73@&R>vSA%211%B6Q1D64M1vS@%511%E6Q4G97Q01%J3G41p0L1pWJQ71").
Proof. intros x.
intros NI. apply dequeue_metas_other.
- intros ->. exact (NI h m_listed).
- intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
- intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
Lemma nonhead_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "L&QB&RLr1vCvS8%211%53641&=':'7%11:(2r2%22=1&Q0%11:%83631%:11r3%82C1vB%11A%811%?3=41%A11p081p0D1pWJK1").
Proof. intros x.
intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
- intros E. inversion E. subst x.
pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
- exact Hh.
Qed.
Lemma MR'_m : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ";':'R4&GvSAvS<%3221&Q9vS@%6214%311%:3951").
Proof.
pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.
Theorem INVL_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "8&FvDvS1vSAvAv0vC%76654321").
Proof.
destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
- intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
+ exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
+ exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
- destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
- apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
- intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
- intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
- intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
- intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
- intros x Hx.
assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
{ intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
- rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
- intros IL'. exact (NI (d_in_list x IL')). }
destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
split; [| exact m_out].
rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
assert (E : MR st' z = MR st z).
{ unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
- intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
destruct (aptr_eq_dec x m) as [->|NEm].
+ destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
* pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
* exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
+ assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
{ destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
split; [| split; [| split; [| split]]].
5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
* intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
* intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
* intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
destruct (decide (LActive sc = h)) as [E|NE].
-- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
-- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
* intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
Qed.
End DEQUEUE.
Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS (LActive sc) = a :: rest.
Hypothesis Hn : m_next (MR st a) = Some a'.
Hypothesis OB : x_fresh X <> Some a -> rest <> [] -> m_avail (MR st a) = 0 /\ m_freed (MR st a) <> 0.
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).
Lemma r_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "?&QB'QI&<&RLr2vCr1%211%53841vB%114%83;71%:241pVD<1pWJ>1").
Proof. intros x h'.
unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
- unfold h. rewrite HL, in_app_iff. cbn. tauto.
- tauto.
Qed.
Lemma r_in_list : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 ":&QB&<&Q2vCr1%3221vB%5213%7231pWJ91").
Proof. intros x. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.
Theorem INVL_rotate : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres4 "8&FvDvS0vSAvAv0vC%76654321").
Proof.
refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
_ _ _ _ _ _ _ _).
- auto.
- apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
- intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
- intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
- intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
- intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
destruct (decide (LActive sc0 = h)) as [E|NE].
+ apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
+ rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
- intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
unfold st'. rewrite set_head_metas. exact E.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
5:{ exact (g_under _ _ _ _ _ _ GO). }
+ intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
+ intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
+ intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
* unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
-- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
-- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
* unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
+ intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
Qed.
End ROTATE.
End CEIL_WRAP_1.
