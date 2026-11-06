(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_Ext () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.MI_Inv.frontier"; "ctrl_eq"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.MI_Inv.inv_SH"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.MI_Inv.gbase"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "OSSVerify.KrLib.Heap.MI_Inv.INVL"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ctrl_eq (st st' : mstate) : Prop := mkCE {
  ce_ctx : s_ctx st' = s_ctx st;
  ce_regions : s_regions st' = s_regions st;
  ce_next_rid : s_next_rid st' = s_next_rid st;
  ce_metas : s_metas st' = s_metas st;
  ce_areas : s_areas st' = s_areas st;
  ce_groups : s_groups st' = s_groups st;
  ce_slots : s_slots st' = s_slots st;
  ce_secret : s_secret st' = s_secret st;
  ce_reserved : s_reserved st' = s_reserved st;
  ce_ceil : s_ceil st' = s_ceil st            (* [comment removed for export] *)
}.

Lemma ctrl_eq_refl st : ctrl_eq st st.
Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_sym st st' : ctrl_eq st st' -> ctrl_eq st' st.
Proof. intros []; constructor; symmetry; assumption. Qed.
Lemma ctrl_eq_trans a b c : ctrl_eq a b -> ctrl_eq b c -> ctrl_eq a c.
Proof. intros [] []; constructor; congruence. Qed.

Lemma ctrl_eq_strip st st' : strip st' = strip st -> ctrl_eq st st'.
Proof. intros H. pose proof (strip_fields st) as A. pose proof (strip_fields st') as B. constructor; intuition congruence. Qed.

(* [comment removed for export] *)
Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr8 st p v : ctrl_eq st (wr8 p v st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr16 st p v : ctrl_eq st (wr16 p v st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr32 st p v : ctrl_eq st (wr32 p v st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_havoc st p n : ctrl_eq st (havoc p n st). Proof. apply ctrl_eq_strip. apply strip_havoc. Qed.
Lemma ctrl_eq_hdr_havoc st b : ctrl_eq st (hdr_havoc b st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_upd_shadow st rid f : ctrl_eq st (upd_shadow rid f st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_zero_hdrs st p size i cnt : ctrl_eq st (zero_hdrs p size i cnt st). Proof. apply ctrl_eq_strip. apply strip_zero_hdrs. Qed.
Lemma ctrl_eq_set_size st p e n b : ctrl_eq st (set_size p e n b st). Proof. apply ctrl_eq_strip. apply strip_set_size. Qed.
Lemma ctrl_eq_enframe_at st g idx n off : ctrl_eq st (fst (enframe_at st g idx n off)). Proof. apply ctrl_eq_strip. apply strip_enframe_at. Qed.
Lemma ctrl_eq_nest_layout st g idx j size cnt : ctrl_eq st (nest_layout st g idx j size cnt). Proof. apply ctrl_eq_strip. apply strip_nest_layout. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VIEWS.
Variables st st' : mstate.

#[using="Type"] Lemma MR_ext : s_metas st' = s_metas st -> forall x, MR st' x = MR st x.
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
#[using="Type"] Lemma hosts_ext : s_groups st' = s_groups st -> forall b m, hosts st' b m <-> hosts st b m.
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
#[using="Type"] Lemma live_group_ext : s_groups st' = s_groups st -> forall m, live_group st' m <-> live_group st m.
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
#[using="Type"] Lemma frontier_ext : ltac2:(CDefT.buildp (gd_tbl_MI_Ext ()) "P,(0.$1.(2.(3.Vst',))(2.(3.Vst,)))Prid,$4.Pr,$5.(0.$6.(7.Vst',R2.R1.)(7.Vst,R2.R1.))")
(* [comment removed for export] *).
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma gcnt_ext : s_groups st' = s_groups st -> s_metas st' = s_metas st -> forall sc, gcnt st' sc = gcnt st sc.
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
#[using="Type"] Lemma get_head_ext : s_ctx st' = s_ctx st -> forall h, get_head st' h = get_head st h.
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.
#[using="Type"] Lemma active_ext : c_active (s_ctx st') = c_active (s_ctx st) -> forall sc, active st' sc = active st sc.
Proof. intros H sc. unfold active, ctx. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma usage_ext : c_usage (s_ctx st') = c_usage (s_ctx st) -> forall sc, usage st' sc = usage st sc.
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_ext' : s_shadow st' = s_shadow st -> forall rid, get_shadow st' rid = get_shadow st rid.
Proof. intros H rid. apply get_shadow_ext. exact H. Qed.
#[using="Type"] Lemma known_ext : s_shadow st' = s_shadow st -> forall p v, known st' p v <-> known st p v.
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
#[using="Type"] Lemma unknown_ext : s_shadow st' = s_shadow st -> forall p, unknown st' p <-> unknown st p.
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
#[using="Type"] Lemma linked_ext_metas : s_metas st' = s_metas st -> forall l, linked st l -> linked st' l.
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
#[using="Type"] Lemma dll_ext_metas : s_metas st' = s_metas st -> forall l, dll st l -> dll st' l.
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE. Let HCL := ce_ceil _ _ CE.

#[using="CE HC HR HN HG HV HCL"] Lemma inv_R_ctrl : inv_R X st L -> inv_R X st' L.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HC, ?HG, ?HCL; try assumption.
  - (* [comment removed for export] *)
    eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r H1 H2. rewrite FR. eauto.
Qed.

#[using="CE HC HR HM HA HG HX"] Lemma inv_A_ctrl : inv_A st -> inv_A st'.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
  destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
  - intros a ar H. ddestruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
  - intros sc Hsc. rewrite US, GC. auto.
Qed.

#[using="CE HM HG"] Lemma inv_M_ctrl : inv_M X st LS -> inv_M X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. ddestruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. ddestruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

#[using="CE HC HM HG"] Lemma inv_L_ctrl : inv_L st LS -> inv_L st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (get_head_ext st st' HC) as HE.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. ddestruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

#[using="CE HR HM HS"] Lemma group_ok_ctrl m b ai : group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
  - intros H. ddestruct (G14 H) as (p & i & ? & ? & ? & ? & ?). dexists p, i. rewrite !ME. auto 10.
Qed.

#[using="CE HR HM HG HS"] Lemma inv_G_ctrl : inv_G X st LS -> inv_G X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [G1 G2 G3 G4 G5]; constructor.
  - intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
  - intros b ai H. rewrite HG in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
  - intros rid r H1 H2 H3. rewrite HR in H1. ddestruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
  - intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
Qed.

#[using="CE HM HG HS"] Lemma inv_S_ctrl : inv_S X st BL -> inv_S X st' BL.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. ddestruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. ddestruct (S6 k Hk) as (m & i & ? & ?). dexists m, i. rewrite HS, ME. auto.
Qed.
End CTRL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_SH_set_tick st BL t : (s_tick st <= t)%N -> inv_SH st BL -> inv_SH (set_tick t st) BL.
Proof.
  intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
  intros rid sh H. ddestruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
  - intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
  - intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
  - intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_ctrl st st' BL : ltac2:(CDefT.buildp (gd_tbl_MI_Ext ()) "P,(8.O3.O2.)P,(0.(9.$4.$:.$;.$<.)(=.O2.)(=.O3.))P,(0.$4.(>.O2.)(>.O3.))P,(?.O3.O1.)(?.O2.O1.)")
(* [comment removed for export] *).
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
    ddestruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !ME.
    ddestruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. ddestruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_view st st' BL : ltac2:(CDefT.buildp (gd_tbl_MI_Ext ()) "P,(0.(9.$4.$:.$;.$<.)(=.O2.)(=.O3.))P,(0.$4.(>.O2.)(>.O3.))P,(0.(9.$4.$:.$;.$5.)(10.O2.)(10.O3.))P,(0.(9.$11.(12.$4.$:.$6.$13.)(14.$4.$:.$;.$6.$13.$15.)$16.)(17.O2.)(17.O3.))P,(0.(9.$11.(12.$4.$:.$6.$13.)(14.$4.$:.$;.$6.$13.$15.)(18.$11.$6.))(19.O2.)(19.O3.))P,Px,$11.(0.$11.(1:.(1;.O2.R1.))(1:.(1;.O3.R1.)))P,Px,$11.(0.$6.(1<.(1;.O2.R1.))(1<.(1;.O3.R1.)))P,Px,$11.(0.$6.(1=.(1;.O2.R1.))(1=.(1;.O3.R1.)))P,Px,$11.(0.$6.(1>.(1;.O2.R1.))(1>.(1;.O3.R1.)))P,(?.O3.O1.)(?.O2.O1.)")
(* [comment removed for export] *).
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
    ddestruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !VS, !VB.
    ddestruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. ddestruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma INVL_ctrl_same X st st' L BL LS : ltac2:(CDefT.buildp (gd_tbl_MI_Ext ()) "P,(8.O5.O4.)P,(0.(9.$4.$:.$;.$<.)(=.O4.)(=.O5.))P,(0.$4.(>.O4.)(>.O5.))P,(1?.O6.O5.O3.O2.O1.)(1?.O6.O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros CE SH TK dd_H; ddestruct dd_H as (IR & IA & IM & IL & IG & IS & ISH)).
  split; [apply (inv_R_ctrl X st st'); assumption|].
  split; [apply (inv_A_ctrl st st'); assumption|].
  split; [apply (inv_M_ctrl X st st'); assumption|].
  split; [apply (inv_L_ctrl st st'); assumption|].
  split; [apply (inv_G_ctrl X st st'); assumption|].
  split; [apply (inv_S_ctrl X st st'); assumption|].
  apply (inv_SH_ctrl st st'); assumption.
Qed.
