(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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

Lemma ctrl_eq_refl st : ctrl_eq st st.
Proof. constructor; reflexivity. Qed.

Lemma ctrl_eq_trans a b c : ctrl_eq a b -> ctrl_eq b c -> ctrl_eq a c.
Proof. intros [] []; constructor; congruence. Qed.

Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr8 st p v : ctrl_eq st (wr8 p v st). Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_wr16 st p v : ctrl_eq st (wr16 p v st). Proof. constructor; reflexivity. Qed.

Section VIEWS.
Variables st st' : mstate.

Lemma MR_ext : s_metas st' = s_metas st -> forall x, MR st' x = MR st x.
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
Lemma hosts_ext : s_groups st' = s_groups st -> forall b m, hosts st' b m <-> hosts st b m.
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
Lemma live_group_ext : s_groups st' = s_groups st -> forall m, live_group st' m <-> live_group st m.
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
Lemma frontier_ext : c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) -> forall rid r, frontier st' rid r = frontier st rid r.
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
Lemma gcnt_ext : s_groups st' = s_groups st -> s_metas st' = s_metas st -> forall sc, gcnt st' sc = gcnt st sc.
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
Lemma get_head_ext : s_ctx st' = s_ctx st -> forall h, get_head st' h = get_head st h.
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.

Lemma usage_ext : c_usage (s_ctx st') = c_usage (s_ctx st) -> forall sc, usage st' sc = usage st sc.
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.

Lemma known_ext : s_shadow st' = s_shadow st -> forall p v, known st' p v <-> known st p v.
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma unknown_ext : s_shadow st' = s_shadow st -> forall p, unknown st' p <-> unknown st p.
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
Lemma linked_ext_metas : s_metas st' = s_metas st -> forall l, linked st l -> linked st' l.
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
Lemma dll_ext_metas : s_metas st' = s_metas st -> forall l, dll st l -> dll st' l.
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE.

Lemma inv_R_ctrl : inv_R X st L -> inv_R X st' L.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HC, ?HG; try assumption.
  -
    eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r H1 H2. rewrite FR. eauto.
Qed.

Lemma inv_A_ctrl : inv_A st -> inv_A st'.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
  destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
  - intros a ar H. destruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
  - intros sc Hsc. rewrite US, GC. auto.
Qed.

Lemma inv_M_ctrl : inv_M X st LS -> inv_M X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

Lemma inv_L_ctrl : inv_L st LS -> inv_L st' LS.
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

Lemma group_ok_ctrl m b ai : group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_G_ctrl : inv_G X st LS -> inv_G X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [G1 G2 G3 G4 G5]; constructor.
  - intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
  - intros b ai H. rewrite HG in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
  - intros rid r H1 H2 H3. rewrite HR in H1. destruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
  - intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
Qed.

Lemma inv_S_ctrl : inv_S X st BL -> inv_S X st' BL.
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

Lemma inv_SH_set_tick st BL t : (s_tick st <= t)%N -> inv_SH st BL -> inv_SH (set_tick t st) BL.
Proof.
  intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
  intros rid sh H. destruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
  - intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
  - intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
  - intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.

Lemma inv_SH_view st st' BL :
  s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> s_regions st' = s_regions st ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  (forall x, gbase (MR st' x) = gbase (MR st x)) ->
  (forall x, get_stride (MR st' x) = get_stride (MR st x)) ->
  (forall x, m_last_idx (MR st' x) = m_last_idx (MR st x)) ->
  (forall x, m_maplen (MR st' x) = m_maplen (MR st x)) ->
  inv_SH st BL -> inv_SH st' BL.
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

End AC_1.
