(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain FxChEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition gsubst (σ : tree lin) (g : lin * lin * gkind) : lin * lin * gkind := (lsubst σ (fst (fst g)), lsubst σ (snd (fst g)), snd g).
Definition psubst (σ : tree lin) (p : lin * Z) : lin * Z := (lsubst σ (fst p), snd p).
Definition ppsubst (σ : tree lin) (p : lin * lin) : lin * lin := (lsubst σ (fst p), lsubst σ (snd p)).
Definition msubst (σ : tree lin) (M : smodel) : smodel :=
  SM (List.map (gsubst σ) (sm_maps M)) (List.map (psubst σ) (sm_allow M)) (sm_zr M) (option_map (lsubst σ) (sm_tid M))
     (lsubst σ (sm_brk M)) (lsubst σ (sm_sbrk M)) (lsubst σ (sm_sp M)) (List.map (ppsubst σ) (sm_frz M)) (List.map (ppsubst σ) (sm_own M)).

Lemma uE_sub : forall E σ l, uE (ecomp E σ) l = uE E (lsubst σ l).
Proof. intros E σ l. unfold uE. rewrite lden_lsubst. reflexivity. Qed.
Lemma gden_sub : forall E σ g, gden (ecomp E σ) g = gden E (gsubst σ g).
Proof. intros E σ [[b z] k]. unfold gden, gsubst. cbn [fst snd]. rewrite !lden_lsubst. reflexivity. Qed.
Lemma allowA_sub : forall E σ M, allowA (ecomp E σ) M = allowA E (msubst σ M).
Proof.
  intros E σ M. unfold allowA, msubst. cbn [sm_allow]. rewrite map_map. apply map_ext. intros [b z].
  unfold allow1, psubst. cbn [fst snd]. rewrite uE_sub. reflexivity.
Qed.
Lemma Hof_sub : forall E σ M model, Hof (ecomp E σ) M model = Hof E (msubst σ M) model.
Proof. intros E σ M model. unfold Hof. rewrite allowA_sub. reflexivity. Qed.
Lemma maps_sub : forall E σ M, List.map (gden (ecomp E σ)) (sm_maps M) = List.map (gden E) (sm_maps (msubst σ M)).
Proof. intros E σ M. unfold msubst. cbn [sm_maps]. rewrite map_map. apply map_ext. intros g. apply gden_sub. Qed.
(* [comment removed for export] *)
Definition marks_ok (σ : tree lin) (gs : list (lin * lin * gkind)) : bool :=
  forallb (fun g => Bool.eqb (is_mark (gsubst σ g)) (is_mark g)) gs.
Lemma marks_ok_in : forall σ gs g, marks_ok σ gs = true -> In g gs -> is_mark (gsubst σ g) = is_mark g.
Proof. intros σ gs g H Hg. unfold marks_ok in H. rewrite forallb_forall in H. apply Bool.eqb_prop. exact (H g Hg). Qed.
Lemma lden_maps_sub : forall E σ BL gs, marks_ok σ gs = true ->
  lden_maps (ecomp E σ) BL gs = lden_maps E BL (List.map (gsubst σ) gs).
Proof.
  intros E σ BL gs. induction gs as [|g r IH]; intros H; [reflexivity|]. cbn [marks_ok forallb] in H. apply andb_prop in H as [H1 H2].
  apply Bool.eqb_prop in H1. cbn [lden_maps List.map]. rewrite H1, (IH H2), gden_sub. reflexivity.
Qed.
Lemma nomark_sub : forall σ gs, marks_ok σ gs = true -> nomark (List.map (gsubst σ) gs) = nomark gs.
Proof.
  intros σ gs. induction gs as [|g r IH]; intros H; [reflexivity|]. cbn [marks_ok forallb] in H. apply andb_prop in H as [H1 H2].
  apply Bool.eqb_prop in H1. cbn [nomark forallb List.map]. fold (nomark (List.map (gsubst σ) r)). fold (nomark r). rewrite H1, (IH H2). reflexivity.
Qed.
Lemma AM_sub : forall model0 E σ M, AM model0 (ecomp E σ) M = AM model0 E (msubst σ M).
Proof. intros model0 E σ M. unfold AM. rewrite allowA_sub. reflexivity. Qed.
Lemma blob_ok_sub : forall E σ MP model BL, marks_ok σ (sm_maps MP) = true -> blob_ok E (msubst σ MP) model BL -> blob_ok (ecomp E σ) MP model BL.
Proof.
  intros E σ MP model BL Hmk (B1 & B2 & B3). split; [exact B1 | split].
  - intros Hn. apply B2. unfold msubst. cbn [sm_maps]. rewrite (nomark_sub σ _ Hmk). exact Hn.
  - intros g Hg Hm. assert (Hg' : In (gsubst σ g) (sm_maps (msubst σ MP))) by (unfold msubst; cbn [sm_maps]; apply in_map; exact Hg).
    rewrite <- (marks_ok_in σ _ g Hmk Hg) in Hm. destruct (B3 _ Hg' Hm) as [K1 K2]. split; [exact K1|].
    unfold gsz, gsubst in *. cbn [fst snd] in *. rewrite uE_sub. exact K2.
Qed.

Lemma blob_ok_sub_rev : forall E σ MP model BL, marks_ok σ (sm_maps MP) = true -> blob_ok (ecomp E σ) MP model BL -> blob_ok E (msubst σ MP) model BL.
Proof.
  intros E σ MP model BL Hmk (B1 & B2 & B3). split; [exact B1 | split].
  - intros Hn. apply B2. unfold msubst in Hn. cbn [sm_maps] in Hn. rewrite (nomark_sub σ _ Hmk) in Hn. exact Hn.
  - intros g' Hg' Hm. unfold msubst in Hg'. cbn [sm_maps] in Hg'. apply in_map_iff in Hg' as (g & <- & Hg).
    rewrite (marks_ok_in σ _ g Hmk Hg) in Hm. destruct (B3 g Hg Hm) as [K1 K2]. split; [exact K1|].
    unfold gsz, gsubst in *. cbn [fst snd] in *. rewrite <- uE_sub. exact K2.
Qed.

Lemma Forall_sub_maps : forall E σ M (P : valu -> lin * lin * gkind -> Prop),
  (forall g, P E (gsubst σ g) -> P (ecomp E σ) g) -> Forall (P E) (sm_maps (msubst σ M)) -> Forall (P (ecomp E σ)) (sm_maps M).
Proof.
  intros E σ M P HP H. unfold msubst in H. cbn [sm_maps] in H. rewrite Forall_map in H.
  rewrite Forall_forall in *. intros g Hg. apply HP. exact (H g Hg).
Qed.
Lemma own_pt_sub : forall E σ M w, own_pt (ecomp E σ) M w <-> own_pt E (msubst σ M) w.
Proof.
  intros E σ M w. unfold own_pt, msubst. cbn [sm_own]. split.
  - intros (p & Hp & Hw). exists (ppsubst σ p). split; [apply in_map; exact Hp|]. unfold ppsubst. cbn [fst snd].
    rewrite <- !uE_sub. exact Hw.
  - intros (p & Hp & Hw). apply in_map_iff in Hp as (q & <- & Hq). exists q. split; [exact Hq|]. unfold ppsubst in Hw. cbn [fst snd] in Hw.
    rewrite !uE_sub. exact Hw.
Qed.

(* [comment removed for export] *)
Section EntM.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_ent_M : forall E S P MP ms model σ,
  DEN segs LIMIT model0 mem0 E S (msubst σ MP) ms model ->
  entails S P σ = true -> state_wf P = true -> sm_wf (s_next P) MP = true -> marks_ok σ (sm_maps MP) = true ->
  DEN segs LIMIT model0 mem0 (ecomp E σ) P MP ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S P MP ms model σ Hd Hent Hwp Hwf0 Hmk.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (E' := ecomp E σ).
  assert (HA : allowA E' MP = allowA E (msubst σ MP)) by exact (allowA_sub E σ MP).
  assert (HH : Hof E' MP model = Hof E (msubst σ MP) model) by exact (Hof_sub E σ MP model).
  assert (Hrge : rgs_ent (s_rgs S) (s_rgs P) σ = true).
  { unfold entails in Hent. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [Hent _]. apply andb_prop in Hent as [_ Hg]. exact Hg. }
  constructor.
  - rewrite HH. apply (entails_sden segs E S P σ _ (sden_0 _ _ _ _ Hsd) Hent Hwp).
  - exact Hwf0.
  - exact (state_wf_bases P Hwp).
  - exact Hh.
  - rewrite HA. exact Hawf.
  - unfold msubst in Hanz. cbn [sm_allow] in Hanz. rewrite Forall_map in Hanz. rewrite Forall_forall in *. intros p Hp. exact (Hanz p Hp).
  - unfold E'. rewrite (AM_sub model0 E σ MP). exact Hminv.
  - rewrite HH. exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - rewrite Hsp. unfold msubst. cbn [sm_sp]. rewrite lden_lsubst. reflexivity.
  - exact Hspok.
  - rewrite Hbrk. unfold msubst. cbn [sm_brk]. rewrite lden_lsubst. reflexivity.
  - rewrite Hsbrk. unfold msubst. cbn [sm_sbrk]. rewrite lden_lsubst. reflexivity.
  - rewrite Htid. unfold msubst. cbn [sm_tid]. destruct (sm_tid MP) as [l|]; [cbn; f_equal; rewrite lden_lsubst; reflexivity | reflexivity].
  - rewrite Hmaps. symmetry. unfold E', msubst. cbn [sm_maps]. exact (lden_maps_sub E σ _ _ Hmk).
  - apply (Forall_sub_maps E σ MP gshape_ok); [|exact Hgsh].
    intros g Hg. unfold gshape_ok, gsz, gsubst in *. cbn [fst snd] in *. rewrite !uE_sub. exact Hg.
  - apply (Forall_sub_maps E σ MP (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model))); [|exact Hgtop].
    intros g Hg. unfold gsz, gsubst in Hg |- *. cbn [fst snd] in *. rewrite !uE_sub. exact Hg.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - apply (Forall_sub_maps E σ MP (fun E g => kind_ok E model g)); [|exact Hkind].
    intros g Hg. unfold kind_ok in *. rewrite gden_sub. unfold gsubst in Hg. cbn [snd] in Hg. exact Hg.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. apply (Hzr w Hw).
    + apply (proj2 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
    + intros Ho. apply Hnow. apply (proj2 (own_pt_sub E σ MP w)). exact Ho.
    + exact Hnb.
  - exact (rl_ok_ent E model (s_rgs S) (s_rgs P) σ Hrge Hrl).
  - exact Hvmo.
  - exact Hproc.
  - intros q Hq w Hw.
    assert (Hq' : In (ppsubst σ q) (sm_frz (msubst σ MP))) by (unfold msubst; cbn [sm_frz]; apply in_map; exact Hq).
    assert (Hw0 : uE E (fst (ppsubst σ q)) <= w < uE E (fst (ppsubst σ q)) + uE E (snd (ppsubst σ q)))
      by (unfold ppsubst; cbn [fst snd]; rewrite <- !uE_sub; exact Hw).
    destruct (Hfrz _ Hq' w Hw0) as (Htp & Hout & Hm). split; [exact Htp|]. split; [|exact Hm].
    apply (proj1 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
  - rom_tac.
  - intros q Hq w Hw.
    assert (Hq' : In (ppsubst σ q) (sm_own (msubst σ MP))) by (unfold msubst; cbn [sm_own]; apply in_map; exact Hq).
    assert (Hw0 : uE E (fst (ppsubst σ q)) <= w < uE E (fst (ppsubst σ q)) + uE E (snd (ppsubst σ q)))
      by (unfold ppsubst; cbn [fst snd]; rewrite <- !uE_sub; exact Hw).
    destruct (Hown _ Hq' w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout.
    apply Hm. apply (proj2 (rgs_ent_outside E (s_rgs S) (s_rgs P) σ _ Hrge)). exact Hout.
  - exact (blob_ok_sub E σ MP model _ Hmk Hblob).
Qed.
End EntM.
