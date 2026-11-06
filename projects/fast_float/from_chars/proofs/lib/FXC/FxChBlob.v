(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxFacts FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChFix FxChAdd FxChUnmap FxChMprot.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition with_blob (BL : list (word * word)) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) BL (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
                 (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Lemma blob_of_with_blob : forall BL m, blob_of (with_blob BL m) = BL.
Proof. intros BL m. destruct m. reflexivity. Qed.
Lemma with_blob_other : forall BL m, m_fd (with_blob BL m) = m_fd m /\ m_io (with_blob BL m) = m_io m /\ m_fsys (with_blob BL m) = m_fsys m /\
  m_lim (with_blob BL m) = m_lim m /\ m_time (with_blob BL m) = m_time m /\ m_proc (with_blob BL m) = m_proc m.
Proof. intros BL m. destruct m. repeat split; reflexivity. Qed.
Lemma with_blob_tid_proc : forall BL t m, m_proc (with_tid t (with_blob BL m)) = m_proc (with_tid t m).
Proof. intros BL t m. destruct m. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MARKT (T : lin) : lin * lin * gkind := (lconst MARKB, T, GE).
Lemma is_mark_MARKT : forall T, is_const T = None -> is_mark (MARKT T) = true.
Proof. intros T H. unfold is_mark, MARKT. cbn [fst snd]. rewrite H. reflexivity. Qed.
Fixpoint ins_mark (i : nat) (T : lin) (gs : list (lin * lin * gkind)) : list (lin * lin * gkind) :=
  match i, gs with
  | O, _ => MARKT T :: gs
  | Datatypes.S i', g :: r => g :: ins_mark i' T r
  | Datatypes.S _, [] => [MARKT T]
  end.
Lemma ins_mark_lden : forall E i T gs, is_const T = None -> lden_maps E [] (ins_mark i T gs) = lden_maps E [] gs.
Proof.
  intros E i T gs HT. revert gs. induction i as [|i IH]; intros gs; [cbn [ins_mark lden_maps]; rewrite (is_mark_MARKT T HT); reflexivity|].
  destruct gs as [|g r]; [cbn [ins_mark lden_maps]; rewrite (is_mark_MARKT T HT); reflexivity|]. cbn [ins_mark lden_maps].
  rewrite (IH r). reflexivity.
Qed.
Lemma ins_mark_In : forall i T gs g, In g (ins_mark i T gs) -> g = MARKT T \/ In g gs.
Proof.
  intros i T. induction i as [|i IH]; intros gs g H; [destruct H as [<-|H]; [left; reflexivity | right; exact H]|].
  destruct gs as [|g0 r]; [destruct H as [<-|[]]; left; reflexivity|]. destruct H as [<-|H]; [right; left; reflexivity|].
  destruct (IH r g H) as [H1|H1]; [left; exact H1 | right; right; exact H1].
Qed.

(* [comment removed for export] *)
Fixpoint absorb (i : nat) (gs : list (lin * lin * gkind)) : option ((lin * lin * gkind) * list (lin * lin * gkind)) :=
  match i, gs with
  | O, g :: mk :: r =>
      if (negb (is_mark g) &&& is_mark mk &&& nomark r &&& is_mark (fst (fst mk), ladd (snd (fst mk)) (lscale 4 (snd (fst g))), snd mk))
      then Some (g, (fst (fst mk), ladd (snd (fst mk)) (lscale 4 (snd (fst g))), snd mk) :: r) else None
  | Datatypes.S i', g0 :: r =>
      if is_mark g0 then None else match absorb i' r with Some (g, r') => Some (g, g0 :: r') | None => None end
  | _, _ => None
  end.
Lemma absorb_spec : forall i gs g gs', absorb i gs = Some (g, gs') ->
  exists pre mk r, gs = pre ++ g :: mk :: r /\ gs' = pre ++ (fst (fst mk), ladd (snd (fst mk)) (lscale 4 (snd (fst g))), snd mk) :: r /\
    nomark pre = true /\ is_mark g = false /\ is_mark mk = true /\ nomark r = true /\ length pre = i /\
    is_mark (fst (fst mk), ladd (snd (fst mk)) (lscale 4 (snd (fst g))), snd mk) = true.
Proof.
  intros i. induction i as [|i IH]; intros gs g gs' H.
  - destruct gs as [|g0 [|mk r]]; try discriminate. cbn [absorb] in H.
    destruct (is_mark g0) eqn:H0; [discriminate|]. cbn [negb] in H. destruct (is_mark mk) eqn:H1; [|discriminate].
    destruct (nomark r) eqn:H2; [|discriminate]. destruct (is_mark (_, _, _)) eqn:H3; [|discriminate]. injection H as <- <-. exists [], mk, r. repeat split; auto.
  - destruct gs as [|g0 r]; [discriminate|]. cbn [absorb] in H. destruct (is_mark g0) eqn:H0; [discriminate|].
    destruct (absorb i r) as [[g1 r']|] eqn:Ha; [|discriminate]. injection H as <- <-.
    destruct (IH r g1 r' Ha) as (pre & mk & rr & -> & -> & P1 & P2 & P3 & P4 & P5 & P6). exists (g0 :: pre), mk, rr.
    repeat split; auto; [cbn [nomark forallb]; rewrite H0; exact P1 | cbn [length]; rewrite P5; reflexivity].
Qed.
Lemma lden_maps_app_nomark : forall E BL pre gs, nomark pre = true -> lden_maps E BL (pre ++ gs) = List.map (gden E) pre ++ lden_maps E BL gs.
Proof.
  intros E BL pre gs. induction pre as [|g r IH]; intros H; [reflexivity|]. cbn [nomark forallb] in H. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1. cbn [app lden_maps List.map]. rewrite H1, (IH H2). reflexivity.
Qed.
Lemma absorb_lden : forall E BL i gs g gs', absorb i gs = Some (g, gs') -> lden_maps E BL gs = lden_maps E (gden E g :: BL) gs'.
Proof.
  intros E BL i gs g gs' H. destruct (absorb_spec i gs g gs' H) as (pre & mk & r & -> & -> & P1 & P2 & P3 & P4 & _ & P6).
  rewrite !(lden_maps_app_nomark E _ pre _ P1). f_equal. cbn [lden_maps]. rewrite P2, P6, P3.
  rewrite !(lden_maps_nomark E _ r P4). reflexivity.
Qed.

(* [comment removed for export] *)
Definition with_maps (M : smodel) (gs : list (lin * lin * gkind)) : smodel :=
  SM gs (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).
Definition with_allow (M : smodel) (al : list (lin * Z)) : smodel :=
  SM (sm_maps M) al (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

Lemma sm_wf_with_maps : forall n M gs, sm_wf n M = true -> forallb (fun g => lwf n (fst (fst g)) && lwf n (snd (fst g)))%bool gs = true ->
  sm_wf n (with_maps M gs) = true.
Proof.
  intros n M gs H Hg. unfold sm_wf in *. cbn [with_maps sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own]. rewrite Hg.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite H2, H3, H4, H5, H6, H7, H8. reflexivity.
Qed.
Lemma sm_wf_maps_b : forall n M, sm_wf n M = true -> forallb (fun g => lwf n (fst (fst g)) && lwf n (snd (fst g)))%bool (sm_maps M) = true.
Proof.
  intros n M H. unfold sm_wf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H.
Qed.
Lemma uE_lconst : forall E z, 0 <= z < two64 -> uE E (lconst z) = z.
Proof. intros E z Hz. unfold uE. rewrite lden_lconst. apply fg64. exact Hz. Qed.

Section Blob.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_mark_ins : forall E S M ms model i T,
  DEN segs LIMIT model0 mem0 E S M ms model -> nomark (sm_maps M) = true ->
  lwf (s_next S) T = true -> is_const T = None -> uE E T = 4096 ->
  DEN segs LIMIT model0 mem0 E S (with_maps M (ins_mark i T (sm_maps M))) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i T Hd Hnm HTw HTc HTv. set (MARK0 := MARKT T). pose proof (den_blob_nil _ _ _ _ _ _ _ _ _ Hd Hnm) as Hb0.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := with_maps M (ins_mark i T (sm_maps M))).
  assert (HM0 : gshape_ok E MARK0 /\ uE E (fst (fst MARK0)) + gsz E MARK0 <= alloc_top (m_vmmaps model) /\ kind_ok E model MARK0).
  { unfold gshape_ok, gsz, MARK0, MARKT, MARKB, kind_ok. cbn [fst snd]. rewrite HTv. rewrite !uE_lconst by (unfold two64; lia).
    pose proof (alloc_top_lo _ (proj1 Hspok)). repeat split; try lia; try reflexivity; intros Hc; try discriminate. exfalso. exact (Hc eq_refl). }
  destruct HM0 as (Hm1 & Hm2 & Hm3).
  assert (HF : forall (P : lin * lin * gkind -> Prop), P MARK0 -> Forall P (sm_maps M) -> Forall P (ins_mark i T (sm_maps M))).
  { intros P HP HFo. apply Forall_forall. intros g Hg. destruct (ins_mark_In i T _ g Hg) as [->|Hin]; [exact HP|]. rewrite Forall_forall in HFo. exact (HFo g Hin). }
  constructor; try assumption.
  - apply sm_wf_with_maps; [exact Hwf|]. apply forallb_forall. intros g Hg. destruct (ins_mark_In i T _ g Hg) as [->|Hin]; [unfold MARKT; cbn [fst snd]; rewrite HTw; reflexivity|].
    pose proof (sm_wf_maps_b _ M Hwf) as Hb. rewrite forallb_forall in Hb. exact (Hb g Hin).
  - cbn [M' with_maps sm_maps]. rewrite Hb0, (ins_mark_lden E i T _ HTc). rewrite Hb0 in Hmaps. exact Hmaps.
  - exact (HF _ Hm1 Hgsh).
  - exact (HF _ Hm2 Hgtop).
  - exact (HF _ Hm3 Hkind).
  - rewrite Hb0. split; [constructor | split; [reflexivity|]]. intros g Hg Hm. cbn [M' with_maps sm_maps] in Hg.
    destruct (ins_mark_In i T _ g Hg) as [->|Hin]; [|rewrite (nomark_in _ g Hnm Hin) in Hm; discriminate].
    split; [reflexivity|]. cbn [ledger_size]. unfold gsz, MARKT. cbn [fst snd]. rewrite HTv. lia.
Qed.

(* [comment removed for export] *)
Definition absorb_ok (S : sst) (M : smodel) (i : nat) : bool :=
  match absorb i (sm_maps M), nth_error (sm_maps M) (Datatypes.S i) with
  | Some (g, gs'), Some mk =>
      gkind_eqb (snd g) GE &&& Z.leb (gsz_hi (s_facts S) mk + 4 * gsz_hi (s_facts S) g) 70368744177664 &&&
      Z.leb (eager_sum (s_facts S) gs' + allow_bound (sm_allow M)) LIMIT
  | _, _ => false
  end.
Definition absorb_M (M : smodel) (i : nat) : smodel :=
  match absorb i (sm_maps M) with Some (_, gs') => with_maps M gs' | None => M end.
Definition absorb_g (M : smodel) (i : nat) : lin * lin * gkind :=
  match absorb i (sm_maps M) with Some (g, _) => g | None => (lconst MARKB, lconst 4096, GE) end.

#[using="Type"] Lemma u_ladd_scale4 : forall E T z, uE E T + 4 * uE E z < two64 -> uE E (ladd T (lscale 4 z)) = uE E T + 4 * uE E z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E T z H. unfold uE in *. rewrite lden_ladd, bv_add_unsigned, lden_lscale.
  pose proof (bv_unsigned_in_range _ (lden E T)) as R1. pose proof (bv_unsigned_in_range _ (lden E z)) as R2. unfold bv_modulus in R1, R2.
  change (2 ^ Z.of_N 64) with two64 in R1, R2.
  rewrite (fg64 (4 * _)) by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. lia.
Qed.

#[using="Type"] Theorem den_blob_absorb : forall E S M ms model i,
  DEN segs LIMIT model0 mem0 E S M ms model -> absorb_ok S M i = true ->
  DEN segs LIMIT (with_blob (gden E (absorb_g M i) :: blob_of model0) model0) mem0 E S (absorb_M M i) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i Hd Hok. unfold absorb_ok in Hok. unfold absorb_M, absorb_g.
  destruct (absorb i (sm_maps M)) as [[g gs']|] eqn:Hab; [|discriminate].
  destruct (nth_error (sm_maps M) (Datatypes.S i)) as [mk|] eqn:Hmk; [|discriminate].
  destruct (gkind_eqb (snd g) GE) eqn:Hge; [|discriminate].
  destruct (Z.leb (gsz_hi (s_facts S) mk + 4 * gsz_hi (s_facts S) g) 70368744177664) eqn:Hsz; [|discriminate].
  apply Z.leb_le in Hsz, Hok.
  destruct (absorb_spec i _ g gs' Hab) as (pre & mk0 & r & Hgs & Hgs' & P1 & P2 & P3 & P4 & P5 & P6).
  assert (Hmk0 : mk0 = mk).
  { rewrite Hgs in Hmk. rewrite <- P5 in Hmk. clear -Hmk. induction pre as [|x pre IH]; cbn in Hmk; [injection Hmk as ->; reflexivity | exact (IH Hmk)]. }
  subst mk0.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  set (BL := blob_of model0) in *. set (BL' := gden E g :: BL).
  set (m0' := with_blob BL' model0).
  set (T' := ladd (snd (fst mk)) (lscale 4 (snd (fst g)))). set (mk' := (fst (fst mk), T', snd mk)).
  set (M' := with_maps M gs').
  assert (Hing : In g (sm_maps M)) by (rewrite Hgs; apply in_or_app; right; left; reflexivity).
  assert (Hinm : In mk (sm_maps M)) by (rewrite Hgs; apply in_or_app; right; right; left; reflexivity).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hing) as (G1 & G2 & G3 & G4 & G5).
  destruct (Hgsh0 mk Hinm) as (K1 & K2 & K3 & K4 & K5).
  pose proof (gsz_bounds E (s_facts S) g HF0) as Bg. pose proof (gsz_bounds E (s_facts S) mk HF0) as Bm.
  destruct Hblob as (B1 & B2 & B3). destruct (B3 mk Hinm P3) as [Kge Kt].
  assert (HT' : uE E T' = gsz E mk + 4 * gsz E g) by (unfold T', gsz; apply u_ladd_scale4; unfold gsz in *; unfold two64; lia).
  assert (Hbmk : uE E (fst (fst mk)) = MARKB).
  { pose proof (is_mark_base E mk P3) as Hb. unfold uE. rewrite Hb. apply fg64. unfold MARKB, two64. lia. }
  assert (Hb0' : blob_of m0' = BL') by apply blob_of_with_blob.
  assert (Hmaps' : vm_maps (m_vmmaps model) = lden_maps E BL' gs') by (rewrite Hmaps; exact (absorb_lden E BL i _ g gs' Hab)).
  assert (Hwf' : sm_wf (s_next S) M' = true).
  { apply sm_wf_with_maps; [exact Hwf|]. pose proof (sm_wf_maps_b _ M Hwf) as Hb. rewrite Hgs in Hb. rewrite Hgs'.
    rewrite forallb_app in Hb |- *. apply andb_prop in Hb as [Hb1 Hb2]. rewrite Hb1. cbn [forallb andb] in Hb2 |- *.
    apply andb_prop in Hb2 as [Hg' Hb2]. apply andb_prop in Hb2 as [Hm' Hb2]. apply andb_prop in Hg' as [_ Hg2]. apply andb_prop in Hm' as [Hm1 Hm2].
    rewrite Hb2. cbn [fst snd]. rewrite Hm1. unfold T'. rewrite (lwf_ladd _ _ _ Hm2 (lwf_lscale _ 4 _ Hg2)). reflexivity. }
  assert (HFo : forall (P : lin * lin * gkind -> Prop), P mk' -> Forall P (sm_maps M) -> Forall P gs').
  { intros P HP HFa. rewrite Hgs in HFa. rewrite Hgs'. apply Forall_app in HFa as [F1 F2]. apply Forall_app. split; [exact F1|].
    inversion F2 as [|? ? _ F3]; subst. inversion F3 as [|? ? _ F4]; subst. constructor; [exact HP | exact F4]. }
  assert (Hgsh' : Forall (gshape_ok E) gs').
  { apply HFo; [|exact Hgsh]. unfold gshape_ok, gsz, mk'. cbn [fst snd]. rewrite HT', Hbmk. unfold gsz in *. unfold MARKB.
    repeat split; try lia.
    all: rewrite Z.add_mod, K2 by lia; replace (4 * uE E (snd (fst g))) with (uE E (snd (fst g)) * 4) by lia;
         rewrite <- (Z.mul_mod_idemp_l (uE E (snd (fst g)))) by lia; unfold uE in *; rewrite G2; reflexivity. }
  assert (Hkind' : Forall (kind_ok E model) gs').
  { apply HFo; [|exact Hkind]. unfold kind_ok, mk'. cbn [snd]. rewrite Kge. split; intros Hc; [exfalso; exact (Hc eq_refl) | discriminate]. }
  assert (Hblob' : blob_ok E M' model BL').
  { split; [|split].
    - constructor; [|exact B1]. unfold blob_ent_ok, gden. cbn [fst snd]. rewrite Forall_forall in Hgtop. pose proof (Hgtop g Hing) as Gt.
      pose proof (Z.div_mod (bv_unsigned (lden E (fst (fst g)))) 4096 ltac:(lia)) as Hdm.
      unfold gsz, uE, MARKB in *. repeat split; lia.
    - intros Hn. exfalso. cbn [M' with_maps sm_maps] in Hn. rewrite Hgs' in Hn. unfold nomark in Hn. rewrite forallb_app in Hn.
      apply andb_prop in Hn as [_ Hn]. cbn [forallb] in Hn. apply andb_prop in Hn as [Hn _]. rewrite P6 in Hn. discriminate.
    - intros g' Hg' Hm'. cbn [M' with_maps sm_maps] in Hg'. rewrite Hgs' in Hg'. apply in_app_or in Hg' as [Hg'|[<-|Hg']].
      + rewrite (nomark_in _ g' P1 Hg') in Hm'. discriminate.
      + cbn [snd]. split; [exact Kge|]. unfold gsz. cbn [fst snd]. fold T'. rewrite HT'. unfold BL'. cbn [ledger_size gden]. unfold gsz, uE in *. lia.
      + rewrite (nomark_in _ g' P4 Hg') in Hm'. discriminate. }
  constructor; try assumption.
  - (* [comment removed for export] *)
    destruct Hminv as [N1 N2 N3 N4 N5]. constructor; try assumption.
    + intros p Hp. specialize (N3 p Hp). unfold AM in *. rewrite Hb0'. change (allowA E M') with (allowA E M). unfold page_allowedb in *. rewrite existsb_app in *.
      apply orb_prop in N3 as [N3|N3]; [rewrite N3; reflexivity|]. unfold BL'. cbn [blobA List.map existsb]. fold (blobA BL). unfold BL. rewrite N3, !orb_true_r. reflexivity.
    + pose proof (eager_le E M' model (s_facts S) BL' HF0 Hmaps' Hgsh' Hkind' Hblob') as He.
      pose proof (A_bytes_allowA E M' Hanz) as Hb. unfold AM. rewrite Hb0', A_bytes_app, Hlim. cbn [M' with_maps sm_maps sm_allow] in He, Hb. lia.
  - apply HFo; [|exact Hgtop]. unfold gsz, mk'. cbn [fst snd]. rewrite HT', Hbmk. pose proof (alloc_top_lo _ (proj1 Hspok)). unfold gsz, MARKB in *. lia.
  - intros w Hw Ho Hno Hnb. apply (Hzr w Hw Ho Hno). intros (p & Hp & Hpw). apply Hnb. rewrite Hb0'. exists p. split; [right; exact Hp | exact Hpw].
Qed.

(* [comment removed for export] *)
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Type"] Lemma remove_nth_incl : forall {A} k (l : list A) x, In x (remove_nth k l) -> In x l.
Proof. LiaFast.lf_pins LiaFast.u0. intros A k l x H. exact (remove_nth_In k l x H). Qed.
#[using="Type"] Lemma In_remove_nth_or : forall {A} k (l : list A) x e, nth_error l k = Some e -> In x l -> x = e \/ In x (remove_nth k l).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A k. induction k as [|k IH]; intros l x e Hk Hx; destruct l as [|y r]; try discriminate.
  - cbn in Hk. injection Hk as ->. destruct Hx as [->|Hx]; [left; reflexivity | right; exact Hx].
  - cbn in Hk. destruct Hx as [->|Hx]; [right; left; reflexivity|]. destruct (IH r x e Hk Hx) as [H|H]; [left; exact H | right; right; exact H].
Qed.
#[using="Type"] Lemma A_bytes_remove : forall A k, A_wf A -> A_bytes (remove_nth k A) <= A_bytes A.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A k. revert A. induction k as [|k IH]; intros A Hw; destruct A as [|iv r]; cbn [remove_nth A_bytes]; try lia.
  - unfold A_wf in Hw. inversion Hw as [|? ? (H1 & _) _]; subst. lia.
  - unfold A_wf in Hw. inversion Hw as [|? ? _ Hr]; subst. specialize (IH r Hr). lia.
Qed.
#[using="Type"] Lemma remove_nth_map' : forall {A B} (f : A -> B) k l, List.map f (remove_nth k l) = remove_nth k (List.map f l).
Proof. LiaFast.lf_pins LiaFast.u0. intros A B f k. induction k as [|k IH]; intros [|x r]; cbn [remove_nth List.map]; try reflexivity. f_equal. apply IH. Qed.

#[using="Hsegb"] Theorem den_unallow : forall E S M ms model k e,
  DEN segs LIMIT model0 mem0 E S M ms model -> nth_error (sm_allow M) k = Some e ->
  In (allow1 E e) (blobA (blob_of model0)) ->
  (forall R, In R (s_rgs S) -> forall i, 0 <= i < rsz E R ->
     Hof E (with_allow M (remove_nth k (sm_allow M))) model (Z_to_bv 64 (uE E (rg_base R) + i)) = false) ->
  (forall w, own_pt E M w -> Hof E (with_allow M (remove_nth k (sm_allow M))) model (Z_to_bv 64 w) = false) ->
  DEN segs LIMIT model0 mem0 E S (with_allow M (remove_nth k (sm_allow M))) ms model.
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E S M ms model k e Hd Hk Hin Hvis Hvo.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := with_allow M (remove_nth k (sm_allow M))) in *.
  set (H := Hof E M model) in *. set (H' := Hof E M' model) in *.
  assert (HA' : allowA E M' = remove_nth k (allowA E M)) by (unfold allowA; cbn [M' with_allow sm_allow]; apply remove_nth_map').
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')).
  { cbn [M' with_allow sm_allow]. apply Forall_forall. intros p Hp. rewrite Forall_forall in Hanz. exact (Hanz p (remove_nth_incl k _ p Hp)). }
  constructor; try assumption.
  - intros E'' Ha. destruct (Hsd E'' Ha) as (Hpc & Hsv & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0. cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr] in *.
    split; [exact Hpc|]. split; [exact Hsv|]. split; [exact Hrv|]. split; [exact HR|]. split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. pose proof (HG R HR') as HRok.
    apply (rg_ok_mem_eq segs E'' (mrestrict H (ms_mem ms))); [exact HRok|].
    intros i Hi. pose proof (rg_ok_visible segs H (ms_mem ms) E'' R Hhoff HRok i Hi) as Hv.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
    assert (HbE : uE E'' (rg_base R) = uE E (rg_base R)) by (unfold uE; rewrite (lden_agree_wf _ E E'' _ Hb1 Ha); reflexivity).
    assert (HsE : rsz E'' R = rsz E R) by (unfold rsz, uE; rewrite (lden_agree_wf _ E E'' _ Hb2 Ha); reflexivity).
    rewrite HbE in Hv |- *. rewrite HsE in Hi. unfold mrestrict. rewrite Hv. fold H'. rewrite (Hvis R HR' i Hi). reflexivity.
  - unfold sm_wf in *. cbn [M' with_allow sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own].
    apply andb_prop in Hwf as [Hwf W8]. apply andb_prop in Hwf as [Hwf W7]. apply andb_prop in Hwf as [Hwf W6]. apply andb_prop in Hwf as [Hwf W5].
    apply andb_prop in Hwf as [Hwf W4]. apply andb_prop in Hwf as [Hwf W3]. apply andb_prop in Hwf as [W1 W2].
    rewrite W1, W3, W4, W5, W6, W7, W8.
    assert (W2' : forallb (fun g => lwf (s_next S) (fst g)) (remove_nth k (sm_allow M)) = true).
    { apply forallb_forall. intros p Hp. rewrite forallb_forall in W2. exact (W2 p (remove_nth_incl k _ p Hp)). }
    rewrite W2'. reflexivity.
  - exact (A_wf_allowA E M' Hanz').
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; try assumption.
    + intros p Hp. specialize (N3 p Hp). unfold AM in *. rewrite HA'. unfold page_allowedb in *. rewrite existsb_app in *.
      apply orb_prop in N3 as [N3|N3]; [|rewrite N3, orb_true_r; reflexivity].
      apply existsb_exists in N3 as (iv & Hiv & Hc).
      assert (Hke : nth_error (allowA E M) k = Some (allow1 E e)) by (unfold allowA; rewrite nth_error_map, Hk; reflexivity).
      destruct (In_remove_nth_or k _ iv _ Hke Hiv) as [->|Hr].
      * apply orb_true_iff. right. apply existsb_exists. exists (allow1 E e). split; [exact Hin | exact Hc].
      * apply orb_true_iff. left. apply existsb_exists. exists iv. split; [exact Hr | exact Hc].
    + unfold AM in *. rewrite A_bytes_app in *. rewrite HA'. pose proof (A_bytes_remove (allowA E M) k Hawf). lia.
  - unfold H', Hof. apply (hoff_of segs _ _ (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) Hsegb Hres Hlzm Hmres).
  - intros q Hq w Hw. cbn [M' with_allow sm_own] in Hq. destruct (Hown q Hq w Hw) as [_ Hm]. split; [|exact Hm].
    apply Hvo. exists q. split; [exact Hq | exact Hw].
Qed.

End Blob.

(* [comment removed for export] *)
Definition exact_al (fs : list fact) (g : lin * lin * gkind) (e : lin * Z) : bool :=
  match gsz_c g with
  | Some n => lin_eqb (lscale 8 (laddc (fst e) (- SH_OFF))) (fst (fst g)) &&& Z.eqb (snd e) (n / 8) &&&
              Z.leb SH_OFF (fst (irange fs (fst e))) &&& Z.leb (snd (irange fs (fst e))) (SH_OFF + 17592186044416)
  | None => false
  end.
Lemma exact_al_sound : forall E fs g e, Forall (fact_ok E) fs -> gshape_ok E g -> exact_al fs g e = true ->
  uE E (fst e) = SHz (uE E (fst (fst g))) /\ snd e = gsz E g / 8 /\ SHz (uE E (fst (fst g)) + gsz E g) = uE E (fst e) + snd e /\
  allow1 E e = blobA1 (gden E g).
Proof.
  intros E fs g e HF Hg H. unfold exact_al in H. destruct (gsz_c g) as [n|] eqn:Hn; [|discriminate].
  destruct (lin_eqb _ _) eqn:H1; [|discriminate]. destruct (Z.eqb (snd e) (n / 8)) eqn:H2; [|discriminate].
  destruct (Z.leb SH_OFF _) eqn:H3; [|discriminate]. apply Z.leb_le in H3, H. apply Z.eqb_eq in H2. apply lin_eqb_eq in H1.
  pose proof (irange_sound E fs (fst e) HF) as Hr. fold (uE E (fst e)) in Hr.
  pose proof (gsz_const E g n Hn) as Hgn. destruct Hg as (G1 & G2 & G3 & G4 & G5).
  assert (Hb : uE E (fst (fst g)) = 8 * (uE E (fst e) - SH_OFF)).
  { rewrite <- H1. unfold uE. rewrite lden_lscale, lden_laddc. rewrite (fg64 (bv_unsigned (lden E (fst e)) + - SH_OFF)) by (unfold uE, SH_OFF, two64 in *; lia).
    apply fg64. unfold uE, SH_OFF, two64 in *. lia. }
  assert (Hs : SHz (uE E (fst (fst g))) = uE E (fst e)).
  { unfold SHz. rewrite Hb. replace (8 * (uE E (fst e) - SH_OFF)) with ((uE E (fst e) - SH_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hs2 : SHz (uE E (fst (fst g)) + gsz E g) = uE E (fst e) + snd e).
  { unfold SHz. rewrite Hb, H2, Hgn. rewrite Hgn in G2.
    assert (Hn8 : n = (n / 8) * 8) by (pose proof (Z.div_mod n 4096 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_divide n 8 ltac:(lia)); lia).
    rewrite Hn8 at 1. replace (8 * (uE E (fst e) - SH_OFF) + n / 8 * 8) with ((uE E (fst e) - SH_OFF + n / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split; [symmetry; exact Hs|]. split; [rewrite Hgn; exact H2|]. split; [exact Hs2|].
  unfold allow1, blobA1, gden. cbn [fst snd]. fold (uE E (fst (fst g))). fold (uE E (snd (fst g))). fold (gsz E g). rewrite Hs, Hs2. reflexivity.
Qed.

Definition pseudo (q : lin * lin) : region := RG (fst q) (snd q) RZ TEmpty.
Definition vis_b (fs : list fact) (al : list (lin * Z)) (R : region) : bool :=
  let n := snd (irange fs (rg_size R)) in
  Z.eqb n 0 ||| sep_noshadow_b fs R ||| allow_cov fs (rg_base R) n al.
Definition dead_b (fs : list fact) (g : lin * lin * gkind) (n : Z) (e : lin * Z) (R : region) : bool :=
  let m := snd (irange fs (rg_size R)) in
  Z.ltb 0 m &&& (contained_b fs (rg_base R) m (fst (fst g)) n ||| contained_b fs (rg_base R) m (fst e) (snd e)).
Fixpoint find_exact (fs : list fact) (g : lin * lin * gkind) (al : list (lin * Z)) (k : nat) : option nat :=
  match al with [] => None | e :: r => if exact_al fs g e then Some k else find_exact fs g r (Datatypes.S k) end.
Lemma find_exact_spec : forall fs g al k0 k, find_exact fs g al k0 = Some k ->
  exists e, nth_error al (k - k0) = Some e /\ exact_al fs g e = true /\ (k0 <= k)%nat.
Proof.
  intros fs g al. induction al as [|e r IH]; intros k0 k H; [discriminate|]. cbn [find_exact] in H.
  destruct (exact_al fs g e) eqn:He.
  - injection H as <-. exists e. rewrite Nat.sub_diag. repeat split; auto.
  - destruct (IH _ _ H) as (e' & H1 & H2 & H3). exists e'. replace (k - k0)%nat with (Datatypes.S (k - Datatypes.S k0)) by lia.
    repeat split; auto. lia.
Qed.

Definition blobadd_ref (LIMIT : Z) (res : list (word * word)) (S : sst) (M : smodel) (i : nat) : option (sst * smodel) :=
  match absorb i (sm_maps M) with
  | Some (g, gs') =>
      match gsz_c g, find_exact (s_facts S) g (sm_allow M) O with
      | Some n, Some k =>
          match nth_error (sm_allow M) k with
          | Some e =>
              let fs := s_facts S in let al' := remove_nth k (sm_allow M) in
              if absorb_ok LIMIT S M i &&& shadow_ok M &&&
                 match is_const (fst (fst g)) with None => true | Some _ => false end &&&
                 forallb (fun R => dead_b fs g n e R ||| vis_b fs al' R) (s_rgs S) &&&
                 forallb (fun q => let Rq := pseudo q in
                            Z.eqb (snd (irange fs (snd q))) 0 |||       (* [comment removed for export] *)
                            Z.leb (snd (irange fs (fst q)) + snd (irange fs (snd q))) two64 &&&
                            (sep_app2_b fs (sm_maps M) i (sm_sp M) (fst (fst g)) n Rq ||| sep_res_b res Rq) &&&
                            sep_pc_b fs (sm_maps M) i (sm_sp M) Rq &&& vis_b fs al' Rq) (sm_own M)
              then Some (drop_post S (dead_b fs g n e), with_allow (absorb_M M i) al') else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Lemma blobadd_ref_parts : forall LIMIT res S M i S' M', blobadd_ref LIMIT res S M i = Some (S', M') -> s_next S' = s_next S /\ sm_frz M' = sm_frz M.
Proof.
  intros LIMIT res S M i S' M' H. unfold blobadd_ref in H. destruct (absorb i (sm_maps M)) as [[g gs']|] eqn:Hab; [|discriminate].
  destruct (gsz_c g); [|discriminate]. destruct (find_exact _ _ _ _) as [k|]; [|discriminate]. destruct (nth_error (sm_allow M) k); [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection H as <- <-.
  split; [reflexivity|]. unfold absorb_M. rewrite Hab. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma existsb_splitB : forall {A} (f p : A -> bool) l,
  (if existsb f (List.filter p l) then true else existsb f (List.filter (fun x => negb (p x)) l)) = existsb f l.
Proof.
  intros A f p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter existsb]. destruct (p x) eqn:Hp; cbn [negb existsb].
  - destruct (f x); [reflexivity | exact IH].
  - destruct (existsb f (List.filter p l)) eqn:H1.
    + rewrite <- IH. destruct (f x); reflexivity.
    + destruct (f x); [reflexivity | exact IH].
Qed.
Definition al_candB (a : lin) (p : lin * Z) : bool := match lin_off a (fst p) with Some _ => true | None => false end.
Definition allow_covB (fs : list fact) (a : lin) (n : Z) (al : list (lin * Z)) : bool :=
  let f := fun p : lin * Z => contained_b fs a n (fst p) (snd p) &&& Z.leb (snd (irange fs (fst p)) + snd p) two64 &&& Z.ltb 0 n in
  if existsb_lz f (List.filter (al_candB a) al) then true else existsb_lz f (List.filter (fun p => negb (al_candB a p)) al).
Lemma allow_covB_eq : forall fs a n al, allow_covB fs a n al = allow_cov fs a n al.
Proof. intros fs a n al. unfold allow_covB, allow_cov. cbv zeta. rewrite !existsb_lz_eq. apply existsb_splitB. Qed.
Definition vis_bB (fs : list fact) (al : list (lin * Z)) (R : region) : bool :=
  let n := snd (irange fs (rg_size R)) in
  Z.eqb n 0 ||| sep_noshadow_b fs R ||| allow_covB fs (rg_base R) n al.
Lemma vis_bB_eq : forall fs al R, vis_bB fs al R = vis_b fs al R.
Proof. intros fs al R. unfold vis_bB, vis_b. cbv zeta. rewrite allow_covB_eq. reflexivity. Qed.
Definition sep_app2_bS (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp : lin) (ns : bool) (R : region) : bool :=
  if (if ns then sep_shadow_b fs R else false) then true
  else if cont1 fs gs j R then true else if band_few2 fs sp R then true
  else if sep_grant_acc fs gs j O R then true else sep_band_b fs sp R.
Lemma sep_app2_bS_eq : forall fs gs j sp a n R, sep_app2_bS fs gs j sp (sep_noshadow_b fs (RGz a n RZ TEmpty)) R = sep_app2_b fs gs j sp a n R.
Proof.
  intros fs gs j sp a n R. unfold sep_app2_bS, sep_app2_b.
  destruct (sep_noshadow_b fs (RGz a n RZ TEmpty)), (sep_shadow_b fs R), (cont1 fs gs j R), (band_few2 fs sp R), (sep_grant_acc fs gs j 0 R), (sep_band_b fs sp R); reflexivity.
Qed.
Fixpoint contp1H_acc (fs : list fact) (gs : list (lin * lin * gkind)) (pbs : list (option lin)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs, pbs with
  | g :: r, pbo :: pr => (negb (is_mark g) &&& negb (Nat.eqb i j) &&&
               match pbo with
               | Some pb => cand_b b (laddc pb SH_OFF) &&& contained_b fs b z (laddc pb SH_OFF) (gsz_lo fs g / 8)
               | None => false
               end) ||| contp1H_acc fs r pr j (Datatypes.S i) b z
  | _, _ => false
  end.
Definition srl3s (fs : list fact) (gs : list (lin * lin * gkind)) : list (option lin) := List.map (fun g : lin * lin * gkind => srl_lin fs 3 (fst (fst g))) gs.
Lemma contp1H_acc_eq : forall fs gs j i b z, contp1H_acc fs gs (srl3s fs gs) j i b z = contp1_acc fs gs j i b z.
Proof.
  intros fs gs j. unfold srl3s. induction gs as [|g r IH]; intros i b z; [reflexivity|]. cbn [List.map contp1H_acc contp1_acc]. rewrite IH. reflexivity.
Qed.
Definition sep_pc_bH (fs : list fact) (gs : list (lin * lin * gkind)) (pbs : list (option lin)) (j : nat) (sp : lin) (R : region) : bool :=
  if (let z := snd (irange fs (rg_size R)) in if Z.leb 1 z then contp1H_acc fs gs pbs j O (rg_base R) z else false) then true
  else if sep_noshadow_b fs R then true
  else if sep_pgrant_acc fs gs j O R then true else sep_pband_b fs sp R.
Lemma sep_pc_bH_eq : forall fs gs j sp R, sep_pc_bH fs gs (srl3s fs gs) j sp R = sep_pc_b fs gs j sp R.
Proof. intros fs gs j sp R. unfold sep_pc_bH, sep_pc_b, contp1. cbv zeta. rewrite contp1H_acc_eq. reflexivity. Qed.
Fixpoint filt_nl {X} (dl : list bool) (l : list X) : list X :=
  match dl, l with d :: dr, x :: r => if d then filt_nl dr r else x :: filt_nl dr r | _, _ => [] end.
Lemma filt_nl_map : forall {X} (f : X -> bool) l, filt_nl (List.map f l) l = List.filter (fun x => negb (f x)) l.
Proof. intros X f l. induction l as [|x r IH]; [reflexivity|]. cbn [List.map filt_nl List.filter]. rewrite IH. destruct (f x); reflexivity. Qed.
Fixpoint all_dv {X} (v : X -> bool) (dl : list bool) (l : list X) : bool :=
  match dl, l with d :: dr, x :: r => ((if d then true else v x) && all_dv v dr r)%bool | _, _ => true end.
Lemma all_dv_map : forall {X} (f v : X -> bool) l, all_dv v (List.map f l) l = forallb (fun x => f x ||| v x) l.
Proof. intros X f v l. induction l as [|x r IH]; [reflexivity|]. cbn [List.map all_dv forallb]. rewrite IH. reflexivity. Qed.
Lemma forallb_extB : forall {X} (f g : X -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros X f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.

Definition blobadd (LIMIT : Z) (res : list (word * word)) (S : sst) (M : smodel) (i : nat) : option (sst * smodel) :=
  match absorb i (sm_maps M) with
  | Some (g, gs') =>
      match gsz_c g, find_exact (s_facts S) g (sm_allow M) O with
      | Some n, Some k =>
          match nth_error (sm_allow M) k with
          | Some e =>
              let fs := s_facts S in let al' := remove_nth k (sm_allow M) in
              if absorb_ok LIMIT S M i &&& shadow_ok M &&&
                 match is_const (fst (fst g)) with None => true | Some _ => false end
              then
                let dl := List.map (dead_b fs g n e) (s_rgs S) in
                let ns := sep_noshadow_b fs (RGz (fst (fst g)) n RZ TEmpty) in
                let pbs := srl3s fs (sm_maps M) in
                if all_dv (vis_bB fs al') dl (s_rgs S) &&&
                   forallb (fun q => let Rq := pseudo q in
                              Z.eqb (snd (irange fs (snd q))) 0 |||
                              Z.leb (snd (irange fs (fst q)) + snd (irange fs (snd q))) two64 &&&
                              (sep_res_b res Rq ||| sep_app2_bS fs (sm_maps M) i (sm_sp M) ns Rq) &&&
                              sep_pc_bH fs (sm_maps M) pbs i (sm_sp M) Rq &&& vis_bB fs al' Rq) (sm_own M)
                then Some (SST (s_pc S) (s_regs S) (filt_nl dl (s_rgs S)) (s_facts S) (s_next S) (s_resv S), with_allow (absorb_M M i) al')
                else None
              else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.
Lemma blobadd_eq : forall LIMIT res S M i, blobadd LIMIT res S M i = blobadd_ref LIMIT res S M i.
Proof.
  intros LIMIT res S M i. unfold blobadd, blobadd_ref.
  destruct (absorb i (sm_maps M)) as [[g gs']|]; [|reflexivity].
  destruct (gsz_c g) as [n|]; [|reflexivity]. destruct (find_exact (s_facts S) g (sm_allow M) 0) as [k|]; [|reflexivity].
  destruct (nth_error (sm_allow M) k) as [e|]; [|reflexivity]. cbv zeta.
  set (fs := s_facts S). set (al' := remove_nth k (sm_allow M)).
  rewrite all_dv_map, filt_nl_map.
  rewrite (forallb_extB (fun R => dead_b fs g n e R ||| vis_bB fs al' R) (fun R => dead_b fs g n e R ||| vis_b fs al' R))
    by (intros R; rewrite vis_bB_eq; reflexivity).
  rewrite (forallb_extB
             (fun q => Z.eqb (snd (irange fs (snd q))) 0 |||
                       Z.leb (snd (irange fs (fst q)) + snd (irange fs (snd q))) two64 &&&
                       (sep_res_b res (pseudo q) ||| sep_app2_bS fs (sm_maps M) i (sm_sp M) (sep_noshadow_b fs (RGz (fst (fst g)) n RZ TEmpty)) (pseudo q)) &&&
                       sep_pc_bH fs (sm_maps M) (srl3s fs (sm_maps M)) i (sm_sp M) (pseudo q) &&& vis_bB fs al' (pseudo q))
             (fun q => Z.eqb (snd (irange fs (snd q))) 0 |||
                       Z.leb (snd (irange fs (fst q)) + snd (irange fs (snd q))) two64 &&&
                       (sep_app2_b fs (sm_maps M) i (sm_sp M) (fst (fst g)) n (pseudo q) ||| sep_res_b res (pseudo q)) &&&
                       sep_pc_b fs (sm_maps M) i (sm_sp M) (pseudo q) &&& vis_b fs al' (pseudo q)))
    by (intros q; rewrite sep_app2_bS_eq, sep_pc_bH_eq, vis_bB_eq;
        destruct (sep_res_b res (pseudo q)), (sep_app2_b fs (sm_maps M) i (sm_sp M) (fst (fst g)) n (pseudo q)); reflexivity).
  unfold drop_post. fold fs.
  destruct (absorb_ok LIMIT S M i); [|reflexivity]. destruct (shadow_ok M); [|reflexivity]. destruct (is_const (fst (fst g))); reflexivity.
Qed.
Lemma blobadd_parts : forall LIMIT res S M i S' M', blobadd LIMIT res S M i = Some (S', M') -> s_next S' = s_next S /\ sm_frz M' = sm_frz M.
Proof. intros LIMIT res S M i S' M' H. rewrite blobadd_eq in H. exact (blobadd_ref_parts LIMIT res S M i S' M' H). Qed.

(* [comment removed for export] *)
Lemma vis_keep : forall E fs (M : smodel) (model : Model) g e k R w,
  Forall (fact_ok E) fs -> gshape_ok E g -> allow1 E e = blobA1 (gden E g) -> nth_error (sm_allow M) k = Some e ->
  vis_b fs (remove_nth k (sm_allow M)) R = true ->
  uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> 0 <= w < two64 ->
  Hof E M model (Z_to_bv 64 w) = false ->
  Hof E (with_allow M (remove_nth k (sm_allow M))) model (Z_to_bv 64 w) = false.
Proof.
  intros E fs M model g e k R w HF Hg Hal Hk Hv Hw Hw64 Hh.
  unfold Hof in *. unfold allowA in *. cbn [with_allow sm_allow].
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (uE E (rg_size R)) in Rs. change (uE E (rg_size R)) with (rsz E R) in Rs.
  unfold vis_b in Hv. destruct (Z.eqb _ 0) eqn:H0; [apply Z.eqb_eq in H0; lia|].
  destruct (sep_noshadow_b fs R) eqn:Hns.
  - pose proof (noshadow_sound E fs R HF Hns w Hw) as Hnsw.
    unfold mkH in *. destruct (page_in_ranges (page_base (Z_to_bv 64 w)) (m_vm_lazy model)); [|reflexivity]. cbn [andb] in *.
    apply negb_false_iff in Hh. apply negb_false_iff. unfold page_allowedb in *. apply existsb_exists in Hh as (iv & Hiv & Hc).
    assert (Hke : nth_error (List.map (allow1 E) (sm_allow M)) k = Some (allow1 E e)) by (rewrite nth_error_map, Hk; reflexivity).
    destruct (In_remove_nth_or k _ iv _ Hke Hiv) as [->|Hr].
    + exfalso. rewrite Hal in Hc. unfold blobA1, gden in Hc. cbn [fst snd] in Hc. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
      destruct (pb_bounds (Z_to_bv 64 w)) as (P1 & P2). rewrite (fg64 w Hw64) in P1. unfold page_size in C2.
      destruct Hg as (G1 & G2 & G3 & G4 & G5). fold (uE E (fst (fst g))) in C1, C2. fold (uE E (snd (fst g))) in C2. fold (gsz E g) in C2.
      unfold SHz in C1, C2.
      pose proof (Z.div_mod (SH_OFF + uE E (fst (fst g)) / 8) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SH_OFF + uE E (fst (fst g)) / 8) 4096 ltac:(lia)) as D2.
      pose proof (Z.div_mod (SH_OFF + (uE E (fst (fst g)) + gsz E g) / 8 + 4095) 4096 ltac:(lia)) as D3.
      pose proof (Z.mod_pos_bound (SH_OFF + (uE E (fst (fst g)) + gsz E g) / 8 + 4095) 4096 ltac:(lia)) as D4.
      assert (Q1 : 0 <= uE E (fst (fst g)) / 8) by (apply Z.div_pos; lia).
      assert (Q2 : (uE E (fst (fst g)) + gsz E g) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
      unfold in_shadow, SH_LO, SH_HI in Hnsw. unfold SH_OFF in *. apply andb_false_iff in Hnsw as [Hn1|Hn1]; [apply Z.leb_gt in Hn1 | apply Z.ltb_ge in Hn1].
      * assert (2147446784 <= (2147450880 + uE E (fst (fst g)) / 8) / 4096 * 4096) by (pose proof (Z.div_le_mono 2147450880 (2147450880 + uE E (fst (fst g)) / 8) 4096 ltac:(lia) ltac:(lia)) as X; change (2147450880 / 4096) with 524280 in X; lia). lia.
      * assert ((2147450880 + (uE E (fst (fst g)) + gsz E g) / 8 + 4095) / 4096 * 4096 <= 17594333495296).
        { pose proof (Z.div_le_mono (2147450880 + (uE E (fst (fst g)) + gsz E g) / 8 + 4095) (17594333495296 + 4095) 4096 ltac:(lia) ltac:(lia)) as X.
          change ((17594333495296 + 4095) / 4096) with 4295491576 in X. lia. }
        lia.
    + apply existsb_exists. exists iv. rewrite remove_nth_map'. split; [exact Hr | exact Hc].
  - apply mkH_allowed. apply (allow_cov_sound E fs (rg_base R) _ _ HF Hv w); [lia | exact Hw64].
Qed.

Section BlobAdd.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem den_blob_add_ref : forall E S M ms model i S' M',
  DEN segs LIMIT model0 mem0 E S M ms model -> blobadd_ref LIMIT (segments_reserved segs) S M i = Some (S', M') ->
  DEN segs LIMIT (with_blob (gden E (absorb_g M i) :: blob_of model0) model0) mem0 E S' M' ms model.
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E S M ms model i S' M' Hd Hb. unfold blobadd_ref in Hb.
  destruct (absorb i (sm_maps M)) as [[g gs']|] eqn:Hab; [|discriminate].
  destruct (gsz_c g) as [n|] eqn:Hn; [|discriminate].
  destruct (find_exact (s_facts S) g (sm_allow M) O) as [k|] eqn:Hfk; [|discriminate].
  destruct (nth_error (sm_allow M) k) as [e|] eqn:Hk; [|discriminate].
  destruct (absorb_ok LIMIT S M i) eqn:Hok; [|discriminate]. destruct (shadow_ok M) eqn:Hsh; [|discriminate].
  destruct (is_const (fst (fst g))) eqn:Hnc; [discriminate|].
  destruct (forallb _ (s_rgs S)) eqn:Hrg; [|discriminate]. destruct (forallb _ (sm_own M)) eqn:Hown; [|discriminate].
  injection Hb as <- <-.
  destruct (find_exact_spec _ _ _ _ _ Hfk) as (e' & He' & Hex & _). rewrite Nat.sub_0_r, Hk in He'. injection He' as <-.
  destruct (absorb_spec i _ g gs' Hab) as (pre & mk & r & Hgs & Hgs' & P1 & P2 & P3 & P4 & P5 & _).
  assert (Hgi : nth_error (sm_maps M) i = Some g).
  { rewrite Hgs, <- P5. clear. induction pre as [|x pre IH]; [reflexivity | exact IH]. }
  assert (Hag : absorb_g M i = g) by (unfold absorb_g; rewrite Hab; reflexivity). rewrite Hag.
  pose proof (den_blob_absorb segs LIMIT model0 mem0 E S M ms model i Hd Hok) as Hd1. rewrite Hag in Hd1.
  set (m0' := with_blob (gden E g :: blob_of model0) model0) in *.
  set (M1 := absorb_M M i) in *.
  assert (HM1a : sm_allow M1 = sm_allow M) by (unfold M1, absorb_M; rewrite Hab; reflexivity).
  assert (HM1o : sm_own M1 = sm_own M) by (unfold M1, absorb_M; rewrite Hab; reflexivity).
  assert (HM1z : sm_zr M1 = sm_zr M) by (unfold M1, absorb_M; rewrite Hab; reflexivity).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hownk Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  assert (Hing : In g (sm_maps M)) by exact (nth_error_In _ _ Hgi).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. pose proof (Hgsh0 g Hing) as Hgg. destruct (Hgg) as (G1 & G2 & G3 & G4 & G5).
  pose proof (gsz_const E g n Hn) as Hgn.
  destruct (exact_al_sound E (s_facts S) g e HF0 Hgg Hex) as (Hue & Hse & Hs2 & Hal1).
  assert (Hb0' : blob_of m0' = gden E g :: blob_of model0) by apply blob_of_with_blob.
  set (f := dead_b (s_facts S) g n e) in *.
  (* [comment removed for export] *)
  assert (Hdead : forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
            (uE E (fst (fst g)) <= w < uE E (fst (fst g)) + n) \/ (uE E (fst e) <= w < uE E (fst e) + snd e)).
  { intros R HR HfR w Hw. unfold f, dead_b in HfR. destruct (Z.ltb 0 _) eqn:Hm; [|discriminate]. apply Z.ltb_lt in Hm.
    pose proof (irange_sound E (s_facts S) (rg_size R) HF0) as Rs. fold (uE E (rg_size R)) in Rs. change (uE E (rg_size R)) with (rsz E R) in Rs.
    destruct (contained_b _ (rg_base R) _ (fst (fst g)) n) eqn:Hc1.
    - left. destruct (contained_sound E _ _ _ _ _ HF0 Hc1 Hm ltac:(unfold two64; lia)) as [C1 C2]. lia.
    - right. assert (Hse0 : 0 <= snd e) by (rewrite Hse; apply Z.div_pos; lia).
      assert (Hue0 : uE E (fst e) + snd e <= two64).
      { rewrite <- Hs2. unfold SHz, SH_OFF, two64. assert ((uE E (fst (fst g)) + gsz E g) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. }
      destruct (contained_sound E _ _ _ _ _ HF0 HfR Hm Hue0) as [C1 C2]. lia. }
  assert (Hd2 : DEN segs LIMIT m0' mem0 E (drop_post S f) M1 ms model).
  { apply den_drop_g; [exact Hd1 | |].
    - intros R HR HfR w Hw Hz. destruct (Hdead R HR HfR w Hw) as [Ha|Hs].
      + exfalso. rewrite HM1z in Hz. pose proof (Hzrsh w Hz) as Hsw.
        rewrite (grant_noshadow E _ M model g w Hmaps Hpd Hgsh Hsh Hing Hnc) in Hsw; [discriminate|].
        unfold gden. rewrite in_iv_word. fold (uE E (fst (fst g))). fold (uE E (snd (fst g))). fold (gsz E g).
        apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
      + right. rewrite Hb0'. exists (gden E g). split; [left; reflexivity|]. unfold gden. cbn [fst snd].
        fold (uE E (fst (fst g))). fold (uE E (snd (fst g))). fold (gsz E g). rewrite Hs2, <- Hue. exact Hs.
    - intros R HR HfR w (q & Hq & Hwq) Hin. rewrite HM1o in Hq. rewrite forallb_forall in Hown. specialize (Hown q Hq). cbn zeta in Hown.
      destruct (Z.eqb (snd (irange (s_facts S) (snd q))) 0) eqn:Hz0.
      { exfalso. apply Z.eqb_eq in Hz0. pose proof (irange_sound E (s_facts S) (snd q) HF0) as Rz. fold (uE E (snd q)) in Rz. lia. }
      destruct (Z.leb _ two64) eqn:Hq64; [|discriminate]. apply Z.leb_le in Hq64.
      destruct (sep_app2_b _ _ _ _ _ _ _ ||| sep_res_b _ _) eqn:Hsa; [|discriminate]. destruct (sep_pc_b _ _ _ _ _) eqn:Hsp2; [|discriminate].
      pose proof (irange_sound E (s_facts S) (fst q) HF0) as Rq1. pose proof (irange_sound E (s_facts S) (snd q) HF0) as Rq2.
      fold (uE E (fst q)) in Rq1. fold (uE E (snd q)) in Rq2.
      assert (Hw64 : 0 <= w < two64) by (pose proof (uE_range E (fst q)); lia).
      rewrite (fg64 w Hw64) in Hin.
      assert (Hrq : rsz E (pseudo q) = uE E (snd q)) by reflexivity.
      assert (Hwq' : uE E (rg_base (pseudo q)) <= w < uE E (rg_base (pseudo q)) + rsz E (pseudo q)) by (rewrite Hrq; exact Hwq).
      destruct (Hdead R HR HfR w Hin) as [Ha|Hs].
      + revert Ha. destruct (sep_app2_b _ _ _ _ _ _ _) eqn:Hs1.
        * apply (sep_app2_sound E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok) i g (fst (fst g)) n (pseudo q) Hgi P2
                   ltac:(lia) ltac:(lia) ltac:(unfold two64 in *; lia) ltac:(rewrite Hrq; pose proof (uE_range E (snd q)); lia) ltac:(rewrite Hrq; cbn [pseudo rg_base]; lia) Hs1 w Hwq').
        * rewrite <- Hres in Hsa.
          apply (sep_res_sound E (sm_maps M) model _ Hmaps Hgsh Hmres i g (fst (fst g)) n (pseudo q) Hgi P2 ltac:(lia) ltac:(lia) Hsa w Hwq').
      + revert Hs. rewrite Hue, Hse, Hgn. unfold SHz. intros Hs.
        apply (sep_pc_sound E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok) i g (fst (fst g)) n (pseudo q) Hgi P2
                 ltac:(lia) ltac:(lia)
                 ltac:(pose proof (Z.div_mod (uE E (fst (fst g))) 4096 ltac:(lia)); pose proof (Z.mod_divide (uE E (fst (fst g))) 8 ltac:(lia)); apply Z.mod_divide; [lia|]; exists (uE E (fst (fst g)) / 4096 * 512); lia)
                 ltac:(rewrite Hgn in G2; apply Z.mod_divide; [lia|]; exists (n / 4096 * 512); pose proof (Z.div_mod n 4096 ltac:(lia)); lia)
                 ltac:(lia)
                 ltac:(unfold SH_LO, SH_OFF; assert (0 <= uE E (fst (fst g)) / 8) by (apply Z.div_pos; lia); lia)
                 ltac:(unfold SH_HI, SH_OFF; assert (uE E (fst (fst g)) / 8 + n / 8 <= 17592186044416) by
                         (pose proof (Z.div_mod (uE E (fst (fst g))) 8 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (uE E (fst (fst g))) 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia); lia)
                 ltac:(rewrite Hrq; pose proof (uE_range E (snd q)); lia) ltac:(rewrite Hrq; cbn [pseudo rg_base]; lia) Hsp2 w Hwq'). lia. }
  (* [comment removed for export] *)
  pose proof (den_unallow segs LIMIT m0' mem0 Hsegb E (drop_post S f) M1 ms model k e Hd2 ltac:(rewrite HM1a; exact Hk)
                ltac:(rewrite Hb0'; left; symmetry; exact Hal1)) as Hd3.
  rewrite HM1a in Hd3. apply Hd3.
  - intros R HR j Hj. cbn [drop_post s_rgs] in HR. apply filter_In in HR as [HR HfR]. apply negb_true_iff in HfR.
    rewrite forallb_forall in Hrg. specialize (Hrg R HR). fold f in Hrg. rewrite HfR in Hrg.
    rewrite Forall_forall in HG0. pose proof (HG0 R HR) as HRok. pose proof (rg_ok_visible segs _ (ms_mem ms) E R Hhoff HRok j Hj) as Hv.
    destruct HRok as (R1 & R2 & _). fold (uE E (rg_base R)) in R2.
    assert (HofM1 : forall w, Hof E (with_allow M1 (remove_nth k (sm_allow M))) model w = Hof E (with_allow M (remove_nth k (sm_allow M))) model w) by reflexivity.
    rewrite HofM1.
    apply (vis_keep E (s_facts S) M model g e k R (uE E (rg_base R) + j) HF0 Hgg Hal1 Hk Hrg ltac:(lia) ltac:(pose proof (uE_range E (rg_base R)); lia) Hv).
  - intros w (q & Hq & Hwq). rewrite HM1o in Hq. pose proof (Hownk q Hq w Hwq) as [Hv _].
    rewrite forallb_forall in Hown. specialize (Hown q Hq). cbn zeta in Hown.
    destruct (Z.eqb (snd (irange (s_facts S) (snd q))) 0) eqn:Hz0.
    { exfalso. apply Z.eqb_eq in Hz0. pose proof (irange_sound E (s_facts S) (snd q) HF0) as Rz. fold (uE E (snd q)) in Rz. lia. }
    destruct (Z.leb _ two64) eqn:Hq64; [|discriminate]. apply Z.leb_le in Hq64.
    destruct (sep_app2_b _ _ _ _ _ _ _ ||| sep_res_b _ _) eqn:Hsa; [|discriminate]. destruct (sep_pc_b _ _ _ _ _) eqn:Hsp2; [|discriminate].
    pose proof (irange_sound E (s_facts S) (fst q) HF0) as Rq1. pose proof (irange_sound E (s_facts S) (snd q) HF0) as Rq2.
    fold (uE E (fst q)) in Rq1. fold (uE E (snd q)) in Rq2.
    assert (Hw64 : 0 <= w < two64) by (pose proof (uE_range E (fst q)); lia).
    assert (HofM1 : forall w, Hof E (with_allow M1 (remove_nth k (sm_allow M))) model w = Hof E (with_allow M (remove_nth k (sm_allow M))) model w) by reflexivity.
    rewrite HofM1.
    exact (vis_keep E (s_facts S) M model g e k (pseudo q) w HF0 Hgg Hal1 Hk Hown Hwq Hw64 Hv).
Qed.
#[using="Hsegb"] Theorem den_blob_add : forall E S M ms model i S' M',
  DEN segs LIMIT model0 mem0 E S M ms model -> blobadd LIMIT (segments_reserved segs) S M i = Some (S', M') ->
  DEN segs LIMIT (with_blob (gden E (absorb_g M i) :: blob_of model0) model0) mem0 E S' M' ms model.
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0). intros E S M ms model i S' M' Hd Hb. rewrite blobadd_eq in Hb. exact (den_blob_add_ref E S M ms model i S' M' Hd Hb). Qed.
End BlobAdd.

(* [comment removed for export] *)
Fixpoint widen_nth (k : nat) (z : Z) (al : list (lin * Z)) : list (lin * Z) :=
  match k, al with
  | O, (b, z0) :: r => (b, Z.max z0 z) :: r
  | Datatypes.S k', e :: r => e :: widen_nth k' z r
  | _, [] => []
  end.
Lemma widen_allowed : forall E k z al p, Forall (fun q => 0 <= snd q) al ->
  page_allowedb (List.map (allow1 E) al) p = true -> page_allowedb (List.map (allow1 E) (widen_nth k z al)) p = true.
Proof.
  intros E k z. induction k as [|k IH]; intros al p Hnz H; destruct al as [|[b z0] r]; try exact H.
  - cbn [widen_nth List.map] in *. unfold page_allowedb in *. cbn [existsb] in *. apply orb_prop in H as [H|H]; [|rewrite H, orb_true_r; reflexivity].
    apply orb_true_iff. left. unfold allow1 in *. cbn [fst snd] in *. apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb].
    apply Z.leb_le in H2. apply Z.leb_le.
    pose proof (Z.div_le_mono (uE E b + z0 + 4095) (uE E b + Z.max z0 z + 4095) 4096 ltac:(lia) ltac:(lia)). lia.
  - cbn [widen_nth List.map] in *. unfold page_allowedb in *. cbn [existsb] in *. apply orb_prop in H as [H|H]; [rewrite H; reflexivity|].
    inversion Hnz; subst. pose proof (IH r p H3 H) as X. unfold page_allowedb in X. rewrite X, orb_true_r. reflexivity.
Qed.
Lemma widen_nz : forall k z al, Forall (fun q : lin * Z => 0 <= snd q) al -> Forall (fun q : lin * Z => 0 <= snd q) (widen_nth k z al).
Proof.
  intros k z. induction k as [|k IH]; intros al H; destruct al as [|[b z0] r]; cbn [widen_nth]; try constructor; inversion H; subst; cbn [snd] in *; try lia; auto.
Qed.
Lemma widen_wf : forall n k z al, forallb (fun g : lin * Z => lwf n (fst g)) al = true -> forallb (fun g : lin * Z => lwf n (fst g)) (widen_nth k z al) = true.
Proof.
  intros n k z. induction k as [|k IH]; intros al H; destruct al as [|[b z0] r]; cbn [widen_nth forallb] in *; try reflexivity; try exact H.
  apply andb_prop in H as [H1 H2]. rewrite H1, (IH r H2). reflexivity.
Qed.
Definition widen_ok (LIMIT : Z) (S : sst) (M : smodel) (k : nat) (z : Z) : bool :=
  Z.leb (eager_sum (s_facts S) (sm_maps M) + allow_bound (widen_nth k z (sm_allow M))) LIMIT.

Section AllowMono.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_allow_mono : forall E S M ms model al',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall p, page_allowedb (allowA E M) p = true -> page_allowedb (List.map (allow1 E) al') p = true) ->
  Forall (fun q => 0 <= snd q) al' -> forallb (fun g => lwf (s_next S) (fst g)) al' = true ->
  eager_sum (s_facts S) (sm_maps M) + allow_bound al' <= LIMIT ->
  DEN segs LIMIT model0 mem0 E S (with_allow M al') ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model al' Hd Hmono Hanz' Hwa Hbud.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := with_allow M al').
  set (H := Hof E M model) in *. set (H' := Hof E M' model).
  assert (HA' : allowA E M' = List.map (allow1 E) al') by reflexivity.
  assert (HH' : forall w, H w = false -> H' w = false).
  { intros w Hw. unfold H', Hof. rewrite HA'. unfold H, Hof, mkH in *.
    destruct (page_in_ranges (page_base w) (m_vm_lazy model)); [|reflexivity]. cbn [andb] in *.
    apply negb_false_iff in Hw. apply negb_false_iff. exact (Hmono _ Hw). }
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0. split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. pose proof (HG R HR') as HRok.
    apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact HRok|].
    intros i Hi. pose proof (rg_ok_visible segs H (ms_mem ms) E'' R Hhoff HRok i Hi) as Hv.
    cbn [ms_mem restrict]. unfold mrestrict. rewrite Hv. fold H'. rewrite (HH' _ Hv). reflexivity.
  - unfold sm_wf in *. cbn [M' with_allow sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own].
    apply andb_prop in Hwf as [Hwf W8]. apply andb_prop in Hwf as [Hwf W7]. apply andb_prop in Hwf as [Hwf W6]. apply andb_prop in Hwf as [Hwf W5].
    apply andb_prop in Hwf as [Hwf W4]. apply andb_prop in Hwf as [Hwf W3]. apply andb_prop in Hwf as [W1 W2].
    rewrite W1, W3, W4, W5, W6, W7, W8, Hwa. reflexivity.
  - exact (A_wf_allowA E M' Hanz').
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; try assumption.
    + intros p Hp. specialize (N3 p Hp). unfold AM in *. rewrite HA'. unfold page_allowedb in *. rewrite existsb_app in *.
      apply orb_prop in N3 as [N3|N3]; [|rewrite N3, orb_true_r; reflexivity].
      pose proof (Hmono p N3) as X. unfold page_allowedb in X. rewrite X. reflexivity.
    + pose proof (eager_le E M model (s_facts S) _ HF0 Hmaps Hgsh Hkind Hblob) as He. pose proof (A_bytes_allowA E M' Hanz') as Hb.
      rewrite Hlim. unfold AM. rewrite A_bytes_app. cbn [M' with_allow sm_allow] in Hb. lia.
  - intros w Hw. apply Hhoff. change (H' w = true) in Hw. destruct (H w) eqn:Hh0; [reflexivity|]. rewrite (HH' w Hh0) in Hw. discriminate.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [exact (HH' _ Hv) | exact Hm].
Qed.

#[using="Type"] Theorem den_allow_widen : forall E S M ms model k z,
  DEN segs LIMIT model0 mem0 E S M ms model -> widen_ok LIMIT S M k z = true ->
  DEN segs LIMIT model0 mem0 E S (with_allow M (widen_nth k z (sm_allow M))) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model k z Hd Hok. unfold widen_ok in Hok. apply Z.leb_le in Hok.
  pose proof (dn_anz _ _ _ _ _ _ _ _ _ Hd) as Hanz. pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  apply den_allow_mono; [exact Hd | | exact (widen_nz k z _ Hanz) | | exact Hok].
  - intros p Hp. exact (widen_allowed E k z _ p Hanz Hp).
  - apply widen_wf. unfold sm_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _].
    apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hwf]. exact Hwf.
Qed.
End AllowMono.

(* [comment removed for export] *)
Definition nth_front {X} (i : nat) (l : list X) : list X := match nth_error l i with Some x => x :: remove_nth i l | None => l end.
Lemma nth_front_perm : forall {X} i (l : list X), Permutation l (nth_front i l).
Proof.
  intros X i. unfold nth_front. induction i as [|i IH]; intros [|y r]; cbn [nth_error remove_nth]; try apply Permutation_refl.
  specialize (IH r). destruct (nth_error r i) as [x|]; [|apply Permutation_refl].
  eapply Permutation_trans; [apply perm_skip; exact IH | apply perm_swap].
Qed.
Definition with_rgs' (s : sst) (rgs : list region) : sst := SST (s_pc s) (s_regs s) rgs (s_facts s) (s_next s) (s_resv s).
Lemma Forall_perm'' : forall {A} (P : A -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros A P l l' HP H. rewrite Forall_forall in *. intros x Hx. apply H. apply (Permutation_in x (Permutation_sym HP) Hx). Qed.
Lemma forallb_perm'' : forall {A} (f : A -> bool) l l', Permutation l l' -> forallb f l = true -> forallb f l' = true.
Proof. intros A f l l' HP H. rewrite forallb_forall in *. intros x Hx. apply H. apply (Permutation_in x (Permutation_sym HP) Hx). Qed.
Lemma rg_disj_sym' : forall E R1 R2, rg_disj E R1 R2 -> rg_disj E R2 R1.
Proof. intros E R1 R2 H. unfold rg_disj in *. cbv zeta in *. lia. Qed.
Lemma rgs_disj_perm' : forall E l l', Permutation l l' -> rgs_disj E l -> rgs_disj E l'.
Proof.
  intros E l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' HP1 IH1 HP2 IH2]; intros H.
  - exact I.
  - destruct H as [Hx Hl]. split; [exact (Forall_perm'' _ _ _ HP Hx) | exact (IH Hl)].
  - destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
    split; [constructor; [exact (rg_disj_sym' E _ _ Hyx) | exact Hx]|]. split; [exact Hyl | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.
Definition front_ok (LIMIT : Z) (S : sst) (M : smodel) (i : nat) : bool :=
  Z.leb (eager_sum (s_facts S) (sm_maps M) + allow_bound (nth_front i (sm_allow M))) LIMIT.

Section Front.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_rgs_perm : forall E S M ms model rgs', DEN segs LIMIT model0 mem0 E S M ms model -> Permutation (s_rgs S) rgs' ->
  DEN segs LIMIT model0 mem0 E (with_rgs' S rgs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model rgs' Hd HP.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HPs : Permutation rgs' (s_rgs S)) by exact (Permutation_sym HP).
  constructor; cbn [with_rgs' s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs' s_pc s_regs s_rgs s_facts s_resv].
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + exact (Forall_perm'' _ _ _ HP A5).
    + exact (rgs_disj_perm' E' _ _ HP A6).
  - unfold bases_wf in *. exact (forallb_perm'' _ _ _ HP Hbw).
  - intros w Hw Hout Hno Hnb. apply (Hzr w Hw); [|exact Hno | exact Hnb]. unfold outside in *. exact (Forall_perm'' _ _ _ HPs Hout).
  - exact (Forall_perm'' _ _ _ HP Hrl).
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [|exact X3]. unfold outside in *. exact (Forall_perm'' _ _ _ HP X2).
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Hout. apply Hm. unfold outside in *. exact (Forall_perm'' _ _ _ HPs Hout).
Qed.
#[using="Type"] Theorem den_rgs_front : forall E S M ms model i, DEN segs LIMIT model0 mem0 E S M ms model ->
  DEN segs LIMIT model0 mem0 E (with_rgs' S (nth_front i (s_rgs S))) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S M ms model i Hd. exact (den_rgs_perm E S M ms model _ Hd (nth_front_perm i _)). Qed.

#[using="Type"] Theorem den_allow_front : forall E S M ms model i, DEN segs LIMIT model0 mem0 E S M ms model -> front_ok LIMIT S M i = true ->
  DEN segs LIMIT model0 mem0 E S (with_allow M (nth_front i (sm_allow M))) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i Hd Hok. unfold front_ok in Hok. apply Z.leb_le in Hok.
  pose proof (dn_anz _ _ _ _ _ _ _ _ _ Hd) as Hanz. pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  pose proof (nth_front_perm i (sm_allow M)) as HP.
  apply den_allow_mono; [exact Hd | | exact (Forall_perm'' _ _ _ HP Hanz) | | exact Hok].
  - intros p Hp. unfold allowA, page_allowedb in *. apply existsb_exists in Hp as (iv & Hiv & Hc). apply existsb_exists. exists iv. split; [|exact Hc].
    exact (Permutation_in iv (Permutation_map (allow1 E) HP) Hiv).
  - apply (forallb_perm'' _ _ _ HP). unfold sm_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _].
    apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hwf]. exact Hwf.
Qed.
End Front.

