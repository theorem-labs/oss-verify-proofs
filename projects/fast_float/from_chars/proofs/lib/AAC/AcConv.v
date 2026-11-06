(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcMrg AcCarve.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition with_own (M : smodel) (own : list (lin * lin)) : smodel :=
  SM (sm_maps M) (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) own.

(* [comment removed for export] *)
Lemma vis_of_rg : forall segs E H m R x, H_off_segments segs H -> rg_ok segs E (mrestrict H m) R -> in_rg E R x -> H x = false.
Proof.
  intros segs E H m R x Hoff HR Hin. destruct (H x) eqn:Hx; [|reflexivity]. exfalso.
  pose proof (Hoff x Hx) as Hns.
  destruct HR as (Hz & Hf & Hall & _). unfold in_rg in Hin. set (A := bv_unsigned (lden E (rg_base R))) in *.
  specialize (Hall (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hall by lia.
  rewrite Z_to_bv_bv_unsigned in Hall.
  assert (Hro : seg_rom segs x = None) by (unfold seg_rom, memory_read; change (Z.of_N 1%N) with 1%Z; rewrite Hns; reflexivity).
  assert (Hrd : rd1 segs (mrestrict H m) x = None) by (unfold rd1, mrestrict; rewrite Hx; exact Hro).
  destruct (rg_kind R); try (apply (proj1 Hall); exact Hrd); try (apply (proj1 (proj1 Hall)); exact Hrd).
  - apply (proj2 Hall). exact Hro.
  - exact (Hall Hrd).
Qed.

Section Conv.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_drop_own : forall E S M ms model keep drop own',
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = keep ++ drop -> sm_own M = [] ->
  forallb (fun p => lwf (s_next S) (fst p) && lwf (s_next S) (snd p))%bool own' = true ->
  (forall p w, In p own' -> uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> exists R, In R drop /\ in_rg E R (Z_to_bv 64 w)) ->
  (forall R x, In R drop -> in_rg E R x -> exists p, In p own' /\ uE E (fst p) <= bv_unsigned x < uE E (fst p) + uE E (snd p)) ->
  DEN segs LIMIT model0 (ms_mem ms) E (with_rgs S keep) (with_own M own') ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model keep drop own' Hd HS Hn0 Hwo Hod Hdo.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HH : Hof E (with_own M own') model = Hof E M model) by reflexivity.
  assert (HA : allowA E (with_own M own') = allowA E M) by reflexivity.
  assert (Hdrop_ok : forall R, In R drop -> rg_ok segs E (ms_mem (restrict (Hof E M model) ms)) R).
  { intros R HR. destruct (Hsd E (agree_refl _ _)) as (_ & _ & _ & _ & A5 & _). rewrite HS, Forall_app in A5. destruct A5 as [_ A5].
    rewrite Forall_forall in A5. exact (A5 R HR). }
  constructor; cbn [with_rgs with_own s_rgs s_next sm_maps sm_allow sm_zr sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l _]. apply rgs_disj_app_iff in A6 as (D1 & _ & _).
    exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5l (conj D1 (conj A7 A8))))))).
  - unfold sm_wf in Hwf |- *. unfold with_own. cbn [sm_maps sm_allow sm_zr sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own].
    apply andb_prop in Hwf as [Hwf _]. rewrite Hwf. exact Hwo.
  - unfold bases_wf in *. rewrite HS, forallb_app in Hbw. apply andb_prop in Hbw as [Hbw _]. exact Hbw.
  - intros w Hw Hout Hno Hnb. apply (Hzr w Hw); [|exact (own_pt_nil E M w Hn0) | exact Hnb].
    rewrite HS. unfold outside in *. apply Forall_app. split; [exact Hout|].
    apply Forall_forall. intros R HR. destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) (bv_unsigned (Z_to_bv 64 w))) as [Y|Y]; [right; exact Y|].
    exfalso. apply Hno. destruct (Hdo R (Z_to_bv 64 w) HR ltac:(unfold in_rg; lia)) as (p & Hp & Hpw).
    exists p. split; [exact Hp|]. (* [comment removed for export] *)
    pose proof (Hzrsh w Hw) as Hs. unfold in_shadow in Hs. apply andb_prop in Hs as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
    rewrite u_small64 in Hpw by (unfold SH_LO, SH_HI, two64 in *; lia). exact Hpw.
  - rewrite HS, Forall_app in Hrl. exact (proj1 Hrl).
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [|reflexivity].
    rewrite HS in X2. unfold outside in *. rewrite Forall_app in X2. exact (proj1 X2).
  - intros p Hp w Hw. split.
    + destruct (Hod p w Hp Hw) as (R & HR & Hin). exact (vis_of_rg segs E _ _ R _ Hhoff (Hdrop_ok R HR) Hin).
    + intros _. reflexivity.
Qed.
End Conv.
