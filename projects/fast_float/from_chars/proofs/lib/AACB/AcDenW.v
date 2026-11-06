(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.

Module AcRegsEq.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxStep FxSubst FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition with_regs_t (S : sst) (R : tree lin) : sst := SST (s_pc S) R (s_rgs S) (s_facts S) (s_next S) (s_resv S).

Section RegsEq.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_regs_eq : forall E S M ms model R2,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E', agree (s_next S) E E' -> forall r : reg, lden E' (rget R2 (rkey r)) = lden E' (rget (s_regs S) (rkey r))) ->
  DEN segs LIMIT model0 mem0 E (with_regs_t S R2) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R2 Hd Heq.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_regs_t s_rgs s_next]; try assumption.
  intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_regs_t s_pc s_regs s_rgs s_facts s_resv].
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj A5 (conj A6 (conj A7 A8))))))).
  intros r. rewrite (A4 r). symmetry. exact (Heq E' Ha r).
Qed.
End RegsEq.
(* [comment removed for export] *)
End AcRegsEq.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition frz_pt (E : valu) (M : smodel) (w : Z) : Prop :=
  exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p).

Section SegW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_isteps_w : forall mem0 E S M ms model T L msr' E',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  isteps segs (restrict (Hof E M model) ms) msr' ->
  sden segs E' L msr' -> agree (s_next S) E E' -> (s_next S <= s_next L)%positive ->
  (forall w, 0 <= w < two64 -> outside E (s_rgs S) (Z_to_bv 64 w) -> ~ own_pt E M w ->
     ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) ->
  (forall w, frz_pt E M w -> ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) ->
  shape (s_rgs L) = shape (s_rgs S) ->
  (forall E' ms' model', DEN segs LIMIT model0 (ms_mem ms') E' L M ms' model' -> agree (s_next S) E E' ->
      (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
      (forall x, Hof E M model x = false -> ms_mem ms' x = ms_mem msr' x) ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 E S M ms model T L msr' E' Hd Hst Hd' Ha Hn Hfr Hfz Hsh Hk.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  assert (Hcov : lazy_cover H (m_vm_lazy model) (AM model0 E M)) by (apply lazy_cover_mkH_app; intros x Hx; exact Hx).
  apply (rzc_fx_isteps segs cfg H Hhoff Hwx (AM model0 E M) (restrict H ms) msr' ms model T eq_refl Hcov (A_wf_app _ _ Hawf (A_wf_blobA _)) Hminv Hh Hst).
  intros model' Hinv' Hsb' Hcl'.
  destruct (same_but_materialized_frame model model' Hsb') as (Hfd & Hvm & Hlz & Hio & Hfs & Hpr & Hli & Htm & _ & _ & _ & _ & Hhl & Htd & _).
  assert (HA : allowA E' M = allowA E M) by exact (allowA_agree (s_next S) E E' M Hwf Ha).
  assert (HH : Hof E' M model' = H) by (unfold Hof, H; rewrite Hlz, HA; reflexivity).
  set (ms' := unrestrict H (ms_mem ms) msr').
  assert (Hfrz0 : forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
  { intros w (q & Hq & Hw). destruct (Hfrz q Hq w Hw) as (_ & Hout & Hm). unfold ms'; cbn [unrestrict ms_mem].
    rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfz w (ex_intro _ q (conj Hq Hw)))). exact Hm. }
  assert (Hvis : forall x, H x = false -> ms_mem ms' x = ms_mem msr' x).
  { intros x Hx. unfold ms'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity. }
  apply (Hk E' ms' model'); [|exact Ha|exact Hfrz0|exact Hvis].
  assert (Hwf' : sm_wf (s_next L) M = true) by exact (sm_wf_mono _ _ M Hn Hwf).
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. unfold ms'. rewrite restrict_unrestrict_clean by exact Hcl'. exact Hd'.
  - exact Hwf'.
  - exact (bases_wf_shape _ _ _ _ Hn Hsh Hbw).
  - rewrite Hhl. exact Hh.
  - rewrite HA. exact Hawf.
  - exact Hanz.
  - rewrite (AM_agree (s_next S) model0 E E' M Hwf Ha). exact Hinv'.
  - rewrite HH. exact Hhoff.
  - rewrite Hvm. exact Hres.
  - rewrite Hvm. exact Hlim.
  - rewrite Hvm, Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - rewrite Hvm. exact Hspok.
  - rewrite Hvm, Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hvm, Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htd, Htid. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - rewrite Hvm, Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha).
  - apply (Forall_agree_maps (s_next S) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
    intros g Hg Hs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hs Ha). tauto.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model')) Hwf Ha).
    + intros g Hg Hs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hs Ha). tauto.
    + rewrite Hvm. exact Hgtop.
  - rewrite Hvm, Hlz. exact Hivwf.
  - rewrite Hvm. exact Hpd.
  - rewrite Hvm. exact Hmres.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => kind_ok E model' g) Hwf Ha).
    + intros g Hg Hs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hs Ha). tauto.
    + unfold kind_ok. rewrite Hvm, Hlz. exact Hkind.
  - rewrite Hlz, Hvm. exact Hlzm.
  - exact Hzrsh.
  - rewrite Hvm. exact Hzrm.
  - intros w Hw Hout Hno Hnb. unfold ms'; cbn [unrestrict ms_mem].
    assert (Hout0 : outside E (s_rgs S) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ Hbw Ha Hsh Hout).
    assert (Hno0 : ~ own_pt E M w) by exact (own_pt_keep _ E E' M M w Hwf Ha eq_refl Hno).
    assert (Hw64 : 0 <= w < two64).
    { pose proof (Hzrsh w Hw) as Hs. unfold in_shadow in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      unfold SH_LO, SH_HI, two64 in *. lia. }
    rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr w Hw64 Hout0 Hno0)).
    exact (Hzr w Hw Hout0 Hno0 Hnb).
  - exact (rl_ok_agree_shape _ E E' model model' (s_rgs S) (s_rgs L) Hbw Ha Hsh Hvm Hrl).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). rewrite Hfd, Hio, Hfs, Hli, Htm. repeat split; assumption.
  - rewrite Hpr, Htd. exact Hproc.
  - intros q Hq w Hw. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hfrz q Hq w Hw0) as (Htp & Hout & Hm). split; [unfold alloc_top in *; rewrite Hvm; exact Htp|]. split; [|reflexivity].
    apply (outside_shape E' (s_rgs S) (s_rgs L) _ Hsh). apply (proj1 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha)). exact Hout.
  - unfold ms'; cbn [unrestrict ms_rom]. rewrite (fx_rom segs _ _ Hst). cbn [restrict ms_rom]. exact Hrom.
  - intros q Hq w Hw. pose proof (sm_wf_own _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hown q Hq w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros _. reflexivity.
  - apply (blob_ok_agree (s_next S) E E' M model model' _ Hwf Ha); [rewrite Hvm; reflexivity | exact Hblob].
Qed.
End SegW.

(* [comment removed for export] *)
Section Snap.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
#[using="Type"] Theorem den_snap : forall mem0 mem0' E S M ms model,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall w, frz_pt E M w -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  (forall w, own_pt E M w -> outside E (s_rgs S) (Z_to_bv 64 w) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  DEN segs LIMIT model0 mem0' E S M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 mem0' E S M ms model Hd Hf Ho.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  - intros q Hq w Hw. destruct (Hfrz q Hq w Hw) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. symmetry. apply Hf. exists q. split; [exact Hq | exact Hw].
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [exact Hv|]. intros Hout. rewrite (Hm Hout).
    symmetry. apply Ho; [exists q; split; [exact Hq | exact Hw] | exact Hout].
Qed.
End Snap.
(* [comment removed for export] *)
