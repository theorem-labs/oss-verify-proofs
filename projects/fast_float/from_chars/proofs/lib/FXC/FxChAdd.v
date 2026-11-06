(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.

Module AcAddOwn.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition addo_post (S : sst) (R : region) : sst := SST (s_pc S) (s_regs S) (R :: s_rgs S) (s_facts S) (s_next S) (s_resv S).
(* [comment removed for export] *)
Definition cont_bk (c : tree bval) : Prop := forall p v, tget p c = Some v -> exists b, v = BK b.

Fixpoint remove_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with [] , _ => [] | _ :: r, O => r | x :: r, Datatypes.S i' => x :: remove_nth i' r end.
Lemma In_remove_nth : forall {A} i (l : list A) x, In x (remove_nth i l) -> In x l.
Proof. intros A i. induction i as [|i IH]; intros [|y r] x H; cbn in H; try (destruct H); [right; exact H | left; exact H | right; exact (IH r x H)]. Qed.
Lemma nth_remove_cases : forall {A} i (l : list A) R x, nth_error l i = Some R -> In x l -> x = R \/ In x (remove_nth i l).
Proof.
  intros A i. induction i as [|i IH]; intros [|y r] R x HR Hx; cbn in HR; try discriminate.
  - injection HR as <-. destruct Hx as [<-|Hx]; [left; reflexivity | right; exact Hx].
  - destruct Hx as [<-|Hx]; [right; left; reflexivity|]. destruct (IH r R x HR Hx) as [->|H]; [left; reflexivity | right; right; exact H].
Qed.
Lemma rgs_disj_remove : forall E i rgs, rgs_disj E rgs -> rgs_disj E (remove_nth i rgs).
Proof.
  intros E i. induction i as [|i IH]; intros [|R rs] H; cbn [remove_nth]; try exact I.
  - exact (proj2 H).
  - destruct H as [H1 H2]. split; [|exact (IH rs H2)]. apply Forall_forall. intros x Hx. rewrite Forall_forall in H1. exact (H1 x (In_remove_nth i rs x Hx)).
Qed.
Definition dropo_post (S : sst) (i : nat) : sst := SST (s_pc S) (s_regs S) (remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S).

Section AddOwn.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_v0 : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p v, tget p (rg_cont R) = Some v -> bwf (s_next S) v = true /\ Zpos p - 1 < rsz E R /\
               ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (bden E v)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts Hcont Hsep Hrl0.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  pose proof (u_lt (lden E (rg_base R))) as Ra.
  assert (Hvis : forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> H (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (Hpts x Hx) as ((q & Hq & Hqw) & _). exact (proj1 (Hown q Hq x Hqw)). }
  assert (Hsden : sden segs E (addo_post S R) (restrict H ms)).
  { intros E'' Ha''. cbn [addo_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R', In R' (s_rgs S) -> uE E'' (rg_base R') = uE E (rg_base R') /\ rsz E'' R' = rsz E R').
    { intros R' HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R' HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    assert (HaE : uE E'' (rg_base R) = uE E (rg_base R)) by (unfold uE; rewrite (lden_agree_wf _ E E'' _ Hwb Ha''); reflexivity).
    assert (HzE : rsz E'' R = rsz E R) by (unfold rsz; rewrite (lden_agree_wf _ E E'' _ Hwz Ha''); reflexivity).
    unfold sden0, addo_post. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    - constructor; [|exact HG].
      unfold rg_ok. cbv zeta. change (bv_unsigned (lden E'' (rg_base R))) with (uE E'' (rg_base R)). rewrite HaE, HzE.
      split; [lia|]. split; [unfold two64; lia|]. split.
      + intros i Hi. destruct (Hpts (uE E (rg_base R) + i) ltac:(lia)) as (_ & Hm & _).
        assert (Hr : ms_mem (restrict H ms) (Z_to_bv 64 (uE E (rg_base R) + i)) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))).
        { cbn [restrict ms_mem]. unfold mrestrict. rewrite (Hvis (uE E (rg_base R) + i) ltac:(lia)). reflexivity. }
        assert (Hrw : rd1 segs (ms_mem (restrict H ms)) (Z_to_bv 64 (uE E (rg_base R) + i)) <> None /\
                      wview segs (ms_mem (restrict H ms)) (Z_to_bv 64 (uE E (rg_base R) + i)) <> None).
        { unfold rd1, wview. rewrite Hr. destruct (ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))); [split; discriminate | contradiction]. }
        destruct Hk as [Hk|[Hk Hzero]]; rewrite Hk; [exact Hrw|]. split; [exact Hrw|]. intros Ht. unfold rd1. rewrite Hr.
        rewrite (Hzero (uE E (rg_base R) + i) ltac:(lia) ltac:(replace (uE E (rg_base R) + i - uE E (rg_base R)) with i by ring; exact Ht)). reflexivity.
      + intros p v Hp. destruct (Hcont p v Hp) as (C0 & C1 & C2). split; [exact C1|]. rewrite <- (bden_agree _ E E'' v C0 Ha'').
        assert (Hr : ms_mem (restrict H ms) (Z_to_bv 64 (uE E (rg_base R) + (Z.pos p - 1))) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Z.pos p - 1)))).
        { cbn [restrict ms_mem]. unfold mrestrict. rewrite (Hvis (uE E (rg_base R) + (Z.pos p - 1)) ltac:(lia)). reflexivity. }
        unfold rd1. rewrite Hr, C2. reflexivity.
    - cbn [rgs_disj]. split; [|exact HD]. apply Forall_forall. intros R2 H2. unfold rg_disj. cbv zeta.
      change (bv_unsigned (lden E'' (rg_base R))) with (uE E'' (rg_base R)). change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)).
      rewrite HaE, HzE, (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
      pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
      apply iv_pts_disj; [lia | lia|]. intros w Hw1 Hw2. exact (Hsep R2 H2 w Hw2 Hw1). }
  constructor.
  - exact Hsden.
  - exact Hwf.
  - cbn [addo_post s_next s_rgs]. unfold bases_wf. cbn [forallb]. rewrite Hwb, Hwz. exact Hbw.
  - exact Hh.
  - exact Hawf.
  - exact Hanz.
  - exact Hminv.
  - exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. cbn [addo_post s_rgs] in Hout. unfold outside in Hout. apply Forall_inv_tail in Hout. exact (Hzr w Hw Hout Hnow Hnb).
  - cbn [addo_post s_rgs]. constructor; [exact Hrl0 | exact Hrl].
  - exact Hvmo.
  - exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    apply (frz_keep mem0 E E S (addo_post S R) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [addo_post s_rgs]. constructor; [|exact Ho].
      assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia). rewrite Hw64.
      right. fold (uE E (rg_base R)). destruct (Hpts (uE E (rg_base R) + rsz E R - 1) ltac:(lia)) as (_ & _ & Hlt). lia.
    + intros w _ _. reflexivity.
  - rom_tac.
  - apply (own_keep mem0 E E S (addo_post S R) M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho. unfold outside in Ho. cbn [addo_post s_rgs] in Ho. exact (Forall_inv_tail Ho).
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
  - exact Hblob.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_v : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  (forall p v, tget p (rg_cont R) = Some v -> bwf (s_next S) v = true) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p v, tget p (rg_cont R) = Some v -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (bden E v)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hbw Hpos Htop Hpts Hcont Hsep Hrl0.
  apply (den_add_own_v0 E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts); [|exact Hsep | exact Hrl0].
  intros p v Hp. destruct (Hcont p v Hp) as [C1 C2]. split; [exact (Hbw p v Hp)|]. split; [exact C1 | exact C2].
Qed.
#[using="Type"] Theorem den_add_own_g : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  cont_bk (rg_cont R) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p b, tget p (rg_cont R) = Some (BK b) -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (Z_to_bv 8 b)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hbk Hpos Htop Hpts Hcont Hsep Hrl0.
  apply (den_add_own_v0 E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts); [|exact Hsep | exact Hrl0].
  intros p v Hp. destruct (Hbk p v Hp) as (b & ->). destruct (Hcont p b Hp) as [C1 C2]. split; [reflexivity|]. split; [exact C1 | exact C2].
Qed.
#[using="Type"] Theorem den_add_own : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true -> rg_kind R = RW -> cont_bk (rg_cont R) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p b, tget p (rg_cont R) = Some (BK b) -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (Z_to_bv 8 b)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S M ms model R Hd Hwb Hwz Hk. exact (den_add_own_g E S M ms model R Hd Hwb Hwz (or_introl Hk)). Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_z : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true -> rg_kind R = RZ -> rg_cont R = TEmpty ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ x < alloc_top (m_vmmaps model)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hc Hpos Htop Hpts Hsep Hrl0.
  apply (den_add_own_g E S M ms model R Hd Hwb Hwz); [| | exact Hpos | exact Htop | | | exact Hsep | exact Hrl0].
  - right. split; [exact Hk|]. intros x Hx _. exact (proj1 (proj2 (Hpts x Hx))).
  - rewrite Hc. intros p v Hp. rewrite tget_empty in Hp. discriminate.
  - intros x Hx. destruct (Hpts x Hx) as (P1 & P2 & P3). split; [exact P1|]. split; [rewrite P2; discriminate | exact P3].
  - rewrite Hc. intros p b Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_drop_own : forall E S M ms model i R,
  DEN segs LIMIT model0 mem0 E S M ms model -> nth_error (s_rgs S) i = Some R ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> own_pt E M w /\ ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  DEN segs LIMIT model0 mem0 E (dropo_post S i) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i R Hd HR Hpts.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _).
  assert (HRw : 0 <= rsz E R /\ uE E (rg_base R) + rsz E R <= two64).
  { rewrite Forall_forall in HG0. destruct (HG0 R (nth_error_In _ _ HR)) as (Hs & Hw & _). unfold uE. lia. }
  (* [comment removed for export] *)
  assert (Hcase : forall x : word, outside E (remove_nth i (s_rgs S)) x ->
            outside E (s_rgs S) x \/ uE E (rg_base R) <= bv_unsigned x < uE E (rg_base R) + rsz E R).
  { intros x Hout. destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R))) as [H1|H1];
      [left | destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R) + rsz E R)) as [H2|H2]; [right; lia | left]].
    all: unfold outside in *; apply Forall_forall; intros y Hy; rewrite Forall_forall in Hout.
    all: destruct (nth_remove_cases i (s_rgs S) R y HR Hy) as [->|Hy']; [unfold uE in *; lia | exact (Hout y Hy')]. }
  constructor; try assumption.
  - intros E'' Ha''. cbn [dropo_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0, dropo_post. cbn [s_pc s_regs s_rgs s_facts s_resv]. repeat split; try assumption.
    + apply Forall_forall. intros x Hx. rewrite Forall_forall in H5. exact (H5 x (In_remove_nth i _ x Hx)).
    + exact (rgs_disj_remove E'' i _ H6).
  - unfold bases_wf in *. cbn [dropo_post s_rgs s_next]. rewrite forallb_forall in *. intros x Hx. exact (Hbw x (In_remove_nth i _ x Hx)).
  - intros w Hw Hout Hnow Hnb. cbn [dropo_post s_rgs] in Hout.
    pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
    destruct (Hcase _ Hout) as [Ho|Hin]; [exact (Hzr w Hw Ho Hnow Hnb)|]. rewrite fg64 in Hin by (unfold two64; lia). exfalso. exact (Hnow (proj1 (Hpts w Hin))).
  - rewrite Forall_forall in *. intros x Hx. exact (Hrl x (In_remove_nth i _ x Hx)).
  - apply (frz_keep mem0 E E S (dropo_post S i) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho. unfold outside in *. cbn [dropo_post s_rgs]. apply Forall_forall. intros x Hx. rewrite Forall_forall in Ho. exact (Ho x (In_remove_nth i _ x Hx)).
    + intros w _ _. reflexivity.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [exact Hv|]. intros Hout. cbn [dropo_post s_rgs] in Hout.
    destruct (Hcase _ Hout) as [Ho|Hin]; [exact (Hm Ho)|].
    pose proof (proj2 (Hpts _ Hin)) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.
End AddOwn.
End AcAddOwn.

Module AcFixS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition al_cand (a : lin) (p : lin * Z) : bool :=
  match l_t a, l_t (fst p) with [], [] => true | ta, tp => shares ta tp end.
Definition allow_cov_f (fs : list fact) (a : lin) (n : Z) (al : list (lin * Z)) : bool :=
  let f := fun p : lin * Z => contained_b fs a n (fst p) (snd p) &&& Z.leb (snd (irange fs (fst p)) + snd p) two64 &&& Z.ltb 0 n in
  if existsb_lz f (List.filter (al_cand a) al) then true else existsb_lz f (List.filter (fun p => negb (al_cand a p)) al).
Lemma existsb_split : forall {A} (f p : A -> bool) l,
  (if existsb f (List.filter p l) then true else existsb f (List.filter (fun x => negb (p x)) l)) = existsb f l.
Proof.
  intros A f p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter existsb]. destruct (p x) eqn:Hp; cbn [negb existsb].
  - destruct (f x); [reflexivity | exact IH].
  - destruct (existsb f (List.filter p l)) eqn:H1.
    + rewrite <- IH. destruct (f x); reflexivity.
    + destruct (f x); [reflexivity | exact IH].
Qed.
Lemma allow_cov_f_eq : forall fs a n al, allow_cov_f fs a n al = allow_cov fs a n al.
Proof. intros fs a n al. unfold allow_cov_f, allow_cov. cbv zeta. rewrite !existsb_lz_eq. apply existsb_split. Qed.

Definition fixkeep_ok_s (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (na : bool) (j : nat) (kd' : gkind) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in let ln := rget (s_regs L) (rkey a1r) in
  match a7c L, arg L 2, arg L 3, arg L 5, nth_error (sm_maps M) j with
  | Some c7, Some prot, Some flags, Some off, Some g =>
      (Z.eqb c7 222 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && len_ok fs ln n &&
       negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       (if na then mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else negb (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
             && mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       contained_b fs a n (fst (fst g)) (gsz_lo fs g) && lal_ok a (fst (fst g)) &&
       (gkind_eqb kd' GE || (gkind_eqb kd' (snd g) && negb (gkind_eqb kd' GN) && (na || mmap_noreserve_b (Z_to_bv 64 flags)))) &&
       Z.ltb n 4611686018427387904 &&
       (negb (mmap_noreserve_b (Z_to_bv 64 flags)) ||| allow_cov_f fs a n (sm_allow M)) &&
       (negb na ||| zr_sep_g fs (sm_maps M) j a n (sm_zr M)) && lwf (s_next L) a &&
       Z.leb (eager_sum (s_facts L) (set_kind j kd' (sm_maps M)) + allow_bound (sm_allow M)) LIMIT &&
       Z.leb (eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M) + (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) LIMIT &&
       negb (is_mark g))%bool        (* [comment removed for export] *)
  | _, _, _, _, _ => false
  end.
(* [comment removed for export] *)
End AcFixS.

Module FxChNullS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition NPS (n : positive) : positive := Pos.succ (Pos.succ n).        (* [comment removed for export] *)
Definition null_factsS (n : positive) (ln : lin) (lo hi : Z) : list fact :=
  [FRange (lvar n) 0 (zmax lo); FRange (lvar (Pos.succ n)) 0 15; FRange (NA n) 4096 (TOPW - lo);
   FRange (laddc (NA n) (- SH_HI)) 0 (two64 + SH_LO - lo - SH_HI); FRange (ladd (NA n) ln) (4096 + lo) TOPW;
   FRange (lvar (NPS n)) (lo / 8) (hi / 8); FRange (lsub ln (lscale 8 (lvar (NPS n)))) 0 0].
Definition null_rgsS (n : positive) (ln : lin) (vis piece : bool) : list region :=
  (if vis then [RG (NA n) ln RZ TEmpty] else []) ++ (if piece then [RG (NP n) (lvar (NPS n)) RZ TEmpty] else []).
Definition null_postS (L : sst) (ln : lin) (lo hi : Z) (vis piece : bool) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (NA (s_next L))) (null_rgsS (s_next L) ln vis piece ++ s_rgs L)
      (null_factsS (s_next L) ln lo hi ++ s_facts L) (Pos.succ (NPS (s_next L))) (s_resv L).
(* [comment removed for export] *)
Definition null_allowS (n : positive) (hi : Z) (k : gkind) (vis piece : bool) : list (lin * Z) :=
  (if (vis && gkind_eqb k GL)%bool then [(NA n, hi)] else []) ++ (if piece then [(NP n, hi / 8)] else []).
Definition null_MS (M : smodel) (n : positive) (ln : lin) (hi : Z) (k : gkind) (vis piece : bool) : smodel :=
  SM ((NA n, ln, k) :: sm_maps M) (null_allowS n hi k vis piece ++ sm_allow M)
     (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

(* [comment removed for export] *)
Lemma agree3 : forall n E z r p E'', agree (Pos.succ (NPS n)) (upd (upd (upd E n z) (Pos.succ n) r) (NPS n) p) E'' ->
  agree n E E'' /\ E'' n = z /\ E'' (Pos.succ n) = r /\ E'' (NPS n) = p.
Proof.
  intros n E z r p E'' Ha. unfold NPS in *. split; [|split; [|split]].
  - intros x Hx. rewrite <- (Ha x ltac:(lia)). rewrite !upd_other by lia. reflexivity.
  - rewrite <- (Ha n ltac:(lia)). rewrite !upd_other by lia. apply upd_same.
  - rewrite <- (Ha (Pos.succ n) ltac:(lia)). rewrite upd_other by lia. apply upd_same.
  - rewrite <- (Ha (Pos.succ (Pos.succ n)) ltac:(lia)). apply upd_same.
Qed.
Lemma agree3_0 : forall n E z r p, agree n E (upd (upd (upd E n z) (Pos.succ n) r) (NPS n) p).
Proof. intros n E z r p. exact (proj1 (agree3 n E z r p _ (agree_refl _ _))). Qed.

Lemma page_round_aligned : forall u, 0 <= u -> u mod 4096 = 0 -> page_round_up_Z u = u.
Proof.
  intros u Hu Hal. unfold page_round_up_Z, page_size. pose proof (Z.div_mod u 4096 ltac:(lia)). rewrite Hal in H.
  replace (u + 4096 - 1) with (u / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

Section NullPostS.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem null_denS : forall E L M ms model (ln : lin) (lo hi : Z) (k : gkind) (vis piece : bool) (flags : word) (na : bool) (a : word),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  lwf (s_next L) ln = true -> lo <= uE E ln <= hi -> 0 < lo -> hi < 0x800000000000 -> uE E ln mod 4096 = 0 ->
  place_ok model (uE E ln) a -> shadow_ok M = true -> (piece = true -> zr_ok M = true) ->
  k = (if na then GN else if mmap_noreserve_b flags then GL else GE) ->
  (vis = true -> na = false) ->
  eager_sum (s_facts L) ((NA (s_next L), ln, k) :: sm_maps M) + allow_bound (null_allowS (s_next L) hi k vis piece ++ sm_allow M) <= LIMIT ->
  own_avoid E M (bv_unsigned a) (bv_unsigned a + uE E ln) ->
  (piece = true -> own_avoid E M (bv_unsigned a / 8 + SH_OFF) ((bv_unsigned a + uE E ln) / 8 + SH_OFF)) ->
  DEN segs LIMIT model0 mem0 (upd (upd (upd E (s_next L) (zval a)) (Pos.succ (s_next L)) (rval a)) (NPS (s_next L)) (Z_to_bv 64 (uE E ln / 8)))
      (null_postS L ln lo hi vis piece) (null_MS M (s_next L) ln hi k vis piece)
      (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a (Z_to_bv 64 (uE E ln))))) (fresh_next na flags a (Z_to_bv 64 (uE E ln)) model).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model ln lo hi k vis piece flags na a Hd Hwln Hlh Hlo0 Hhi0 Hnal Hplace Hsh Hzrok Hk Hvis Hbud Hav Havp.
  set (nZ := uE E ln) in *.
  assert (HnZ : 0 < nZ) by lia.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (place_facts_of E M model _ nZ a Hmaps Hsh (proj2 Hspok) HnZ Hplace) as PF.
  pose proof PF as PF0. destruct PF0 as [Hal Hlo Hhi Hshd].
  destruct Hplace as (_ & _ & Htop & Hfree).
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg64; unfold TOPW, two64 in *; pose proof (u_lt a); lia).
  assert (Hlnv : lden E ln = Z_to_bv 64 nZ) by (unfold nZ, uE; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hnc : forall x, bv_unsigned a <= x < bv_unsigned a + nZ ->
                  covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = false).
  { intros x Hx. apply (region_free_pt _ a (Z_to_bv 64 nZ)); [exact Hfree | rewrite HnZw; exact Hx]. }
  set (E' := upd (upd (upd E (s_next L) (zval a)) (Pos.succ (s_next L)) (rval a)) (NPS (s_next L)) (Z_to_bv 64 (nZ / 8))).
  assert (Ha : agree (s_next L) E E') by exact (agree3_0 (s_next L) E _ _ _).
  set (model' := fresh_next na flags a (Z_to_bv 64 nZ) model).
  set (M' := null_MS M (s_next L) ln hi k vis piece).
  set (H := Hof E M model) in *.
  set (H' := Hof E' M' model').
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  assert (Hn8 : (bv_unsigned a + nZ) / 8 = bv_unsigned a / 8 + nZ / 8).
  { pose proof (Z.div_mod nZ 4096 ltac:(lia)). rewrite Hnal in H0.
    replace (bv_unsigned a + nZ) with (bv_unsigned a + (nZ / 4096 * 512) * 8) by lia.
    rewrite Z.div_add by lia. f_equal. pose proof (Z.div_mod nZ 8 ltac:(lia)).
    assert (nZ mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (nZ / 4096 * 512); lia). lia. }
  assert (Hnz8 : nZ = 8 * (nZ / 8)).
  { assert (nZ mod 8 = 0) by (apply Z.mod_divide; [lia|]; pose proof (Z.div_mod nZ 4096 ltac:(lia)); exists (nZ / 4096 * 512); lia).
    pose proof (Z.div_mod nZ 8 ltac:(lia)). lia. }
  assert (Hhi8 : nZ / 8 <= hi / 8) by (apply Z.div_le_mono; lia).
  assert (Hlo8 : lo / 8 <= nZ / 8) by (apply Z.div_le_mono; lia).
  (* [comment removed for export] *)
  assert (HA' : allowA E' M' = List.map (allow1 E') (null_allowS (s_next L) hi k vis piece) ++ allowA E M).
  { unfold allowA, M', null_MS. cbn [sm_allow]. rewrite map_app. f_equal. exact (allowA_agree _ E E' M Hwf Ha). }
  assert (Hlz' : m_vm_lazy model' = (if mmap_noreserve_b flags then lazy_interior a (Z_to_bv 64 nZ) else []) ++ m_vm_lazy model)
    by exact (fn_lazy na flags a (Z_to_bv 64 nZ) model).
  assert (Hli : lazy_interior a (Z_to_bv 64 nZ) = [(a, Z_to_bv 64 nZ)]).
  { apply lazy_interior_aligned; rewrite ?HnZw; unfold page_size; try lia. unfold TOPW in Hhi. lia. }
  (* [comment removed for export] *)
  assert (HNA : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> lden E'' (NA (s_next L)) = a).
  { intros E'' Ha''. destruct (agree3 _ _ _ _ _ _ Ha'') as (_ & Hz & Hr & _). exact (NA_val (s_next L) a E'' Hz Hr Hal). }
  assert (HNP : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> uE E'' (NP (s_next L)) = bv_unsigned a / 8 + SH_OFF).
  { intros E'' Ha''. destruct (agree3 _ _ _ _ _ _ Ha'') as (_ & Hz & Hr & _). exact (NP_val (s_next L) a E'' Hz Hr Hal). }
  assert (HPS : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> uE E'' (lvar (NPS (s_next L))) = nZ / 8).
  { intros E'' Ha''. destruct (agree3 _ _ _ _ _ _ Ha'') as (_ & _ & _ & Hp). unfold uE. rewrite lden_lvar, Hp. apply fg64.
    split; [apply Z.div_pos; lia|]. unfold two64. lia. }
  assert (HLN : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> uE E'' ln = nZ).
  { intros E'' Ha''. destruct (agree3 _ _ _ _ _ _ Ha'') as (Ha0 & _). unfold nZ, uE. rewrite (lden_agree_wf _ E E'' _ Hwln Ha0). reflexivity. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  (* [comment removed for export] *)
  assert (Hpp : forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                  in_shadow y = true /\ (zr_ok M = true -> in_zr (sm_zr M) y = true) /\ covered (lden_maps E (blob_of model0) (sm_maps M)) y = true)
    by (intros y Hy; exact (piece_pts E (blob_of model0) M a nZ y Hsh PF HnZ Hnal Hy)).
  (* [comment removed for export] *)
  assert (Hold : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
             ~ (bv_unsigned a <= w < bv_unsigned a + nZ) /\ ~ (bv_unsigned a / 8 + SH_OFF <= w < (bv_unsigned a + nZ) / 8 + SH_OFF)).
  { intros R HR w Hw. rewrite Forall_forall in Hrl.
    destruct (old_pts E model a nZ R w PF HnZ Hnal Hnc Htop (Hrl R HR) Hw) as [H1 H2]. split; [exact H1|].
    apply H2. intros y Hy. exact (proj1 (Hpp y Hy)). }
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  assert (Hua : 0 <= bv_unsigned a < two64) by exact (u_lt a).
  (* [comment removed for export] *)
  assert (Hvold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R -> H' (Z_to_bv 64 (uE E (rg_base R) + i)) = false).
  { intros R HR i Hi. rewrite Forall_forall in HG0.
    pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    unfold H', Hof. rewrite Hlz', HA'. apply mkH_grow; [exact Hv|].
    intros Hp. destruct (mmap_noreserve_b flags); [|discriminate]. rewrite Hli in Hp. apply page_in_one in Hp.
    rewrite HnZw in Hp. rewrite fg64 in Hp by lia.
    apply (proj1 (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia))). exact Hp. }
  assert (Hvapp : vis = true -> forall i, 0 <= i < nZ -> H' (Z_to_bv 64 (bv_unsigned a + i)) = false).
  { intros Hv i Hi. pose proof (Hvis Hv) as Hna. unfold H', Hof. rewrite Hlz', HA'.
    destruct (mmap_noreserve_b flags) eqn:Hnr.
    - apply mkH_allowed. apply page_allowedb_app_l. rewrite Hk, Hna; rewrite ?Hnr. unfold null_allowS. rewrite Hv. cbn [andb gkind_eqb app List.map].
      change (allow1 E' (NA (s_next L), hi) :: List.map (allow1 E') (if piece then [(NP (s_next L), hi / 8)] else []))
        with ([allow1 E' (NA (s_next L), hi)] ++ List.map (allow1 E') (if piece then [(NP (s_next L), hi / 8)] else [])).
      apply page_allowedb_app_l. apply allow1_covers; [unfold TOPW, two64 in *; lia|]. cbn [fst snd].
      unfold uE. rewrite (HNA E' (agree_refl _ _)). lia.
    - apply mkH_notlazy. rewrite app_nil_l. apply not_true_iff_false. intros Hp.
      destruct (pb_bounds (Z_to_bv 64 (bv_unsigned a + i))) as [Hb _].
      pose proof (Hlzm _ (page_in_covered _ _ _ Hp Hb)) as Hc. rewrite fg64 in Hc by (unfold TOPW, two64 in *; lia).
      pose proof (Hnc (bv_unsigned a + i) ltac:(lia)) as Hf. rewrite covered_app, Hc, orb_true_r in Hf. discriminate. }
  assert (Hvpc : piece = true -> forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                   H' (Z_to_bv 64 y) = false).
  { intros Hpc y Hy. unfold H', Hof. rewrite Hlz', HA'. apply mkH_allowed. apply page_allowedb_app_l.
    unfold null_allowS. rewrite Hpc, map_app. apply page_allowedb_app_r. cbn [List.map].
    apply allow1_covers; [|cbn [fst snd]; rewrite (HNP E' (agree_refl _ _))].
    - assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, TOPW, two64 in *. lia.
    - lia. }
  (* [comment removed for export] *)
  set (mem' := fresh_mem na (ms_mem ms) a (Z_to_bv 64 nZ)).
  assert (Hmold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
                    mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    apply fresh_mem_out. rewrite HnZw. rewrite fg64 by lia. exact (proj1 (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia))). }
  assert (Hmapp : vis = true -> forall i, 0 <= i < nZ -> mem' (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)).
  { intros Hv i Hi. unfold mem'. rewrite (Hvis Hv). apply fresh_mem_in. rewrite HnZw, fg64 by (unfold TOPW, two64 in *; lia). lia. }
  assert (Hnotpl : forall y, in_shadow y = true -> ~ (bv_unsigned a <= y < bv_unsigned a + nZ)).
  { intros y Hy Hin. unfold in_shadow in Hy. apply andb_prop in Hy as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hmpc : piece = true -> forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                   mem' (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { intros Hpc y Hy. destruct (Hpp y Hy) as (Hys & Hyz & _).
    assert (Hy64 : 0 <= y < two64) by (assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia);
                                        unfold SH_OFF, TOPW, two64 in *; lia).
    unfold mem'. rewrite fresh_mem_out by (rewrite HnZw, fg64 by exact Hy64; exact (Hnotpl y Hys)).
    apply Hzr; [exact (Hyz (Hzrok Hpc))| |exact (own_avoid_pt E M _ _ y (Havp Hpc) Hy64 Hy)
                | apply (blob_sh_fresh E M model _ a (Z_to_bv 64 nZ) y Hmaps Hblob Hfree); rewrite HnZw; exact Hy].
    unfold outside. apply Forall_forall. intros R HR. rewrite fg64 by exact Hy64.
    destruct (Hrgw R HR) as [Hw1 Hw2].
    destruct (Z_lt_le_dec y (bv_unsigned (lden E (rg_base R)))) as [Hlt|Hge]; [left; exact Hlt|].
    destruct (Z_lt_le_dec y (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [Hlt2|Hge2]; [|right; exact Hge2].
    exfalso. apply (proj2 (Hold R HR y ltac:(unfold uE; lia))). exact Hy. }
  assert (Hpw : (bv_unsigned a + nZ) / 8 + SH_OFF <= two64).
  { assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, TOPW, two64 in *. lia. }
  (* [comment removed for export] *)
  assert (HszA : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> rsz E'' (RG (NA (s_next L)) ln RZ TEmpty) = nZ).
  { intros E'' Ha''. unfold rsz. cbn [rg_size]. fold (uE E'' ln). exact (HLN E'' Ha''). }
  assert (HszP : forall E'', agree (Pos.succ (NPS (s_next L))) E' E'' -> rsz E'' (RG (NP (s_next L)) (lvar (NPS (s_next L))) RZ TEmpty) = nZ / 8).
  { intros E'' Ha''. unfold rsz. cbn [rg_size]. fold (uE E'' (lvar (NPS (s_next L)))). exact (HPS E'' Ha''). }
  (* [comment removed for export] *)
  assert (Hsden : sden segs E' (null_postS L ln lo hi vis piece)
                    (restrict H' (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a (Z_to_bv 64 nZ)))))).
  { rewrite (fresh_restrict H' ms na a (Z_to_bv 64 nZ) (s_pc L) Hpc0).
    intros E'' Ha''. destruct (agree3 _ _ _ _ _ _ Ha'') as (Ha0 & Hz & Hr & Hp).
    destruct (Hsd E'' Ha0) as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha0), (lden_agree_wf _ E E'' _ Hb2 Ha0). split; reflexivity. }
    unfold sden0, null_postS. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | exact (HNA E'' Ha'')]|].
    split; [|split; [|split; [|exact Hfrm]]].
    - (* [comment removed for export] *)
      apply Forall_app. split.
      + unfold null_rgsS. apply Forall_app. split.
        * destruct vis eqn:Hv; [|constructor]. constructor; [|constructor].
          apply rg_ok_fresh_rz_gen; fold (uE E'' ln); rewrite (HLN E'' Ha''); [unfold uE; rewrite (HNA E'' Ha''); unfold TOPW, two64 in *; lia|].
          intros i Hi. unfold uE. rewrite (HNA E'' Ha''). unfold mrestrict. rewrite (Hvapp eq_refl i Hi). exact (Hmapp eq_refl i Hi).
        * destruct piece eqn:Hpc; [|constructor]. constructor; [|constructor].
          apply rg_ok_fresh_rz_gen; fold (uE E'' (lvar (NPS (s_next L)))); rewrite (HPS E'' Ha''); [rewrite (HNP E'' Ha''); lia|].
          intros i Hi. rewrite (HNP E'' Ha''). unfold mrestrict.
          rewrite (Hvpc eq_refl) by lia. exact (Hmpc eq_refl (bv_unsigned a / 8 + SH_OFF + i) ltac:(lia)).
      + apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
        intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. unfold mrestrict.
        rewrite (Hvold R HR' i Hi). rewrite Forall_forall in HG0.
        rewrite (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR') i Hi). exact (Hmold R HR' i Hi).
    - (* [comment removed for export] *)
      apply rgs_disj_app; [| exact HD |].
      + unfold null_rgsS. destruct vis, piece; cbn [app rgs_disj];
          try (split; [apply Forall_nil | exact I]); try exact I.
        split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
        unfold rg_disj. cbv zeta. rewrite (HszA E'' Ha''), (HszP E'' Ha''). cbn [rg_base].
        change (bv_unsigned (lden E'' (NP (s_next L)))) with (uE E'' (NP (s_next L))). rewrite (HNA E'' Ha''), (HNP E'' Ha'').
        apply iv_pts_disj; [lia | apply Z.div_str_pos; lia|]. intros w Hw1 Hw2. apply (Hnotpl w); [|lia].
        exact (proj1 (Hpp w ltac:(lia))).
      + intros R1 R2 H1 H2. unfold rg_disj. cbv zeta.
        change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)). rewrite (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
        pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
        unfold null_rgsS in H1. apply in_app_iff in H1 as [H1|H1].
        * destruct vis; [|destruct H1]. destruct H1 as [<-|[]]. rewrite (HszA E'' Ha''). cbn [rg_base].
          rewrite (HNA E'' Ha'').
          apply iv_pts_disj; [lia | lia|]. intros w Hw1 Hw2. exact (proj1 (Hold R2 H2 w Hw2) Hw1).
        * destruct piece; [|destruct H1]. destruct H1 as [<-|[]]. rewrite (HszP E'' Ha''). cbn [rg_base].
          change (bv_unsigned (lden E'' (NP (s_next L)))) with (uE E'' (NP (s_next L))). rewrite (HNP E'' Ha'').
          apply iv_pts_disj; [apply Z.div_str_pos; lia | lia|]. intros w Hw1 Hw2.
          exact (proj2 (Hold R2 H2 w Hw2) ltac:(lia)).
    - (* [comment removed for export] *)
      apply Forall_app. split; [|exact HF]. unfold null_factsS. cbn [fact_ok].
      assert (HA3 : forall x, uE E'' x = bv_unsigned (lden E'' x)) by reflexivity.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok].
      + rewrite lden_lvar, Hz, vz_zval. split; [apply Z.div_pos; lia|]. unfold zmax. apply Z.div_le_mono; lia.
      + rewrite lden_lvar, Hr, vz_rval. pose proof (Z.mod_pos_bound (bv_unsigned a / 4096) 16 ltac:(lia)). lia.
      + rewrite (HNA E'' Ha''). lia.
      + rewrite lden_laddc, (HNA E'' Ha''), u_Z_to_bv. destruct Hshd as [Hlw|Hhg].
        * replace (bv_unsigned a + - SH_HI) with ((bv_unsigned a - SH_HI + two64) + (-1) * two64) by ring.
          rewrite Z_mod_plus_full. rewrite Z.mod_small by (unfold SH_HI, SH_LO, two64 in *; lia). unfold SH_HI, SH_LO, two64 in *. lia.
        * rewrite Z.mod_small by (unfold SH_HI, TOPW, two64 in *; lia). unfold SH_HI, SH_LO, TOPW, two64 in *. lia.
      + rewrite lden_ladd, (HNA E'' Ha''). pose proof (HLN E'' Ha'') as Hl''. unfold uE in Hl''. rewrite bv_add_unsigned, Hl''.
        unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.mod_small by (unfold TOPW, two64 in *; lia). unfold TOPW in *. lia.
      + assert (Hp8 : bv_unsigned (Z_to_bv 64 (nZ / 8)) = nZ / 8) by (apply fg64; split; [apply Z.div_pos; lia | unfold two64; lia]).
        rewrite lden_lvar, Hp, Hp8. lia.
      + assert (Hp8 : bv_unsigned (Z_to_bv 64 (nZ / 8)) = nZ / 8) by (apply fg64; split; [apply Z.div_pos; lia | unfold two64; lia]).
        rewrite lden_lsub, bv_sub_unsigned, lden_lscale, lden_lvar, Hp, Hp8. pose proof (HLN E'' Ha'') as Hl''. unfold uE in Hl''. rewrite Hl''.
        rewrite (fg64 (8 * (nZ / 8))) by (unfold TOPW, two64 in *; lia). rewrite <- Hnz8, Z.sub_diag.
        unfold bv_wrap. change (bv_modulus 64) with two64. rewrite Z.mod_0_l by (unfold two64; lia). lia. }
  (* [comment removed for export] *)
  assert (Hvm' : m_vmmaps model' = mkVmMapsFull (vm_reserved (m_vmmaps model)) ((a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps model))
    (if na then (a, Z_to_bv 64 nZ) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model))
    (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model)) (vm_mmap_base (m_vmmaps model))
    (vm_init_sp (m_vmmaps model))) by exact (fn_vmmaps na flags a (Z_to_bv 64 nZ) model).
  assert (Hmat' : m_vm_materialized model' = m_vm_materialized model) by exact (fn_mat na flags a (Z_to_bv 64 nZ) model).
  assert (Hhl' : m_halted model' = m_halted model) by exact (fn_halted na flags a (Z_to_bv 64 nZ) model).
  assert (Htd' : m_tid model' = m_tid model) by exact (fn_tid na flags a (Z_to_bv 64 nZ) model).
  assert (Hoth' : m_proc model' = m_proc model /\ m_fd model' = m_fd model /\ m_io model' = m_io model /\ m_fsys model' = m_fsys model
                  /\ m_lim model' = m_lim model /\ m_time model' = m_time model) by exact (fn_other na flags a (Z_to_bv 64 nZ) model).
  assert (HLN' : lden E' ln = Z_to_bv 64 nZ) by (rewrite (lden_agree_wf _ E E' _ Hwln Ha); exact Hlnv).
  assert (Hmaps' : vm_maps (m_vmmaps model') = lden_maps E' (blob_of model0) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' null_MS lden_maps]. rewrite is_mark_NA. unfold gden at 1. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), HLN'.
    f_equal. rewrite Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha). }
  assert (Hblob' : blob_ok E' M' model' (blob_of model0)).
  { pose proof (blob_ok_agree (s_next L) E E' M model model' _ Hwf Ha ltac:(rewrite Hvm'; reflexivity) Hblob) as (B1 & B2 & B3).
    split; [exact B1 | split].
    - cbn [sm_maps M' null_MS nomark forallb]. rewrite is_mark_NA. cbn [negb andb]. exact B2.
    - intros g Hg Hmk. cbn [sm_maps M' null_MS] in Hg. destruct Hg as [<-|Hg]; [rewrite is_mark_NA in Hmk; discriminate | exact (B3 g Hg Hmk)]. }
  assert (Hgsz' : gsz E' (NA (s_next L), ln, k) = nZ) by (unfold gsz, uE; cbn [fst snd]; rewrite HLN'; exact HnZw).
  assert (Hgsh' : Forall (gshape_ok E') (sm_maps M')).
  { cbn [sm_maps M' null_MS]. constructor.
    - unfold gshape_ok. rewrite Hgsz'. unfold uE. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)). unfold TOPW in Hhi. lia.
    - apply (Forall_agree_maps (s_next L) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
      intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto. }
  assert (Hcovm : forall x, covered (vm_maps (m_vmmaps model')) x = (in_iv (a, Z_to_bv 64 nZ) x || covered (vm_maps (m_vmmaps model)) x)%bool)
    by (intros x; rewrite Hvm'; reflexivity).
  assert (Hcovl : forall x, covered (m_vm_lazy model') x = true -> covered (m_vm_lazy model) x = true \/ in_iv (a, Z_to_bv 64 nZ) x = true).
  { intros x Hx. rewrite Hlz', covered_app in Hx. destruct (mmap_noreserve_b flags); [|left; exact Hx].
    rewrite Hli in Hx. cbn [covered existsb] in Hx. rewrite orb_false_r in Hx. apply orb_prop in Hx as [Hx|Hx]; [right|left]; exact Hx. }
  assert (Hinv : forall x, in_iv (a, Z_to_bv 64 nZ) x = true -> bv_unsigned a <= x < bv_unsigned a + nZ).
  { intros x Hx. rewrite in_iv_word, HnZw in Hx. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hinv' : forall x, bv_unsigned a <= x < bv_unsigned a + nZ -> in_iv (a, Z_to_bv 64 nZ) x = true).
  { intros x Hx. rewrite in_iv_word, HnZw. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hcovm. destruct (Hcovl x Hx) as [H1|H1]; [rewrite (Hlzm x H1), orb_true_r; reflexivity | rewrite H1; reflexivity]. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved]. rewrite Hcovm in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact (Hmres x Hx)].
    pose proof (Hnc x (Hinv x Hx)) as Hf. rewrite covered_app in Hf. apply orb_false_iff in Hf. exact (proj1 Hf). }
  assert (Hkind' : Forall (kind_ok E' model') (sm_maps M')).
  { cbn [sm_maps M' null_MS]. constructor.
    - unfold kind_ok, gden. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), HLN'. split.
      2:{ intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. rewrite Hk in Hgn. destruct na; [left; reflexivity|].
          destruct (mmap_noreserve_b flags); discriminate. }
      intros Hne x Hx. rewrite Hvm'. cbn [vm_noaccess].
      rewrite covered_app. rewrite Hk in Hne. destruct na.
      + cbn [covered existsb]. rewrite Hx. reflexivity.
      + destruct (mmap_noreserve_b flags) eqn:Hnr; [|exfalso; exact (Hne eq_refl)].
        rewrite Hlz'; rewrite ?Hnr, ?Hli. cbn [covered existsb app]. rewrite Hx, orb_true_r. reflexivity.
    - apply (Forall_agree_maps (s_next L) E E' M (fun E g => kind_ok E model' g) Hwf Ha).
      + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      + rewrite Forall_forall in Hkind |- *. intros g Hg. split.
        2:{ intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. pose proof (proj2 (Hkind g Hg) Hgn) as Hi0. destruct na; [right; exact Hi0 | exact Hi0]. }
        intros Hne x Hx. pose proof (proj1 (Hkind g Hg) Hne x Hx) as Hkx.
        rewrite Hvm'. cbn [vm_noaccess]. rewrite Hlz'. rewrite !covered_app in *. apply orb_prop in Hkx as [H1|H1].
        * destruct na; [rewrite covered_cons, H1, orb_true_r; reflexivity | rewrite H1; reflexivity].
        * rewrite H1, !orb_true_r. reflexivity. }
  assert (Hnan : Forall (fun p => 0 <= snd p) (null_allowS (s_next L) hi k vis piece)).
  { unfold null_allowS. apply Forall_app. split.
    - destruct (vis && gkind_eqb k GL)%bool; [apply Forall_cons; [cbn; lia | apply Forall_nil] | apply Forall_nil].
    - destruct piece; [apply Forall_cons; [cbn [snd]; apply Z.div_pos; lia | apply Forall_nil] | apply Forall_nil]. }
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')) by (cbn [sm_allow M' null_MS]; apply Forall_app; split; assumption).
  assert (Hbud' : eager_used model' + A_bytes (AM model0 E' M') <= LIMIT).
  { assert (HFL' : Forall (fact_ok E') (s_facts L)) by (destruct (Hsd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (eager_le E' M' model' (s_facts L) _ HFL' Hmaps' Hgsh' Hkind' Hblob') as He.
    pose proof (A_bytes_allowA E' M' Hanz') as Hb. unfold AM. rewrite A_bytes_app. cbn [sm_maps sm_allow M' null_MS] in He, Hb. lia. }
  assert (HNAw : lwf (Pos.succ (NPS (s_next L))) (NA (s_next L)) = true)
    by (unfold NA, NPS; apply lwf_ladd; apply lwf_lscale; apply lwf_lvar; lia).
  assert (HNPw : lwf (Pos.succ (NPS (s_next L))) (NP (s_next L)) = true)
    by (unfold NP, NPS; apply lwf_laddc, lwf_ladd; apply lwf_lscale; apply lwf_lvar; lia).
  assert (HLNw : lwf (Pos.succ (NPS (s_next L))) ln = true) by (apply (lwf_mono (s_next L)); [unfold NPS; lia | exact Hwln]).
  assert (HPSw : lwf (Pos.succ (NPS (s_next L))) (lvar (NPS (s_next L))) = true) by (apply lwf_lvar; lia).
  assert (Hcovrm : forall x, covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = true ->
                     covered (vm_reserved (m_vmmaps model') ++ vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app in *. apply orb_prop in Hx as [Hx|Hx];
      [rewrite Hx; reflexivity | rewrite covered_cons, Hx, !orb_true_r; reflexivity]. }
  assert (Hcovm' : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_maps (m_vmmaps model')) x = true)
    by (intros x Hx; rewrite Hcovm, Hx, orb_true_r; reflexivity).
  assert (Htop' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
  assert (Happ' : forall w, bv_unsigned a <= w < bv_unsigned a + nZ -> app_pt model' w).
  { intros w Hw. split; [left|split].
    - rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app, covered_cons, (Hinv' w Hw), orb_true_r. reflexivity.
    - apply not_true_iff_false. intros Hs. exact (Hnotpl w Hs Hw).
    - unfold TOPW in Hhi. lia. }
  constructor.
  - exact Hsden.
  - cbn [null_postS s_next]. unfold M', null_MS. apply sm_wf_cons_own; [exact (sm_wf_mono (s_next L) (Pos.succ (NPS (s_next L))) M ltac:(unfold NPS; lia) Hwf) | exact HNAw | exact HLNw |].
    unfold null_allowS. rewrite forallb_app. apply andb_true_intro. split.
    + destruct (vis && gkind_eqb k GL)%bool; cbn [forallb fst]; [rewrite HNAw; reflexivity | reflexivity].
    + destruct piece; cbn [forallb fst]; [rewrite HNPw; reflexivity | reflexivity].
  - cbn [null_postS s_next s_rgs]. unfold bases_wf. rewrite forallb_app. apply andb_true_intro. split.
    + unfold null_rgsS. rewrite forallb_app. apply andb_true_intro. split.
      * destruct vis; cbn [forallb rg_base rg_size]; [rewrite HNAw, HLNw; reflexivity | reflexivity].
      * destruct piece; cbn [forallb rg_base rg_size]; [rewrite HNPw, HPSw; reflexivity | reflexivity].
    + unfold bases_wf in Hbw. rewrite forallb_forall in *. intros R HR. destruct (andb_prop _ _ (Hbw R HR)) as [Hb1 Hb2].
      apply andb_true_intro. split; apply (lwf_mono (s_next L)); [unfold NPS; lia | exact Hb1 | unfold NPS; lia | exact Hb2].
  - rewrite Hhl'. exact Hh.
  - rewrite HA'. unfold A_wf. apply Forall_app. split; [exact (A_wf_map_allow1 E' _ Hnan) | exact Hawf].
  - exact Hanz'.
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat'.
    + exact N1.
    + exact N2.
    + intros p Hp. unfold AM. rewrite HA', <- app_assoc. apply page_allowedb_app_r. exact (N3 p Hp).
    + intros p Hp. rewrite Hlz', page_in_ranges_app, (N4 p Hp), orb_true_r. reflexivity.
    + rewrite Hvm'. cbn [vm_limit]. rewrite Hlim. exact Hbud'.
  - unfold H', Hof. apply (hoff_of segs _ _ (vm_maps (m_vmmaps model')) (vm_reserved (m_vmmaps model')) Hsegb);
      [rewrite Hvm'; exact Hres | exact Hlzm' | exact Hmres'].
  - rewrite Hvm'. exact Hres.
  - rewrite Hvm'. exact Hlim.
  - rewrite Hvm'. cbn [vm_init_sp sm_sp M' null_MS]. rewrite Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - rewrite Hvm'. exact Hspok.
  - rewrite Hvm'. cbn [vm_brk sm_brk M' null_MS]. rewrite Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hvm'. cbn [vm_start_brk sm_sbrk M' null_MS]. rewrite Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htd', Htid. cbn [sm_tid M' null_MS]. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' null_MS]. constructor.
    + rewrite Hgsz'. unfold uE. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), Htop'. exact Htop.
    + apply (Forall_agree_maps (s_next L) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model')) Hwf Ha).
      * intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      * rewrite Htop'. exact Hgtop.
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. destruct Hivwf as [Hw1 Hw2]. split.
    + destruct na; [apply ivs_wf_cons; [unfold iv_wf, B, S; cbn [fst snd]; rewrite HnZw; unfold TOPW in Hhi; lia | exact Hw1] | exact Hw1].
    + apply ivs_wf_app; [|exact Hw2]. destruct (mmap_noreserve_b flags); [rewrite Hli; apply ivs_wf_cons; [|apply ivs_wf_nil] | apply ivs_wf_nil].
      unfold iv_wf, B, S; cbn [fst snd]; rewrite HnZw; unfold TOPW in Hhi; lia.
  - rewrite Hvm'. cbn [vm_maps pdisj]. split; [|exact Hpd]. apply Forall_forall. intros q Hq. destruct q as [b sz].
    assert (Hq' : In (b, sz) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) by (apply in_or_app; right; exact Hq).
    destruct (region_free_avoid _ _ _ _ _ Hfree Hq') as [H1|H1]; unfold iv_disj, B, S; cbn [fst snd]; lia.
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - cbn [sm_zr M' null_MS]. exact Hzrsh.
  - cbn [sm_zr M' null_MS]. intros w Hw. exact (Hcovm' w (Hzrm w Hw)).
  - intros w Hw Hout Hnow Hnb. cbn [sm_zr M' null_MS] in Hw. rewrite fresh_full_mem. unfold outside in Hout. cbn [null_postS s_rgs] in Hout.
    apply Forall_app in Hout as [_ Hout]. pose proof (Hzrsh w Hw) as Hws.
    assert (Hw64 : 0 <= w < two64) by (unfold in_shadow, SH_LO, SH_HI in Hws; apply andb_prop in Hws as [H1 H2];
                                        apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold two64; lia).
    rewrite fresh_mem_out by (rewrite HnZw, fg64 by exact Hw64; exact (Hnotpl w Hws)).
    apply (Hzr w Hw); [apply (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha); exact Hout | | exact Hnb].
    exact (own_pt_keep _ E E' M M' w Hwf Ha eq_refl Hnow).
  - cbn [null_postS s_rgs]. apply Forall_app. split.
    + unfold null_rgsS. apply Forall_app. split.
      * destruct vis; [|constructor]. constructor; [|constructor]. unfold rl_ok. rewrite (HszA E' (agree_refl _ _)).
        split; [exact HnZ|]. left. cbn [rg_base]. unfold uE. rewrite (HNA E' (agree_refl _ _)). exact Happ'.
      * destruct piece; [|constructor]. constructor; [|constructor]. unfold rl_ok. rewrite (HszP E' (agree_refl _ _)).
        split; [apply Z.div_str_pos; lia|]. right. cbn [rg_base]. rewrite (HNP E' (agree_refl _ _)). split; [pose proof (Z.div_pos (bv_unsigned a) 8 ltac:(lia) ltac:(lia)); lia|].
        split.
        -- intros x Hx. apply Happ'. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)).
           assert (Ha8 : bv_unsigned a = 8 * (bv_unsigned a / 8)).
           { assert (bv_unsigned a mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (bv_unsigned a / 4096 * 512); lia).
             pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)). lia. }
           lia.
        -- intros w Hw. destruct (Hpp w ltac:(lia)) as (Hs & _ & Hc). split; [exact Hs|]. apply Hcovm'. rewrite Hmaps. exact Hc.
    + rewrite Forall_forall in Hrl |- *. intros R HR. apply (rl_ok_mono E' model model' R Hcovrm Hcovm' Htop').
      unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR)) as [Hb1 Hb2].
      exact (rl_ok_agree _ E E' model R Hb1 Hb2 Ha (Hrl R HR)).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - destruct Hoth' as (Hp & _). rewrite Hp, Htd'. exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    apply (frz_keep mem0 E E' L (null_postS L ln lo hi vis piece) M M' ms _ model model' Hwf Ha eq_refl Htop'); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [null_postS s_rgs]. apply Forall_app. split.
      * assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia).
        unfold null_rgsS. apply Forall_app. split.
        -- destruct vis; [|constructor]. constructor; [|constructor]. right. rewrite (HszA E' (agree_refl _ _)). cbn [rg_base].
           rewrite (HNA E' (agree_refl _ _)), Hw64. lia.
        -- destruct piece; [|constructor]. constructor; [|constructor]. right. rewrite (HszP E' (agree_refl _ _)). cbn [rg_base].
           fold (uE E' (NP (s_next L))). rewrite (HNP E' (agree_refl _ _)), Hw64.
           assert ((bv_unsigned a + nZ) / 8 <= TOPW / 8) by (apply Z.div_le_mono; [lia | exact Hhi]).
           unfold TOPW, SH_OFF in *. lia.
      * apply (proj1 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha)). exact Ho.
    + intros w Hw Ho. rewrite fresh_full_mem. rewrite fresh_mem_out; [reflexivity|].
      rewrite HnZw, fg64 by (unfold two64; lia). lia.
  - rom_tac.
  - apply (own_keep2 mem0 E E' L (null_postS L ln lo hi vis piece) M M' ms _ model model' Hwf Ha eq_refl); [| | exact Hown].
    + intros w Hop Ho. unfold outside in Ho. cbn [null_postS s_rgs] in Ho. apply Forall_app in Ho as [_ Ho]. split.
      * apply (proj2 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha)). exact Ho.
      * rewrite fresh_full_mem. apply fresh_mem_out. rewrite HnZw. exact (Hav w Hop).
    + intros w Hop Hv. unfold H', Hof. rewrite Hlz', HA'. apply mkH_grow; [exact Hv|].
      intros Hp. destruct (mmap_noreserve_b flags); [|discriminate]. rewrite Hli in Hp. apply page_in_one in Hp.
      rewrite HnZw in Hp. exact (Hav w Hop Hp).
  - exact Hblob'.
Qed.
End NullPostS.

(* [comment removed for export] *)
Definition null_okS (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (k : gkind) (vis piece na : bool) : bool :=
  let fs := s_facts L in let ln := rget (s_regs L) (rkey a1r) in let '(lo, hi) := irange fs ln in
  match a7c L, arg L 0, arg L 2, arg L 3, arg L 5 with
  | Some c7, Some c0, Some prot, Some flags, Some off =>
      (Z.eqb c7 222 && Z.eqb c0 0 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) &&
       Z.ltb 0 lo && Z.ltb hi 0x800000000000 && Z.leb 12 (lalign fs ln) && lwf (s_next L) ln &&
       (if na then negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
                   && mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       shadow_ok M && (negb piece || zr_ok M) &&
       gkind_eqb k (if na then GN else if mmap_noreserve_b (Z_to_bv 64 flags) then GL else GE) && (negb vis || negb na) &&
       (page_size + ledger_size res + gsize_sum fs (sm_maps M) + (Z.of_nat (length res + length (sm_maps M)) + mark_len fs (sm_maps M)) * (hi + page_size) + hi
          <=? 0x7fff7f800000) &&
       (eager_sum fs ((NA (s_next L), ln, k) :: sm_maps M) + allow_bound (null_allowS (s_next L) hi k vis piece ++ sm_allow M) <=? LIMIT))%bool
  | _, _, _, _, _ => false
  end.
Definition null_loS (L : sst) : Z := fst (irange (s_facts L) (rget (s_regs L) (rkey a1r))).
Definition null_hiS (L : sst) : Z := snd (irange (s_facts L) (rget (s_regs L) (rkey a1r))).

Section NullNodeS.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hsegb Hoff"] Theorem den_nullS : forall E L M ms model T k vis piece na,
  DEN segs LIMIT model0 mem0 E L M ms model ->
  null_okS (segments_reserved segs) LIMIT L M k vis piece na = true ->
  (forall a : word, place_ok model (uE E (rget (s_regs L) (rkey a1r))) a ->
     own_avoid E M (bv_unsigned a) (bv_unsigned a + uE E (rget (s_regs L) (rkey a1r))) /\
     (piece = true -> own_avoid E M (bv_unsigned a / 8 + SH_OFF) ((bv_unsigned a + uE E (rget (s_regs L) (rkey a1r))) / 8 + SH_OFF))) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (null_postS L (rget (s_regs L) (rkey a1r)) (null_loS L) (null_hiS L) vis piece)
                            (null_MS M (s_next L) (rget (s_regs L) (rkey a1r)) (null_hiS L) k vis piece) ms' model' ->
      agree (s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T k vis piece na Hd Hok Havoid Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  unfold null_okS, null_loS, null_hiS in *. set (ln := rget (s_regs L) (rkey a1r)) in *.
  destruct (irange (s_facts L) ln) as [lo hi] eqn:Hir. cbn [fst snd] in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg L 2) as [prot|] eqn:H2; [|discriminate].
  destruct (arg L 3) as [flags|] eqn:H3; [|discriminate]. destruct (arg L 5) as [off|] eqn:H5; [|discriminate].
  repeat (apply andb_prop in Hok as [Hok ?]).
  match goal with H : (_ <=? LIMIT) = true |- _ => apply Z.leb_le in H; rename H into Hbud end.
  match goal with H : (_ <=? 0x7fff7f800000) = true |- _ => apply Z.leb_le in H; rename H into Hex end.
  match goal with H : (hi <? 0x800000000000) = true |- _ => apply Z.ltb_lt in H; rename H into Hhi47 end.
  match goal with H : (0 <? lo) = true |- _ => apply Z.ltb_lt in H; rename H into Hlo0 end.
  match goal with H : (12 <=? lalign (s_facts L) ln) = true |- _ => apply Z.leb_le in H; rename H into Hal12 end.
  match goal with H : lwf (s_next L) ln = true |- _ => rename H into Hwln end.
  apply Z.eqb_eq in Hok. subst c7.
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E (s_facts L) ln HF0) as Ir. rewrite Hir in Ir. cbn [fst snd] in Ir.
  set (nZ := uE E ln) in *.
  assert (Hlh : lo <= nZ <= hi) by (unfold nZ, uE; exact Ir).
  assert (Hnal : nZ mod 4096 = 0).
  { pose proof (lalign_sound E (s_facts L) ln HF0) as [_ Hd4]. unfold nZ, uE.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ lalign (s_facts L) ln)); [|exact Hd4].
    replace (2 ^ lalign (s_facts L) ln) with (2 ^ 12 * 2 ^ (lalign (s_facts L) ln - 12)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    exists (2 ^ (lalign (s_facts L) ln - 12)). ring. }
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg1 : ms_gpr ms1 1 = lden E ln) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  assert (HnZ : page_round_up_Z (bv_unsigned (lden E ln)) = nZ) by (fold (uE E ln); fold nZ; apply page_round_aligned; [lia | exact Hnal]).
  assert (Hnz0 : w_is0 (lden E ln) = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq. fold (uE E ln). fold nZ. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
  assert (HnZpos : 0 < nZ) by lia.
  assert (Hbud0 : vm_backing_used model + (if gkind_eqb k GE then nZ else 0) <= LIMIT).
  { pose proof (den_backing_le segs LIMIT model0 mem0 E L M ms model (s_facts L) Hd HF0) as Hv.
    assert (Hnan : Forall (fun p => 0 <= snd p) (null_allowS (s_next L) hi k vis piece)).
    { unfold null_allowS. apply Forall_app. split.
      - destruct (vis && gkind_eqb k GL)%bool; [apply Forall_cons; [cbn; lia | apply Forall_nil] | apply Forall_nil].
      - destruct piece; [apply Forall_cons; [cbn [snd]; apply Z.div_pos; lia | apply Forall_nil] | apply Forall_nil]. }
    pose proof (allow_bound_app _ (sm_allow M) Hnan) as Hab. cbn [eager_sum fold_right fst snd] in Hbud. fold (eager_sum (s_facts L) (sm_maps M)) in Hbud.
    assert (Hhi0 : nZ <= gsz_hi (s_facts L) (NA (s_next L), ln, k)).
    { pose proof (gsz_bounds E (s_facts L) (NA (s_next L), ln, k) HF0) as Gb. unfold gsz in Gb. cbn [fst snd] in Gb. fold nZ in Gb. lia. }
    destruct (gkind_eqb k GE); lia. }
  assert (Hex' : page_size + ledger_size (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))
                 + Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) * (nZ + page_size) + nZ
                 <= alloc_top (m_vmmaps model)).
  { rewrite ledger_size_app, length_app, Hres, Hmaps.
    destruct (ledger_lden_bounds E model (s_facts L) _ _ HF0 Hgsh (proj1 Hblob) (proj2 (proj2 Hblob))) as [Hls Hln].
    pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn.
    rewrite Nat2Z.inj_add in *.
    assert ((Z.of_nat (length (segments_reserved segs)) + Z.of_nat (length (lden_maps E (blob_of model0) (sm_maps M)))) * (nZ + page_size)
            <= (Z.of_nat (length (segments_reserved segs)) + Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * (hi + page_size))
      by (unfold page_size; nia).
    destruct Hspok as [Hsp1 _]. unfold init_sp_ok, sp_window_lo in Hsp1. unfold alloc_top, stack_max_size. lia. }
  assert (Hkk : k = (if na then GN else if mmap_noreserve_b (Z_to_bv 64 flags) then GL else GE)).
  { match goal with H : gkind_eqb k _ = true |- _ => destruct k, na, (mmap_noreserve_b (Z_to_bv 64 flags)); try discriminate; reflexivity end. }
  assert (Hvn : vis = true -> na = false).
  { intros Hv. match goal with H : (negb vis || negb na)%bool = true |- _ => rewrite Hv in H; destruct na; [discriminate | reflexivity] end. }
  assert (Hsh' : shadow_ok M = true) by assumption.
  assert (Hzr' : piece = true -> zr_ok M = true).
  { intros Hp. match goal with H : (negb piece || zr_ok M)%bool = true |- _ => rewrite Hp in H; exact H end. }
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  destruct na.
  - (* [comment removed for export] *)
    match goal with H : (negb (mmap_modeled_b _ _ _) && mmap_noaccess_b _ _ _)%bool = true |- _ => apply andb_prop in H as [Hm Hna0] end.
    apply negb_true_iff in Hm.
    apply (rzc_mmap_fresh_na segs cfg Hoff ms1 model (ms_reg ms 17) T Hh Hsvc Hno); rewrite ?Hg1, ?Hg2, ?Hg3, ?Hg5; try assumption.
    + rewrite HnZ. exact (place_ok_exists model nZ HnZpos Hex').
    + intros a Hplace. rewrite HnZ in Hplace |- *.
      apply (Hk _ _ _ (null_denS segs LIMIT model0 mem0 Hsegb E L M ms model ln lo hi k vis piece (Z_to_bv 64 flags) true a Hd Hwln Hlh Hlo0 Hhi47
                          Hnal Hplace Hsh' Hzr' Hkk Hvn Hbud (proj1 (Havoid a Hplace)) (proj2 (Havoid a Hplace)))).
      exact (agree3_0 (s_next L) E _ _ _).
  - (* [comment removed for export] *)
    apply (rzc_mmap_fresh_rw segs cfg Hoff ms1 model (ms_reg ms 17) T Hh Hsvc Hno); rewrite ?Hg1, ?Hg2, ?Hg3, ?Hg5; try assumption.
    + rewrite HnZ. apply (fresh_rw_guard_exists (Z_to_bv 64 flags) model nZ HnZpos); [|exact Hex'].
      unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b (Z_to_bv 64 flags)) eqn:Hnr; [reflexivity|].
      apply Z.leb_le. rewrite Hlim. rewrite Hkk in Hbud0; rewrite ?Hnr in Hbud0. cbn in Hbud0. lia.
    + intros a Hg. rewrite HnZ in Hg |- *. apply fresh_rw_guard_iff in Hg as [Hplace _].
      apply (Hk _ _ _ (null_denS segs LIMIT model0 mem0 Hsegb E L M ms model ln lo hi k vis piece (Z_to_bv 64 flags) false a Hd Hwln Hlh Hlo0 Hhi47
                          Hnal Hplace Hsh' Hzr' Hkk Hvn Hbud (proj1 (Havoid a Hplace)) (proj2 (Havoid a Hplace)))).
      exact (agree3_0 (s_next L) E _ _ _).
Qed.
End NullNodeS.
End FxChNullS.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition add_rgs (a : lin) (n : Z) (pc : option lin) : list region :=
  RGz a n RZ TEmpty :: match pc with Some P => [RGz P (n / 8) RZ TEmpty] | None => [] end.
Definition add_post (S : sst) (a : lin) (n : Z) (pc : option lin) : sst :=
  SST (s_pc S) (s_regs S) (add_rgs a n pc ++ s_rgs S) (s_facts S) (s_next S) (s_resv S).
Definition add_M (M : smodel) (n : Z) (pc : option lin) : smodel :=
  SM (sm_maps M) (match pc with Some P => [(P, n / 8)] | None => [] end ++ sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

Section Add.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_add : forall E S M ms model (a : lin) (n : Z) (pc : option lin),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) a = true -> 0 < n -> n mod 4096 = 0 -> uE E a mod 4096 = 0 -> uE E a + n <= 0x800000000000 ->
  (forall x, uE E a <= x < uE E a + n -> covered (vm_maps (m_vmmaps model)) x = true /\ in_shadow x = false) ->
  (forall x, uE E a <= x < uE E a + n -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ Hof E M model (Z_to_bv 64 x) = false) ->
  (forall R, In R (s_rgs S) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n)) ->
  (forall P, pc = Some P -> lwf (s_next S) P = true /\ uE E P = uE E a / 8 + SH_OFF /\
     (forall y, uE E P <= y < uE E P + n / 8 -> in_shadow y = true /\ in_zr (sm_zr M) y = true /\ covered (vm_maps (m_vmmaps model)) y = true) /\
     (forall R, In R (s_rgs S) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E P <= w < uE E P + n / 8))) ->
  eager_sum (s_facts S) (sm_maps M) + allow_bound (sm_allow (add_M M n pc)) <= LIMIT ->
  (forall P, pc = Some P -> own_avoid E M (uE E P) (uE E P + n / 8)) ->
  (forall P, pc = Some P -> forall y, uE E P <= y < uE E P + n / 8 -> ~ blob_sh (blob_of model0) y) ->    (* [comment removed for export] *)
  DEN segs LIMIT model0 mem0 E (add_post S a n pc) (add_M M n pc) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a n pc Hd Hwa HnZ Hnal Hal Htop Happ Hz Hsep Hpc Hbud Hpav Hpnb.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := add_M M n pc).
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model).
  assert (HA' : allowA E M' = List.map (allow1 E) (match pc with Some P => [(P, n / 8)] | None => [] end) ++ allowA E M)
    by (unfold allowA, M', add_M; cbn [sm_allow]; apply map_app).
  assert (HH' : forall w, H w = false -> H' w = false).
  { intros w Hw. unfold H', Hof. rewrite HA'. unfold H, Hof in Hw. unfold mkH in *.
    destruct (page_in_ranges (page_base w) (m_vm_lazy model)); [|reflexivity]. cbn [andb] in *.
    apply negb_false_iff in Hw. apply negb_false_iff. apply page_allowedb_app_r. exact Hw. }
  pose proof (u_lt (lden E a)) as Ra.
  assert (Hn64 : 0 <= n < two64) by (unfold uE, two64 in *; lia).
  assert (Hn864 : 0 <= n / 8 < two64) by (split; [apply Z.div_pos; lia | assert (n / 8 <= n) by (apply Z.div_le_upper_bound; lia); lia]).
  assert (Hpc' : forall P y, pc = Some P -> uE E P <= y < uE E P + n / 8 -> H' (Z_to_bv 64 y) = false).
  { intros P y HP Hy. unfold H', Hof. rewrite HA'. apply mkH_allowed. rewrite HP. cbn [List.map].
    change ([allow1 E (P, n / 8)] ++ allowA E M) with ([allow1 E (P, n / 8)] ++ allowA E M). apply page_allowedb_app_l.
    apply allow1_covers; [|exact Hy]. destruct (Hpc P HP) as (_ & HP1 & _). rewrite HP1 in Hy.
    assert (uE E a / 8 <= uE E a) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, uE, two64 in *. lia. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs S) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  assert (Ha8 : uE E a = 8 * (uE E a / 8)).
  { assert (uE E a mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (uE E a / 4096 * 512); pose proof (Z.div_mod (uE E a) 4096 ltac:(lia)); lia).
    pose proof (Z.div_mod (uE E a) 8 ltac:(lia)). lia. }
  assert (Hn8 : n = 8 * (n / 8)).
  { assert (n mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (n / 4096 * 512); pose proof (Z.div_mod n 4096 ltac:(lia)); lia).
    pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
  (* [comment removed for export] *)
  assert (Hpt : forall R, In R (s_rgs S) -> forall i, 0 <= i < rsz E R ->
             mrestrict H' (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. rewrite Forall_forall in HG0. pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    unfold mrestrict. rewrite Hv, (HH' _ Hv). reflexivity. }
  assert (Hsden : sden segs E (add_post S a n pc) (restrict H' ms)).
  { intros E'' Ha''. cbn [add_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs S) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    assert (HaE : uE E'' a = uE E a) by (unfold uE; rewrite (lden_agree_wf _ E E'' a Hwa Ha''); reflexivity).
    unfold sden0, add_post. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    - apply Forall_app. split.
      + unfold add_rgs. constructor.
        * apply rg_ok_fresh_rz; [exact Hn64 | rewrite HaE; unfold two64; lia|]. intros i Hi. rewrite HaE. cbn [restrict ms_mem].
          destruct (Hz (uE E a + i) ltac:(lia)) as [Hz1 Hz2]. unfold mrestrict. rewrite (HH' _ Hz2). exact Hz1.
        * destruct pc as [P|]; [|constructor]. constructor; [|constructor].
          destruct (Hpc P eq_refl) as (HwP & HP1 & HP2 & HP3).
          assert (HPE : uE E'' P = uE E P) by (unfold uE; rewrite (lden_agree_wf _ E E'' P HwP Ha''); reflexivity).
          apply rg_ok_fresh_rz; [exact Hn864 | rewrite HPE, HP1; assert (uE E a / 8 <= uE E a) by (apply Z.div_le_upper_bound; lia);
                                                unfold SH_OFF, two64 in *; lia|].
          intros i Hi. rewrite HPE. cbn [restrict ms_mem]. unfold mrestrict.
          rewrite (Hpc' P (uE E P + i) eq_refl ltac:(lia)).
          destruct (HP2 (uE E P + i) ltac:(lia)) as (Hsh & Hzr' & _).
          assert (Hy64 : 0 <= uE E P + i < two64) by (rewrite HP1; assert (uE E a / 8 <= uE E a) by (apply Z.div_le_upper_bound; lia);
                                                      pose proof (Z.div_pos (uE E a) 8 ltac:(unfold uE; lia) ltac:(lia)); unfold SH_OFF, two64 in *; lia).
          apply Hzr; [exact Hzr'| |exact (own_avoid_pt E M _ _ _ (Hpav P eq_refl) Hy64 ltac:(lia)) | exact (Hpnb P eq_refl (uE E P + i) ltac:(lia))].
          unfold outside. apply Forall_forall. intros R HR'. rewrite fg64 by exact Hy64.
          destruct (Hrgw R HR') as [Hw1 Hw2]. pose proof (HP3 R HR' (uE E P + i)) as Hnot.
          destruct (Z_lt_le_dec (uE E P + i) (bv_unsigned (lden E (rg_base R)))) as [Hlt|Hge]; [left; exact Hlt|].
          destruct (Z_lt_le_dec (uE E P + i) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [Hlt2|Hge2]; [|right; exact Hge2].
          exfalso. apply Hnot; [unfold uE in *; lia | lia].
      + apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
        intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. exact (Hpt R HR' i Hi).
    - apply rgs_disj_app; [| exact HD |].
      + unfold add_rgs. destruct pc as [P|]; cbn [app rgs_disj]; [|split; [apply Forall_nil | exact I]].
        destruct (Hpc P eq_refl) as (HwP & HP1 & HP2 & HP3).
        assert (HPE : uE E'' P = uE E P) by (unfold uE; rewrite (lden_agree_wf _ E E'' P HwP Ha''); reflexivity).
        split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
        unfold rg_disj. cbv zeta. rewrite (rsz_RGz E'' _ _ _ _ Hn64), (rsz_RGz E'' _ _ _ _ Hn864). unfold RGz. cbn [rg_base].
        change (bv_unsigned (lden E'' a)) with (uE E'' a). change (bv_unsigned (lden E'' P)) with (uE E'' P). rewrite HaE, HPE.
        apply iv_pts_disj; [lia | apply Z.div_str_pos; lia|]. intros w Hw1 Hw2.
        destruct (Happ w Hw1) as [_ Hns]. destruct (HP2 w Hw2) as (Hs & _). rewrite Hs in Hns. discriminate.
      + intros R1 R2 H1 H2. unfold rg_disj. cbv zeta.
        change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)). rewrite (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
        pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
        unfold add_rgs in H1. destruct H1 as [<-|H1].
        * rewrite (rsz_RGz E'' _ _ _ _ Hn64). unfold RGz. cbn [rg_base]. change (bv_unsigned (lden E'' a)) with (uE E'' a). rewrite HaE.
          apply iv_pts_disj; [lia | lia|]. intros w Hw1 Hw2. exact (Hsep R2 H2 w Hw2 Hw1).
        * destruct pc as [P|]; [|destruct H1]. destruct H1 as [<-|[]].
          destruct (Hpc P eq_refl) as (HwP & HP1 & HP2 & HP3).
          assert (HPE : uE E'' P = uE E P) by (unfold uE; rewrite (lden_agree_wf _ E E'' P HwP Ha''); reflexivity).
          rewrite (rsz_RGz E'' _ _ _ _ Hn864). unfold RGz. cbn [rg_base]. change (bv_unsigned (lden E'' P)) with (uE E'' P). rewrite HPE.
          apply iv_pts_disj; [apply Z.div_str_pos; lia | lia|]. intros w Hw1 Hw2. exact (HP3 R2 H2 w Hw2 Hw1). }
  assert (Hnan : Forall (fun p => 0 <= snd p) (match pc with Some P => [(P, n / 8)] | None => [] end)).
  { destruct pc; [apply Forall_cons; [cbn [snd]; apply Z.div_pos; lia | apply Forall_nil] | apply Forall_nil]. }
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')) by (cbn [sm_allow M' add_M]; apply Forall_app; split; assumption).
  constructor.
  - exact Hsden.
  - cbn [add_post s_next]. unfold M', add_M, sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_own] in *.
    rewrite forallb_app. destruct pc as [P|]; [|exact Hwf]. destruct (Hpc P eq_refl) as (HwP & _). cbn [forallb fst]. rewrite HwP. exact Hwf.
  - cbn [add_post s_next s_rgs]. unfold bases_wf. rewrite forallb_app. apply andb_true_intro. split; [|exact Hbw].
    unfold add_rgs, RGz. destruct pc as [P|]; cbn [forallb rg_base rg_size app]; rewrite Hwa, lwf_lconst; [|reflexivity].
    destruct (Hpc P eq_refl) as (HwP & _). rewrite HwP, lwf_lconst. reflexivity.
  - exact Hh.
  - rewrite HA'. unfold A_wf. apply Forall_app. split; [exact (A_wf_map_allow1 E _ Hnan) | exact Hawf].
  - exact Hanz'.
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; try assumption.
    + intros p Hp. unfold AM. rewrite HA', <- app_assoc. apply page_allowedb_app_r. exact (N3 p Hp).
    + assert (HFL : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
      pose proof (eager_le E M model (s_facts S) _ HFL Hmaps Hgsh Hkind Hblob) as He. pose proof (A_bytes_allowA E M' Hanz') as Hb.
      rewrite Hlim. unfold AM. rewrite A_bytes_app. unfold M' in Hb |- *. cbn [sm_allow add_M] in Hb, Hbud. lia.
  - intros w Hw. apply Hhoff. change (Hof E M' model w = true) in Hw. fold H' in Hw. destruct (H w) eqn:Hh0; [reflexivity|]. rewrite (HH' w Hh0) in Hw. discriminate.
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. cbn [add_post s_rgs] in Hout. unfold outside in Hout. apply Forall_app in Hout as [_ Hout].
    exact (Hzr w Hw Hout (own_pt_keep _ E E M M' w Hwf (agree_refl _ _) eq_refl Hnow) Hnb).
  - cbn [add_post s_rgs]. apply Forall_app. split; [|exact Hrl]. unfold add_rgs. constructor.
    + unfold rl_ok. rewrite (rsz_RGz E _ _ _ _ Hn64). unfold RGz. cbn [rg_base]. split; [exact HnZ|]. left. intros w Hw.
      destruct (Happ w Hw) as [Hc Hns]. split; [left; rewrite covered_app, Hc, orb_true_r; reflexivity|]. split; [exact Hns | lia].
    + destruct pc as [P|]; [|constructor]. constructor; [|constructor]. destruct (Hpc P eq_refl) as (HwP & HP1 & HP2 & HP3).
      unfold rl_ok. rewrite (rsz_RGz E _ _ _ _ Hn864). unfold RGz. cbn [rg_base]. split; [apply Z.div_str_pos; lia|]. right.
      rewrite HP1. split; [pose proof (Z.div_pos (uE E a) 8 ltac:(unfold uE; lia) ltac:(lia)); lia|]. split.
      * intros x Hx. replace (8 * (uE E a / 8 + SH_OFF - SH_OFF)) with (uE E a) in Hx by lia.
        replace (8 * (uE E a / 8 + SH_OFF - SH_OFF + n / 8)) with (uE E a + n) in Hx by lia.
        destruct (Happ x Hx) as [Hc Hns]. split; [left; rewrite covered_app, Hc, orb_true_r; reflexivity|]. split; [exact Hns | lia].
      * intros w Hw. rewrite <- HP1 in Hw. destruct (HP2 w Hw) as (Hs & _ & Hc). split; [exact Hs | exact Hc].
  - exact Hvmo.
  - exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    apply (frz_keep mem0 E E S (add_post S a n pc) M M' ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [add_post s_rgs]. apply Forall_app. split; [|exact Ho].
      assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia). rewrite Hw64.
      unfold add_rgs. constructor.
      * right. rewrite (rsz_RGz E _ _ _ _ Hn64). unfold RGz. cbn [rg_base]. fold (uE E a).
        pose proof (covered_below_top segs LIMIT model0 mem0 E S M ms model (uE E a + n - 1) Hd (proj1 (Happ (uE E a + n - 1) ltac:(lia)))). lia.
      * destruct pc as [P|]; [|constructor]. constructor; [|constructor]. right. rewrite (rsz_RGz E _ _ _ _ Hn864). unfold RGz. cbn [rg_base].
        destruct (Hpc P eq_refl) as (HwP & HP1 & HP2 & HP3). fold (uE E P).
        assert (Hn8x : 1 <= n / 8) by (apply Z.div_le_lower_bound; [lia|]; pose proof (Z.mod_pos_bound n 4096 ltac:(lia)); pose proof (Z.div_mod n 4096 ltac:(lia)); nia).
        pose proof (proj1 (HP2 (uE E P + n / 8 - 1) ltac:(lia))) as Hs.
        unfold in_shadow, SH_HI in Hs. apply andb_prop in Hs as [_ Hs]. apply Z.ltb_lt in Hs. lia.
    + intros w _ _. reflexivity.
  - rom_tac.
  - apply (own_keep mem0 E E S (add_post S a n pc) M M' ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho. unfold outside in Ho. cbn [add_post s_rgs] in Ho. apply Forall_app in Ho as [_ Ho]. exact Ho.
    + intros w _. reflexivity.
    + intros x Hx. exact (HH' x Hx).
  - exact (blob_ok_same E M M' model model _ eq_refl eq_refl Hblob).
Qed.
End Add.

(* [comment removed for export] *)
Definition drop_post (S : sst) (f : region -> bool) : sst :=
  SST (s_pc S) (s_regs S) (List.filter (fun R => negb (f R)) (s_rgs S)) (s_facts S) (s_next S) (s_resv S).

Lemma rgs_disj_filter : forall E f rgs, rgs_disj E rgs -> rgs_disj E (List.filter f rgs).
Proof.
  intros E f rgs. induction rgs as [|R rs IH]; intros H; [exact I|]. destruct H as [H1 H2]. cbn [List.filter].
  destruct (f R); [|exact (IH H2)]. split; [|exact (IH H2)]. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  rewrite Forall_forall in H1. exact (H1 x Hx).
Qed.

Section Drop.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_drop_g : forall E S M ms model (f : region -> bool),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     in_zr (sm_zr M) w = true -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0) \/ blob_sh (blob_of model0) w) ->
  (forall R, In R (s_rgs S) -> f R = true -> own_avoid E M (uE E (rg_base R)) (uE E (rg_base R) + rsz E R)) ->
  DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hf Hfo.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  - intros E'' Ha''. cbn [drop_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0, drop_post. cbn [s_pc s_regs s_rgs s_facts s_resv]. repeat split; try assumption.
    + apply Forall_forall. intros R HR. apply filter_In in HR as [HR _]. rewrite Forall_forall in H5. exact (H5 R HR).
    + exact (rgs_disj_filter E'' _ _ H6).
  - unfold bases_wf in *. cbn [drop_post s_rgs s_next]. rewrite forallb_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hbw R HR).
  - intros w Hw Hout Hnow Hnb. cbn [drop_post s_rgs] in Hout.
    destruct (Z_lt_le_dec w 0) as [Hneg|Hnn].
    + pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO in Hs. apply andb_prop in Hs as [Hs _]. apply Z.leb_le in Hs. lia.
    + (* [comment removed for export] *)
      destruct (existsb (fun R => f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool (s_rgs S)) eqn:He.
      * apply existsb_exists in He as (R & HR & Hc). apply andb_prop in Hc as [HfR Hc]. apply andb_prop in Hc as [C1 C2].
        apply Z.leb_le in C1. apply Z.ltb_lt in C2. destruct (Hf R HR HfR w ltac:(lia) Hw) as [Hz|Hbs]; [exact Hz | exfalso; exact (Hnb Hbs)].
      * apply (Hzr w Hw); [|exact Hnow | exact Hnb]. unfold outside in *. apply Forall_forall. intros R HR. rewrite Forall_forall in Hout.
        destruct (f R) eqn:HfR.
        -- assert (Hc : (f R && (Z.leb (uE E (rg_base R)) w && Z.ltb w (uE E (rg_base R) + rsz E R)))%bool = false)
             by (apply not_true_iff_false; intros Hc'; rewrite (proj2 (existsb_exists _ _) (ex_intro _ R (conj HR Hc'))) in He; discriminate).
           rewrite HfR in Hc. cbn [andb] in Hc. pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_HI in Hs.
           apply andb_prop in Hs as [_ Hs]. apply Z.ltb_lt in Hs. rewrite fg64 by (unfold two64; lia).
           apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc; left; unfold uE in Hc; exact Hc | apply Z.ltb_ge in Hc; right; unfold uE in Hc; exact Hc].
        -- apply Hout. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
  - rewrite Forall_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hrl R HR).
  - apply (frz_keep mem0 E E S (drop_post S f) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho. unfold outside in *. cbn [drop_post s_rgs]. apply Forall_forall. intros R HR. apply filter_In in HR as [HR _].
      rewrite Forall_forall in Ho. exact (Ho R HR).
    + intros w _ _. reflexivity.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho. apply Hm.
    assert (Hop : own_pt E M w) by (exists q; split; assumption).
    unfold outside in *. cbn [drop_post s_rgs] in Ho. apply Forall_forall. intros R HR. rewrite Forall_forall in Ho.
    destruct (f R) eqn:HfR.
    + pose proof (Hfo R HR HfR w Hop) as Hna. unfold uE in Hna.
      destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) (bv_unsigned (lden E (rg_base R)))) as [Hlt|Hge]; [left; exact Hlt|]. right.
      destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [Hlt2|Hge2]; [exfalso; apply Hna; lia | exact Hge2].
    + apply Ho. apply filter_In. split; [exact HR | rewrite HfR; reflexivity].
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem den_drop : forall E S M ms model (f : region -> bool),
  DEN segs LIMIT model0 mem0 E S M ms model -> sm_own M = [] ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     in_zr (sm_zr M) w = true -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0)) ->
  DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hon Hf. apply (den_drop_g E S M ms model f Hd).
  - intros R HR HfR w Hw Hz. left. exact (Hf R HR HfR w Hw Hz).
  - intros R HR HfR. apply own_avoid_nil. exact Hon.
Qed.
End Drop.
