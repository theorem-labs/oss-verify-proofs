(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChAdd FxChStart FxChain FxChDir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxDirConv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxDropOwn.

Section ConvOwn.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
#[using="Type"] Theorem den_conv_rt_own : forall E S M ms model (f : region -> bool) (R0 : region) (fs : list fact) (pv sz : lin) (bs : list Z),
  DEN segs LIMIT model0 mem0 E S M ms model -> drop_own_ok S M f = true ->
  In R0 (s_rgs S) -> f R0 = true ->
  (forall R, In R (s_rgs S) -> f R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> in_shadow w = false) ->
  Forall (fun g => fwf (s_next S) g = true /\ fact_ok E g) fs ->
  lwf (s_next S) pv = true -> lwf (s_next S) sz = true -> 0 < uE E sz -> Z.of_nat (length bs) <= uE E sz ->
  Forall (fun b => 0 <= b < 256) bs ->
  uE E (sm_sp M) <= uE E pv ->
  (forall w, uE E pv <= w < uE E pv + uE E sz ->
     (exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p) /\ mem0 (Z_to_bv 64 w) <> None) \/
     uE E (rg_base R0) <= w < uE E (rg_base R0) + rsz E R0) ->
  (forall k, (k < length bs)%nat ->
     (exists p, In p (sm_frz M) /\ uE E (fst p) <= uE E pv + Z.of_nat k < uE E (fst p) + uE E (snd p)) /\
     mem0 (Z_to_bv 64 (uE E pv + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0))) ->
  DEN segs LIMIT model0 mem0 E (conv_post S f fs pv sz bs) (frz_clear M) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f R0 fs pv sz bs Hd Hon Hin Hf0 Hsh Hfs Hwv Hws Hsz Hlen Hbs Hsp Hpts Hby.
  assert (Hd1 : DEN segs LIMIT model0 mem0 E (drop_post S f) M ms model).
  { apply (den_drop_own segs LIMIT model0 mem0 E S M ms model f Hd (drop_own_sound segs LIMIT model0 mem0 E S M ms model f Hd Hon)).
    intros R HR HfR w Hw Hz. exfalso. pose proof (dn_zrsh _ _ _ _ _ _ _ _ _ Hd w Hz) as Hs.
    rewrite (Hsh R HR HfR w Hw) in Hs. discriminate. }
  assert (Hd2 : DEN segs LIMIT model0 mem0 E (add_facts (drop_post S f) fs) M ms model) by exact (den_add_facts segs LIMIT model0 mem0 fs E _ M ms model Hd1 Hfs).
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG0 & HD0 & _ & _).
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE.
  pose proof (dn_rl _ _ _ _ _ _ _ _ _ Hd) as Hrl.
  unfold conv_post.
  apply (den_mat_rt segs LIMIT model0 mem0 E _ M ms model pv sz bs Hd2); rewrite ?add_facts_next; cbn [drop_post s_next]; try assumption.
  - intros w Hw. rewrite add_facts_rgs. cbn [drop_post s_rgs].
    destruct (Hpts w Hw) as [(p & Hp & Hwp & Hm0)|HwR].
    + destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp w Hwp) as (Htop & Hout & _).
      split; [exact Htop|]. split.
      * unfold outside in *. rewrite Forall_forall in *. intros R HR. apply filter_In in HR as [HR _]. exact (Hout R HR).
      * unfold rd1. rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model w Hd (ex_intro _ p (conj Hp Hwp))).
        destruct (mem0 (Z_to_bv 64 w)) as [b|]; [discriminate | exact (fun _ => Hm0 eq_refl)].
    + rewrite Forall_forall in Hrl. destruct (Hrl R0 Hin) as [Hpos [Happ|(_ & _ & Hshw)]].
      2: { destruct (Hshw w HwR) as [Hs _]. rewrite (Hsh R0 Hin Hf0 w HwR) in Hs. discriminate. }
      destruct (Happ w HwR) as (_ & _ & Hw47).
      split; [|split].
      * split; [|lia]. unfold alloc_top, stack_max_size. rewrite HspE. fold (uE E (sm_sp M)). lia.
      * apply (outside_filter_R0 E f (s_rgs S) R0 w HD0 Hin Hf0 HwR). unfold two64. lia.
      * rewrite Forall_forall in HG0.
        pose proof (rg_ok_rd1 segs E _ R0 (w - uE E (rg_base R0)) (HG0 R0 Hin) ltac:(lia)) as Hr.
        replace (uE E (rg_base R0) + (w - uE E (rg_base R0))) with w in Hr by lia. exact Hr.
  - intros k Hk. destruct (Hby k Hk) as [Hcov Hm].
    unfold rd1. rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd Hcov). rewrite Hm. reflexivity.
Qed.
End ConvOwn.
