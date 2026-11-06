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

(* [comment removed for export] *)
Fixpoint add_facts (S : sst) (fs : list fact) : sst :=
  match fs with [] => S | f :: r => add_facts (add_fact S f) r end.
Lemma add_facts_next : forall fs S, s_next (add_facts S fs) = s_next S.
Proof. induction fs as [|f r IH]; intros S; cbn [add_facts]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma add_facts_rgs : forall fs S, s_rgs (add_facts S fs) = s_rgs S.
Proof. induction fs as [|f r IH]; intros S; cbn [add_facts]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition conv_post (S : sst) (f : region -> bool) (fs : list fact) (pv sz : lin) (bs : list Z) : sst :=
  mat_post2 (add_facts (drop_post S f) fs) pv sz bs.

Lemma conv_post_next : forall S f fs pv sz bs, s_next (conv_post S f fs pv sz bs) = s_next S.
Proof. intros S f fs pv sz bs. unfold conv_post, mat_post2. cbn [s_next]. rewrite add_facts_next. reflexivity. Qed.

Section Conv.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma den_add_facts : forall fs E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  Forall (fun g => fwf (s_next S) g = true /\ fact_ok E g) fs -> DEN segs LIMIT model0 mem0 E (add_facts S fs) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|g r IH]; intros E S M ms model Hd Hfs; cbn [add_facts]; [exact Hd|].
  inversion Hfs as [|? ? [Hw Hg] Hr]; subst.
  apply IH; [|exact Hr].
  apply den_addfact; [exact Hd|]. intros E' Ha. exact (fact_ok_agree _ E E' g Hw Ha Hg).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_rd1 : forall E m R i, rg_ok segs E m R -> 0 <= i < rsz E R ->
  rd1 segs m (Z_to_bv 64 (uE E (rg_base R) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (_ & _ & Hpts & _) Hi. specialize (Hpts i Hi). unfold uE.
  destruct (rg_kind R).
  all: first [ exact (proj1 Hpts) | exact (proj1 (proj1 Hpts)) | exact Hpts
             | (destruct Hpts as [H1 H2]; unfold rd1; rewrite H1; exact H2) ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_filter_R0 : forall E (f : region -> bool) rgs R0 w, rgs_disj E rgs -> In R0 rgs -> f R0 = true ->
  uE E (rg_base R0) <= w < uE E (rg_base R0) + rsz E R0 -> 0 <= w < two64 ->
  outside E (List.filter (fun R => negb (f R)) rgs) (Z_to_bv 64 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E f rgs R0 w. induction rgs as [|R rs IH]; intros Hdj Hin Hf Hw Hw64; [destruct Hin|].
  cbn [rgs_disj] in Hdj. destruct Hdj as [HR Hrs].
  assert (Hu : bv_unsigned (Z_to_bv 64 w) = w) by exact (u64_small w Hw64).
  unfold outside. rewrite Forall_forall. intros R' HR'. apply filter_In in HR' as [HR' Hf'].
  rewrite Hu. unfold uE in Hw. rewrite Forall_forall in HR.
  destruct Hin as [<-|Hin].
  - destruct HR' as [<-|HR']; [rewrite Hf in Hf'; discriminate|].
    specialize (HR R' HR'). unfold rg_disj in HR. lia.
  - destruct HR' as [<-|HR'].
    + specialize (HR R0 Hin). unfold rg_disj in HR. lia.
    + specialize (IH Hrs Hin Hf Hw Hw64). unfold outside in IH. rewrite Forall_forall in IH.
      assert (Hk : In R' (List.filter (fun R => negb (f R)) rs)) by (apply filter_In; split; assumption).
      specialize (IH R' Hk). rewrite Hu in IH. exact IH.
Qed.

#[using="Type"] Theorem den_conv_rt : forall E S M ms model (f : region -> bool) (R0 : region) (fs : list fact) (pv sz : lin) (bs : list Z),
  DEN segs LIMIT model0 mem0 E S M ms model -> sm_own M = [] ->
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
  { apply (den_drop segs LIMIT model0 mem0 E S M ms model f Hd Hon).
    intros R HR HfR w Hw Hz. exfalso. pose proof (dn_zrsh _ _ _ _ _ _ _ _ _ Hd w Hz) as Hs.
    rewrite (Hsh R HR HfR w Hw) in Hs. discriminate. }
  assert (Hd2 : DEN segs LIMIT model0 mem0 E (add_facts (drop_post S f) fs) M ms model) by exact (den_add_facts fs E _ M ms model Hd1 Hfs).
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
        pose proof (rg_ok_rd1 E _ R0 (w - uE E (rg_base R0)) (HG0 R0 Hin) ltac:(lia)) as Hr.
        replace (uE E (rg_base R0) + (w - uE E (rg_base R0))) with w in Hr by lia. exact Hr.
  - intros k Hk. destruct (Hby k Hk) as [Hcov Hm].
    unfold rd1. rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd Hcov). rewrite Hm. reflexivity.
Qed.
End Conv.
(* [comment removed for export] *)
