(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcPri AcHA AcSubst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lsubst_lconst_d : forall σ c, lsubst σ (lconst c) = lconst c.
Proof. intros σ c. unfold lsubst, lconst, laddc. cbn [l_c l_t tsubst]. f_equal. rewrite !w64_land. rewrite Z.add_0_l. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lsubst_laddc : forall σ l k, lsubst σ (laddc l k) = laddc (lsubst σ l) k.
Proof.
  intros σ l k. unfold lsubst, laddc. cbn [l_c l_t]. f_equal. rewrite !w64_mod.
  rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.
Lemma map_flat_map : forall {A B C} (f : B -> C) (g : A -> list B) l, List.map f (List.flat_map g l) = List.flat_map (fun x => List.map f (g x)) l.
Proof. intros A B C f g l. induction l as [|x r IH]; cbn; [reflexivity|]. rewrite map_app, IH. reflexivity. Qed.
Lemma pri_own_sub : forall σ a, List.map (ppsubst σ) (pri_own a) = pri_own (asubst σ a).
Proof.
  intros σ a. unfold pri_own. cbn [List.map]. unfold ppsubst at 1 2 3. cbn [fst snd]. rewrite !lsubst_lconst_d.
  unfold l_rip, l_cb, p_ca, p_sb. rewrite !lsubst_laddc, <- !p_nth_sub. f_equal. f_equal. f_equal.
  rewrite map_flat_map. apply flat_map_ext. intros c. unfold cls_own. cbn [List.map]. unfold ppsubst. cbn [fst snd].
  unfold l_rb, l_fa, l_shu, l_shf, p_z, p_sb, p_sh. rewrite !lsubst_laddc, !lsubst_lconst_d, <- !p_nth_sub. reflexivity.
Qed.
Theorem HA_subst_rev : forall E σ M a m0, HA (ecomp E σ) M a m0 -> HA E (msubst σ M) (asubst σ a) m0.
Proof.
  intros E σ M a m0 H Hon. rewrite asubst_on in Hon. specialize (H Hon). destruct H as [Hdep Hown Hownx Hhi Hg1 Hg2 Hpri].
  assert (E1 : dD1 E (asubst σ a) = dD1 (ecomp E σ) a) by (unfold dD1, asubst, ppsubst; cbn [a_dep fst]; symmetry; apply uE_sub).
  assert (E2 : dB1 E (asubst σ a) = dB1 (ecomp E σ) a) by (unfold dB1, asubst, ppsubst; cbn [a_dep snd]; symmetry; apply uE_sub).
  assert (E0 : uE E (a_nl (asubst σ a)) = uE (ecomp E σ) (a_nl a)) by (unfold asubst; cbn [a_nl]; symmetry; apply uE_sub).
  constructor; rewrite ?E1, ?E2, ?E0.
  - exact Hdep.
  - intros x Hx Hdw. apply own_pt_sub. exact (Hown x Hx Hdw).
  - change (a_own (asubst σ a)) with (List.map (ppsubst σ) (a_own a)). rewrite Hownx. unfold aown_of. rewrite map_app.
    assert (X1 : List.map (ppsubst σ) (own_of (fst (a_dep a)) (snd (a_dep a))) = own_of (fst (a_dep (asubst σ a))) (snd (a_dep (asubst σ a)))).
    { unfold own_of. cbn [List.map]. unfold ppsubst, asubst. cbn [a_dep fst snd]. rewrite !lsubst_lconst_d. reflexivity. }
    rewrite X1. f_equal.
    change (a_pri (asubst σ a)) with (List.map (lsubst σ) (a_pri a)). pose proof (pri_own_sub σ a) as X2.
    destruct (a_pri a) as [|l0 r0]; [reflexivity|]. cbn [List.map]. exact X2.
  - exact Hhi.
  - destruct Hg1 as (k & Hk). exists k. unfold msubst, asubst, ppsubst. cbn [sm_maps a_dep fst snd].
    change (lsubst σ (fst (a_dep a)), lconst 1048576, k) with (gsubst σ (fst (a_dep a), lconst 1048576, k)) at 1.
    apply in_map. exact Hk.
  - destruct Hg2 as (k & Hk). exists k. unfold msubst, asubst, ppsubst. cbn [sm_maps a_dep fst snd].
    change (lsubst σ (snd (a_dep a)), lconst 8388608, k) with (gsubst σ (snd (a_dep a), lconst 8388608, k)) at 1.
    apply in_map. exact Hk.
  - intros Hne. destruct (Hpri (proj1 (pri_nil_sub σ a) Hne)) as [Hi Hox (kp & Hp) (kt & Ht) Hz Hs Hxt Hlv Hsd]. constructor.
    + unfold INV_A. rewrite <- pden_sub. exact Hi.
    + intros x Hx Hf. apply own_pt_sub. apply (Hox x Hx). unfold pri_foot in *. rewrite pden_sub. exact Hf.
    + exists kp. unfold p_pg. rewrite p_nth_sub. unfold msubst. cbn [sm_maps].
      change (lsubst σ (p_nth a 3), lconst PG_SIZE, kp) with (lsubst σ (p_nth a 3), lconst PG_SIZE, kp).
      replace (lsubst σ (p_nth a 3), lconst PG_SIZE, kp) with (gsubst σ (p_nth a 3, lconst PG_SIZE, kp)) by (unfold gsubst; cbn [fst snd]; rewrite lsubst_lconst_d; reflexivity).
      apply in_map. exact Hp.
    + exists kt. unfold p_tg. rewrite p_nth_sub. unfold msubst. cbn [sm_maps].
      replace (lsubst σ (p_nth a 4), lconst TG_SIZE, kt) with (gsubst σ (p_nth a 4, lconst TG_SIZE, kt)) by (unfold gsubst; cbn [fst snd]; rewrite lsubst_lconst_d; reflexivity).
      apply in_map. exact Ht.
    + intros x Hx. apply Hz. unfold pri_shadow in *. rewrite pden_sub. exact Hx.
    + intros p Hpl. rewrite <- pden_sub. unfold asubst in Hpl. cbn [a_live] in Hpl. apply in_map_iff in Hpl as (q & <- & Hq).
      unfold ppsubst. cbn [fst snd]. rewrite <- !uE_sub. exact (Hs q Hq).
    + intros p Hpl. rewrite <- pden_sub. rewrite a_ext_sub in Hpl. apply in_map_iff in Hpl as (q & <- & Hq).
      unfold ppsubst. cbn [fst snd]. rewrite <- !uE_sub. exact (Hxt q Hq).
    + exact (proj2 (lv_inv_sub E σ a m0) Hlv).
    + intros p Hpl x Hx. rewrite E1, E2. unfold asubst in Hpl. cbn [a_live] in Hpl. apply in_map_iff in Hpl as (q & <- & Hq).
      unfold ppsubst in Hx. cbn [fst snd] in Hx. rewrite <- !uE_sub in Hx. exact (Hsd q Hq x Hx).
Qed.
