(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcConv AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcMALlib AcConvA AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.

Module AcPriGrant.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcDenW AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALlib AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma foot_not_virgin : forall pz m0 c, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) -> In c CLS -> z_z pz c = 0 ->
  forall x, pri_foot_z pz x ->
    ~ (z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + 262144) /\
    ~ (z_sb pz + 4294967296 * c + 3758096384 <= x < z_sb pz + 4294967296 * c + 3758096384 + 262144).
Proof.
  intros pz m0 c HI Hdisj Hc Hz x Hf. pose proof (az_geo pz m0 HI) as G. pose proof (in_cls_rng c Hc) as Hcr. unfold PG_SIZE in Hdisj.
  assert (S1 : z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
  destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [clear - Hf G Hdisj Hcr; lia | clear - Hf G Hcr; lia | clear - Hf G Hcr; lia|].
  pose proof (in_cls_rng c' Hc') as Hcr'.
  assert (Hz' : z_z pz c' = 0 \/ z_z pz c' = 262144) by (destruct (iz_cls _ _ HI c' Hc') as [(_ & Z0 & _)|(_ & Z1 & _)]; [left; exact Z0 | right; exact Z1]).
  destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite Hz in Hf; clear - Hf G S1 Hcr; lia|].
  clear - Hf G S1 Hcr Hcr' Hne Hz'. lia.
Qed.

Section PriGrant.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma pg_not_dcov : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> a_pri a <> [] ->
  forall x, z_pg (pden E a) <= x < z_pg (pden E a) + PG_SIZE -> ~ dcov (dD1 E a) (dB1 E a) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA Hne x Hx Hdc.
  pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh.
  pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd) as Hmres. pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd.
  destruct (ha_pri _ _ _ _ HA Hne) as [_ _ (kp & Hp) _ _ _ _].
  set (g := (p_pg a, lconst PG_SIZE, kp)) in *.
  assert (Hgm : is_mark g = false) by apply is_mark_csize.
  assert (Zpg : uE E (p_pg a) = z_pg (pden E a)) by (symmetry; apply zn_pden).
  assert (GP : gsz E g = PG_SIZE) by (unfold gsz, g; cbn [fst snd]; apply uE_lc; unfold PG_SIZE; lia).
  assert (Hin : uE E (fst (fst g)) <= x < uE E (fst (fst g)) + gsz E g) by (rewrite GP; unfold g; cbn [fst snd]; rewrite Zpg; exact Hx).
  assert (Hcg : covered (vm_maps (m_vmmaps model)) x = true) by exact (grant_covered E _ M model g Hmaps Hgsh Hp Hgm x Hin).
  destruct (dcov_covered LIMIT model0 mem0 E S M ms model a m0 Hd HA x Hdc) as [[_ Hc]|(g' & Hg' & Hin' & _ & _ & Hg'e)].
  - rewrite (Hmres x Hcg) in Hc. discriminate.
  - destruct (In_nth_error _ _ Hp) as (j & Hj). destruct (In_nth_error _ _ Hg') as (j' & Hj').
    assert (Hnj : j <> j').
    { intros Ejj. rewrite Ejj in Hj. assert (Egg : g' = g) by (rewrite Hj in Hj'; injection Hj' as X0; symmetry; exact X0). subst g'.
      destruct Hg'e as [E1|E1]; pose proof (f_equal (fun t => snd (fst t)) E1) as Q; unfold g in Q; cbn [fst snd] in Q; vm_compute in Q; discriminate Q. }
    assert (Hgm' : is_mark g' = false) by (destruct Hg'e as [E1|E1]; rewrite E1; apply is_mark_csize).
    assert (Hd' : iv_disj (gden E g) (gden E g')).
    { pose proof Hpd as Hpd2. rewrite Hmaps in Hpd2. exact (pdisj_lden_nth E _ _ j j' g g' Hpd2 Hj Hj' Hnj Hgm Hgm'). }
    rewrite Forall_forall in Hgsh. destruct (Hgsh g Hp) as (G1 & _ & _ & G4 & _). destruct (Hgsh g' Hg') as (G1' & _ & _ & G4' & _).
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd'. cbn [fst snd] in Hd'. unfold gsz, uE in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pg_not_frz : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> a_pri a <> [] ->
  forall x, z_pg (pden E a) <= x < z_pg (pden E a) + PG_SIZE -> ~ frz_pt E M x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA Hne x Hx (p & Hp & Hw).
  pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp x Hw) as (Htop & _ & _).
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgtop. rewrite Forall_forall in Hgtop.
  destruct (ha_pri _ _ _ _ HA Hne) as [_ _ (kp & Hgp) _ _ _ _].
  pose proof (Hgtop _ Hgp) as Ht. cbn [fst snd] in Ht.
  assert (Zpg : uE E (p_pg a) = z_pg (pden E a)) by (symmetry; apply zn_pden).
  assert (GP : gsz E (p_pg a, lconst PG_SIZE, kp) = PG_SIZE) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold PG_SIZE; lia).
  rewrite GP, Zpg in Ht. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma virgin_not_own : forall E S M ms model a, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  sm_own M = a_own a -> forall c, In c CLS -> z_z (pden E a) c = 0 ->
  forall w, own_pt E M w ->
    ~ (z_sb (pden E a) + 4294967296 * c <= w < z_sb (pden E a) + 4294967296 * c + 262144) /\
    ~ (z_sb (pden E a) + 4294967296 * c + 3758096384 <= w < z_sb (pden E a) + 4294967296 * c + 3758096384 + 262144).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a Hd HA Hne Hown c Hc Hz w Hw.
  pose proof (ha_pri _ _ _ _ HA Hne) as HP. pose proof (po_inv _ _ _ _ HP) as HI. unfold INV_A in HI.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP) as Hdisj.
  pose proof (az_geo _ _ HI) as G. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (ha_ownx _ _ _ _ HA w (own_pt_a_M E M a w Hown Hw)) as [Dc|[_ Pf]].
  - assert (Hn : ~ (z_pg (pden E a) <= w < z_pg (pden E a) + PG_SIZE)) by (intros Hx; exact (pg_not_dcov E S M ms model a mem0 Hd HA Hne w Hx Dc)).
    unfold PG_SIZE in Hn. clear - Hn G Hcr. lia.
  - exact (foot_not_virgin _ _ c HI Hdisj Hc Hz w Pf).
Qed.
End PriGrant.
End AcPriGrant.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a_with (a : ast) (pri' : list lin) : ast :=
  with_pri a (own_of (fst (a_dep a)) (snd (a_dep a)) ++ pri_own (with_pri a (a_own a) pri')) pri'.
Lemma pri_own_pri : forall a b, a_pri a = a_pri b -> pri_own a = pri_own b.
Proof.
  intros a b H. unfold pri_own, l_cb, l_rip, p_ca, p_sb, p_nth. rewrite H. f_equal. f_equal. f_equal. apply flat_map_ext. intros c.
  unfold cls_own, l_rb, l_fa, l_shu, l_shf, p_z, p_sb, p_sh, p_nth. rewrite H. reflexivity.
Qed.

Section PriHA.
Variables (n : positive) (E E' : valu) (M : smodel) (a : ast) (m0 m0' : word -> option byte) (pri' : list lin).
Hypothesis HA0 : HA_on E M a m0.
Hypothesis Hwf : sm_wf n M = true.
Hypothesis Haw : awf n a = true.
Hypothesis Ha : agree n E E'.
Hypothesis Hne : a_pri a <> [].
Hypothesis Hne' : pri' <> [].
Hypothesis Hown_eq : sm_own M = a_own a.
Let a' := a_with a pri'.
Let M' := with_own M (a_own a').
Hypothesis HI' : INV_Az (pden E' a') m0'.
Hypothesis Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0.
Hypothesis Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' a') x.
Hypothesis Hdep : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> m0' (wa x) = m0 (wa x).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' a') b z.
(* [comment removed for export] *)
Hypothesis Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> m0' (wa x) = m0 (wa x).

#[using="Type"] Lemma a_with_pri : a_pri a' = pri'.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma a_with_own : a_own a' = own_of (fst (a_dep a)) (snd (a_dep a)) ++ pri_own a'.
Proof. LiaFast.lf_pins LiaFast.u0. unfold a', a_with. cbn [with_pri a_own]. f_equal. Qed.

#[using="n m0 m0' HA0 Haw Ha Hne Hown_eq HI' Hbase Hmono"] Lemma own_pt_with : forall x, own_pt E M x -> own_pt E' M' x.
Proof. LiaFast.lf_pins (fun (n m0 m0' HA0 Haw Ha Hne Hown_eq HI' Hbase Hmono : LiaFast.U) => LiaFast.u0).
  intros x (p & Hp & Hx). rewrite Hown_eq, (ha_aown _ _ _ _ HA0) in Hp. unfold aown_of in Hp. apply in_app_or in Hp as [Hp|Hp].
  - exists p. split; [unfold M'; cbn [with_own sm_own]; rewrite a_with_own; apply in_or_app; left; exact Hp|].
    assert (Hpw : pwf n p = true).
    { pose proof Haw as X. unfold awf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X].
      rewrite forallb_forall in X. apply X. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hp. }
    unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite (uE_agree n E E' _ Hp1 Ha), (uE_agree n E E' _ Hp2 Ha). exact Hx.
  - assert (Hp' : In p (pri_own a)) by (destruct (a_pri a); [destruct Hp | exact Hp]).
    pose proof (pri_own_foot E a m0 (po_inv _ _ _ _ (ha_pri _ _ _ _ HA0 Hne)) p Hp' x Hx) as Hf.
    destruct (pri_foot_own E' a' m0' HI' x (Hmono x Hf)) as (q & Hq & Hqx).
    exists q. split; [unfold M'; cbn [with_own sm_own]; rewrite a_with_own; apply in_or_app; right; exact Hq | exact Hqx].
Qed.

#[using="Hbase"] Lemma p_nth_with : forall k, (k < 5)%nat -> p_nth a' k = p_nth a k.
Proof. LiaFast.lf_pins (fun (Hbase : LiaFast.U) => LiaFast.u0). intros k Hk. unfold p_nth. rewrite a_with_pri. exact (Hbase k Hk). Qed.

#[using="n E m0 HA0 Haw Ha Hne Hne' Hown_eq HI' Hbase Hmono Hdep Hext_step Hext_fr"] Theorem HA_pri_step : HA_on E' M' a' m0'.
Proof. LiaFast.lf_pins (fun (n E m0 HA0 Haw Ha Hne Hne' Hown_eq HI' Hbase Hmono Hdep Hext_step Hext_fr : LiaFast.U) => LiaFast.u0).
  pose proof HA0 as HA1. destruct HA1 as [Hdep0 Hown Hownx Hhi HgD HgB Hpri].
  pose proof (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv Hsd].
  assert (Hpw : pwf n (a_dep a) = true) by (pose proof Haw as X; unfold awf in X; apply andb_prop in X as [X _]; apply andb_prop in X as [X _]; apply andb_prop in X as [_ X]; exact X).
  unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2].
  assert (E1 : dD1 E' a' = dD1 E a) by (unfold dD1; exact (uE_agree n E E' _ Hp1 Ha)).
  assert (E2 : dB1 E' a' = dB1 E a) by (unfold dB1; exact (uE_agree n E E' _ Hp2 Ha)).
  assert (E0 : uE E' (a_nl a') = uE E (a_nl a)) by exact (uE_agree n E E' _ (awf_nl n a Haw) Ha).
  assert (Zsh : z_sh (pden E' a') = z_sh (pden E a)).
  { unfold z_sh. rewrite !zn_pden. rewrite (p_nth_with 1%nat ltac:(lia)). apply (uE_agree n E E'); [apply lwf_p_nth; exact (awf_pri n a Haw) | exact Ha]. }
  assert (Zpg : z_pg (pden E' a') = z_pg (pden E a)).
  { unfold z_pg. rewrite !zn_pden. rewrite (p_nth_with 3%nat ltac:(lia)). apply (uE_agree n E E'); [apply lwf_p_nth; exact (awf_pri n a Haw) | exact Ha]. }
  assert (Zca : z_ca (pden E' a') = z_ca (pden E a)).
  { unfold z_ca. rewrite !zn_pden. rewrite (p_nth_with 2%nat ltac:(lia)). apply (uE_agree n E E'); [apply lwf_p_nth; exact (awf_pri n a Haw) | exact Ha]. }
  constructor; rewrite ?E1, ?E2, ?E0.
  - destruct Hdep0 as (nd & F & st & I & R). exists nd, F, st. split; [exact (INV_D_frame _ _ _ _ _ _ _ I Hdep) | exact R].
  - intros x Hx Hdw. exact (own_pt_with x (Hown x Hx Hdw)).
  - rewrite a_with_own. unfold aown_of. change (a_dep a') with (a_dep a). rewrite a_with_pri. destruct pri' as [|l0 r0] eqn:Ep; [exfalso; exact (Hne' eq_refl) | reflexivity].
  - exact Hhi.
  - exact HgD.
  - exact HgB.
  - intros _. constructor.
    + exact HI'.
    + intros x Hx Hf. destruct (pri_foot_own E' a' m0' HI' x Hf) as (q & Hq & Hqx).
      exists q. split; [unfold M'; cbn [with_own sm_own]; rewrite a_with_own; apply in_or_app; right; exact Hq | exact Hqx].
    + unfold p_pg. rewrite (p_nth_with 3%nat ltac:(lia)). exact Hp.
    + unfold p_tg. rewrite (p_nth_with 4%nat ltac:(lia)). exact Ht.
    + intros x Hx. apply Hz. unfold pri_shadow in *. rewrite Zsh in Hx. exact Hx.
    + intros p Hp'. change (a_live a') with (a_live a) in Hp'.
      assert (Hpw : pwf n p = true).
      { pose proof Haw as X. unfold awf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. rewrite forallb_forall in X. exact (X p Hp'). }
      unfold pwf in Hpw. apply andb_prop in Hpw as [Hq1 Hq2]. rewrite (uE_agree n E E' _ Hq1 Ha), (uE_agree n E E' _ Hq2 Ha).
      destruct (Hs p Hp') as [S1 S2]. split; [exact S1|]. intros x Hx HF. apply (S2 x Hx). unfold FPmax in *. rewrite Zpg, Zca, Zsh in HF. exact HF.
    + intros p Hp'. change (a_ext a') with (a_ext a) in Hp'.
      destruct (awf_ext n a Haw p Hp') as [Hq1 Hq2]. rewrite (uE_agree n E E' _ Hq1 Ha), (uE_agree n E E' _ Hq2 Ha).
      exact (Hext_step _ _ (Hxt p Hp')).
    + apply (lv_inv_mono E E' a a' m0 m0'); [| | exact Hext_step | exact Hext_fr | exact Hlv].
      * intros i. change (lv_nth a' i) with (lv_nth a i). exact (uE_agree n E E' _ (awf_lv n a Haw i) Ha).
      * change (e_rngs E' a') with (e_rngs E' a). exact (e_rngs_agree n E E' a Haw Ha).
    + (* [comment removed for export] *)
      intros p Hp' x Hx. change (a_live a') with (a_live a) in Hp'. rewrite E1, E2.
      destruct (live_agree n E E' a p Haw Ha Hp') as [L1 L2]. rewrite L1, L2 in Hx. exact (Hsd p Hp' x Hx).
Qed.
End PriHA.
