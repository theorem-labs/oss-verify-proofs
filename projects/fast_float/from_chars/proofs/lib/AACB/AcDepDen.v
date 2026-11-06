(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA AcDenW.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma gq_res : in_res_b (segments_reserved ASEGS) 930696 930736 = true.
Proof. vm_compute. reflexivity. Qed.

Section DepDen.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_covered : forall E BL M model g, vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) -> Forall (gshape_ok E) (sm_maps M) ->
  In g (sm_maps M) -> is_mark g = false -> forall x, uE E (fst (fst g)) <= x < uE E (fst (fst g)) + gsz E g -> covered (vm_maps (m_vmmaps model)) x = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E BL M model g Hmaps Hgsh Hg Hgm x Hx. destruct (In_nth_error _ _ Hg) as (j & Hj).
  exact (grant_pts_covered E (sm_maps M) model BL Hmaps Hgsh j g (fst (fst g)) (gsz E g) Hj Hgm ltac:(lia) ltac:(lia) x Hx).
Qed.

#[using="Type"] Lemma downed_covered : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 ->
  forall x, downed (dD1 E a) (dB1 E a) x ->
    ((DT_LO <= x < DT_HI \/ DF_LO <= x < DF_HI) /\ covered (vm_reserved (m_vmmaps model)) x = true) \/
    (exists g, In g (sm_maps M) /\ uE E (fst (fst g)) <= x < uE E (fst (fst g)) + gsz E g /\ covered (vm_maps (m_vmmaps model)) x = true /\
       g <> (lc0, lc0, GE) /\ (g = (fst (a_dep a), lconst 1048576, snd g) \/ g = (snd (a_dep a), lconst 8388608, snd g))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA x Hx.
  pose proof (dn_res _ _ _ _ _ _ _ _ _ Hd) as Hres. pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh.
  destruct HA as [_ _ _ _ (k1 & Hg1) (k2 & Hg2)]. destruct (downed_cases _ _ x Hx) as [D|[D|[D|D]]].
  - left. split; [left; exact D|]. rewrite Hres. destruct dep_res as [R1 _]. exact (in_res_sound _ _ _ x R1 D).
  - left. split; [right; exact D|]. rewrite Hres. destruct dep_res as [_ R2]. exact (in_res_sound _ _ _ x R2 D).
  - right. exists (fst (a_dep a), lconst 1048576, k1). split; [exact Hg1|]. unfold dD1 in D. cbn [fst snd]. split; [exact D|].
    split; [exact (grant_covered E _ M model _ Hmaps Hgsh Hg1 (is_mark_csize _ _ _) x D)|]. split; [intros He; injection He; intros; discriminate|]. left; reflexivity.
  - right. exists (snd (a_dep a), lconst 8388608, k2). split; [exact Hg2|]. unfold dB1 in D. cbn [fst snd]. split; [exact D|].
    split; [exact (grant_covered E _ M model _ Hmaps Hgsh Hg2 (is_mark_csize _ _ _) x D)|]. split; [intros He; injection He; intros; discriminate|]. right; reflexivity.
Qed.
#[using="Type"] Lemma dcov_covered : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 ->
  forall x, dcov (dD1 E a) (dB1 E a) x ->
    ((DT_LO <= x < DT_HI \/ DF_LO <= x < DF_HI) /\ covered (vm_reserved (m_vmmaps model)) x = true) \/
    (exists g, In g (sm_maps M) /\ uE E (fst (fst g)) <= x < uE E (fst (fst g)) + gsz E g /\ covered (vm_maps (m_vmmaps model)) x = true /\
       g <> (lc0, lc0, GE) /\ (g = (fst (a_dep a), lconst 1048576, snd g) \/ g = (snd (a_dep a), lconst 8388608, snd g))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA x Hx.
  pose proof (dn_res _ _ _ _ _ _ _ _ _ Hd) as Hres. pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh.
  destruct HA as [_ _ _ _ (k1 & Hg1) (k2 & Hg2)]. unfold dcov in Hx. destruct Hx as [D|[D|[D|D]]].
  - left. split; [left; exact D|]. rewrite Hres. destruct dep_res as [R1 _]. exact (in_res_sound _ _ _ x R1 D).
  - left. split; [right; exact D|]. rewrite Hres. destruct dep_res as [_ R2]. exact (in_res_sound _ _ _ x R2 D).
  - right. exists (fst (a_dep a), lconst 1048576, k1). split; [exact Hg1|]. unfold dD1 in D. cbn [fst snd]. split; [exact D|].
    split; [exact (grant_covered E _ M model _ Hmaps Hgsh Hg1 (is_mark_csize _ _ _) x D)|]. split; [intros He; injection He; intros; discriminate|]. left; reflexivity.
  - right. exists (snd (a_dep a), lconst 8388608, k2). split; [exact Hg2|]. unfold dB1 in D. cbn [fst snd]. split; [exact D|].
    split; [exact (grant_covered E _ M model _ Hmaps Hgsh Hg2 (is_mark_csize _ _ _) x D)|]. split; [intros He; injection He; intros; discriminate|]. right; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dep_not_frz : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 ->
  forall x, downed (dD1 E a) (dB1 E a) x -> ~ frz_pt E M x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA x Hx (p & Hp & Hw).
  pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp x Hw) as (Htop & _ & _).
  pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Hlo.
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgtop. rewrite Forall_forall in Hgtop.
  destruct (downed_covered E S M ms model a m0 Hd HA x Hx) as [[[D|D] _]|(g & Hg & Hin & _ & _ & _)].
  - unfold DT_LO, DT_HI in D. lia.
  - unfold DF_LO, DF_HI in D. lia.
  - pose proof (Hgtop g Hg). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pri_cases : forall E M a m0, HA_on E M a m0 -> a_pri a <> [] -> forall x, pri_foot E a x ->
  (exists g, In g (sm_maps M) /\ is_mark g = false /\ uE E (fst (fst g)) <= x < uE E (fst (fst g)) + gsz E g /\ (fst (fst g) = p_pg a \/ fst (fst g) = p_tg a) /\ in_shadow x = false) \/
  (pri_shadow E a x /\ in_shadow x = true /\ exists g y, In g (sm_maps M) /\ is_mark g = false /\ fst (fst g) = p_pg a /\ uE E (fst (fst g)) <= y < uE E (fst (fst g)) + gsz E g /\
     y mod 8 = 0 /\ x = y / 8 + SH_OFF) \/
  930696 <= x < 930736.     (* [comment removed for export] *)
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M a m0 HA Hne x Hx. destruct (ha_pri _ _ _ _ HA Hne) as [[Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls] _ (kp & Hp) (kt & Ht) _].
  assert (Zpg : uE E (p_pg a) = z_pg (pden E a)) by (symmetry; apply zn_pden).
  assert (Ztg : uE E (p_tg a) = z_tg (pden E a)) by (symmetry; apply zn_pden).
  assert (GP : gsz E (p_pg a, lconst PG_SIZE, kp) = 137439023104) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold PG_SIZE; lia).
  assert (GT : gsz E (p_tg a, lconst TG_SIZE, kt) = 4096) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold TG_SIZE; lia).
  unfold PG_SIZE in Hpg. unfold pri_foot, pri_foot_z in Hx.
  assert (Hm8 : z_sb (pden E a) mod 8 = 0).
  { destruct Hsb as [_ Hm]. pose proof (Z.div_mod (z_sb (pden E a)) 4096 ltac:(lia)) as Ed. rewrite Hm, Z.add_0_r in Ed. rewrite Ed.
    replace (4096 * (z_sb (pden E a) / 4096)) with (512 * (z_sb (pden E a) / 4096) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Hd8 : z_sb (pden E a) = 8 * (z_sb (pden E a) / 8)) by (pose proof (Z.div_mod (z_sb (pden E a)) 8 ltac:(lia)) as Ed; lia).
  destruct Hx as [Hx|[Hx|[Hx|(c & Hc & Hx)]]]; [| | right; right; exact Hx |].
  - left. exists (p_tg a, lconst TG_SIZE, kt). split; [exact Ht|]. split; [apply is_mark_csize|]. cbn [fst snd]. rewrite GT, Ztg. split; [lia|]. split; [right; reflexivity|].
    unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. destruct Hnsh as [_ [Hn|Hn]]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
  - left. exists (p_pg a, lconst PG_SIZE, kp). split; [exact Hp|]. split; [apply is_mark_csize|]. cbn [fst snd]. rewrite GP, Zpg. split; [lia|]. split; [left; reflexivity|]. unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - pose proof (in_cls_rng c Hc) as Hcr.
    assert (Hz : z_z (pden E a) c = 0 \/ z_z (pden E a) c = 262144) by (destruct (Hcls c Hc) as [(_ & Z0 & _)|(_ & Z1 & _)]; lia).
    destruct Hx as [Hx|[Hx|Hx]].
    + left. exists (p_pg a, lconst PG_SIZE, kp). split; [exact Hp|]. split; [apply is_mark_csize|]. cbn [fst snd]. rewrite GP, Zpg. split; [lia|]. split; [left; reflexivity|]. unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
    + left. exists (p_pg a, lconst PG_SIZE, kp). split; [exact Hp|]. split; [apply is_mark_csize|]. cbn [fst snd]. rewrite GP, Zpg. split; [lia|]. split; [left; reflexivity|]. unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
    + right. left. split; [exists c; split; [exact Hc | exact Hx]|]. split; [unfold in_shadow, SH_LO, SH_HI; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
      exists (p_pg a, lconst PG_SIZE, kp), (8 * (x - SH_OFF)). split; [exact Hp|]. split; [apply is_mark_csize|]. split; [reflexivity|]. cbn [fst snd]. rewrite GP, Zpg.
      unfold SH_OFF in *. split; [lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
      rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.
#[using="Type"] Lemma pri_covered : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> a_pri a <> [] ->
  forall x, pri_foot E a x -> in_shadow x = false -> ~ (930696 <= x < 930736) -> covered (vm_maps (m_vmmaps model)) x = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA Hne x Hx Hns Hng.
  destruct (pri_cases E M a m0 HA Hne x Hx) as [(g & Hg & Hgm & Hin & _)|[(_ & Hsh & _)|Hgq]]; [|congruence|exfalso; exact (Hng Hgq)].
  exact (grant_covered E _ M model g (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_gsh _ _ _ _ _ _ _ _ _ Hd) Hg Hgm x Hin).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma pri_not_frz : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> a_pri a <> [] ->
  forall x, pri_foot E a x -> ~ frz_pt E M x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA Hne x Hx (p & Hp & Hw).
  pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp x Hw) as (Htop & _ & _).
  pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Hlo.
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgtop. rewrite Forall_forall in Hgtop.
  destruct (pri_cases E M a m0 HA Hne x Hx) as [(g & Hg & _ & Hin & _)|[(_ & Hsh & _)|Hgq]].
  - pose proof (Hgtop g Hg). lia.
  - unfold in_shadow, SH_HI in Hsh. apply andb_prop in Hsh as [_ H2]. apply Z.ltb_lt in H2. lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dep_avoid_place : forall E S M ms model a m0 nZ (ad : word), DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> sm_own M = a_own a ->
  place_ok model nZ ad -> 0 <= nZ < two64 -> own_avoid E M (bv_unsigned ad) (bv_unsigned ad + nZ).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 nZ ad Hd HA Hoa Hpl HnZ w Hw Hin.
  destruct Hpl as (_ & _ & _ & Hfree).
  assert (Hfr : forall y, bv_unsigned ad <= y < bv_unsigned ad + nZ -> covered (vm_reserved (m_vmmaps model)) y = false /\ covered (vm_maps (m_vmmaps model)) y = false).
  { intros y Hy. assert (Hnc : covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) y = false).
    { apply (region_free_pt _ ad (Z_to_bv 64 nZ)); [exact Hfree | rewrite u_small64 by exact HnZ; exact Hy]. }
    unfold covered in Hnc. rewrite existsb_app in Hnc. apply orb_false_iff in Hnc as [Hn1 Hn2]. split; assumption. }
  destruct (ha_ownx _ _ _ _ HA w (own_pt_a_M E M a w Hoa Hw)) as [Hdw0|[Hne Hpf]].
  - pose proof Hdw0 as Hdw. unfold dcov in Hdw.
    assert (Hw64 : 0 <= w < two64).
    { destruct HA as [(n & F & st & I & _) _ _ _ _ _ _]. destruct I as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
      destruct Hdw as [D|[D|[D|D]]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, two64 in *; lia. }
    rewrite u_small64 in Hin by exact Hw64. destruct (Hfr w Hin) as [Hn1 Hn2].
    destruct (dcov_covered E S M ms model a m0 Hd HA w Hdw0) as [[_ Hc]|(g & _ & _ & Hc & _)]; unfold covered in *; congruence.
  - pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh. rewrite Forall_forall in Hgsh.
    destruct (pri_cases E M a m0 HA Hne w Hpf) as [(g & Hg & Hgm & Hgin & _)|[(Hps & Hsh & g & y & Hg & Hgm & _ & Hy & _ & Ew)|Hgq]].
    + destruct (Hgsh g Hg) as (G1 & _ & _ & G4 & G5).
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia). rewrite u_small64 in Hin by exact Hw64.
      destruct (Hfr w Hin) as [_ Hn2].
      pose proof (grant_covered E _ M model g (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_gsh _ _ _ _ _ _ _ _ _ Hd) Hg Hgm w Hgin). congruence.
    + (* [comment removed for export] *)
      unfold in_shadow, SH_LO, SH_HI in Hsh. apply andb_prop in Hsh as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia). rewrite u_small64 in Hin by exact Hw64.
      destruct (Hfr w Hin) as [_ Hn2].
      pose proof (dn_zrm _ _ _ _ _ _ _ _ _ Hd w (po_zr _ _ _ _ (ha_pri _ _ _ _ HA Hne) w Hps)) as Hc. congruence.
    + (* [comment removed for export] *)
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia). rewrite u_small64 in Hin by exact Hw64.
      destruct (Hfr w Hin) as [Hn1 _]. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd) in Hn1.
      rewrite (in_res_sound _ _ _ w gq_res Hgq) in Hn1. discriminate.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma dep_avoid_shadow2 : forall E S M ms model a m0 lo n slo shi, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> sm_own M = a_own a ->
  SH_LO <= slo -> shi <= SH_HI ->
  (forall w, slo <= w < shi -> lo - 8 < 8 * (w - SH_OFF) < lo + n) ->
  (a_pri a <> [] -> forall g, In g (sm_maps M) -> is_mark g = false -> fst (fst g) = p_pg a -> lo + n <= uE E (fst (fst g)) \/ uE E (fst (fst g)) + gsz E g <= lo) ->
  own_avoid E M slo shi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 lo n slo shi Hd HA Hoa Hlo Hhi Hrel Hpg w Hw Hin.
  destruct (ha_ownx _ _ _ _ HA w (own_pt_a_M E M a w Hoa Hw)) as [Hdw0|[Hne Hpf]].
  - pose proof Hdw0 as Hdw. unfold dcov in Hdw. destruct (ha_hi _ _ _ _ HA) as [H1 H2].
    assert (Hw64 : 0 <= w < two64).
    { destruct HA as [(n0 & F & st & I & _) _ _ _ _ _ _]. destruct I as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
      destruct Hdw as [D|[D|[D|D]]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, two64 in *; lia. }
    rewrite u_small64 in Hin by exact Hw64.
    destruct Hdw as [D|[D|[D|D]]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, SH_LO, SH_HI in *; lia.
  - pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh. rewrite Forall_forall in Hgsh.
    pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgtop. rewrite Forall_forall in Hgtop.
    pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Htl.
    destruct (pri_cases E M a m0 HA Hne w Hpf) as [(g & Hg & Hgm & Hgin & Hgk)|[(_ & Hsh & g & y & Hg & Hgm & Hgp & Hy & Hy8 & Ew)|Hgq]];
      [| | (* [comment removed for export] *) rewrite u_small64 in Hin by (unfold two64; lia); unfold SH_LO in Hlo; lia].
    + (* [comment removed for export] *)
      destruct Hgk as [_ Hns]. destruct (Hgsh g Hg) as (G1 & _ & _ & G4 & G5).
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia). rewrite u_small64 in Hin by exact Hw64.
      unfold in_shadow in Hns. apply andb_false_iff in Hns. destruct Hns as [Hns|Hns]; [apply Z.leb_gt in Hns | apply Z.ltb_ge in Hns]; lia.
    + unfold in_shadow, SH_LO, SH_HI in Hsh. apply andb_prop in Hsh as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia). rewrite u_small64 in Hin by exact Hw64.
      destruct (Hgsh g Hg) as (G1 & G2 & G3 & G4 & G5).
      pose proof (Hrel w Hin) as Hr. rewrite Ew in Hr.
      replace (8 * (y / 8 + SH_OFF - SH_OFF)) with (8 * (y / 8)) in Hr by ring.
      pose proof (Z.div_mod y 8 ltac:(lia)) as Ey. rewrite Hy8, Z.add_0_r in Ey. rewrite <- Ey in Hr.
      destruct (Hpg Hne g Hg Hgm Hgp) as [Hd1|Hd1]; [lia|].
      (* [comment removed for export] *)
      assert (E8 : (uE E (fst (fst g)) + gsz E g) mod 8 = 0).
      { pose proof (Z.div_mod (uE E (fst (fst g))) 4096 ltac:(lia)) as Eb. rewrite G3, Z.add_0_r in Eb.
        pose proof (Z.div_mod (gsz E g) 4096 ltac:(lia)) as Es. rewrite G2, Z.add_0_r in Es. rewrite Eb, Es.
        replace (4096 * (uE E (fst (fst g)) / 4096) + 4096 * (gsz E g / 4096)) with ((512 * (uE E (fst (fst g)) / 4096) + 512 * (gsz E g / 4096)) * 8) by ring.
        apply Z.mod_mul. lia. }
      pose proof (Z.div_mod (uE E (fst (fst g)) + gsz E g) 8 ltac:(lia)) as Ee. rewrite E8, Z.add_0_r in Ee. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dep_avoid_shadow_place : forall E S M ms model a m0 nZ (ad : word), DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> sm_own M = a_own a ->
  place_ok model nZ ad -> 0 <= nZ < two64 ->
  own_avoid E M (bv_unsigned ad / 8 + SH_OFF) ((bv_unsigned ad + nZ) / 8 + SH_OFF).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 nZ ad Hd HA Hoa Hpl HnZ.
  pose proof (bv_unsigned_in_range _ ad) as Rad. unfold bv_modulus in Rad. change (2 ^ Z.of_N 64) with (2^64) in Rad.
  apply (dep_avoid_shadow2 E S M ms model a m0 (bv_unsigned ad) nZ _ _ Hd HA Hoa).
  - unfold SH_LO, SH_OFF. assert (X : 0 <= bv_unsigned ad / 8) by (apply Z.div_pos; lia). lia.
  - destruct Hpl as (_ & _ & Htop & _). destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [_ Hhi']. clear - Htop Hhi' HnZ.
    unfold alloc_top, stack_max_size, sp_window_hi in *.
    unfold SH_HI, SH_OFF. assert (Q : (bv_unsigned ad + nZ) / 8 <= 17592185044992) by (apply Z.div_le_upper_bound; lia). lia.
  - intros w Hw.
    pose proof (Z.div_mod (bv_unsigned ad) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (bv_unsigned ad) 8 ltac:(lia)) as B1.
    pose proof (Z.div_mod (bv_unsigned ad + nZ) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (bv_unsigned ad + nZ) 8 ltac:(lia)) as B2.
    lia.
  - intros Hne g Hg Hgm Hgp. destruct Hpl as (_ & _ & _ & Hfree).
    assert (Hin : In (gden E g) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))).
    { apply in_or_app. right. rewrite (dn_maps _ _ _ _ _ _ _ _ _ Hd). exact (lden_maps_in E _ _ g Hg Hgm). }
    unfold gden in Hin. pose proof (region_free_avoid _ ad (Z_to_bv 64 nZ) _ _ Hfree Hin) as X.
    rewrite u_small64 in X by exact HnZ. unfold gsz, uE. exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dep_avoid_grant : forall E S M ms model a m0 j g lo hi, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> sm_own M = a_own a ->
  a_pri a = [] ->
  nth_error (sm_maps M) j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= lo -> hi <= uE E (fst (fst g)) + gsz E g ->
  fst (fst g) <> fst (a_dep a) -> fst (fst g) <> snd (a_dep a) ->
  own_avoid E M lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 j g lo hi Hd HA Hoa Hnil Hj Hgm Hlo Hhi Hn1 Hn2 w Hw Hin.
  destruct (ha_ownx _ _ _ _ HA w (own_pt_a_M E M a w Hoa Hw)) as [Hdw0|[Hne _]]; [|exfalso; exact (Hne Hnil)].
  pose proof Hdw0 as Hdw. unfold dcov in Hdw.
  assert (Hw64 : 0 <= w < two64).
  { destruct HA as [(n & F & st & I & _) _ _ _ _ _ _]. destruct I as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
    destruct Hdw as [D|[D|[D|D]]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, two64 in *; lia. }
  rewrite u_small64 in Hin by exact Hw64.
  pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh.
  pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd) as Hmres. pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd.
  assert (Hcg : covered (vm_maps (m_vmmaps model)) w = true) by (apply (grant_covered E _ M model g Hmaps Hgsh (nth_error_In _ _ Hj) Hgm); lia).
  destruct (dcov_covered E S M ms model a m0 Hd HA w Hdw0) as [[_ Hc]|(g' & Hg' & Hin' & _ & _ & Hg'e)].
  - rewrite (Hmres w Hcg) in Hc. discriminate.
  - destruct (In_nth_error _ _ Hg') as (j' & Hj').
    assert (Hne : j <> j') by (intros ->; rewrite Hj in Hj'; injection Hj' as <-; destruct Hg'e as [E1|E1]; rewrite E1 in Hn1, Hn2; cbn in *; congruence).
    assert (Hgm' : is_mark g' = false) by (destruct Hg'e as [E1|E1]; rewrite E1; apply is_mark_csize).
    assert (Hd' : iv_disj (gden E g) (gden E g')).
    { rewrite Hmaps in Hpd. exact (pdisj_lden_nth E _ _ j j' g g' Hpd Hj Hj' Hne Hgm Hgm'). }
    rewrite Forall_forall in Hgsh. destruct (Hgsh g (nth_error_In _ _ Hj)) as (G1 & _ & _ & G4 & _). destruct (Hgsh g' Hg') as (G1' & _ & _ & G4' & _).
    unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd'. cbn [fst snd] in Hd'.
    unfold gsz, uE in *. lia.
Qed.
(* [comment removed for export] *)
Definition downed_b (D1 B1 x : Z) : bool :=
  ((1869144 <=? x) && (x <? 1869144 + 4194304) || (6063448 <=? x) && (x <? 6063448 + 4) || (6063464 <=? x) && (x <? 6063464 + 8) ||
   (D1 <=? x) && (x <? D1 + 1048576) || (1803592 <=? x) && (x <? 1803592 + 28) || (B1 <=? x) && (x <? B1 + 8388608))%bool.
#[using="Type"] Lemma downed_b_spec : forall D1 B1 x, downed_b D1 B1 x = true <-> downed D1 B1 x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros D1 B1 x. unfold downed_b, downed. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto.
Qed.
Definition hyb_dep (D1 B1 : Z) (mnew mold : word -> option byte) : word -> option byte :=
  fun w => if downed_b D1 B1 (bv_unsigned w) then mnew w else mold w.

(* [comment removed for export] *)
#[using="Type"] Lemma pri_not_downed : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a m0 -> a_pri a <> [] ->
  forall x, pri_foot E a x -> ~ downed (dD1 E a) (dB1 E a) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd HA Hne x Hpf Hdw.
  pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh.
  pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd) as Hmres. pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd.
  destruct (ha_hi _ _ _ _ HA) as [Hh1 Hh2].
  destruct (pri_cases E M a m0 HA Hne x Hpf) as [(g & Hg & Hgm & Hin & Hgk & _)|[(_ & Hsh & _)|Hgq]].
  - assert (Hcg : covered (vm_maps (m_vmmaps model)) x = true) by exact (grant_covered E _ M model g Hmaps Hgsh Hg Hgm x Hin).
    destruct (downed_covered E S M ms model a m0 Hd HA x Hdw) as [[_ Hc]|(g' & Hg' & Hin' & _ & _ & Hg'e)].
    + rewrite (Hmres x Hcg) in Hc. discriminate.
    + destruct (In_nth_error _ _ Hg) as (j & Hj). destruct (In_nth_error _ _ Hg') as (j' & Hj').
      assert (Hnj : j <> j').
      { intros Ejj. rewrite Ejj in Hj. assert (Egg : g' = g) by (rewrite Hj in Hj'; injection Hj' as X0; symmetry; exact X0). subst g'.
        destruct (ha_pri _ _ _ _ HA Hne) as [_ _ (kp & Hp) (kt & Ht) _].
        (* [comment removed for export] *)
        assert (X : forall g2, In g2 (sm_maps M) -> is_mark g2 = false -> fst (fst g2) = fst (fst g) -> snd (fst g2) <> snd (fst g) -> False).
        { intros g2 Hg2 Hm2 Eb Es. destruct (In_nth_error _ _ Hg2) as (j2 & Hj2).
          assert (Hn2 : j' <> j2) by (intros Ej2; rewrite Ej2 in Hj; rewrite Hj in Hj2; injection Hj2 as X0; apply Es; rewrite X0; reflexivity).
          assert (Hd2 : iv_disj (gden E g) (gden E g2)).
          { pose proof Hpd as Hpd2. rewrite Hmaps in Hpd2. exact (pdisj_lden_nth E _ _ j' j2 g g2 Hpd2 Hj Hj2 Hn2 Hgm Hm2). }
          rewrite Forall_forall in Hgsh. destruct (Hgsh g Hg) as (G1 & _ & _ & G4 & _). destruct (Hgsh g2 Hg2) as (G1' & _ & _ & G4' & _).
          unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd2. cbn [fst snd] in Hd2. rewrite Eb in Hd2. unfold gsz, uE in *. lia. }
        destruct Hgk as [Eg|Eg].
        - apply (X (p_pg a, lconst PG_SIZE, kp) Hp); cbn [fst snd]; [apply is_mark_csize | symmetry; exact Eg|].
          destruct Hg'e as [E1|E1]; rewrite E1; cbn [fst snd]; intros Q; vm_compute in Q; discriminate Q.
        - apply (X (p_tg a, lconst TG_SIZE, kt) Ht); cbn [fst snd]; [apply is_mark_csize | symmetry; exact Eg|].
          destruct Hg'e as [E1|E1]; rewrite E1; cbn [fst snd]; intros Q; vm_compute in Q; discriminate Q. }
      assert (Hgm' : is_mark g' = false) by (destruct Hg'e as [E1|E1]; rewrite E1; apply is_mark_csize).
      assert (Hd' : iv_disj (gden E g) (gden E g')).
      { pose proof Hpd as Hpd2. rewrite Hmaps in Hpd2. exact (pdisj_lden_nth E _ _ j j' g g' Hpd2 Hj Hj' Hnj Hgm Hgm'). }
      rewrite Forall_forall in Hgsh. destruct (Hgsh g Hg) as (G1 & _ & _ & G4 & _). destruct (Hgsh g' Hg') as (G1' & _ & _ & G4' & _).
      unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd'. cbn [fst snd] in Hd'. unfold gsz, uE in *. lia.
  - unfold in_shadow, SH_LO, SH_HI in Hsh. apply andb_prop in Hsh as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
    destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, SH_LO, SH_HI in *; lia.
  - (* [comment removed for export] *)
    destruct (downed_covered E S M ms model a m0 Hd HA x Hdw) as [[Hr _]|(g' & _ & _ & Hc & _)].
    + unfold DT_LO, DT_HI, DF_LO, DF_HI in Hr. lia.
    + pose proof (Hmres x Hc) as Hn. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd) in Hn. rewrite (in_res_sound _ _ _ x gq_res Hgq) in Hn. discriminate.
Qed.
End DepDen.
(* [comment removed for export] *)
