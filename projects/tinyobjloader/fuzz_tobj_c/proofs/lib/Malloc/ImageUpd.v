(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "mc_w"; "used_metas"; "image"; "meta_slot_cells"; "MT"; "area_cells"; "ctx_cells"; "group_cells"; "areas_cells"; "footprint"; "layout_ok"; "pairwise"; "loc"; "slot_cells"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "mslot"; "MUsed"; "mupdate"; "astate"; "st_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_regions"; "st_usage"; "brkst"; "region"; "sptr_eqb"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "Some"; "app"; "bool"; "cons"; "option"; "true"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.ZArith.BinInt.Z"; "ltb"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocFooter.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mupdate_mupdate_same l p x y : ltac2:(tb__ "0|0|
S11S25S27S16S18A2A1S1aS1aVl;Vp;Vx;A3Vp;Vy;A3S1aVl;Vp;Vy;A3A3").
Proof.
  induction l as [|[q z] t IH]; cbn.
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma upd_meta_twice g x y s : ltac2:(tb__ "0|0|
S11S1bS2fVg;Vy;S2fVg;Vx;Vs;A3A3S2fVg;Vy;Vs;A3A3").
Proof. unfold upd_meta. cbn. rewrite mupdate_mupdate_same. reflexivity. Qed.

Lemma pairwise_In_cases {A B} (R : B -> B -> Prop) (f : A -> B) l a b : ltac2:(tb__ "0|2|
SeVB;VR;S33VA;VB;Vf;Vl;A4A3S0VA;Va;Vl;A3S0VA;Vb;Vl;A3S13S11VA;Va;Vb;A3S13VR;Vf;Va;A1M0Vf;Vb;A1M1A2VR;G1G0A2A2A2F_;F_;F_;").
Proof.
  induction l as [|x t IH]; intros HP Ha Hb; [destruct Ha|]. cbn in HP. destruct HP as [H1 H2].
  destruct Ha as [->|Ha]; destruct Hb as [->|Hb].
  - left. reflexivity.
  - right; left. apply H1. apply in_map. exact Hb.
  - right; right. apply H1. apply in_map. exact Ha.
  - apply IH; assumption.
Qed.

Lemma pairwise_app_mid {B} (R : B -> B -> Prop) l1 x l2 y : ltac2:(tb__ "0|0|
SeVB;VR;S29VB;Vl1;S2bVB;Vx;Vl2;A3A3A3S0VB;Vy;S29VB;Vl1;Vl2;A3A3S13VR;Vx;Vy;A2VR;Vy;Vx;A2A2F_;F_;").
Proof.
  induction l1 as [|h t IH]; cbn; intros HP Hy.
  - destruct HP as [H1 _]. left. apply H1. exact Hy.
  - destruct HP as [H1 H2]. destruct Hy as [->|Hy].
    + right. apply H1. apply in_app_iff. right. left. reflexivity.
    + apply IH; assumption.
Qed.

Section Upd.
  Variables (s : astate) (g : sptr) (am am' : ameta).
  Hypothesis ND : NoDup (keys s).
  Hypothesis Hg : ltac2:(tb__ "0|0|
S11S2cS18A1S7Vs;Vg;A2S28S18S19Vam;A1A2A3").
  Let s' : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
S2fVg;S19Vam';A1Vs;A3").

  Lemma upd_fields : ltac2:(tb__ "0|0|
S12S11S25S16A1S1cVs';A1S1cVs;A1A3S12S11S25S23A1S20Vs';A1S20Vs;A1A3S12S11S22S1dVs';A1S1dVs;A1A3S12S11S2aS1eVs';A1S1eVs;A1A3S12S11S25S30A1S21Vs';A1S21Vs;A1A3S11S30S1fVs';A1S1fVs;A1A3A2A2A2A2A2").
  Proof using am' g. repeat split; reflexivity. Qed.

  Lemma upd_footprint : ltac2:(tb__ "0|0|
S11S25S27SfS30A2A1ScVs';A1ScVs;A1A3").
  Proof using am' g. reflexivity. Qed.

  Lemma upd_ctx_cells : ltac2:(tb__ "0|0|
S11S25S2A1S9Vs';A1S9Vs;A1A3").
  Proof using am' g. reflexivity. Qed.

  Lemma upd_MT q : ltac2:(tb__ "0|1|
S11S2cS18A1M0S7Vs';Vq;A2S2aG0L_;S24Vq;Vg;A2S28S18S19Vam';A1A2S7Vs;Vq;A2X2ax2A3").
  Proof using . unfold s'. apply MT_upd. Qed.

  Lemma upd_used_metas : ltac2:(tb__ "0|2|
S15S25S27S16S17A2M0A1M1G1S15G1G1S12S11G1S4Vs;A1S29G0R2S2bG0S26S16S17Vg;Vam;A4R1A3A3A3S12S11G1S4Vs';A1S29G0R2S2bG0S26S16S17Vg;Vam';A4R1A3A3A3S16S17S0G0S26S16S17R2R1A4S29G0R4R3A3A3S14S11S16R3Vg;A3A1F_;Fa;Fq;A2A2Ll2;A2Ll1;A2").
  Proof using Hg ND.
    unfold s', upd_meta, used_metas. cbn [st_metas set_metas].
    unfold MT in Hg. unfold keys in ND.
    revert ND Hg. generalize (st_metas s) as l. clear s'.
    assert (MU : forall q x t, mupdate ((q, x) :: t) g (MUsed am') = if sptr_eqb g q then (q, MUsed am') :: t else (q, x) :: mupdate t g (MUsed am')) by reflexivity.
    assert (UM : forall q x t, flat_map (fun e : sptr * mslot => let (p, m) := e in match m with MUsed am0 => [(p, am0)] | _ => [] end) ((q, x) :: t)
                 = match x with MUsed am0 => [(q, am0)] | _ => [] end ++ flat_map (fun e : sptr * mslot => let (p, m) := e in match m with MUsed am0 => [(p, am0)] | _ => [] end) t) by reflexivity.
    assert (ML : forall q x t, mlookup ((q, x) :: t) g = if sptr_eqb g q then Some x else mlookup t g) by reflexivity.
    induction l as [|[q x] t IH]; intros ND Hl; [discriminate|].
    rewrite ML in Hl. inversion ND as [|q0 t0 Hq Ht]; subst.
    rewrite MU. destruct (sptr_eqb g q) eqn:E.
    - apply sptr_eqb_eq in E. subst q. injection Hl as ->. rewrite !UM. cbn [app].
      exists [], (flat_map (fun e : sptr * mslot => let (p, m) := e in match m with MUsed am0 => [(p, am0)] | _ => [] end) t).
      split; [reflexivity|]. split; [reflexivity|].
      intros q a Hin ->. apply Hq. apply in_flat_map in Hin as [[p m] [Hp Hm]].
      apply in_map_iff. exists (p, m). split; [|exact Hp]. destruct m; cbn in Hm; try destruct Hm as [Hm|[]]; try (injection Hm as -> _); try reflexivity; destruct Hm.
    - destruct (IH Ht Hl) as (l1 & l2 & E1 & E2 & Hne). rewrite !UM. rewrite E1, E2.
      assert (Hqg : q <> g) by (intros ->; rewrite sptr_eqb_refl in E; discriminate).
      destruct x as [pr nx| |am0].
      + exists l1, l2. auto.
      + exists l1, l2. auto.
      + exists ((q, am0) :: l1), l2. cbn [app]. split; [reflexivity|]. split; [reflexivity|].
        intros q' a [Hin|Hin]; [injection Hin as -> _; exact Hqg | exact (Hne q' a Hin)].
  Qed.

  Lemma upd_used_metas_In q a : ltac2:(tb__ "0|3|
S0S27S16S17A2M0S26S16S17Vq;Va;A4M1S4Vs';A1A3S13S12S11S16Vq;Vg;A3M2S11S17Va;Vam';A3A2S12S14G2A1S0G0G1S4Vs;A1A3A2A2F_;").
  Proof using Hg ND.
    intros Hin. destruct upd_used_metas as (l1 & l2 & E1 & E2 & Hne). rewrite E2 in Hin. rewrite E1.
    apply in_app_iff in Hin as [Hin|[Hin|Hin]].
    - right. split; [exact (Hne q a ltac:(apply in_app_iff; left; exact Hin))|]. apply in_app_iff. left. exact Hin.
    - injection Hin as -> ->. left. auto.
    - right. split; [exact (Hne q a ltac:(apply in_app_iff; right; exact Hin))|]. apply in_app_iff. right. right. exact Hin.
  Qed.

  Lemma used_metas_In_old q a : ltac2:(tb__ "0|2|
S14S11S16Vq;Vg;A3A1S0S27S16S17A2M0S26S16S17Vq;Va;A4M1S4Vs';A1A3S0G0G1S4Vs;A1A3F_;F_;").
  Proof using Hg ND am'. intros Hq Hin. destruct (upd_used_metas_In q a Hin) as [[E _]|[_ H]]; [exfalso; exact (Hq E) | exact H]. Qed.

  Lemma used_metas_g_old : ltac2:(tb__ "0|0|
S0S27S16S17A2S26S16S17Vg;Vam;A4S4Vs;A1A3").
  Proof using Hg ND s'. destruct upd_used_metas as (l1 & l2 & -> & _). apply in_app_iff. right. left. reflexivity. Qed.

  Lemma used_metas_g_new : ltac2:(tb__ "0|0|
S0S27S16S17A2S26S16S17Vg;Vam';A4S4Vs';A1A3").
  Proof using Hg ND. destruct upd_used_metas as (l1 & l2 & _ & -> & _). apply in_app_iff. right. left. reflexivity. Qed.

  Lemma upd_area_cells_In a next c : ltac2:(tb__ "0|0|
S0S2Vc;S8Vs';Va;Vnext;A3A3S13S0S2Vc;S8Vs;Va;Vnext;A3A3S0S2Vc;S6Vg;S28S18S19Vam';A1A2A2A3A2F_;").
  Proof using .
    intros Hin. unfold area_cells in *. apply in_app_iff in Hin as [Hin|Hin]; [left; apply in_app_iff; left; exact Hin|].
    apply in_flat_map in Hin as [k [Hk Hin]].
    change (st_metas s') with (mupdate (st_metas s) g (MUsed am')) in Hin.
    rewrite mlookup_mupdate in Hin.
    destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E.
    - apply sptr_eqb_eq in E. rewrite E in Hin. right. exact Hin.
    - left. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk | exact Hin].
  Qed.

  Lemma upd_areas_cells_In l c : ltac2:(tb__ "0|0|
S0S2Vc;SbVs';Vl;A2A3S13S0S2Vc;SbVs;Vl;A2A3S0S2Vc;S6Vg;S28S18S19Vam';A1A2A2A3A2F_;").
  Proof using .
    induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [destruct Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (upd_area_cells_In a (hd_error t) c Hin) as [H|H]; [left; apply in_app_iff; left; exact H | right; exact H].
    - destruct (IH Hin) as [H|H]; [left; apply in_app_iff; right; exact H | right; exact H].
  Qed.

  Theorem upd_image_In c : ltac2:(tb__ "0|0|
S0S2Vc;S5Vs';A1A3S13S0S2Vc;S5Vs;A1A3S13S0S2Vc;S6Vg;S28S18S19Vam';A1A2A2A3S0S2Vc;SaVg;Vam';A2A3A2A2F_;").
  Proof using Hg ND.
    intros Hin. unfold image in Hin. rewrite upd_ctx_cells in Hin.
    change (st_areas s') with (st_areas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [left; unfold image; apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (upd_areas_cells_In _ c Hin) as [H|H]; [left | right; left; exact H].
      unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [fst snd] in Hc.
      destruct (upd_used_metas_In q a Hq) as [[-> ->]|[Hne Hold]]; [right; right; exact Hc|].
      left. apply (In_image_group s q a c Hold Hc).
  Qed.

  Theorem upd_footer_In c : ltac2:(tb__ "0|0|
S0S2Vc;S31Vs';A1A3S13S0S2Vc;S31Vs;A1A3S0S2Vc;S32Vam';A1A3A2F_;").
  Proof using Hg ND.
    intros Hin. unfold footer_cells in *. apply in_flat_map in Hin as [[q a] [Hq Hc]]. cbn [snd] in Hc.
    destruct (upd_used_metas_In q a Hq) as [[-> ->]|[Hne Hold]]; [right; exact Hc|].
    left. apply in_flat_map. exists (q, a). auto.
  Qed.

  Lemma upd_image_group c : ltac2:(tb__ "0|0|
S0S2Vc;SaVg;Vam';A2A3S0S2Vc;S5Vs';A1A3F_;").
  Proof using Hg ND. intros Hc. apply (In_image_group s' g am' c used_metas_g_new Hc). Qed.

  Lemma upd_image_meta c (HW' : WF s') : ltac2:(tb__ "0|0|
S0S2Vc;S6Vg;S28S18S19Vam';A1A2A2A3S0S2Vc;S5Vs';A1A3F_;").
  Proof using s.
    intros Hc. apply (meta_cells_in_image s' g am' c HW'); [|exact Hc].
    apply usedX_intro; [reflexivity|]. rewrite upd_MT, sptr_eqb_refl. reflexivity.
  Qed.

  Lemma upd_layout_ok L : ltac2:(tb__ "0|0|
SdVL;Vs;A2SdVL;Vs';A2F_;").
  Proof using am' g. intros H. exact H. Qed.
End Upd.

Lemma ctx_cells_w s : ltac2:(tb__ "0|0|
S11S2aS1S2S2S34Z0S35S3R1A1A1A2Lc;S9Vs;A1A3S2dA3").
Proof. destruct s. vm_compute. reflexivity. Qed.

Lemma meta_slot_cells_w q x c : ltac2:(tb__ "0|0|
S0S2Vc;S6Vq;Vx;A2A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold meta_slot_cells in Hin.
  destruct x as [[pr nx| |am]|]; cbn in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]); destruct Hin.
Qed.

Lemma area_cells_w s a next c : ltac2:(tb__ "0|0|
S0S2Vc;S8Vs;Va;Vnext;A3A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold area_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
  - apply in_flat_map in Hin as [k [_ Hin]]. exact (meta_slot_cells_w _ _ _ Hin).
Qed.

Lemma slot_cells_w am i c : ltac2:(tb__ "0|0|
S0S2Vc;S10Vam;Vi;A2A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold slot_cells in Hin.
  apply in_app_iff in Hin as [Hin|Hin]; [destruct Hin as [<-|[]]; cbn; lia|].
  apply in_app_iff in Hin as [Hin|Hin].
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hin].
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
  - destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin]. destruct (fr_off fr =? 0); [destruct Hin|].
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
Qed.

Lemma group_cells_w g am c : ltac2:(tb__ "0|0|
S0S2Vc;SaVg;Vam;A2A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold group_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct Hin as [<-|[<-|[]]]; [cbn; lia|]. destruct (am_maplen am =? 0); cbn; lia.
  - apply in_flat_map in Hin as [i [_ Hin]]. exact (slot_cells_w _ _ _ Hin).
Qed.

Lemma image_cell_w s c : ltac2:(tb__ "0|0|
S0S2Vc;S5Vs;A1A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. destruct (In_image_inv s c Hin) as [Hc | [(a & next & _ & Hc) | (g & am & _ & Hc)]].
  - pose proof (ctx_cells_w s) as H. rewrite forallb_forall in H. specialize (H c Hc). apply Z.ltb_lt in H. lia.
  - exact (area_cells_w _ _ _ _ Hc).
  - exact (group_cells_w _ _ _ Hc).
Qed.

Lemma footer_cell_w am c : ltac2:(tb__ "0|0|
S0S2Vc;S32Vam;A1A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold group_footer_cells in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply in_flat_map in Hin as [i [_ Hin]]. destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin].
  unfold frame_footer_cells in Hin. destruct (fr_kind fr); [|destruct Hin].
  apply in_app_iff in Hin as [Hin|Hin]; [destruct (0 <? reserved_of am fr); [|destruct Hin]; destruct Hin as [<-|[]]; cbn; lia|].
  apply in_app_iff in Hin as [Hin|Hin]; [destruct (5 <=? reserved_of am fr); [|destruct Hin]; destruct Hin as [<-|[]]; cbn; lia|].
  destruct (5 <? reserved_of am fr); [|destruct Hin]; destruct Hin as [<-|[]]; cbn; lia.
Qed.

Lemma footer_cells_w s c : ltac2:(tb__ "0|0|
S0S2Vc;S31Vs;A1A3S2eU0S3Vc;A1A2F_;").
Proof.
  intros Hin. unfold footer_cells in Hin. apply in_flat_map in Hin as [[g am] [_ Hc]]. exact (footer_cell_w _ _ Hc).
Qed.
