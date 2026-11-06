(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition XNU (X : list sptr) (s : astate) : Prop := forall x, In x X -> forall a, MT s x <> Some (MUsed a).

Lemma XNU_nil : forall s, XNU [] s.
Proof. intros s x []. Qed.

Lemma used_metas_usedX_X : forall X R U s g am, Inv X R U s -> XNU X s -> (In (g, am) (used_metas s) <-> usedX X s g am).
Proof.
  intros X R U s g am HI HX. rewrite (used_metas_iff s g am (proj1 (inv_keys HI))). unfold usedX, MTX.
  destruct (memb g X) eqn:E; [|tauto]. split; [|discriminate]. intros H. exfalso.
  assert (Hg : In g X).
  { clear - E. induction X as [|x t IH]; cbn in E; [discriminate|].
    destruct (sptr_eqb g x) eqn:E2; [left; symmetry; apply sptr_eqb_eq; exact E2 | right; exact (IH E)]. }
  exact (HX g Hg am H).
Qed.

Lemma group_cell_home_X L X R U s g am c :
  Inv X R U s -> usedX X s g am -> In c (group_cells g am) ->
  exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
    In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
    range_incl (cell_range L c) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
Proof.
  intros HW Hu Hc. destruct (used_group_region X R U s g am HW Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
  exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
  destruct (In_group_cells_span X R U s g am c HW Hu Hc) as (d & E & Hd & Hw).
  unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in Hext. lia.
Qed.

Lemma groups_cells_disjoint_X L X R U s g1 a1 g2 a2 x y :
  Inv X R U s -> layout_ok L s -> usedX X s g1 a1 -> usedX X s g2 a2 -> g1 <> g2 ->
  In x (group_cells g1 a1) -> In y (group_cells g2 a2) -> ranges_disjoint (cell_range L x) (cell_range L y).
Proof.
  intros HW HL U1 U2 Hne Hx Hy.
  destruct (group_cell_home_X L X R U s g1 a1 x HW U1 Hx) as (rg1 & R1 & K1 & L1 & In1 & I1).
  destruct (group_cell_home_X L X R U s g2 a2 y HW U2 Hy) as (rg2 & R2 & K2 & L2 & In2 & I2).
  destruct (Nat.eq_dec (prid (am_mem a1)) (prid (am_mem a2))) as [Hsame | Hdiff].
  2:{ eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
      intros E. injection E. intros _ Ep. exact (Hdiff Ep). }
  destruct (In_group_cells_span X R U s g1 a1 x HW U1 Hx) as (d1 & E1 & Hd1 & Hw1).
  destruct (In_group_cells_span X R U s g2 a2 y HW U2 Hy) as (d2 & E2 & Hd2 & Hw2).
  assert (GOAL : forall u v du dv au av, mc_loc u = LMem (padd (am_mem au) du) -> mc_loc v = LMem (padd (am_mem av) dv) ->
            prid (am_mem au) = prid (am_mem av) ->
            (poff (am_mem au) + du + Z.of_nat (mc_w u) <= poff (am_mem av) + dv \/ poff (am_mem av) + dv + Z.of_nat (mc_w v) <= poff (am_mem au) + du) ->
            ranges_disjoint (cell_range L u) (cell_range L v)).
  { intros u v du dv au av Eu Ev Hp D. cellsimp. rewrite Eu, Ev. cellsimp. rewrite Hp. lia. }
  assert (INS : forall ga a gb b u v du, usedX X s ga a -> usedX X s gb b -> inside X s a b ->
            In v (group_cells gb b) -> mc_loc u = LMem (padd (am_mem a) du) -> 0 <= du -> du + Z.of_nat (mc_w u) <= group_extent a ->
            prid (am_mem a) = prid (am_mem b) ->
            ranges_disjoint (cell_range L u) (cell_range L v)).
  { intros ga a gb b u v du Ua Ub I Hv Eu Hdu Hwu Hp.
    destruct I as (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mlc & Memc & Lo & Hi & Fit).
    pose proof (inv_groups HW gb b Ub) as (_ & _ & Gslb & _). pose proof (Gslb j Hj) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (Nf & Of & Bf & _ & FG) & _). destruct (FG Hk) as [Off _].
    rewrite Memc, poff_slot_start in Lo, Hi.
    destruct (group_cells_vs_body X R U s gb b j (poff (am_mem a) + du) (poff (am_mem a) + du + Z.of_nat (mc_w u)) v HW Ub Hj Hv
                ltac:(rewrite Hfr, Off, poff_slot_start; unfold UNIT in *; lia)
                ltac:(rewrite poff_slot_start; unfold UNIT, IB in *; lia)) as (dv & Ev & D).
    eapply (GOAL u v du dv a b Eu Ev Hp). lia. }
  destruct (inv_laminar HW g1 a1 g2 a2 U1 U2 Hne Hsame) as [Dj | [I | I]].
  - eapply (GOAL x y d1 d2 a1 a2 E1 E2 Hsame). unfold spans_disjoint in Dj. lia.
  - eapply (INS g1 a1 g2 a2 x y d1); eauto.
  - apply ranges_disjoint_sym. eapply (INS g2 a2 g1 a1 y x d2); eauto.
Qed.

Lemma areas_cells_pairwise_X L X R U s l :
  Inv X R U s -> layout_ok L s -> NoDup l -> (forall a, In a l -> In a (st_areas s)) ->
  pairwise ranges_disjoint (map (cell_range L) (areas_cells s l)).
Proof.
  intros HW HL. induction l as [|a t IH]; intros ND Hsub; cbn [areas_cells]; [exact I|].
  inversion ND as [|a' t' Ha Ht]; subst. rewrite map_app.
  apply pairwise_app.
  - apply area_cells_disjoint.
  - apply IH; [exact Ht | intros b Hb; apply Hsub; right; exact Hb].
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. apply in_map_iff in Hy as [c' [<- Hc']].
    destruct (In_areas_cells s t c' Hc') as (a' & next' & Ha' & Hc'').
    destruct (area_cell_home L s a (hd_error t) c (Hsub a (or_introl eq_refl)) Hc) as [In1 I1].
    destruct (area_cell_home L s a' next' c' (Hsub a' (or_intror Ha')) Hc'') as [In2 I2].
    eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
    intros E. injection E as <-. exact (Ha Ha').
Qed.

Theorem image_in_footprint_X : forall X R U s L c,
  Inv X R U s -> XNU X s -> layout_ok L s -> In c (image s) ->
  exists rg, In rg (footprint s) /\ range_incl (cell_range L c) (crange L rg).
Proof.
  intros X R U s L c HW HX HL Hin. destruct (In_image_inv s c Hin) as [Hc | [(a & next & Ha & Hc) | (g & am & Hg & Hc)]].
  - destruct (In_ctx_cells s c Hc) as (off & E & Ho & Hw). exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  - destruct (In_area_cells s a next c Hc) as (d & E & Hd & Hw). exists (LMem a, PGSZ). split.
    + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  - apply (used_metas_usedX_X X R U s g am HW HX) in Hg.
    destruct (used_group_region X R U s g am HW Hg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    destruct (In_group_cells X R U s g am c HW Hg Hc) as (d & E & Hd & Hw).
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [apply footprint_region_In; assumption|].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. lia.
Qed.

Theorem image_cells_disjoint_X : forall X R U s L,
  Inv X R U s -> XNU X s -> layout_ok L s -> pairwise ranges_disjoint (map (cell_range L) (image s)).
Proof.
  intros X R U s L HW HX HL. pose proof (inv_areas HW) as (AND & A2 & _).
  assert (HOMEa : forall c, In c (areas_cells s (st_areas s)) -> exists a, In a (st_areas s) /\ In (LMem a, PGSZ) (footprint s) /\
             range_incl (cell_range L c) (crange L (LMem a, PGSZ)) /\ poff a <> 0).
  { intros c Hc. destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc').
    destruct (area_cell_home L s a next c Ha Hc') as [In1 I1]. exists a. split; [exact Ha|]. split; [exact In1|]. split; [exact I1|].
    destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _). rewrite Ea. cbn. unfold PGSZ in Hoa. lia. }
  assert (HOMEg : forall c, In c (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s)) ->
             exists k len, In (LMem (SP k 0), len) (footprint s) /\ range_incl (cell_range L c) (crange L (LMem (SP k 0), len))).
  { intros c Hc. apply in_flat_map in Hc as [[g am] [Hg Hc]]. cbn [fst snd] in Hc. apply (used_metas_usedX_X X R U s g am HW HX) in Hg.
    destruct (group_cell_home_X L X R U s g am c HW Hg Hc) as (rg & _ & _ & _ & In1 & I1). eexists _, _. split; [exact In1 | exact I1]. }
  unfold image. rewrite !map_app. apply pairwise_app; [apply ctx_cells_disjoint | apply pairwise_app |].
  - apply (areas_cells_pairwise_X L X R U); [exact HW | exact HL | exact AND | intros a Ha; exact Ha].
  - apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)). apply pairwise_flat_map.
    + intros [g am] Hg. cbn [fst snd]. apply (used_metas_usedX_X X R U s g am HW HX) in Hg.
      apply (pairwise_map_iff ranges_disjoint (cell_range L)). eapply group_cells_disjoint; [exact HW | exact Hg].
    + intros l1 [g1 a1] l2 [g2 a2] E Hin x y Hx Hy. cbn [fst snd] in Hx, Hy.
      pose proof (used_metas_split s l1 g1 a1 l2 g2 a2 (proj1 (inv_keys HW)) E Hin) as Hne.
      assert (U1 : usedX X s g1 a1) by (apply (used_metas_usedX_X X R U s g1 a1 HW HX); rewrite E; apply in_app_iff; right; left; reflexivity).
      assert (U2 : usedX X s g2 a2) by (apply (used_metas_usedX_X X R U s g2 a2 HW HX); rewrite E; apply in_app_iff; right; right; exact Hin).
      exact (groups_cells_disjoint_X L X R U s g1 a1 g2 a2 x y HW HL U1 U2 Hne Hx Hy).
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. apply in_map_iff in Hy as [c' [<- Hc']].
    destruct (HOMEa c Hc) as (a & Ha & In1 & I1 & Hpa). destruct (HOMEg c' Hc') as (k & len & In2 & I2).
    eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
    intros E. injection E as Ea _. rewrite Ea in Hpa. exact (Hpa eq_refl).
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. destruct (ctx_cell_home L s c Hc) as [In1 I1].
    apply in_app_iff in Hy as [Hy|Hy]; apply in_map_iff in Hy as [c' [<- Hc']].
    + destruct (HOMEa c' Hc') as (a & Ha & In2 & I2 & _).
      eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | discriminate | exact I1 | exact I2].
    + destruct (HOMEg c' Hc') as (k & len & In2 & I2).
      eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | discriminate | exact I1 | exact I2].
Qed.
