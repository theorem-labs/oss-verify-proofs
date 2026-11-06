(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition KS (s : astate) : Prop :=
  NoDup (keys s) /\ (forall g, In g (keys s) -> filter (fun q => sptr_eqb q g) (all_slots (st_areas s)) = [g]).

Lemma KS_of_WF : forall s, WF s -> KS s.
Proof. intros s HW. split; [exact (proj1 (inv_keys HW)) | intros g Hg; exact (key_once s g HW Hg)]. Qed.

Lemma keys_set_meta : forall s g x, In g (keys s) -> keys (set_meta s g x) = keys s.
Proof. intros s g x Hg. unfold keys, set_meta. cbn [st_metas set_metas]. apply map_fst_mupdate_In. exact Hg. Qed.

Lemma KS_set_meta : forall s g x, KS s -> In g (keys s) -> KS (set_meta s g x).
Proof.
  intros s g x [ND KO] Hg. split.
  - rewrite keys_set_meta by exact Hg. exact ND.
  - intros q Hq. rewrite keys_set_meta in Hq by exact Hg. exact (KO q Hq).
Qed.

Lemma MT_keys : forall s g x, MT s g = Some x -> In g (keys s).
Proof. intros s g x H. unfold keys. eapply mlookup_In_keys. exact H. Qed.

Lemma MT_set_same : forall s g x, MT (set_meta s g x) g = Some x.
Proof. intros s g x. unfold MT, set_meta. cbn [st_metas set_metas]. apply mlookup_mupdate_same. Qed.

Lemma MT_set_other : forall s g x q, q <> g -> MT (set_meta s g x) q = MT s q.
Proof. intros s g x q H. unfold MT. apply mlookup_set_other. exact H. Qed.

Lemma image_decomp_ks : forall s g am, KS s -> MT s g = Some (MUsed am) ->
  Permutation (image s)
    ((ctx_cells s ++ ahdr (st_areas s)
       ++ flat_map (mcells (st_metas s)) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s)))
       ++ flat_map gcells (filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas s)))
     ++ meta_slot_cells g (Some (MUsed am)) ++ group_cells g am).
Proof.
  intros s g am [ND KO] Hg.
  assert (Hkey : In g (keys s)) by (eapply MT_keys; exact Hg).
  assert (Hused : In (g, am) (used_metas s)) by (apply (used_metas_iff s g am ND); exact Hg).
  unfold image.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply areas_cells_perm|].
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_head. apply (flat_map_filter_perm gcells (fun gm => sptr_eqb (fst gm) g)). }
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head.
    apply (flat_map_filter_perm (mcells (st_metas s)) (fun q => sptr_eqb q g)). }
  rewrite (KO g Hkey), (filter_key_single (used_metas s) g am (NoDup_used_metas_keys s ND) Hused).
  cbn [flat_map]. rewrite !app_nil_r. unfold mcells at 1, gcells at 1.
  change (mlookup (st_metas s) g) with (MT s g). rewrite Hg. cbn [fst snd].
  apply perm_surgery.
Qed.

Lemma image_setm_ks : forall s g am am', KS s -> MT s g = Some (MUsed am) ->
  exists U, Permutation (image s) (U ++ meta_slot_cells g (Some (MUsed am)) ++ group_cells g am) /\
            Permutation (image (set_meta s g (MUsed am'))) (U ++ meta_slot_cells g (Some (MUsed am')) ++ group_cells g am').
Proof.
  intros s g am am' HK Hg. eexists. split; [apply image_decomp_ks; assumption|].
  set (s' := set_meta s g (MUsed am')).
  assert (Hkey : In g (keys s)) by (eapply MT_keys; exact Hg).
  assert (HK' : KS s') by (apply KS_set_meta; assumption).
  assert (Hg' : MT s' g = Some (MUsed am')) by apply MT_set_same.
  eapply Permutation_trans; [apply image_decomp_ks; [exact HK' | exact Hg']|].
  replace (ctx_cells s') with (ctx_cells s) by reflexivity.
  replace (st_areas s') with (st_areas s) by reflexivity.
  replace (filter (fun gm : sptr * ameta => negb (sptr_eqb (fst gm) g)) (used_metas s'))
    with (filter (fun gm : sptr * ameta => negb (sptr_eqb (fst gm) g)) (used_metas s)) by (symmetry; exact (used_metas_set_filter s g am')).
  replace (flat_map (mcells (st_metas s')) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s))))
    with (flat_map (mcells (st_metas s)) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s)))).
  2:{ apply flat_map_ext_in'. intros q Hq. apply filter_In in Hq as [_ Hq]. unfold mcells.
      change (mlookup (st_metas s') q) with (mlookup (st_metas (set_meta s g (MUsed am'))) q).
      rewrite (mlookup_set_other s g (MUsed am') q); [reflexivity|]. intro E. subst q. rewrite sptr_eqb_refl in Hq. discriminate. }
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cov_setm : forall s g am am' c, KS s -> MT s g = Some (MUsed am) ->
  In c (image (set_meta s g (MUsed am'))) ->
  In c (image s) \/ In c (meta_slot_cells g (Some (MUsed am'))) \/ In c (group_cells g am').
Proof.
  intros s g am am' c HK Hg Hc. destruct (image_setm_ks s g am am' HK Hg) as (U & P1 & P2).
  apply (Permutation_in c P2) in Hc. apply in_app_iff in Hc as [Hu|Hc].
  - left. apply (Permutation_in c (Permutation_sym P1)). apply in_app_iff. left. exact Hu.
  - right. apply in_app_iff in Hc. exact Hc.
Qed.

Lemma In_image_setm_new : forall s g am am' c, KS s -> MT s g = Some (MUsed am) ->
  In c (meta_slot_cells g (Some (MUsed am'))) \/ In c (group_cells g am') -> In c (image (set_meta s g (MUsed am'))).
Proof.
  intros s g am am' c HK Hg Hc. destruct (image_setm_ks s g am am' HK Hg) as (U & P1 & P2).
  apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. right. apply in_app_iff. exact Hc.
Qed.

Lemma In_image_used : forall s g am c, KS s -> MT s g = Some (MUsed am) ->
  In c (meta_slot_cells g (Some (MUsed am))) \/ In c (group_cells g am) -> In c (image s).
Proof.
  intros s g am c HK Hg Hc. pose proof (image_decomp_ks s g am HK Hg) as P.
  apply (Permutation_in c (Permutation_sym P)). apply in_app_iff. right. apply in_app_iff. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof. intros [r1 o1] [r2 o2]. destruct (Nat.eq_dec r1 r2) as [->|H]; [destruct (Z.eq_dec o1 o2) as [->|H2]|].
  - left. reflexivity. - right. intro E. injection E. auto. - right. intro E. injection E. auto. Qed.

Lemma loc_eq_dec : forall l l' : loc, {l = l'} + {l <> l'}.
Proof. decide equality; [apply Z.eq_dec | apply sptr_eq_dec]. Qed.

Lemma sval_eq_dec : forall v v' : sval, {v = v'} + {v <> v'}.
Proof. decide equality; first [apply Z.eq_dec | apply sptr_eq_dec]. Qed.

Lemma mcell_eq_dec : forall c c' : mcell, {c = c'} + {c <> c'}.
Proof. decide equality; [apply sval_eq_dec | apply Nat.eq_dec | apply loc_eq_dec]. Qed.

Section Final.
Variable L : layout.

#[using="Type"] Lemma repr_update_final : forall s s' bv bv' Cold Cnew,
  WF s -> repr L s bv -> WF s' -> layout_ok L s' -> Forall (range_mapped L bv') (footprint s') ->
  (forall c, In c Cold -> In c (image s)) ->
  (forall c, In c Cnew -> In c (image s')) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) ->
  (forall c, In c Cold -> exists c', In c' Cnew /\ mc_loc c' = mc_loc c) ->
  Forall (cell_holds L bv') Cnew ->
  writes_only L s Cold bv bv' ->
  repr L s' bv'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s s' bv bv' Cold Cnew HW HR HW' HL' HF' HCold HNin Hcov Hrep HNew HWO.
  apply (repr_update L s s' bv bv' Cold Cnew HW HR HL' HF' HCold); [|exact HNew | exact HWO].
  intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn]; [right; exact Hn|].
  left. destruct (Hcov c Hc) as [Hs|Hn']; [|contradiction]. split; [exact Hs|].
  intros Ho. destruct (Hrep c Ho) as (c' & Hc' & Eloc).
  assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
  pose proof (image_pair_disjoint s' L c c' HW' HL' Hc (HNin c' Hc') Hne) as D.
  pose proof (image_cell_width s' c Hc) as W1. pose proof (image_cell_width s' c' (HNin c' Hc')) as W2.
  unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D. rewrite Eloc in D. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_mapped_same : forall s bv bv' Cold Cnew,
  Forall (range_mapped L bv) (footprint s) ->
  (forall c, In c Cold -> exists c', In c' Cnew /\ mc_loc c' = mc_loc c /\ mc_w c' = mc_w c) ->
  (forall c, In c Cnew -> forall z, mc_val c <> VLo5 z) ->
  Forall (cell_holds L bv') Cnew ->
  (forall a, bv' a <> bv a -> (exists c, In c Cold /\ in_rng (cell_range L c) a) \/ bv' a <> None) ->
  Forall (range_mapped L bv') (footprint s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s bv bv' Cold Cnew HF Hrep HV HNew HWO. apply Forall_forall. intros rg Hrg x Hx.
  pose proof (proj1 (Forall_forall _ _) HF rg Hrg x Hx) as Hm.
  destruct (option_Z_eq_dec (bv' x) (bv x)) as [E|E]; [rewrite E; exact Hm|].
  destruct (HWO x E) as [(c & Hc & Hin) | Hs]; [|exact Hs].
  destruct (Hrep c Hc) as (c' & Hc' & El & Ew).
  pose proof (proj1 (Forall_forall _ _) HNew c' Hc') as Hh. unfold cell_holds in Hh.
  unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. rewrite <- El, <- Ew in Hin.
  pose proof (HV c' Hc') as HV'.
  destruct (mc_val c') as [z|p|z|] eqn:Ev; [ | | exfalso; exact (HV' z eq_refl) | ];
  replace x with (loc_addr L (mc_loc c') + Z.of_nat (Z.to_nat (x - loc_addr L (mc_loc c')))) by lia;
  rewrite Hh by lia; discriminate.
Qed.
End Final.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Step.
Variable L : layout.

#[using="Type"] Lemma repr_step : forall s1 s' bv1 bv' (Cnew : list mcell),
  repr L s1 bv1 -> WF s' -> layout_ok L s' -> Forall (range_mapped L bv') (footprint s') ->
  (forall c, In c (image s') -> In c (image s1) \/ In c Cnew) ->
  (forall c, In c Cnew -> In c (image s')) ->
  Forall (cell_holds L bv') Cnew ->
  (forall a, bv' a <> bv1 a -> exists c', In c' Cnew /\ in_rng (cell_range L c') a) ->
  repr L s' bv'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s1 s' bv1 bv' Cnew (HL1 & HC1 & HF1) HW' HL' HF' Hcov HNin HNew HWO.
  split; [exact HL'|]. split; [|exact HF'].
  apply Forall_forall. intros c Hc. destruct (In_dec mcell_eq_dec c Cnew) as [Hn|Hn].
  - exact (proj1 (Forall_forall _ _) HNew c Hn).
  - destruct (Hcov c Hc) as [H1|H1]; [|contradiction].
    apply (cell_holds_frame L bv1 bv' c (image_cell_width s' c Hc) (proj1 (Forall_forall _ _) HC1 c H1)).
    intros a Ha. destruct (option_Z_eq_dec (bv' a) (bv1 a)) as [E|E]; [exact E|].
    exfalso. destruct (HWO a E) as (c' & Hc' & Ha').
    assert (Hne : c <> c') by (intros ->; exact (Hn Hc')).
    pose proof (image_pair_disjoint s' L c c' HW' HL' Hc (HNin c' Hc') Hne) as D.
    unfold ranges_disjoint, in_rng in *. lia.
Qed.

End Step.

(* [comment removed for export] *)
Lemma msc_links_cov : forall q am pr nx c,
  In c (meta_slot_cells q (Some (MUsed (am_set_links pr nx am)))) ->
  In c (meta_slot_cells q (Some (MUsed am))) \/ c = MCell (LMem (padd q META_prev)) 8 (optr pr) \/ c = MCell (LMem (padd q META_next)) 8 (optr nx).
Proof.
  intros q am pr nx c Hc. cbn [meta_slot_cells am_set_links am_prev am_next am_mem am_avail am_freed] in Hc.
  unfold meta_bits in *. cbn [am_set_links am_last am_sc am_maplen] in Hc.
  destruct Hc as [<-|[<-|Hc]]; [right; left; reflexivity | right; right; reflexivity |].
  left. cbn [meta_slot_cells]. right. right. exact Hc.
Qed.

Lemma msc_freed_cov : forall q am f c,
  In c (meta_slot_cells q (Some (MUsed (am_set_freed f am)))) ->
  In c (meta_slot_cells q (Some (MUsed am))) \/ c = MCell (LMem (padd q META_freed)) 4 (VZ f).
Proof.
  intros q am f c Hc. cbn [meta_slot_cells am_set_freed am_prev am_next am_mem am_avail am_freed] in Hc.
  unfold meta_bits in *. cbn [am_set_freed am_last am_sc am_maplen] in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[<-|Hc]]]]]; try (left; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [meta_slot_cells In]; tauto ]); right; reflexivity.
Qed.

Lemma msc_avail_cov : forall q am v c,
  In c (meta_slot_cells q (Some (MUsed (am_set_avail v am)))) ->
  In c (meta_slot_cells q (Some (MUsed am))) \/ c = MCell (LMem (padd q META_avail)) 4 (VZ v).
Proof.
  intros q am v c Hc. cbn [meta_slot_cells am_set_avail am_prev am_next am_mem am_avail am_freed] in Hc.
  unfold meta_bits in *. cbn [am_set_avail am_last am_sc am_maplen] in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|Hc]]]]; try (left; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [meta_slot_cells In]; tauto ]); right; reflexivity.
Qed.

Lemma gc_links : forall q am pr nx, group_cells q (am_set_links pr nx am) = group_cells q am.
Proof. reflexivity. Qed.
Lemma gc_freed : forall q am f, group_cells q (am_set_freed f am) = group_cells q am.
Proof. reflexivity. Qed.
Lemma gc_avail : forall q am v, group_cells q (am_set_avail v am) = group_cells q am.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cov_setm_links : forall s q am pr nx c, KS s -> MT s q = Some (MUsed am) ->
  In c (image (set_meta s q (MUsed (am_set_links pr nx am)))) ->
  In c (image s) \/ c = MCell (LMem (padd q META_prev)) 8 (optr pr) \/ c = MCell (LMem (padd q META_next)) 8 (optr nx).
Proof.
  intros s q am pr nx c HK Hq Hc. destruct (cov_setm s q am _ c HK Hq Hc) as [H|[H|H]].
  - left. exact H.
  - destruct (msc_links_cov q am pr nx c H) as [H'|H']; [left; apply (In_image_used s q am c HK Hq); left; exact H' | right; exact H'].
  - left. rewrite gc_links in H. apply (In_image_used s q am c HK Hq). right. exact H.
Qed.

(* [comment removed for export] *)
Lemma mupdate_comm : forall l p q x y, p <> q -> In p (map fst l) -> In q (map fst l) ->
  mupdate (mupdate l p x) q y = mupdate (mupdate l q y) p x.
Proof.
  induction l as [|[k z] t IH]; intros p q x y Hne Hp Hq; [destruct Hp|].
  cbn [mupdate]. destruct (sptr_eqb p k) eqn:Ep; destruct (sptr_eqb q k) eqn:Eq.
  - apply sptr_eqb_eq in Ep. apply sptr_eqb_eq in Eq. subst. contradiction.
  - cbn [mupdate]. rewrite Eq, Ep. reflexivity.
  - cbn [mupdate]. rewrite Ep, Eq. reflexivity.
  - cbn [mupdate]. rewrite Ep, Eq. f_equal. cbn [map fst In] in Hp, Hq.
    destruct Hp as [Hp|Hp]; [subst; rewrite sptr_eqb_refl in Ep; discriminate|].
    destruct Hq as [Hq|Hq]; [subst; rewrite sptr_eqb_refl in Eq; discriminate|].
    apply IH; assumption.
Qed.

Lemma set_meta_comm : forall s p q x y, p <> q -> In p (keys s) -> In q (keys s) ->
  set_meta (set_meta s p x) q y = set_meta (set_meta s q y) p x.
Proof.
  intros s p q x y Hne Hp Hq. unfold set_meta. cbn [st_metas set_metas]. rewrite mupdate_comm by assumption. reflexivity.
Qed.

Lemma set_meta_twice : forall s p x y, set_meta (set_meta s p x) p y = set_meta s p y.
Proof.
  intros s p x y. unfold set_meta. cbn [st_metas set_metas].
  assert (E : forall l, mupdate (mupdate l p x) p y = mupdate l p y).
  { induction l as [|[q z] t IH]; cbn [mupdate]; [rewrite sptr_eqb_refl; reflexivity|].
    destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity | rewrite IH; reflexivity]. }
  rewrite E. reflexivity.
Qed.

Lemma footprint_set_meta : forall s p x, footprint (set_meta s p x) = footprint s.
Proof. reflexivity. Qed.

Lemma layout_ok_set_meta : forall L s p x, layout_ok L s -> layout_ok L (set_meta s p x).
Proof. intros L s p x H. exact H. Qed.
