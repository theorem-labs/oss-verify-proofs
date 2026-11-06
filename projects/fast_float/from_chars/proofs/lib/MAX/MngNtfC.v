(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngSurgery MngCtx MngExc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RS (L : layout) (s' s : astate) : Prop :=
  exists l, Permutation (map (cell_range L) (image s)) (map (cell_range L) (image s') ++ l).

Lemma RS_refl : forall L s, RS L s s.
Proof. intros L s. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma RS_trans : forall L s1 s2 s3, RS L s3 s2 -> RS L s2 s1 -> RS L s3 s1.
Proof.
  intros L s1 s2 s3 (l2 & P2) (l1 & P1). exists (l2 ++ l1).
  eapply Permutation_trans; [exact P1|]. rewrite app_assoc. apply Permutation_app_tail. exact P2.
Qed.

Lemma RS_of_perm : forall L s' s, Permutation (map (cell_range L) (image s)) (map (cell_range L) (image s')) -> RS L s' s.
Proof. intros L s' s P. exists []. rewrite app_nil_r. exact P. Qed.

Lemma RS_of_eq : forall L s' s, map (cell_range L) (image s') = map (cell_range L) (image s) -> RS L s' s.
Proof. intros L s' s E. apply RS_of_perm. rewrite E. reflexivity. Qed.

Lemma pairwise_app_l : forall {A} (R : A -> A -> Prop) (l1 l2 : list A), pairwise R (l1 ++ l2) -> pairwise R l1.
Proof.
  intros A R l1. induction l1 as [|x t IH]; intros l2 H; [exact I|]. cbn in H |- *. destruct H as [H1 H2].
  split; [intros y Hy; apply H1; apply in_app_iff; left; exact Hy | exact (IH l2 H2)].
Qed.

Lemma PW_of_RS : forall L s' s, PW L s -> RS L s' s -> PW L s'.
Proof.
  intros L s' s HP (l & P). unfold PW in *.
  apply (pairwise_app_l _ _ l). apply (pairwise_perm _ _ _ ranges_disjoint_sym' P). exact HP.
Qed.

Lemma RS_range : forall L s' s c, RS L s' s -> In c (image s') -> exists c0, In c0 (image s) /\ cell_range L c0 = cell_range L c.
Proof.
  intros L s' s c (l & P) Hc. assert (Hr : In (cell_range L c) (map (cell_range L) (image s))).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_app_iff. left. apply in_map. exact Hc. }
  apply in_map_iff in Hr as (c0 & E & H0). exists c0. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_ranges : forall L s s', map (cell_range L) (ctx_cells s') = map (cell_range L) (ctx_cells s).
Proof.
  intros L s s'. unfold ctx_cells. rewrite !map_app, !map_map. reflexivity.
Qed.

Lemma ranges_ctx_only : forall L s s', st_metas s' = st_metas s -> st_areas s' = st_areas s ->
  map (cell_range L) (image s') = map (cell_range L) (image s).
Proof.
  intros L s s' Em Ea. unfold image. rewrite !map_app. rewrite (ctx_ranges L s s'). rewrite Ea.
  rewrite (areas_cells_metas s s' (st_areas s) Em). rewrite (used_metas_metas s s' Em). reflexivity.
Qed.

Lemma RS_ctx_only : forall L s s', st_metas s' = st_metas s -> st_areas s' = st_areas s -> RS L s' s.
Proof. intros L s s' Em Ea. apply RS_of_eq. apply ranges_ctx_only; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition REST (s : astate) (g : sptr) : list mcell :=
  ctx_cells s ++ ahdr (st_areas s)
  ++ flat_map (mcells (st_metas s)) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s)))
  ++ flat_map gcells (filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas s)).

Lemma used_metas_set_filter_any : forall s g x,
  filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas (set_meta s g x))
  = filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas s).
Proof.
  intros s g x. unfold set_meta, used_metas. cbn [st_metas set_metas].
  induction (st_metas s) as [|[q y] t IH]; cbn [mupdate].
  - destruct x as [pr nx| |am]; cbn [flat_map app filter fst]; try rewrite sptr_eqb_refl; reflexivity.
  - destruct (sptr_eqb g q) eqn:E.
    + apply sptr_eqb_eq in E. subst q. cbn [flat_map app].
      destruct x as [pr nx| |am]; destruct y as [pr' nx'| |am']; cbn [filter fst app]; try rewrite sptr_eqb_refl; cbn [negb]; reflexivity.
    + cbn [flat_map]. rewrite !filter_app. rewrite IH. reflexivity.
Qed.

Lemma REST_set_meta : forall s g x, REST (set_meta s g x) g = REST s g.
Proof.
  intros s g x. unfold REST.
  replace (ctx_cells (set_meta s g x)) with (ctx_cells s) by reflexivity.
  replace (st_areas (set_meta s g x)) with (st_areas s) by reflexivity.
  rewrite used_metas_set_filter_any. f_equal. f_equal. f_equal.
  apply flat_map_ext_in'. intros q Hq. apply filter_In in Hq as [_ Hq]. unfold mcells.
  rewrite (mlookup_set_other s g x q); [reflexivity|]. intro E. subst q. rewrite sptr_eqb_refl in Hq. discriminate.
Qed.

Lemma not_used_key : forall s g, List.NoDup (keys s) -> (forall am, MT s g <> Some (MUsed am)) ->
  filter (fun gm => sptr_eqb (fst gm) g) (used_metas s) = [].
Proof.
  intros s g ND Hn. apply filter_key_none. intros Hin. apply in_map_iff in Hin as ([q am] & E & Hin). cbn [fst] in E. subst q.
  apply (Hn am). apply (used_metas_iff s g am ND). exact Hin.
Qed.

Lemma MT_of_key : forall s g, In g (keys s) -> exists y, MT s g = Some y.
Proof.
  intros s g. unfold keys, MT. induction (st_metas s) as [|[k y] t IH]; intros H; [destruct H|].
  cbn [map fst In mlookup] in *. destruct (sptr_eqb g k) eqn:E; [exists y; reflexivity|].
  destruct H as [H|H]; [subst k; rewrite sptr_eqb_refl in E; discriminate | exact (IH H)].
Qed.

Lemma image_decomp_key : forall s g, KS s -> In g (keys s) ->
  Permutation (image s)
    (REST s g ++ meta_slot_cells g (MT s g) ++ match MT s g with Some (MUsed am) => group_cells g am | _ => [] end).
Proof.
  intros s g [ND KO] Hkey. unfold image, REST.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply areas_cells_perm|].
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_head. apply (flat_map_filter_perm gcells (fun gm => sptr_eqb (fst gm) g)). }
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head.
    apply (flat_map_filter_perm (mcells (st_metas s)) (fun q => sptr_eqb q g)). }
  rewrite (KO g Hkey). cbn [flat_map]. rewrite app_nil_r. unfold mcells at 1. change (mlookup (st_metas s) g) with (MT s g).
  destruct (MT s g) as [[pr nx| |am]|] eqn:Hg.
  - rewrite (not_used_key s g ND) by (intros am E; rewrite Hg in E; discriminate). cbn [flat_map]. rewrite !app_nil_r.
    pose proof (perm_surgery (ctx_cells s) (ahdr (st_areas s)) (meta_slot_cells g (Some (MFree pr nx)))
      (flat_map (mcells (st_metas s)) (filter (fun x : sptr => negb (sptr_eqb x g)) (all_slots (st_areas s)))) []
      (flat_map gcells (filter (fun x : sptr * ameta => negb (sptr_eqb (fst x) g)) (used_metas s)))) as P.
    rewrite !app_nil_r in P. cbn [app] in P. exact P.
  - rewrite (not_used_key s g ND) by (intros am E; rewrite Hg in E; discriminate). cbn [flat_map]. rewrite !app_nil_r.
    pose proof (perm_surgery (ctx_cells s) (ahdr (st_areas s)) (meta_slot_cells g (Some MRaw))
      (flat_map (mcells (st_metas s)) (filter (fun x : sptr => negb (sptr_eqb x g)) (all_slots (st_areas s)))) []
      (flat_map gcells (filter (fun x : sptr * ameta => negb (sptr_eqb (fst x) g)) (used_metas s)))) as P.
    rewrite !app_nil_r in P. cbn [app] in P. exact P.
  - assert (Hused : In (g, am) (used_metas s)) by (apply (used_metas_iff s g am ND); exact Hg).
    rewrite (filter_key_single (used_metas s) g am (NoDup_used_metas_keys s ND) Hused).
    cbn [flat_map]. rewrite !app_nil_r. unfold gcells at 1. cbn [fst snd]. apply perm_surgery.
  - exfalso. destruct (MT_of_key s g Hkey) as (y & Hy). rewrite Hg in Hy. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msc_ranges_any : forall L q x y, x <> None -> y <> None ->
  map (cell_range L) (meta_slot_cells q x) = map (cell_range L) (meta_slot_cells q y).
Proof. intros L q x y Hx Hy. destruct x as [[pr nx| |a]|]; [| | | contradiction]; destruct y as [[pr' nx'| |b]|]; try contradiction; reflexivity. Qed.

Lemma image_set_key : forall s g x, KS s -> In g (keys s) ->
  Permutation (image (set_meta s g x))
    (REST s g ++ meta_slot_cells g (Some x) ++ match x with MUsed am => group_cells g am | _ => [] end).
Proof.
  intros s g x HK Hk. assert (HK' : KS (set_meta s g x)) by (apply KS_set_meta; assumption).
  assert (Hk' : In g (keys (set_meta s g x))) by (rewrite keys_set_meta by exact Hk; exact Hk).
  eapply Permutation_trans; [apply (image_decomp_key _ g HK' Hk')|]. rewrite REST_set_meta, MT_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma RS_set_used : forall L s g am am', KS s -> MT s g = Some (MUsed am) ->
  map (cell_range L) (group_cells g am') = map (cell_range L) (group_cells g am) -> RS L (set_meta s g (MUsed am')) s.
Proof.
  intros L s g am am' HK Hg Hgc. assert (Hk : In g (keys s)) by (eapply MT_keys; exact Hg).
  pose proof (image_decomp_key s g HK Hk) as P1. pose proof (image_set_key s g (MUsed am') HK Hk) as P2. rewrite Hg in P1.
  apply RS_of_perm. eapply Permutation_trans; [apply Permutation_map; exact P1|]. eapply Permutation_trans.
  2:{ apply Permutation_map. apply Permutation_sym. exact P2. }
  rewrite !map_app. rewrite Hgc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma RS_set_free : forall L s g pr nx, KS s -> In g (keys s) -> RS L (set_meta s g (MFree pr nx)) s.
Proof.
  intros L s g pr nx HK Hk. pose proof (image_decomp_key s g HK Hk) as P1. pose proof (image_set_key s g (MFree pr nx) HK Hk) as P2.
  destruct (MT_of_key s g Hk) as (y & Hy). rewrite Hy in P1.
  change (match MFree pr nx with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in P2. rewrite app_nil_r in P2.
  exists (map (cell_range L) (match y with MUsed am => group_cells g am | _ => [] end)).
  eapply Permutation_trans; [apply Permutation_map; exact P1|]. eapply Permutation_trans.
  2:{ apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact P2. }
  rewrite !map_app, <- !app_assoc. apply Permutation_app_head. rewrite (msc_ranges_any L g (Some y) (Some (MFree pr nx))) by discriminate.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cov_set_free : forall s g pr nx c, KS s -> In g (keys s) ->
  In c (image (set_meta s g (MFree pr nx))) -> In c (image s) \/ In c (meta_slot_cells g (Some (MFree pr nx))).
Proof.
  intros s g pr nx c HK Hk Hc. pose proof (image_decomp_key s g HK Hk) as P1. pose proof (image_set_key s g (MFree pr nx) HK Hk) as P2.
  change (match MFree pr nx with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in P2.
  apply (Permutation_in c P2) in Hc. rewrite app_nil_r in Hc. apply in_app_iff in Hc as [Hc|Hc]; [left|right; exact Hc].
  apply (Permutation_in c (Permutation_sym P1)). apply in_app_iff. left. exact Hc.
Qed.

Lemma In_image_set_free : forall s g pr nx c, KS s -> In g (keys s) ->
  In c (meta_slot_cells g (Some (MFree pr nx))) -> In c (image (set_meta s g (MFree pr nx))).
Proof.
  intros s g pr nx c HK Hk Hc. pose proof (image_set_key s g (MFree pr nx) HK Hk) as P2.
  change (match MFree pr nx with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in P2.
  apply (Permutation_in c (Permutation_sym P2)). rewrite app_nil_r. apply in_app_iff. right. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma In_REST_image : forall s g c, KS s -> In g (keys s) -> In c (REST s g) -> In c (image s).
Proof.
  intros s g c HK Hk Hc. apply (Permutation_in c (Permutation_sym (image_decomp_key s g HK Hk))). apply in_app_iff. left. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma footprint_shape : forall s s', st_areas s' = st_areas s -> st_regions s' = st_regions s -> footprint s' = footprint s.
Proof.
  intros s s' Ea Er. unfold footprint. rewrite Ea. unfold region_of. rewrite Er. reflexivity.
Qed.

Lemma layout_ok_shape : forall L s s', st_areas s' = st_areas s -> st_regions s' = st_regions s -> layout_ok L s -> layout_ok L s'.
Proof.
  intros L s s' Ea Er H. unfold layout_ok in *. destruct H as (H1 & H2 & H3 & H4). rewrite (footprint_shape s s' Ea Er). split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
  intros k rg Hk. unfold region_of in Hk. rewrite Er in Hk. exact (H2 k rg Hk).
Qed.

Lemma repr_x_next : forall L s s' (bv bv' : byteview) EXC (Cnew : list mcell),
  repr_x L s bv EXC -> st_areas s' = st_areas s -> st_regions s' = st_regions s -> RS L s' s ->
  (forall a, bv a <> None -> bv' a <> None) ->
  (forall c, In c (image s') -> In c (image s) \/ In c Cnew) ->
  (forall c, In c Cnew -> In c (image s')) ->
  Forall (cell_holds L bv') Cnew ->
  (forall a, bv' a <> bv a -> (exists c', In c' Cnew /\ in_rng (cell_range L c') a) \/
                            (forall c, In c (image s') -> ~ In (mc_loc c) EXC -> ~ in_rng (cell_range L c) a)) ->
  repr_x L s' bv' EXC.
Proof.
  intros L s s' bv bv' EXC Cnew HR Ea Er HRS Hgrow Hcov HNin HNew HWO.
  pose proof HR as (HL & HPW & HC & HF).
  apply (repr_x_step L s s' bv bv' EXC EXC Cnew HR).
  - exact (layout_ok_shape L s s' Ea Er HL).
  - exact (PW_of_RS L s' s HPW HRS).
  - rewrite (footprint_shape s s' Ea Er). apply Forall_forall. intros rg Hrg x Hx. apply Hgrow.
    exact (proj1 (Forall_forall _ _) HF rg Hrg x Hx).
  - intros c Hc. destruct (In_dec loc_eq_dec (mc_loc c) EXC) as [He|He]; [right; right; exact He|].
    destruct (Hcov c Hc) as [H1|H1]; [left; split; [exact H1 | exact He] | right; left; exact H1].
  - exact HNin.
  - exact HNew.
  - exact HWO.
Qed.

(* [comment removed for export] *)
Lemma repr_x_same : forall L s (bv bv' : byteview) EXC,
  repr_x L s bv EXC -> (forall a, bv a <> None -> bv' a <> None) ->
  (forall a, bv' a <> bv a -> forall c, In c (image s) -> ~ In (mc_loc c) EXC -> ~ in_rng (cell_range L c) a) ->
  repr_x L s bv' EXC.
Proof.
  intros L s bv bv' EXC HR Hgrow HWO.
  apply (repr_x_next L s s bv bv' EXC [] HR eq_refl eq_refl (RS_refl L s) Hgrow).
  - intros c Hc. left. exact Hc.
  - intros c [].
  - constructor.
  - intros a Ha. right. exact (HWO a Ha).
Qed.

(* [comment removed for export] *)
Lemma repr_x_drop : forall L s bv l EXC, repr_x L s bv (l :: EXC) -> (forall c, In c (image s) -> mc_loc c <> l) -> repr_x L s bv EXC.
Proof.
  intros L s bv l EXC (HL & HPW & HC & HF) Hn. split; [exact HL|]. split; [exact HPW|]. split; [|exact HF].
  apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HC c Hc) as [[E|E]|H].
  - exfalso. exact (Hn c Hc (eq_sym E)).
  - left. exact E.
  - right. exact H.
Qed.

(* [comment removed for export] *)
Lemma repr_x_weaken : forall L s bv EXC EXC', repr_x L s bv EXC -> (forall l, In l EXC -> In l EXC') -> repr_x L s bv EXC'.
Proof.
  intros L s bv EXC EXC' (HL & HPW & HC & HF) Hsub. split; [exact HL|]. split; [exact HPW|]. split; [|exact HF].
  apply Forall_forall. intros c Hc. destruct (proj1 (Forall_forall _ _) HC c Hc) as [E|H]; [left; exact (Hsub _ E) | right; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cov_links_freed : forall s q am pr nx f c, KS s -> MT s q = Some (MUsed am) ->
  In c (image (set_meta s q (MUsed (am_set_freed f (am_set_links pr nx am))))) ->
  In c (image s) \/ c = MCell (LMem (padd q META_prev)) 8 (optr pr) \/ c = MCell (LMem (padd q META_next)) 8 (optr nx) \/
  c = MCell (LMem (padd q META_freed)) 4 (VZ f).
Proof.
  intros s q am pr nx f c HK Hq Hc. destruct (cov_setm s q am _ c HK Hq Hc) as [H|[H|H]].
  - left. exact H.
  - cbn [meta_slot_cells In] in H.
    change (meta_bits (am_set_freed f (am_set_links pr nx am))) with (meta_bits am) in H.
    cbn [am_set_freed am_set_links am_prev am_next am_mem am_avail am_freed] in H.
    destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
    + right. right. right. reflexivity.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
  - left. rewrite gc_freed, gc_links in H. apply (In_image_used s q am c HK Hq). right. exact H.
Qed.

Lemma cov_avail_freed : forall s q am v f c, KS s -> MT s q = Some (MUsed am) ->
  In c (image (set_meta s q (MUsed (am_set_avail v (am_set_freed f am))))) ->
  In c (image s) \/ c = MCell (LMem (padd q META_avail)) 4 (VZ v) \/ c = MCell (LMem (padd q META_freed)) 4 (VZ f).
Proof.
  intros s q am v f c HK Hq Hc. destruct (cov_setm s q am _ c HK Hq Hc) as [H|[H|H]].
  - left. exact H.
  - cbn [meta_slot_cells In] in H.
    change (meta_bits (am_set_avail v (am_set_freed f am))) with (meta_bits am) in H.
    cbn [am_set_freed am_set_avail am_prev am_next am_mem am_avail am_freed] in H.
    destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
    + right. left. reflexivity.
    + right. right. reflexivity.
    + left. apply (In_image_used s q am _ HK Hq). left. cbn [meta_slot_cells In]. tauto.
  - left. rewrite gc_avail, gc_freed in H. apply (In_image_used s q am c HK Hq). right. exact H.
Qed.

Lemma cov_freed' : forall s q am f c, KS s -> MT s q = Some (MUsed am) ->
  In c (image (set_meta s q (MUsed (am_set_freed f am)))) -> In c (image s) \/ c = MCell (LMem (padd q META_freed)) 4 (VZ f).
Proof.
  intros s q am f c HK Hq Hc. destruct (cov_setm s q am _ c HK Hq Hc) as [H|[H|H]].
  - left. exact H.
  - destruct (msc_freed_cov q am f c H) as [H'|H']; [left; apply (In_image_used s q am c HK Hq); left; exact H' | right; exact H'].
  - left. rewrite gc_freed in H. apply (In_image_used s q am c HK Hq). right. exact H.
Qed.

Lemma msc_loc_same : forall q x y c, x <> None -> y <> None -> In c (meta_slot_cells q x) ->
  exists c0, In c0 (meta_slot_cells q y) /\ mc_loc c0 = mc_loc c /\ mc_w c0 = mc_w c.
Proof.
  intros q x y c Hx Hy Hc.
  assert (Ex : exists v1 v2 v3 v4 v5 v6, meta_slot_cells q x =
     [MCell (LMem (padd q META_prev)) 8 v1; MCell (LMem (padd q META_next)) 8 v2; MCell (LMem (padd q META_mem)) 8 v3;
      MCell (LMem (padd q META_avail)) 4 v4; MCell (LMem (padd q META_freed)) 4 v5; MCell (LMem (padd q META_bits)) 8 v6]).
  { destruct x as [[pr nx| |a]|]; [| | | contradiction]; eexists _, _, _, _, _, _; reflexivity. }
  assert (Ey : exists v1 v2 v3 v4 v5 v6, meta_slot_cells q y =
     [MCell (LMem (padd q META_prev)) 8 v1; MCell (LMem (padd q META_next)) 8 v2; MCell (LMem (padd q META_mem)) 8 v3;
      MCell (LMem (padd q META_avail)) 4 v4; MCell (LMem (padd q META_freed)) 4 v5; MCell (LMem (padd q META_bits)) 8 v6]).
  { destruct y as [[pr nx| |a]|]; [| | | contradiction]; eexists _, _, _, _, _, _; reflexivity. }
  destruct Ex as (v1 & v2 & v3 & v4 & v5 & v6 & Ex). destruct Ey as (w1 & w2 & w3 & w4 & w5 & w6 & Ey). rewrite Ex in Hc. rewrite Ey.
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - exists (MCell (LMem (padd q META_prev)) 8 w1). split; [left; reflexivity | split; reflexivity].
  - exists (MCell (LMem (padd q META_next)) 8 w2). split; [right; left; reflexivity | split; reflexivity].
  - exists (MCell (LMem (padd q META_mem)) 8 w3). split; [right; right; left; reflexivity | split; reflexivity].
  - exists (MCell (LMem (padd q META_avail)) 4 w4). split; [right; right; right; left; reflexivity | split; reflexivity].
  - exists (MCell (LMem (padd q META_freed)) 4 w5). split; [right; right; right; right; left; reflexivity | split; reflexivity].
  - exists (MCell (LMem (padd q META_bits)) 8 w6). split; [right; right; right; right; right; left; reflexivity | split; reflexivity].
Qed.

Lemma msc_free_links : forall q pr nx pr' nx' c, In c (meta_slot_cells q (Some (MFree pr' nx'))) ->
  In c (meta_slot_cells q (Some (MFree pr nx))) \/ c = MCell (LMem (padd q META_prev)) 8 (optr pr') \/ c = MCell (LMem (padd q META_next)) 8 (optr nx').
Proof.
  intros q pr nx pr' nx' c Hc. cbn [meta_slot_cells In] in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - right. left. reflexivity.
  - right. right. reflexivity.
  - left. cbn [meta_slot_cells In]. right. right. left. reflexivity.
  - left. cbn [meta_slot_cells In]. right. right. right. left. reflexivity.
  - left. cbn [meta_slot_cells In]. right. right. right. right. left. reflexivity.
  - left. cbn [meta_slot_cells In]. right. right. right. right. right. left. reflexivity.
Qed.

Lemma msc_key_in_image : forall s q x c, KS s -> MT s q = Some x -> In c (meta_slot_cells q (Some x)) -> In c (image s).
Proof.
  intros s q x c HK Hq Hc. assert (Hk : In q (keys s)) by (eapply MT_keys; exact Hq).
  apply (Permutation_in c (Permutation_sym (image_decomp_key s q HK Hk))). rewrite Hq. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
Qed.
