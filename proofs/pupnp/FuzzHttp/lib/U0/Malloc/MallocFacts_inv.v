(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_Ext
  MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_WRealloc MI_Sim MI_Contracts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import KRemapDef MRemapOp MI_WRemap.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocRep MallocTree MallocBlocks.
Import ListNotations.
Local Open Scope Z_scope.

Definition corr1 (st : mstate) (b : block) (k : blk) : Prop :=
  blk_slot b = bslot k /\ blk_size b = bsize k /\ blk_addr b = conc st (bslot k) + UNIT * boff k.
Definition CORR (st : mstate) (LB : list block) (BL : list blk) : Prop := Forall2 (corr1 st) LB BL.

Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.

Lemma conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.

Lemma conc_same st st' p : (exists r, s_regions st !! fst p = Some r /\ s_regions st' !! fst p = Some r) -> conc st' p = conc st p.
Proof. intros (r & H1 & H2). unfold conc, get_region. rewrite H1, H2. reflexivity. Qed.

Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
Lemma cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

Lemma Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
  destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
Qed.

Lemma Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
  - apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.

Lemma Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof.
  induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
  rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.

Lemma Forall2_map_eq {A B C} (P : A -> B -> Prop) (f : A -> C) (g : B -> C) l1 l2 :
  Forall2 P l1 l2 -> (forall a b, P a b -> f a = g b) -> map f l1 = map g l2.
Proof. induction 1; intros E; cbn; [reflexivity|]. rewrite (E _ _ H). f_equal. apply IHForall2. exact E. Qed.

Lemma filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma bl_remove_filter c BL : NoDup (map bslot BL) ->
  bl_remove c BL = filter (fun k => negb (aptr_eqb (bslot k) c)) BL.
Proof.
  induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
  cbn in ND. apply NoDup_cons in ND as [NI ND].
  destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
  - symmetry. apply filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
    exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
  - f_equal. apply IH. exact ND.
Qed.

Lemma mresize_eq st c off n n' m i : s_slots st !! c = Some (m, i) ->
  mresize st c off n n' = rs_st3 st c off n n' m i.
Proof.
  intros Hs. unfold mresize. rewrite Hs. unfold rs_st3, rs_st2, rs_st1. cbv zeta.
  rewrite set_size_eq by reflexivity. reflexivity.
Qed.

Theorem areach_inv resv st LB : AREACH_from resv st LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = 0 /\ CORR st LB BL.
Proof.
  induction 1 as [ceil Hceil|st LB n o o' ans st' pf cst c AR IH Hn FF FC|st LB n o o' ans st' AR IH Hn FF|st LB b pf o o' ans st' AR IH Hb Hfst Hconc FF
                 |st LB b off n' AR IH Hb Hoff HA Hn' ROK|st LB b off n' dst g rg AR IH Hb Hoff HA Hn' Hs SC Hrg OK].
  - exists (led_init resv ceil), (fun _ => []), []. split; [apply INVL_init; [lia| exact Hceil]|]. repeat split; try reflexivity. constructor.
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' (Some pf) INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    unfold mrun in FC |- *. rewrite FC in FT. inversion FT. subst cst rc.
    destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot (((c, off), n) :: BL)) L'), LS', (((c, off), n) :: BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    constructor.
    + split; [reflexivity|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd]. rewrite Epf. apply conc_aadd.
      destruct (blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (r & Hr & _). exists r. exact Hr.
    + eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
      rewrite (conc_same st st' (bslot k)); [reflexivity|].
      destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (malloc_sim pans_mem pupd_mem pans_mem_range st L BL LS n o ans o' st' None INV Hn FF) as (rc & FT & CP & LIVE' & [GPR GPS] & RES).
    destruct rc as [c|]; [destruct RES|]. destruct RES as (LS' & INV').
    set (L' := lafter L (cmalloc (strip st) n) ans) in *.
    exists (set_live (map bslot BL) L'), LS', BL.
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite GPS; exact SEC|].
    eapply Forall2_impl_in; [exact CR|]. intros bb k Hb Hk (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. rewrite C3.
    rewrite (conc_same st st' (bslot k)); [reflexivity|].
    destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
  - destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    destruct (blk_region _ _ _ _ _ ((c, off), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (Epf : pf = aadd c (UNIT * off)).
    { unfold conc, get_region in Hconc, C3. rewrite Hfst, C1 in Hconc. rewrite Hr in Hconc, C3. rewrite C3 in Hconc.
      apply injective_projections; unfold aadd; cbn [fst snd]; [rewrite Hfst, C1; reflexivity| lia]. }
    subst pf.
    destruct (free_sim pans_mem pupd_mem pans_mem_range st L BL LS c off n o ans o' st' INV Hk FF) as (FT & CP & LIVE' & LS' & INV').
    destruct (free_leaf_facts pans_mem pupd_mem st L BL LS c off n o ans o' st' INV Hk FF) as [SUB SEC'].
    set (L' := lafter L (cfree (strip st) (Some c)) ans) in *.
    exists (set_live (map bslot (bl_remove c BL)) L'), LS', (bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
    split; [rewrite SEC'; exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    rewrite C1.
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    rewrite (conc_same st st' (bslot k')); [reflexivity|].
    rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
    destruct (blk_region _ _ _ _ _ k' INV' Hk') as (r' & Hr' & _). exists r'. split; [exact (SUB _ _ Hr')| exact Hr'].
  -
    destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    destruct (blk_region _ _ _ _ _ ((c, bo), n) INV Hk) as (r & Hr & Kr). cbn [bslot fst snd] in Hr.
    assert (bo = off) as -> by (rewrite C1 in HA; rewrite HA in C3; pose proof C3; unfold UNIT in *; lia).
    destruct ROK as (m & i & Hs & FIT & CLS & R32). rewrite C1 in Hs.
    pose proof (INVL_resize x0 st L BL LS c off n n' m i INV Hk eq_refl Hs Hn' FIT R32 CLS) as INV'.
    rewrite C1, C2, (mresize_eq st c off n n' m i Hs).
    pose proof (proj1 (st3_ctrl st c off n n' m i)) as CE.
    exists (set_live (map bslot (((c, off), n') :: bl_remove c BL)) L), LS, (((c, off), n') :: bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; exact RESV|].
    split; [rewrite (ce_secret _ _ CE); exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    constructor.
    + split; [cbn; unfold blk_id, blk_slot in *; cbn in C1 |- *; exact C1|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd].
      rewrite C3. rewrite (conc_same st (rs_st3 st c off n n' m i) c); [reflexivity|].
      exists r. split; [exact Hr|]. rewrite (ce_regions _ _ CE). exact Hr.
    + pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                    ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
      eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
      rewrite (conc_same st (rs_st3 st c off n n' m i) (bslot k')); [reflexivity|].
      rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
      destruct (blk_region _ _ _ _ _ k' INV' ltac:(right; exact Hk')) as (r' & Hr' & _). exists r'. rewrite (ce_regions _ _ CE) in Hr'. split; [exact Hr'|].
      rewrite (ce_regions _ _ CE). exact Hr'.
  -
    destruct IH as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
    assert (bo = off) as -> by (rewrite C1 in HA; rewrite HA in C3; pose proof C3; unfold UNIT in *; lia).
    rewrite C1 in Hs, Hrg, OK |- *. rewrite C2.
    destruct OK as (D0 & DA & NA & N2 & NL & DC & _ & DISJ). cbn [s_reserved s_regions strip] in DISJ.
    change (get_meta_rec st g) with (MR st g) in SC.
    pose proof (INVL_remap x0 st L BL LS c g off n n' dst INV Hk eq_refl eq_refl Hs SC Hn' D0 DA NL N2 DC DISJ rg Hrg) as INV'.
    rewrite <- (rm_eq st c g off n n' dst Hs).
    set (nn := mremap_needed off n') in *.
    exists (set_live (map bslot (((c, off), n') :: bl_remove c BL)) (lremap L (r_base rg) dst nn)), LS, (((c, off), n') :: bl_remove c BL).
    split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; exact RESV|].
    split; [rewrite (rm_secret st c g off n n' dst); exact SEC|].
    rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    constructor.
    + split; [cbn; unfold blk_id, blk_slot in *; cbn in C1 |- *; exact C1|]. split; [reflexivity|]. cbn [blk_addr bslot boff fst snd].
      rewrite (rm_conc_c x0 st L BL LS c g off n n' dst INV Hk eq_refl Hs SC). reflexivity.
    + pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
                    ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
      eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
      rewrite <- (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))) in Hk'.
      rewrite (rm_conc_other st c g off n n' dst (bslot k')); [reflexivity|].
      exact (rm_other_blocks x0 st L BL LS c g off n n' dst INV Hk eq_refl Hs SC D0 k' Hk').
Qed.

Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.