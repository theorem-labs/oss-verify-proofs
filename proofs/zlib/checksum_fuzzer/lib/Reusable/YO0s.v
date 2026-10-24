(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac simp_st :=
cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count
st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas
st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas
set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas
am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots
am_set_links am_set_prev am_set_next am_set_avail am_set_freed am_set_aidx am_set_slots] in *.
Section d.
Context (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Lemma Inv_set_seq s v : Inv X R U s -> 0 <= v <= 255 -> Inv X R U (set_seq v s).
Proof.
intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
Qed.
Lemma Inv_set_mmap_counter s v : Inv X R U s -> 0 <= v < 2 ^ 32 -> Inv X R U (set_mmap_counter v s).
Proof.
intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
Qed.
Lemma Inv_set_init_done s : Inv X R U s -> Inv X R U (set_init_done true s).
Proof.
intros H. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st.
repeat match goal with |- _ /\ _ => split end; try tauto. discriminate.
Qed.
Lemma Inv_set_unmap_seq s l :
Inv X R U s -> length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) ->
Inv X R U (set_unmap_seq l s).
Proof.
intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
Qed.
Lemma Inv_set_bounces s l :
Inv X R U s -> length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) ->
Inv X R U (set_bounces l s).
Proof.
intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
Qed.
End d.
Lemma zset_length32_range l k v :
length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) -> 0 <= v <= 255 ->
length (zset k v l) = 32%nat /\ (forall u, In u (zset k v l) -> 0 <= u <= 255).
Proof.
intros Hl Hr Hv. split; [rewrite length_zset; exact Hl|].
intros u Hu. unfold zset in Hu.
revert Hu. generalize (Z.to_nat k) as n. intros n Hu.
assert (G : forall l' n', (forall u, In u l' -> 0 <= u <= 255) -> In u (zupd l' n' v) -> 0 <= u <= 255).
{ clear - Hv. induction l' as [|h t IH]; intros [|n'] Hr' Hu; cbn in Hu; try contradiction.
- destruct Hu as [<-|Hu]; [lia | apply Hr'; right; exact Hu].
- destruct Hu as [<-|Hu]; [apply Hr'; left; reflexivity | apply (IH n'); [intros w Hw; apply Hr'; right; exact Hw | exact Hu]]. }
eapply G; eauto.
Qed.
Lemma repeat0_32_range : length (repeat 0 32) = 32%nat /\ (forall u, In u (repeat 0 32) -> 0 <= u <= 255).
Proof. split; [reflexivity|]. intros u Hu. apply repeat_spec in Hu. lia. Qed.
Definition upd_meta (g : sptr) (x : mslot) (s : astate) : astate :=
set_metas (mupdate (st_metas s) g x) s.
Lemma MT_upd_same g x s : MT (upd_meta g x s) g = Some x.
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_same. Qed.
Lemma MT_upd_other g x s p : p <> g -> MT (upd_meta g x s) p = MT s p.
Proof. intros. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_other. assumption. Qed.
Lemma MT_upd g x s p : MT (upd_meta g x s) p = if sptr_eqb p g then Some x else MT s p.
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate. Qed.
Lemma keys_upd_In g x s : In g (keys s) -> keys (upd_meta g x s) = keys s.
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_In. assumption. Qed.
Lemma keys_upd_notIn g x s : ~ In g (keys s) -> keys (upd_meta g x s) = keys s ++ [g].
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_notIn. assumption. Qed.
Lemma MT_Some_In_keys s g x : MT s g = Some x -> In g (keys s).
Proof. unfold MT, keys. apply mlookup_In_keys. Qed.
Lemma MTX_upd X g x s p :
MTX X (upd_meta g x s) p = if sptr_eqb p g then (if memb g X then None else Some x) else MTX X s p.
Proof.
unfold MTX. rewrite MT_upd. destruct (sptr_eqb p g) eqn:E; [|reflexivity].
apply sptr_eqb_eq in E. subst. reflexivity.
Qed.
Lemma usedX_upd X g x s p am :
usedX X (upd_meta g x s) p am <->
(p = g /\ memb g X = false /\ x = MUsed am) \/ (p <> g /\ usedX X s p am).
Proof.
unfold usedX. rewrite MTX_upd. destruct (sptr_eqb p g) eqn:E.
- apply sptr_eqb_eq in E. subst p. destruct (memb g X) eqn:M.
+ split; [discriminate | intros [[_ [H _]] | [H _]]; congruence].
+ split.
* intros H. left. injection H as ->. auto.
* intros [[_ [_ ->]] | [H _]]; [reflexivity | congruence].
- apply sptr_eqb_neq in E. split.
+ intros H. right. auto.
+ intros [[H _] | [_ H]]; [congruence | exact H].
Qed.
Lemma usedX_MT X s g am : usedX X s g am -> MT s g = Some (MUsed am) /\ memb g X = false.
Proof. unfold usedX, MTX. destruct (memb g X); [discriminate | auto]. Qed.
Lemma usedX_intro X s g am : memb g X = false -> MT s g = Some (MUsed am) -> usedX X s g am.
Proof. intros M H. unfold usedX, MTX. rewrite M. exact H. Qed.
Lemma usedX_fun X s g a1 a2 : usedX X s g a1 -> usedX X s g a2 -> a1 = a2.
Proof. unfold usedX. intros H1 H2. rewrite H1 in H2. injection H2. auto. Qed.
Definition geom_same (am0 am1 : ameta) : Prop :=
am_mem am1 = am_mem am0 /\ am_last am1 = am_last am0 /\ am_sc am1 = am_sc am0 /\
am_maplen am1 = am_maplen am0 /\
(forall j fr, ss_fr (nth_slot am0 j) = Some fr -> fr_kind fr = FGroup -> ss_fr (nth_slot am1 j) = Some fr).
Lemma geom_same_stride am0 am1 : geom_same am0 am1 -> stride_of am1 = stride_of am0.
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.
Lemma geom_same_slot_start am0 am1 i : geom_same am0 am1 -> slot_start am1 i = slot_start am0 i.
Proof. intros G. unfold slot_start. rewrite (geom_same_stride _ _ G). destruct G as (-> & _). reflexivity. Qed.
Lemma geom_same_extent am0 am1 : geom_same am0 am1 -> group_extent am1 = group_extent am0.
Proof. intros G. unfold group_extent. rewrite (geom_same_stride _ _ G). destruct G as (_ & -> & _). reflexivity. Qed.
Definition gframes_kept (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop :=
forall j fr, 0 <= j -> ss_fr (nth_slot am0 j) = Some fr -> fr_kind fr = FGroup ->
ss_fr (nth_slot am1 j) = Some fr \/
(forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am0 j).
Definition geom_same_upto (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop :=
am_mem am1 = am_mem am0 /\ am_last am1 = am_last am0 /\ am_sc am1 = am_sc am0 /\
am_maplen am1 = am_maplen am0 /\ gframes_kept X s am0 am1.
Lemma geom_same_upto_of X s am0 am1 : geom_same am0 am1 -> geom_same_upto X s am0 am1.
Proof. intros (A & B & C & D & E). repeat split; auto. intros j fr _ H1 H2. left. apply E; assumption. Qed.
Lemma geom_same_upto_stride X s am0 am1 : geom_same_upto X s am0 am1 -> stride_of am1 = stride_of am0.
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.
Section e.
Variables (X : list sptr) (R R' : option (sptr * Z)) (U : Z -> Z) (s : astate) (g : sptr) (am0 am1 : ameta).
Hypothesis HI : Inv X R U s.
Hypothesis Hg : usedX X s g am0.
Hypothesis G : geom_same_upto X s am0 am1.
Hypothesis Lk : am_prev am1 = am_prev am0 /\ am_next am1 = am_next am0.
Local Notation s' := (upd_meta g (MUsed am1) s).
Lemma uu_keys : keys s' = keys s.
Proof. apply keys_upd_In. eapply MT_Some_In_keys. apply (proj1 (usedX_MT _ _ _ _ Hg)). Qed.
Lemma uu_notX : memb g X = false.
Proof. exact (proj2 (usedX_MT _ _ _ _ Hg)). Qed.
Lemma uu_usedX_g : usedX X s' g am1.
Proof. apply usedX_upd. left. auto using uu_notX. Qed.
Lemma uu_usedX_other p am : p <> g -> (usedX X s' p am <-> usedX X s p am).
Proof. intros Hp. rewrite usedX_upd. split; [intros [[H _]|[_ H]]; [congruence|exact H] | intros H; right; auto]. Qed.
Lemma uu_usedX_inv p am : usedX X s' p am -> (p = g /\ am = am1) \/ (p <> g /\ usedX X s p am).
Proof.
intros H. apply usedX_upd in H as [[-> [_ H]] | [Hp H]]; [left; injection H; auto | right; auto].
Qed.
Lemma uu_ctx : ctx_ok s'.
Proof.
pose proof (inv_ctx HI) as C. unfold ctx_ok in *. unfold upd_meta. simp_st.
destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
intros Hinit. exfalso. destruct (C12 Hinit) as (Hm & _).
pose proof (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hg))) as K.
unfold keys in K. rewrite Hm in K. exact K.
Qed.
Lemma uu_keys_ok : keys_ok s'.
Proof.
pose proof (inv_keys HI) as K. unfold keys_ok in *. rewrite uu_keys.
unfold upd_meta. simp_st. exact K.
Qed.
Lemma uu_areas : areas_ok s'.
Proof. exact (inv_areas HI). Qed.
Lemma uu_Xok : Xok X s'.
Proof.
intros x Hx. destruct (inv_X HI x Hx) as [K M]. split; [rewrite uu_keys; exact K|].
rewrite MT_upd_other; [exact M|]. intros ->.
pose proof uu_notX as N. unfold memb in N.
assert (E : existsb (sptr_eqb g) X = true) by (apply existsb_exists; exists g; split; [exact Hx | apply sptr_eqb_refl]).
congruence.
Qed.
Lemma uu_used_fwd p a : usedX X s p a -> exists a', usedX X s' p a' /\
am_mem a' = am_mem a /\ am_last a' = am_last a /\ am_sc a' = am_sc a /\ am_maplen a' = am_maplen a /\
stride_of a' = stride_of a /\ gframes_kept X s a a'.
Proof.
intros Hp. destruct (sptr_eq_dec p g) as [->|Hne].
- exists am1. pose proof (usedX_fun _ _ _ _ _ Hp Hg) as ->. split; [apply uu_usedX_g|].
destruct G as (G1 & G2 & G3 & G4 & G5). repeat split; auto. eapply geom_same_upto_stride. exact G.
- exists a. split; [apply uu_usedX_other; assumption|]. repeat split; auto. intros j fr _ H1 H2. left. exact H1.
Qed.
Lemma uu_used_bwd p a' : usedX X s' p a' -> exists a, usedX X s p a /\
am_mem a' = am_mem a /\ am_last a' = am_last a /\ am_sc a' = am_sc a /\ am_maplen a' = am_maplen a /\
stride_of a' = stride_of a /\ am_prev a' = am_prev a /\ am_next a' = am_next a /\
(p <> g -> a' = a) /\ (p = g -> a' = am1 /\ a = am0).
Proof.
intros Hp. apply uu_usedX_inv in Hp as [[-> ->] | [Hne Hp]].
- exists am0. split; [exact Hg|]. destruct G as (G1 & G2 & G3 & G4 & G5). destruct Lk as [L1 L2].
repeat split; auto; try congruence. eapply geom_same_upto_stride. exact G.
- exists a'. repeat split; auto; congruence.
Qed.
Lemma uu_nested p a a' :
usedX X s p a ->
am_maplen a' = am_maplen a -> am_sc a' = am_sc a -> am_mem a' = am_mem a -> am_last a' = am_last a ->
nested_ok X s a -> nested_ok X s' a'.
Proof.
intros Up E1 E2 E3 E4 N Hm. rewrite E1 in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
split; [congruence|].
destruct (uu_used_fwd _ _ Hu) as (b' & Hu' & M1 & M2 & M3 & M4 & M5 & M6).
assert (Hf' : ss_fr (nth_slot b' i') = Some fr').
{ destruct (M6 i' fr' ltac:(lia) Hf Hk) as [H|H]; [exact H|]. exfalso. exact (H p a Up Hm Hmem). }
exists g', b', i', fr'. rewrite E2, E3, E4. split; [exact Hu'|]. split; [rewrite M2; exact Hi|].
split; [exact Hf'|]. split; [exact Hk|]. split; [unfold slot_start in *; rewrite M1, M5; exact Hmem|].
split; [rewrite M3; exact Hsc|]. split; [rewrite M3; exact Hsc'|]. exact Hfit.
Qed.
Lemma uu_mapped a a' :
am_maplen a' = am_maplen a -> am_mem a' = am_mem a -> am_last a' = am_last a -> stride_of a' = stride_of a ->
am_sc a' = am_sc a ->
mapped_ok s a -> mapped_ok s' a'.
Proof.
intros E1 E2 E3 E4 E5 M Hm. rewrite E1 in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6 & H7).
exists r, rg. rewrite E1, E2, E3, E4, E5. repeat split; auto.
Qed.
Lemma uu_inside a a' b b' :
am_mem a' = am_mem a -> group_extent a' = group_extent a ->
am_mem b' = am_mem b -> am_last b' = am_last b -> stride_of b' = stride_of b ->
gframes_kept X s b b' ->
inside X s a b -> inside X s' a' b'.
Proof.
intros A1 A2 B1 B2 B3 B4 (j & fr & c & ac & Hj & Hfr & Hk & Hc & Hml & Hmem & Hlo & Hhi & Hfit).
destruct (uu_used_fwd _ _ Hc) as (ac' & Hc' & C1 & C2 & C3 & C4 & C5 & C6).
exists j, fr, c, ac'.
split; [rewrite B2; exact Hj|].
split; [destruct (B4 j fr ltac:(lia) Hfr Hk) as [H|H]; [exact H | exfalso; exact (H c ac Hc Hml Hmem)]|].
split; [exact Hk|].
split; [exact Hc'|].
split; [rewrite C4; exact Hml|].
split; [unfold slot_start in *; rewrite C1, B1, B3; exact Hmem|].
split; [rewrite C1, A1; exact Hlo|].
split; [rewrite A1, A2, C1; unfold group_extent in *; rewrite C5, C2; exact Hhi|].
unfold group_extent in *. rewrite C5, C2. exact Hfit.
Qed.
Lemma uu_laminar : laminar X s'.
Proof.
intros p1 a1' p2 a2' H1 H2 Hne Hr.
destruct (uu_used_bwd _ _ H1) as (a1 & U1 & M1 & L1 & S1 & P1 & T1 & _ & _ & _).
destruct (uu_used_bwd _ _ H2) as (a2 & U2 & M2 & L2 & S2 & P2 & T2 & _ & _ & _).
assert (X1 : group_extent a1' = group_extent a1) by (unfold group_extent; rewrite T1, L1; reflexivity).
assert (X2 : group_extent a2' = group_extent a2) by (unfold group_extent; rewrite T2, L2; reflexivity).
assert (F1 : gframes_kept X s a1 a1').
{ destruct (uu_used_fwd _ _ U1) as (x & Ux & _ & _ & _ & _ & _ & Fx). pose proof (usedX_fun _ _ _ _ _ Ux H1) as ->. exact Fx. }
assert (F2 : gframes_kept X s a2 a2').
{ destruct (uu_used_fwd _ _ U2) as (x & Ux & _ & _ & _ & _ & _ & Fx). pose proof (usedX_fun _ _ _ _ _ Ux H2) as ->. exact Fx. }
destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne ltac:(rewrite <- M1, <- M2; exact Hr)) as [D | [I | I]].
- left. unfold spans_disjoint in *. rewrite M1, M2, X1, X2. exact D.
- right. left. eapply uu_inside; eauto.
- right. right. eapply uu_inside; eauto.
Qed.
Lemma uu_maps : maps_unique X s'.
Proof.
intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
destruct (uu_used_bwd _ _ H1) as (a1 & U1 & M1 & _ & _ & P1 & _).
destruct (uu_used_bwd _ _ H2) as (a2 & U2 & M2 & _ & _ & P2 & _).
eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
Qed.
Lemma uu_alinks sc q : alinks X s' sc q = alinks X s sc q.
Proof.
unfold alinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
destruct G as (_ & _ & -> & _). destruct Lk as [-> ->]. reflexivity.
Qed.
Lemma uu_flinks q : flinks X s' q = flinks X s q.
Proof.
unfold flinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'. reflexivity.
Qed.
Lemma uu_usage : usage_ok X U s'.
Proof.
intros sc Hsc. pose proof (inv_usage HI sc Hsc) as E.
unfold usage_of in *. unfold upd_meta at 1. simp_st. rewrite E. f_equal.
unfold class_sum. rewrite uu_keys. apply (f_equal (fun l => fold_right _ 0 l)) || idtac.
induction (keys s) as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
unfold contrib. rewrite MTX_upd. destruct (sptr_eqb k g) eqn:Ek; [|reflexivity].
apply sptr_eqb_eq in Ek. subst k. rewrite uu_notX. pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
destruct G as (_ & -> & -> & _). reflexivity.
Qed.
Lemma uu_active_hd sc : active_hd s' sc = active_hd s sc.
Proof. reflexivity. Qed.
Section o.
Hypothesis Hmasks : masks_ok am1.
Hypothesis Hslots : forall i, 0 <= i <= am_last am1 -> slot_ok R' g am1 i.
Hypothesis Hclass : class_ok R' g am1.
Hypothesis HRother : forall p i, p <> g -> (R' = Some (p, i) <-> R = Some (p, i)).
Hypothesis HRg : forall i, R' = Some (g, i) ->
0 <= i <= am_last am1 /\ ss_fr (nth_slot am1 i) = None /\ allocated am1 i = true.
Hypothesis Hfull : am_sc am0 < 48 -> (am_prev am0, am_next am0) = (None, None) ->
am_avail am1 = 0 /\ am_freed am1 = 0.
Hypothesis HR1 : am_sc am0 < 48 -> am_avail am1 <> 0 -> active_hd s (am_sc am0) = Some g.
Hypothesis HR2 : am_sc am0 < 48 -> (am_prev am0, am_next am0) <> (None, None) ->
active_hd s (am_sc am0) <> Some g -> (forall i, R' <> Some (g, i)) -> am_freed am1 <> 0.
Hypothesis Hpart : am_aidx am1 < am_last am1 ->
forall p a, usedX X s p a -> p <> g -> am_sc a = am_sc am0 -> ~ am_aidx a < am_last a.
Lemma uu_groups p am : usedX X s' p am -> group_ok X R' s' p am.
Proof.
intros Hp. destruct (uu_used_bwd _ _ Hp) as (a & Ua & M1 & M2 & M3 & M4 & M5 & _ & _ & Ho & Hs).
pose proof (inv_groups HI p a Ua) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
destruct (sptr_eq_dec p g) as [->|Hne].
- destruct (Hs eq_refl) as [-> ->].
split; [exact Hmasks|]. split; [rewrite M4; exact Gml|]. split; [exact Hslots|].
split; [exact Hclass|]. split; [eapply uu_mapped; eauto|]. eapply uu_nested; eauto.
- pose proof (Ho Hne) as ->.
split; [exact Gm|]. split; [exact Gml|]. split.
{ intros i Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
destruct (ss_fr (nth_slot a i)) as [fr|].
- destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|].
split; [intros HR'; apply A2; apply (HRother p i Hne); exact HR'|].
split; [exact A3 | exact A4].
- destruct S3 as [A1|A1]; [left; exact A1 | right]. apply (HRother p i Hne). exact A1. }
split.
{ destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C].
- left. repeat split; auto. destruct C6 as [C6|C6]; [left | right; exact C6].
apply (HRother p 0 Hne). exact C6.
- right. exact C. }
split; [eapply uu_mapped; eauto | eapply uu_nested; eauto].
Qed.
Lemma uu_rings : rings_ok X R' s'.
Proof.
destruct (inv_rings HI) as (F & A & D).
split.
{ destruct F as (ms & Rg & Fall). exists ms. split.
- eapply ring_ok_ext; [| exact Rg]. intros. apply uu_flinks.
- intros q pr nx Hq. rewrite MTX_upd in Hq. destruct (sptr_eqb q g); [|eapply Fall; exact Hq].
destruct (memb g X); discriminate. }
split.
{ intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
split; [eapply ring_ok_ext; [intros; apply uu_alinks | exact Rg] |].
rewrite uu_active_hd.
split.
{ intros q a Hq Hsca. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & _ & _).
rewrite P1, P2. apply (Mem q a0 Ua). congruence. }
split.
{ intros q a Hq Hsca Hnin. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
destruct (sptr_eq_dec q g) as [->|Hne].
- destruct (Hs eq_refl) as [-> ->]. apply Hfull; [lia|].
destruct (Mem g am0 Hg ltac:(congruence)) as [M1 M2].
destruct (am_prev am0), (am_next am0); try reflexivity; exfalso; apply Hnin, M2; discriminate.
- pose proof (Ho Hne) as ->. apply (Full q a0 Ua); [congruence | exact Hnin]. }
split.
{ intros q a Hq Hsca Hav. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
destruct (sptr_eq_dec q g) as [->|Hne].
- destruct (Hs eq_refl) as [-> ->]. rewrite <- Hsca, M3. apply HR1; [lia|exact Hav].
- pose proof (Ho Hne) as ->. eapply Q1; eauto; congruence. }
{ intros q a Hq Hsca Hin Hnh HnR. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
destruct (sptr_eq_dec q g) as [->|Hne].
- destruct (Hs eq_refl) as [-> ->]. apply HR2; [lia| |rewrite <- M3, Hsca; exact Hnh|exact HnR].
intros E. apply (Mem g am0 Hg ltac:(congruence)) in Hin. apply Hin. exact E.
- pose proof (Ho Hne) as ->. eapply Q2; eauto; try congruence.
intros i E. apply (HnR i). apply (HRother q i Hne). exact E. } }
{ intros q a Hq H63. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & _ & _).
rewrite P1, P2. eapply D; eauto; congruence. }
Qed.
Lemma uu_partial : partial_unique X s'.
Proof.
pose proof (inv_partial HI) as P.
intros p1 a1 p2 a2 H1 H2 Hsc Hp1 Hp2.
destruct (uu_used_bwd _ _ H1) as (b1 & U1 & _ & L1 & S1 & _ & _ & _ & _ & Ho1 & Hs1).
destruct (uu_used_bwd _ _ H2) as (b2 & U2 & _ & L2 & S2 & _ & _ & _ & _ & Ho2 & Hs2).
destruct (sptr_eq_dec p1 g) as [->|N1]; destruct (sptr_eq_dec p2 g) as [->|N2]; try reflexivity.
- destruct (Hs1 eq_refl) as [-> ->]. pose proof (Ho2 N2) as ->.
exfalso. eapply (Hpart Hp1 p2 b2 U2 N2); [congruence | exact Hp2].
- destruct (Hs2 eq_refl) as [-> ->]. pose proof (Ho1 N1) as ->.
exfalso. eapply (Hpart Hp2 p1 b1 U1 N1); [congruence | exact Hp1].
- pose proof (Ho1 N1) as ->. pose proof (Ho2 N2) as ->. eapply P; eauto.
Qed.
Lemma uu_reserved : reserved_ok X R' s'.
Proof.
intros p i HR'. destruct (sptr_eq_dec p g) as [->|Hne].
- exists am1. split; [apply uu_usedX_g|]. apply HRg. exact HR'.
- apply (HRother p i Hne) in HR'. destruct (inv_reserved HI p i HR') as (a & Ua & Hi & Hf & Ha).
exists a. split; [apply uu_usedX_other; assumption|]. auto.
Qed.
Lemma Inv_used_update : Inv X R' U s'.
Proof.
split; [apply uu_ctx|]. split; [apply uu_keys_ok|]. split; [apply uu_areas|].
split; [apply uu_Xok|]. split; [apply uu_groups|]. split; [apply uu_laminar|].
split; [apply uu_maps|]. split; [apply uu_rings|]. split; [apply uu_usage|].
split; [apply uu_reserved | apply uu_partial].
Qed.
End o.
End e.
Section y.
Variables (X X' : list sptr) (R : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
Hypothesis HI : Inv X R U s.
Hypothesis EU : forall p am, usedX X' s' p am <-> usedX X s p am.
Hypothesis ER : st_regions s' = st_regions s.
Lemma tr_nested a : nested_ok X s a -> nested_ok X' s' a.
Proof.
intros N Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hrest)].
split; [exact N63|]. exists g', b, i', fr'. split; [apply EU; exact Hu | exact Hrest].
Qed.
Lemma tr_mapped a : mapped_ok s a -> mapped_ok s' a.
Proof.
intros M Hm. destruct (M Hm) as (r & rg & H). exists r, rg. unfold region_of in *. rewrite ER. exact H.
Qed.
Lemma tr_inside a b : inside X s a b -> inside X' s' a b.
Proof.
intros (j & fr & c & ac & H1 & H2 & H3 & H4 & H5). exists j, fr, c, ac.
repeat split; try tauto. apply EU. exact H4.
Qed.
Lemma tr_groups : forall g am, usedX X' s' g am -> group_ok X' R s' g am.
Proof.
intros g am Hg. apply EU in Hg. pose proof (inv_groups HI g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply tr_mapped; exact G5 | apply tr_nested; exact G6].
Qed.
Lemma tr_laminar : laminar X' s'.
Proof.
intros p1 a1 p2 a2 H1 H2 Hne Hr. apply EU in H1. apply EU in H2.
destruct (inv_laminar HI p1 a1 p2 a2 H1 H2 Hne Hr) as [D|[I|I]];
[left; exact D | right; left; apply tr_inside; exact I | right; right; apply tr_inside; exact I].
Qed.
Lemma tr_maps : maps_unique X' s'.
Proof. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_maps HI); eauto. Qed.
Lemma tr_partial : partial_unique X' s'.
Proof. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_partial HI); eauto. Qed.
Lemma tr_reserved : reserved_ok X' R s'.
Proof.
intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & H). exists am. split; [apply EU; exact Hu | exact H].
Qed.
Lemma tr_direct : direct_unlinked X' s'.
Proof. intros g am Hg. apply EU in Hg. exact (proj2 (proj2 (inv_rings HI)) g am Hg). Qed.
Lemma tr_alinks sc q : alinks X' s' sc q = alinks X s sc q.
Proof.
unfold alinks.
destruct (MTX X' s' q) as [[pr nx| |am]|] eqn:E1; destruct (MTX X s q) as [[pr' nx'| |am']|] eqn:E2; try reflexivity.
all: try (assert (Hu : usedX X' s' q am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate; injection E2 as ->; reflexivity).
all: try (assert (Hu : usedX X s q am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
Qed.
Lemma tr_active sc : st_active s' = st_active s -> active_ring_ok X R s sc -> active_ring_ok X' R s' sc.
Proof.
intros EA (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
assert (EH : active_hd s' sc = active_hd s sc) by (unfold active_hd; rewrite EA; reflexivity).
rewrite EH. split; [eapply ring_ok_ext; [intros; apply tr_alinks | exact Rg] |].
split; [intros q a Hq; apply EU in Hq; apply Mem; exact Hq|].
split; [intros q a Hq; apply EU in Hq; apply Full; exact Hq|].
split; [intros q a Hq; apply EU in Hq; apply Q1; exact Hq|].
intros q a Hq; apply EU in Hq; apply Q2; exact Hq.
Qed.
Theorem Inv_transfer :
ctx_ok s' -> keys_ok s' -> areas_ok s' -> Xok X' s' -> rings_ok X' R s' -> usage_ok X' U' s' ->
Inv X' R U' s'.
Proof.
intros C K A XO RG US.
split; [exact C|]. split; [exact K|]. split; [exact A|].
split; [exact XO|]. split; [apply tr_groups|]. split; [apply tr_laminar|]. split; [apply tr_maps|].
split; [exact RG|]. split; [exact US|]. split; [apply tr_reserved | apply tr_partial].
Qed.
End y.
Lemma nth_slot_upd_slot am i j x :
0 <= i -> 0 <= j -> (Z.to_nat i < length (am_slots am))%nat ->
nth_slot (upd_slot am i x) j = if j =? i then x else nth_slot am j.
Proof.
intros Hi Hj Hlen. unfold nth_slot, upd_slot. cbn [am_slots am_set_slots]. rewrite nth_lupd.
destruct (j =? i) eqn:E.
- apply Z.eqb_eq in E. subst j. rewrite Nat.eqb_refl.
replace (Nat.ltb (Z.to_nat i) (length (am_slots am))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. exact Hlen.
- replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false; [reflexivity|].
symmetry. apply Nat.eqb_neq. apply Z.eqb_neq in E. lia.
Qed.
Lemma flat_map_ext_In {A B} (f g : A -> list B) l :
(forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity).
rewrite IH by (intros a Ha; apply H; right; exact Ha). reflexivity.
Qed.
Definition slot_block0 (am : ameta) (i : Z) : list (sptr * Z) :=
match ss_fr (nth_slot am i) with
| Some fr => match fr_kind fr with
| FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
| FGroup => []
end
| None => []
end.
Definition blocks_of0 (am : ameta) : list (sptr * Z) := flat_map (slot_block0 am) (zseq 0 (am_last am + 1)).
Definition ucontrib0 (x : option mslot) : list (sptr * Z) :=
match x with Some (MUsed am) => blocks_of0 am | _ => [] end.
Definition ublist0 (s : astate) : list (sptr * Z) := flat_map (fun g => ucontrib0 (MT s g)) (keys s).
Lemma user_blocks_ublist0 s : NoDup (keys s) -> user_blocks s = ublist0 s.
Proof.
unfold user_blocks, ublist0, used_metas, keys, MT. generalize (st_metas s) as l. clear s.
induction l as [|[p x] t IH]; intros ND; cbn; [reflexivity|].
inversion ND as [|p' t' Hp Ht]; subst. rewrite sptr_eqb_refl.
assert (E : flat_map (fun g => ucontrib0 (mlookup ((p, x) :: t) g)) (map fst t) = flat_map (fun g => ucontrib0 (mlookup t g)) (map fst t)).
{ apply flat_map_ext_In. intros g Hg. cbn. destruct (sptr_eqb g p) eqn:Eg; [|reflexivity].
apply sptr_eqb_eq in Eg. subst g. exfalso. exact (Hp Hg). }
cbn in E. rewrite E, <- (IH Ht). destruct x as [| |am]; cbn; reflexivity.
Qed.
Notation ublk := ((sptr * Z) * (sptr * Z))%type (only parsing).
Definition slot_block (g : sptr) (am : ameta) (i : Z) : list ublk :=
match ss_fr (nth_slot am i) with
| Some fr => match fr_kind fr with
| FUser => [((padd (slot_start am i) (UNIT * fr_off fr), fr_n fr), (g, i))]
| FGroup => []
end
| None => []
end.
Definition blocks_of (g : sptr) (am : ameta) : list ublk := flat_map (slot_block g am) (zseq 0 (am_last am + 1)).
Definition ucontrib (g : sptr) (x : option mslot) : list ublk :=
match x with Some (MUsed am) => blocks_of g am | _ => [] end.
Definition ublist (s : astate) : list ublk := flat_map (fun g => ucontrib g (MT s g)) (keys s).
Lemma map_fst_blocks_of g am : map fst (blocks_of g am) = blocks_of0 am.
Proof.
unfold blocks_of, blocks_of0. induction (zseq 0 (am_last am + 1)) as [|i z IH]; [reflexivity|].
simpl. rewrite map_app, IH. f_equal.
unfold slot_block, slot_block0. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; reflexivity.
Qed.
Lemma map_fst_ucontrib g x : map fst (ucontrib g x) = ucontrib0 x.
Proof. destruct x as [[| |am]|]; cbn [ucontrib ucontrib0 map]; try reflexivity. apply map_fst_blocks_of. Qed.
Lemma map_fst_ublist s : map fst (ublist s) = ublist0 s.
Proof.
unfold ublist, ublist0. induction (keys s) as [|g k IH]; [reflexivity|]. simpl. rewrite map_app, IH, map_fst_ucontrib. reflexivity.
Qed.
Lemma user_blocks_ublist s : NoDup (keys s) -> user_blocks s = map fst (ublist s).
Proof. intros ND. rewrite map_fst_ublist. apply user_blocks_ublist0. exact ND. Qed.
Definition ub_same (s s' : astate) : Prop :=
exists ext, keys s' = keys s ++ ext /\ (forall m, In m ext -> ucontrib m (MT s' m) = []) /\
(forall g, In g (keys s) -> ucontrib g (MT s' g) = ucontrib g (MT s g)).
Lemma ub_same_refl s : ub_same s s.
Proof. exists []. rewrite app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.
Lemma ub_same_trans s1 s2 s3 : ub_same s1 s2 -> ub_same s2 s3 -> ub_same s1 s3.
Proof.
intros (e1 & K1 & Z1 & S1) (e2 & K2 & Z2 & S2). exists (e1 ++ e2). rewrite K2, K1, <- app_assoc. split; [reflexivity|]. split.
- intros m Hm. apply in_app_iff in Hm as [Hm|Hm]; [|apply Z2; exact Hm].
rewrite S2; [apply Z1; exact Hm|]. rewrite K1. apply in_app_iff. right. exact Hm.
- intros g Hg. rewrite S2; [apply S1; exact Hg|]. rewrite K1. apply in_app_iff. left. exact Hg.
Qed.
Lemma flat_map_nil_In {A B} (f : A -> list B) l : (forall a, In a l -> f a = []) -> flat_map f l = [].
Proof.
induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). cbn. apply IH. intros a Ha. apply H. right. exact Ha.
Qed.
Lemma ub_same_ublist s s' : ub_same s s' -> ublist s' = ublist s.
Proof.
intros (ext & K & Zx & Sm). unfold ublist. rewrite K, flat_map_app.
rewrite (flat_map_ext_In _ _ (keys s) Sm). rewrite (flat_map_nil_In _ ext Zx). apply app_nil_r.
Qed.
Lemma ub_same_user_blocks s s' : NoDup (keys s) -> NoDup (keys s') -> ub_same s s' -> user_blocks s' = user_blocks s.
Proof. intros N N' H. rewrite (user_blocks_ublist s N), (user_blocks_ublist s' N'). f_equal. apply ub_same_ublist. exact H. Qed.
Lemma ub_same_metas s s' : st_metas s' = st_metas s -> ub_same s s'.
Proof. intros E. exists []. unfold keys, MT. rewrite E, app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.
Lemma ub_same_upd_In s g x : In g (keys s) -> ucontrib g (Some x) = ucontrib g (MT s g) -> ub_same s (upd_meta g x s).
Proof.
intros Hg Hx. exists []. rewrite app_nil_r. split; [apply keys_upd_In; exact Hg|]. split; [intros m []|].
intros q Hq. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; subst q; exact Hx | reflexivity].
Qed.
Lemma ub_same_upd_notIn s g x : ~ In g (keys s) -> ucontrib g (Some x) = [] -> ub_same s (upd_meta g x s).
Proof.
intros Hg Hx. exists [g]. split; [apply keys_upd_notIn; exact Hg|]. split.
- intros m [<-|[]]. rewrite MT_upd_same. exact Hx.
- intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. exact (Hg Hq).
Qed.
Lemma blocks_of_ext g a b :
am_mem b = am_mem a -> am_last b = am_last a -> am_sc b = am_sc a -> am_maplen b = am_maplen a -> am_slots b = am_slots a ->
blocks_of g b = blocks_of g a.
Proof. intros E1 E2 E3 E4 E5. unfold blocks_of, slot_block, nth_slot, slot_start, stride_of. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.
Lemma blocks_of_links g p n am : blocks_of g (am_set_links p n am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.
Lemma blocks_of_masks g av fr ai am : blocks_of g (am_set_aidx ai (am_set_freed fr (am_set_avail av am))) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.
Lemma blocks_of_avail g av am : blocks_of g (am_set_avail av am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.
Lemma blocks_of_freed g fr am : blocks_of g (am_set_freed fr am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.
Lemma blocks_of_aidx g ai am : blocks_of g (am_set_aidx ai am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.
Lemma ucontrib_with_links g x p n : ucontrib g (Some (with_links x p n)) = ucontrib g (Some x).
Proof. destruct x; cbn; [reflexivity | reflexivity | apply blocks_of_links]. Qed.
Lemma blocks_of_frameless g am : (forall j, ss_fr (nth_slot am j) = None) -> blocks_of g am = [].
Proof.
intros H. unfold blocks_of. induction (zseq 0 (am_last am + 1)) as [|i t IH]; [reflexivity|]. cbn. unfold slot_block at 1. rewrite H. exact IH.
Qed.
Definition slotst_block (g : sptr) (am : ameta) (i : Z) (x : slotst) : list ublk :=
match ss_fr x with
| Some fr => match fr_kind fr with
| FUser => [((padd (slot_start am i) (UNIT * fr_off fr), fr_n fr), (g, i))]
| FGroup => []
end
| None => []
end.
Lemma slot_block_upd_slot g am i x j :
0 <= i -> 0 <= j -> (Z.to_nat i < length (am_slots am))%nat ->
slot_block g (upd_slot am i x) j = if j =? i then slotst_block g am i x else slot_block g am j.
Proof.
intros Hi Hj Hlen. unfold slot_block, slotst_block. rewrite nth_slot_upd_slot by assumption.
replace (slot_start (upd_slot am i x) j) with (slot_start am j) by (destruct am; reflexivity).
destruct (j =? i) eqn:E; [apply Z.eqb_eq in E; subst j|]; reflexivity.
Qed.
Lemma zseq_NoDup lo n : NoDup (zseq lo n).
Proof.
unfold zseq. apply NoDup_map_inv with (f := fun z => Z.to_nat (z - lo)).
rewrite map_map. erewrite map_ext; [rewrite map_id; apply seq_NoDup|]. intros a. cbn. lia.
Qed.
Lemma blocks_of_upd_slot g am i x :
0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
exists l1 l2, blocks_of g am = l1 ++ slot_block g am i ++ l2 /\ blocks_of g (upd_slot am i x) = l1 ++ slotst_block g am i x ++ l2.
Proof.
intros Hi Hlen. unfold blocks_of.
replace (am_last (upd_slot am i x)) with (am_last am) by (destruct am; reflexivity).
assert (Hin : In i (zseq 0 (am_last am + 1))) by (apply In_zseq; lia).
destruct (in_split _ _ Hin) as (z1 & z2 & Ez).
pose proof (zseq_NoDup 0 (am_last am + 1)) as ND. rewrite Ez in ND. pose proof (NoDup_remove_2 _ _ _ ND) as Hni.
assert (EF : forall j, In j (z1 ++ z2) -> slot_block g (upd_slot am i x) j = slot_block g am j).
{ intros j Hj.
assert (Hj0 : 0 <= j).
{ assert (In j (zseq 0 (am_last am + 1))) as H.
{ rewrite Ez. apply in_app_iff in Hj. apply in_app_iff. destruct Hj; [left | right; right]; assumption. }
apply In_zseq in H. lia. }
rewrite slot_block_upd_slot by (try lia; rewrite Hlen; lia). destruct (j =? i) eqn:E; [|reflexivity].
apply Z.eqb_eq in E. subst j. exfalso. exact (Hni Hj). }
exists (flat_map (slot_block g am) z1), (flat_map (slot_block g am) z2).
rewrite Ez, !flat_map_app. cbn [flat_map]. split; [reflexivity|].
rewrite (flat_map_ext_In _ _ z1 (fun j Hj => EF j ltac:(apply in_app_iff; left; exact Hj))).
rewrite (flat_map_ext_In _ _ z2 (fun j Hj => EF j ltac:(apply in_app_iff; right; exact Hj))).
rewrite slot_block_upd_slot, Z.eqb_refl by (try lia; rewrite Hlen; lia). reflexivity.
Qed.
Lemma blocks_of_upd_slot_same g am i x :
0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
slotst_block g am i x = slot_block g am i -> blocks_of g (upd_slot am i x) = blocks_of g am.
Proof.
intros Hi Hlen E. destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & E1 & E2). rewrite E2, E, <- E1. reflexivity.
Qed.
Lemma ublist_split s g :
NoDup (keys s) -> In g (keys s) ->
exists L1 L2, (forall x, ublist (upd_meta g x s) = L1 ++ ucontrib g (Some x) ++ L2) /\ ublist s = L1 ++ ucontrib g (MT s g) ++ L2.
Proof.
intros ND Hg. destruct (in_split _ _ Hg) as (k1 & k2 & Ek).
pose proof ND as ND'. rewrite Ek in ND'. pose proof (NoDup_remove_2 _ _ _ ND') as Hni.
exists (flat_map (fun q => ucontrib q (MT s q)) k1), (flat_map (fun q => ucontrib q (MT s q)) k2). split.
- intros x. unfold ublist. rewrite (keys_upd_In _ _ _ Hg), Ek, flat_map_app. cbn [flat_map]. rewrite MT_upd_same.
rewrite (flat_map_ext_In (fun q => ucontrib q (MT (upd_meta g x s) q)) (fun q => ucontrib q (MT s q)) k1).
2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. left. exact Hq. }
rewrite (flat_map_ext_In (fun q => ucontrib q (MT (upd_meta g x s) q)) (fun q => ucontrib q (MT s q)) k2).
2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. right. exact Hq. }
reflexivity.
- unfold ublist. rewrite Ek, flat_map_app. reflexivity.
Qed.
Lemma ublist_upd_slot s g am i x :
NoDup (keys s) -> MT s g = Some (MUsed am) -> 0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
exists l1 l2, ublist s = l1 ++ slot_block g am i ++ l2 /\
ublist (upd_meta g (MUsed (upd_slot am i x)) s) = l1 ++ slotst_block g am i x ++ l2.
Proof.
intros ND Mg Hi Hlen.
destruct (ublist_split s g ND (MT_Some_In_keys _ _ _ Mg)) as (L1 & L2 & Hupd & Hs).
destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & B1 & B2).
exists (L1 ++ l1), (l2 ++ L2). rewrite Hs, Hupd, Mg. cbn [ucontrib]. rewrite B1, B2, <- !app_assoc. split; reflexivity.
Qed.
