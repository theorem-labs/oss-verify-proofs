(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "am_last"; "MUsed"; "am_mem"; "am_sc"; "frame"; "am_maplen"; "ameta"; "stride_of"; "nth_slot"; "ss_fr"; "fkind"; "slotst"; "am_slots"; "am_next"; "am_prev"; "slot_start"; "fr_kind"; "upd_slot"; "UNIT"; "fr_n"; "fr_off"; "padd"; "st_metas"; "FGroup"; "am_aidx"; "am_avail"; "am_freed"; "am_set_aidx"; "am_set_avail"; "am_set_freed"; "set_init_done"; "sptr_eqb"; "st_active"; "st_regions"; "BrkNever"; "am_set_links"; "astate"; "brkst"; "mupdate"; "region"; "set_bounces"; "set_metas"; "set_mmap_counter"; "set_seq"; "set_unmap_seq"; "st_brk"; "st_init_done"; "with_links"; "zset"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "option"; "list"; "Some"; "bool"; "app"; "pair"; "length"; "nil"; "nat"; "None"; "cons"; "false"; "fst"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "blocks_of"; "ucontrib"; "ub_same"; "ublist"; "slot_block"; "geom_same"; "slotst_block"; "geom_same_upto"; "gframes_kept"; "blocks_of0"; "ublist0"; "ucontrib0"; "slot_block0"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "to_nat"; "mul"; "eqb"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "keys"; "MT"; "Inv"; "memb"; "active_hd"; "alinks"; "group_extent"; "inside"; "mapped_ok"; "nested_ok"; "user_blocks"; "MTX"; "active_ring_ok"; "flinks"; "group_ok"; "reserved_ok"; "rings_ok"; "usage_ok"; "zseq"; "Xok"; "allocated"; "areas_ok"; "class_ok"; "ctx_ok"; "keys_ok"; "slot_ok"; "@Stdlib.Lists.List"; "In"; "flat_map"; "NoDup"; "@Corelib.Lists.ListDef"; "map"; "repeat"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

Section Scalars.
  Context (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).

  Lemma Inv_set_seq s v : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4S1S57Z0Vv;A2S57Vv;ZffA2A2S61VX;VR;VU;S33Vv;Vs;A2A4F_;F_;").
  Proof using .
    intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  Lemma Inv_set_mmap_counter s v : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4S1S57Z0Vv;A2S58Vv;S5dZ2Z20A2A2A2S61VX;VR;VU;S32Vv;Vs;A2A4F_;F_;").
  Proof using .
    intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  Lemma Inv_set_init_done s : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4S2S0S2dS35Vs;A1S2aA3A1S61VX;VR;VU;S26S48Vs;A2A4F_;F_;").
  Proof using .
    intros H Hb. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st.
    repeat match goal with |- _ /\ _ => split end; try tauto. discriminate.
  Qed.

  Lemma set_init_done_same s : ltac2:(tb__ "0|0|
S0S3eS36Vs;A1S48A3S0S2cS26S48Vs;A2Vs;A3F_;").
  Proof using . intros E. destruct s; cbn in *. subst. reflexivity. Qed.

  Lemma Inv_set_unmap_seq s l : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4S0S43S41S39Vl;A2U20A3S39S79S39R1Vl;A3S1S57Z0R2A2S57R2ZffA2A2F_;Fu;S61VX;VR;VU;S34Vl;Vs;A2A4F_;F_;F_;").
  Proof using .
    intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  Lemma Inv_set_bounces s l : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4S0S43S41S39Vl;A2U20A3S39S79S39R1Vl;A3S1S57Z0R2A2S57R2ZffA2A2F_;Fu;S61VX;VR;VU;S30Vl;Vs;A2A4F_;F_;F_;").
  Proof using .
    intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.
End Scalars.

Lemma zset_length32_range l k v : ltac2:(tb__ "0|5|
S0S43S41S39Vl;A2U20M0A3S39S79S39R1Vl;A3S1S57Z0M1R2A2S57R2ZffM2A2A2M3F_;Fu;S1S57G1Vv;A2S57Vv;G2A2A2S1S0S43S41S39S38Vk;Vv;Vl;A3M4A2G0A3S39S79S39R1G4A3G3F_;Fu;A2F_;F_;F_;").
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

Lemma repeat0_32_range : ltac2:(tb__ "0|3|
S1S0S43S41S39S7dS39Z0M0U20M1A3M2A2G1A3S39S79S39R1G2A3S1S57G0R2A2S57R2ZffA2A2F_;Fu;A2").
Proof. split; [reflexivity|]. intros u Hu. apply repeat_spec in Hu. lia. Qed.

Definition upd_meta (g : sptr) (x : mslot) (s : astate) : astate := ltac2:(tb__ "0|0|
S31S2eS1eVs;A1Vg;Vx;A3Vs;A2").

Lemma MT_upd_same g x s : ltac2:(tb__ "0|0|
S0S3bS7A1S60S49Vg;Vx;Vs;A3Vg;A2S3dS7Vx;A2A3").
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_same. Qed.

Lemma MT_upd_other g x s p : ltac2:(tb__ "0|0|
S2S0S6Vp;Vg;A3A1S0S3bS7A1S60S49Vg;Vx;Vs;A3Vp;A2S60Vs;Vp;A2A3F_;").
Proof. intros. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_other. assumption. Qed.

Lemma MT_upd g x s p : ltac2:(tb__ "0|1|
S0S3bS7A1M0S60S49Vg;Vx;Vs;A3Vp;A2S3eG0L_;S27Vp;Vg;A2S3dS7Vx;A2S60Vs;Vp;A2X3ex2A3").
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate. Qed.

Lemma keys_upd_In g x s : ltac2:(tb__ "0|1|
S79S6Vg;S5fVs;A1M0A3S0S3cS6A1S5fS49Vg;Vx;Vs;A3A1G0A3F_;").
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_In. assumption. Qed.

Lemma keys_upd_notIn g x s : ltac2:(tb__ "0|1|
S2S79S6Vg;S5fVs;A1M0A3A1S0S3cS6A1S5fS49Vg;Vx;Vs;A3A1S3fS6G0S45S6Vg;S42S6A1A3A3A3F_;").
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_notIn. assumption. Qed.

Lemma MT_Some_In_keys s g x : ltac2:(tb__ "0|0|
S0S3bS7A1S60Vs;Vg;A2S3dS7Vx;A2A3S79S6Vg;S5fVs;A1A3F_;").
Proof. unfold MT, keys. apply mlookup_In_keys. Qed.

Lemma MTX_upd X g x s p : ltac2:(tb__ "0|2|
S0S3bS7A1M0S6aVX;S49Vg;Vx;Vs;A3Vp;A3S3eG0L_;M1S27Vp;Vg;A2G1S62Vg;VX;A2S44S7A1S3dS7Vx;A2X3ex2S6aVX;Vs;Vp;A3X3ex2A3").
Proof.
  unfold MTX. rewrite MT_upd. destruct (sptr_eqb p g) eqn:E; [|reflexivity].
  apply sptr_eqb_eq in E. subst. reflexivity.
Qed.

Lemma usedX_upd X g x s p am : ltac2:(tb__ "0|1|
S4S5eVX;S49Vg;Vx;Vs;A3Vp;Vam;A4S5S1S0S6Vp;Vg;A3M0S1S0S3eS62Vg;VX;A2S46A3S0S7Vx;S9Vam;A1A3A2A2S1S2G0A1S5eVX;Vs;Vp;Vam;A4A2A2A2").
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

Lemma usedX_MT X s g am : ltac2:(tb__ "0|0|
S5eVX;Vs;Vg;Vam;A4S1S0S3bS7A1S60Vs;Vg;A2S3dS7S9Vam;A1A2A3S0S3eS62Vg;VX;A2S46A3A2F_;").
Proof. unfold usedX, MTX. destruct (memb g X); [discriminate | auto]. Qed.

Lemma usedX_intro X s g am : ltac2:(tb__ "0|0|
S0S3eS62Vg;VX;A2S46A3S0S3bS7A1S60Vs;Vg;A2S3dS7S9Vam;A1A2A3S5eVX;Vs;Vg;Vam;A4F_;F_;").
Proof. intros M H. unfold usedX, MTX. rewrite M. exact H. Qed.

Lemma usedX_fun X s g a1 a2 : ltac2:(tb__ "0|0|
S5eVX;Vs;Vg;Va1;A4S5eVX;Vs;Vg;Va2;A4S0SeVa1;Va2;A3F_;F_;").
Proof. unfold usedX. intros H1 H2. rewrite H1 in H2. injection H2. auto. Qed.

Definition geom_same (am0 am1 : ameta) : Prop := ltac2:(tb__ "0|1|
S1S0S6SaVam1;A1SaVam0;A1A3S1S0S39S8Vam1;A1S8Vam0;A1A3S1S0S39SbVam1;A1SbVam0;A1A3S1S0S39SdVam1;A1SdVam0;A1A3S39ScS0S3bScA1M0S11S10Vam0;R2A2A1S3dScR1A2A3S0S12S18R2A1S1fA3S0G0S11S10Vam1;R4A2A1S3dScR3A2A3F_;F_;Ffr;Fj;A2A2A2A2").

Lemma geom_same_stride am0 am1 : ltac2:(tb__ "0|0|
S4fVam0;Vam1;A2S0S39SfVam1;A1SfVam0;A1A3F_;").
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.

Lemma geom_same_slot_start am0 am1 i : ltac2:(tb__ "0|0|
S4fVam0;Vam1;A2S0S6S17Vam1;Vi;A2S17Vam0;Vi;A2A3F_;").
Proof. intros G. unfold slot_start. rewrite (geom_same_stride _ _ G). destruct G as (-> & _). reflexivity. Qed.

Lemma geom_same_extent am0 am1 : ltac2:(tb__ "0|0|
S4fVam0;Vam1;A2S0S39S65Vam1;A1S65Vam0;A1A3F_;").
Proof. intros G. unfold group_extent. rewrite (geom_same_stride _ _ G). destruct G as (_ & -> & _). reflexivity. Qed.

Definition gframes_kept (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop := ltac2:(tb__ "0|2|
S39ScS57Z0M0R2A2S0S3bScA1M1S11S10Vam0;R3A2A1S3dScR2A2A3S0S12S18R3A1S1fA3S5S0G1S11S10Vam1;R5A2A1S3dScR4A2A3S6SeS5eVX;Vs;R2R1A4S0S39SdR2A1G0A3S2S0S6SaR3A1S17Vam0;R9A2A3A1F_;F_;Fac;Fc;A2F_;F_;F_;Ffr;Fj;").

Definition geom_same_upto (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop := ltac2:(tb__ "0|0|
S1S0S6SaVam1;A1SaVam0;A1A3S1S0S39S8Vam1;A1S8Vam0;A1A3S1S0S39SbVam1;A1SbVam0;A1A3S1S0S39SdVam1;A1SdVam0;A1A3S52VX;Vs;Vam0;Vam1;A4A2A2A2A2").

Lemma geom_same_upto_of X s am0 am1 : ltac2:(tb__ "0|0|
S4fVam0;Vam1;A2S51VX;Vs;Vam0;Vam1;A4F_;").
Proof. intros (A & B & C & D & E). repeat split; auto. intros j fr _ H1 H2. left. apply E; assumption. Qed.

Lemma geom_same_upto_stride X s am0 am1 : ltac2:(tb__ "0|0|
S51VX;Vs;Vam0;Vam1;A4S0S39SfVam1;A1SfVam0;A1A3F_;").
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.

Section UsedUpdate.
  Variables (X : list sptr) (R R' : option (sptr * Z)) (U : Z -> Z) (s : astate) (g : sptr) (am0 am1 : ameta).
  Hypothesis HI : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4").
  Hypothesis Hg : ltac2:(tb__ "0|0|
S5eVX;Vs;Vg;Vam0;A4").
  Hypothesis G : ltac2:(tb__ "0|0|
S51VX;Vs;Vam0;Vam1;A4").
  Hypothesis Lk : ltac2:(tb__ "0|1|
S1S0S3bS6A1M0S16Vam1;A1S16Vam0;A1A3S0G0S15Vam1;A1S15Vam0;A1A3A2").
  Local Notation s' := (upd_meta g (MUsed am1) s).

  Lemma uu_keys : ltac2:(tb__ "0|0|
S0S3cS6A1S5fS49Vg;S9Vam1;A1Vs;A3A1S5fVs;A1A3").
  Proof using Hg. apply keys_upd_In. eapply MT_Some_In_keys. apply (proj1 (usedX_MT _ _ _ _ Hg)). Qed.

  Lemma uu_notX : ltac2:(tb__ "0|0|
S0S3eS62Vg;VX;A2S46A3").
  Proof using Hg. exact (proj2 (usedX_MT _ _ _ _ Hg)). Qed.

  Lemma uu_usedX_g : ltac2:(tb__ "0|0|
S5eVX;S49Vg;S9Vam1;A1Vs;A3Vg;Vam1;A4").
  Proof using Hg. apply usedX_upd. left. auto using uu_notX. Qed.

  Lemma uu_usedX_other p am : ltac2:(tb__ "0|0|
S2S0S6Vp;Vg;A3A1S4S5eVX;S49Vg;S9Vam1;A1Vs;A3Vp;Vam;A4S5eVX;Vs;Vp;Vam;A4A2F_;").
  Proof using . intros Hp. rewrite usedX_upd. split; [intros [[H _]|[_ H]]; [congruence|exact H] | intros H; right; auto]. Qed.

  Lemma uu_usedX_inv p am : ltac2:(tb__ "0|1|
S5eVX;S49Vg;S9Vam1;A1Vs;A3Vp;Vam;A4S5S1S0S6Vp;Vg;A3M0S0SeVam;Vam1;A3A2S1S2G0A1S5eVX;Vs;Vp;Vam;A4A2A2F_;").
  Proof using .
    intros H. apply usedX_upd in H as [[-> [_ H]] | [Hp H]]; [left; injection H; auto | right; auto].
  Qed.

  Lemma uu_ctx : ctx_ok s'.
  Proof using HI Hg.
    pose proof (inv_ctx HI) as C. unfold ctx_ok in *. unfold upd_meta. simp_st.
    destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 (conj _ C13)))))))))))).
    intros Hinit. exfalso. destruct (C12 Hinit) as (Hm & _).
    pose proof (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hg))) as K.
    unfold keys in K. rewrite Hm in K. exact K.
  Qed.

  Lemma uu_keys_ok : keys_ok s'.
  Proof using HI Hg.
    pose proof (inv_keys HI) as K. unfold keys_ok in *. rewrite uu_keys.
    unfold upd_meta. simp_st. exact K.
  Qed.

  Lemma uu_areas : areas_ok s'.
  Proof using HI. exact (inv_areas HI). Qed.

  Lemma uu_Xok : Xok X s'.
  Proof using HI Hg.
    intros x Hx. destruct (inv_X HI x Hx) as [K M]. split; [rewrite uu_keys; exact K|].
    rewrite MT_upd_other; [exact M|]. intros ->.
    pose proof uu_notX as N. unfold memb in N.
    assert (E : existsb (sptr_eqb g) X = true) by (apply existsb_exists; exists g; split; [exact Hx | apply sptr_eqb_refl]).
    congruence.
  Qed.

  Lemma uu_used_fwd p a : ltac2:(tb__ "0|0|
S5eVX;Vs;Vp;Va;A4S3SeSeS1S5eVX;S49Vg;S9Vam1;A1Vs;A3Vp;R1A4S1S0S6SaR1A1SaVa;A1A3S1S0S39S8R1A1S8Va;A1A3S1S0S39SbR1A1SbVa;A1A3S1S0S39SdR1A1SdVa;A1A3S1S0S39SfR1A1SfVa;A1A3S52VX;Vs;Va;R1A4A2A2A2A2A2A2La';A2F_;").
  Proof using G Hg.
    intros Hp. destruct (sptr_eq_dec p g) as [->|Hne].
    - exists am1. pose proof (usedX_fun _ _ _ _ _ Hp Hg) as ->. split; [apply uu_usedX_g|].
      destruct G as (G1 & G2 & G3 & G4 & G5). repeat split; auto. eapply geom_same_upto_stride. exact G.
    - exists a. split; [apply uu_usedX_other; assumption|]. repeat split; auto. intros j fr _ H1 H2. left. exact H1.
  Qed.

  Lemma uu_used_bwd p a' : ltac2:(tb__ "0|2|
S5eVX;S49Vg;S9Vam1;A1Vs;A3Vp;Va';A4S3SeSeS1S5eVX;Vs;Vp;R1A4S1S0S6SaVa';A1SaR1A1A3S1S0S39S8Va';A1S8R1A1A3S1S0S39SbVa';A1SbR1A1A3S1S0S39SdVa';A1SdR1A1A3S1S0S39SfVa';A1SfR1A1A3S1S0S3bS6A1M0S16Va';A1S16R1A1A3S1S0G0S15Va';A1S15R1A1A3S1S2S0S6Vp;Vg;A3M1A1S0SeVa';R2A3F_;G1S1S0SeVa';Vam1;A3S0SeR2Vam0;A3A2F_;A2A2A2A2A2A2A2A2A2La;A2F_;").
  Proof using G Hg Lk.
    intros Hp. apply uu_usedX_inv in Hp as [[-> ->] | [Hne Hp]].
    - exists am0. split; [exact Hg|]. destruct G as (G1 & G2 & G3 & G4 & G5). destruct Lk as [L1 L2].
      repeat split; auto; try congruence. eapply geom_same_upto_stride. exact G.
    - exists a'. repeat split; auto; congruence.
  Qed.

  Lemma uu_nested p a a' : ltac2:(tb__ "0|0|
S5eVX;Vs;Vp;Va;A4S0S39SdVa';A1SdVa;A1A3S0S39SbVa';A1SbVa;A1A3S0S6SaVa';A1SaVa;A1A3S0S39S8Va';A1S8Va;A1A3S68VX;Vs;Va;A3S68VX;S49Vg;S9Vam1;A1Vs;A3Va';A3F_;F_;F_;F_;F_;F_;").
  Proof using G Hg.
    intros Up E1 E2 E3 E4 N Hm. rewrite E1 in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
    split; [congruence|].
    destruct (uu_used_fwd _ _ Hu) as (b' & Hu' & M1 & M2 & M3 & M4 & M5 & M6).
    assert (Hf' : ss_fr (nth_slot b' i') = Some fr').
    { destruct (M6 i' fr' ltac:(lia) Hf Hk) as [H|H]; [exact H|]. exfalso. exact (H p a Up Hm Hmem). }
    exists g', b', i', fr'. rewrite E2, E3, E4. split; [exact Hu'|]. split; [rewrite M2; exact Hi|].
    split; [exact Hf'|]. split; [exact Hk|]. split; [unfold slot_start in *; rewrite M1, M5; exact Hmem|].
    split; [rewrite M3; exact Hsc|]. split; [rewrite M3; exact Hsc'|]. exact Hfit.
  Qed.

  Lemma uu_mapped a a' : ltac2:(tb__ "0|0|
S0S39SdVa';A1SdVa;A1A3S0S6SaVa';A1SaVa;A1A3S0S39S8Va';A1S8Va;A1A3S0S39SfVa';A1SfVa;A1A3S0S39SbVa';A1SbVa;A1A3S67Vs;Va;A2S67S49Vg;S9Vam1;A1Vs;A3Va';A2F_;F_;F_;F_;F_;F_;").
  Proof using .
    intros E1 E2 E3 E4 E5 M Hm. rewrite E1 in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    exists r, rg. rewrite E1, E2, E3, E4, E5. repeat split; auto.
  Qed.

  Lemma uu_inside a a' b b' : ltac2:(tb__ "0|0|
S0S6SaVa';A1SaVa;A1A3S0S39S65Va';A1S65Va;A1A3S0S6SaVb';A1SaVb;A1A3S0S39S8Vb';A1S8Vb;A1A3S0S39SfVb';A1SfVb;A1A3S52VX;Vs;Vb;Vb';A4S66VX;Vs;Va;Vb;A4S66VX;S49Vg;S9Vam1;A1Vs;A3Va';Vb';A4F_;F_;F_;F_;F_;F_;F_;").
  Proof using G Hg.
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
  Proof using G HI Hg Lk.
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
  Proof using G HI Hg Lk.
    intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
    destruct (uu_used_bwd _ _ H1) as (a1 & U1 & M1 & _ & _ & P1 & _).
    destruct (uu_used_bwd _ _ H2) as (a2 & U2 & M2 & _ & _ & P2 & _).
    eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
  Qed.

  Lemma uu_alinks sc q : ltac2:(tb__ "0|1|
S0S3bS3aS3bS6A1M0G0A2A1S64VX;S49Vg;S9Vam1;A1Vs;A3Vsc;Vq;A4S64VX;Vs;Vsc;Vq;A4A3").
  Proof using G Hg Lk.
    unfold alinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
    pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
    destruct G as (_ & _ & -> & _). destruct Lk as [-> ->]. reflexivity.
  Qed.

  Lemma uu_flinks q : ltac2:(tb__ "0|1|
S0S3bS3aS3bS6A1M0G0A2A1S6cVX;S49Vg;S9Vam1;A1Vs;A3Vq;A3S6cVX;Vs;Vq;A3A3").
  Proof using Hg.
    unfold flinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
    pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'. reflexivity.
  Qed.

  Lemma uu_usage : ltac2:(tb__ "0|0|
S70VX;VU;S49Vg;S9Vam1;A1Vs;A3A3").
  Proof using G HI Hg.
    intros sc Hsc. pose proof (inv_usage HI sc Hsc) as E.
    unfold usage_of in *. unfold upd_meta at 1. simp_st. rewrite E. f_equal.
    unfold class_sum. rewrite uu_keys. apply (f_equal (fun l => fold_right _ 0 l)) || idtac.
    induction (keys s) as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
    unfold contrib. rewrite MTX_upd. destruct (sptr_eqb k g) eqn:Ek; [|reflexivity].
    apply sptr_eqb_eq in Ek. subst k. rewrite uu_notX. pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
    destruct G as (_ & -> & -> & _). reflexivity.
  Qed.

  Lemma uu_active_hd sc : ltac2:(tb__ "0|0|
S0S3bS6A1S63S49Vg;S9Vam1;A1Vs;A3Vsc;A2S63Vs;Vsc;A2A3").
  Proof using . reflexivity. Qed.

  Section WithObligations.
    Hypothesis Hmasks : masks_ok am1.
    Hypothesis Hslots : ltac2:(tb__ "0|0|
S39S1S57Z0R1A2S57R1S8Vam1;A1A2A2S78VR';Vg;Vam1;R2A4F_;Fi;").
    Hypothesis Hclass : ltac2:(tb__ "0|0|
S75VR';Vg;Vam1;A3").
    Hypothesis HRother : ltac2:(tb__ "0|3|
S6S39S2S0S6R2Vg;A3A1S4S0S3bS3aS6S39A2M0A1M1VR';S3dG0S40S6S39R3R2A4A2M2A3S0G1VR;G2A3A2F_;Fi;Fp;").
    Hypothesis HRg : ltac2:(tb__ "0|1|
S39S0S3bS3aS6S39A2M0A1VR';S3dG0S40S6S39Vg;R1A4A2A3S1S1S57Z0R2A2S57R2S8Vam1;A1A2A2S1S0S3bScA1S11S10Vam1;R2A2A1S44ScA1A3S0S3eS73Vam1;R2A2S48A3A2A2F_;Fi;").
    Hypothesis Hfull : ltac2:(tb__ "0|3|
S58SbVam0;A1Z30A2S0S3aS3bS6A1M0G0A2S40G0G0S16Vam0;A1S15Vam0;A1A4S40G0G0S44S6A1M1G1A4A3S1S0S39S21Vam1;A1Z0M2A3S0S39S22Vam1;A1G2A3A2F_;F_;").
    Hypothesis HR1 : ltac2:(tb__ "0|1|
S58SbVam0;A1M0Z30A2S2S0S39S21Vam1;A1Z0A3A1S0S3bS6A1S63Vs;G0A2S3dS6Vg;A2A3F_;F_;").
    Hypothesis HR2 : ltac2:(tb__ "0|4|
S58SbVam0;A1M0Z30A2S2S0S3aS3bS6A1M1G1A2S40G1G1S16Vam0;A1S15Vam0;A1A4S40G1G1S44S6A1M2G2A4A3A1S2S0G1S63Vs;G0A2S3dS6Vg;A2A3A1S39S2S0S3bS3aS6S39A2M3A1VR';S3dG3S40S6S39Vg;R1A4A2A3A1Fi;S2S0S39S22Vam1;A1Z0A3A1F_;F_;F_;F_;").
    Hypothesis Hpart : ltac2:(tb__ "0|0|
S58S20Vam1;A1S8Vam1;A1A2S6SeS5eVX;Vs;R2R1A4S2S0S6R3Vg;A3A1S0S39SbR3A1SbVam0;A1A3S2S58S20R4A1S8R4A1A2A1F_;F_;F_;Fa;Fp;F_;").

    Lemma uu_groups p am : ltac2:(tb__ "0|1|
S5eVX;S49Vg;S9Vam1;A1Vs;A3M0Vp;Vam;A4S6dVX;VR';G0Vp;Vam;A5F_;").
    Proof using G HI HRother Hclass Hg Hmasks Hslots Lk.
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

    Lemma uu_rings : ltac2:(tb__ "0|0|
S6fVX;VR';S49Vg;S9Vam1;A1Vs;A3A3").
    Proof using G HI HR1 HR2 HRother Hfull Hg Lk.
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
    Proof using G HI Hg Hpart Lk.
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

    Lemma uu_reserved : ltac2:(tb__ "0|0|
S6eVX;VR';S49Vg;S9Vam1;A1Vs;A3A3").
    Proof using HI HRg HRother Hg.
      intros p i HR'. destruct (sptr_eq_dec p g) as [->|Hne].
      - exists am1. split; [apply uu_usedX_g|]. apply HRg. exact HR'.
      - apply (HRother p i Hne) in HR'. destruct (inv_reserved HI p i HR') as (a & Ua & Hi & Hf & Ha).
        exists a. split; [apply uu_usedX_other; assumption|]. auto.
    Qed.

    Lemma Inv_used_update : ltac2:(tb__ "0|0|
S61VX;VR';VU;S49Vg;S9Vam1;A1Vs;A3A4").
    Proof using G HI HR1 HR2 HRg HRother Hclass Hfull Hg Hmasks Hpart Hslots Lk.
      split; [apply uu_ctx|]. split; [apply uu_keys_ok|]. split; [apply uu_areas|].
      split; [apply uu_Xok|]. split; [apply uu_groups|]. split; [apply uu_laminar|].
      split; [apply uu_maps|]. split; [apply uu_rings|]. split; [apply uu_usage|].
      split; [apply uu_reserved | apply uu_partial].
    Qed.
  End WithObligations.
End UsedUpdate.

Section Transfer.
  Variables (X X' : list sptr) (R : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S61VX;VR;VU;Vs;A4").
  Hypothesis EU : ltac2:(tb__ "0|0|
S6SeS4S5eVX';Vs';R2R1A4S5eVX;Vs;R2R1A4A2Fam;Fp;").
  Hypothesis ER : ltac2:(tb__ "0|0|
S0S3cS2fA1S29Vs';A1S29Vs;A1A3").

  Lemma tr_nested a : ltac2:(tb__ "0|0|
S68VX;Vs;Va;A3S68VX';Vs';Va;A3F_;").
  Proof using EU.
    intros N Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hrest)].
    split; [exact N63|]. exists g', b, i', fr'. split; [apply EU; exact Hu | exact Hrest].
  Qed.

  Lemma tr_mapped a : ltac2:(tb__ "0|0|
S67Vs;Va;A2S67Vs';Va;A2F_;").
  Proof using ER.
    intros M Hm. destruct (M Hm) as (r & rg & H). exists r, rg. unfold region_of in *. rewrite ER. exact H.
  Qed.

  Lemma tr_inside a b : ltac2:(tb__ "0|0|
S66VX;Vs;Va;Vb;A4S66VX';Vs';Va;Vb;A4F_;").
  Proof using EU U'.
    intros (j & fr & c & ac & H1 & H2 & H3 & H4 & H5). exists j, fr, c, ac.
    repeat split; try tauto. apply EU. exact H4.
  Qed.

  Lemma tr_groups : ltac2:(tb__ "0|0|
S6SeS5eVX';Vs';R2R1A4S6dVX';VR;Vs';R3R2A5F_;Fam;Fg;").
  Proof using ER EU HI.
    intros g am Hg. apply EU in Hg. pose proof (inv_groups HI g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply tr_mapped; exact G5 | apply tr_nested; exact G6].
  Qed.

  Lemma tr_laminar : laminar X' s'.
  Proof using EU HI U'.
    intros p1 a1 p2 a2 H1 H2 Hne Hr. apply EU in H1. apply EU in H2.
    destruct (inv_laminar HI p1 a1 p2 a2 H1 H2 Hne Hr) as [D|[I|I]];
      [left; exact D | right; left; apply tr_inside; exact I | right; right; apply tr_inside; exact I].
  Qed.

  Lemma tr_maps : maps_unique X' s'.
  Proof using EU HI. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_maps HI); eauto. Qed.

  Lemma tr_partial : partial_unique X' s'.
  Proof using EU HI. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_partial HI); eauto. Qed.

  Lemma tr_reserved : ltac2:(tb__ "0|0|
S6eVX';VR;Vs';A3").
  Proof using EU HI.
    intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & H). exists am. split; [apply EU; exact Hu | exact H].
  Qed.

  Lemma tr_direct : direct_unlinked X' s'.
  Proof using EU HI. intros g am Hg. apply EU in Hg. exact (proj2 (proj2 (inv_rings HI)) g am Hg). Qed.

  Lemma tr_alinks sc q : ltac2:(tb__ "0|1|
S0S3bS3aS3bS6A1M0G0A2A1S64VX';Vs';Vsc;Vq;A4S64VX;Vs;Vsc;Vq;A4A3").
  Proof using EU.
    unfold alinks.
    destruct (MTX X' s' q) as [[pr nx| |am]|] eqn:E1; destruct (MTX X s q) as [[pr' nx'| |am']|] eqn:E2; try reflexivity.
    all: try (assert (Hu : usedX X' s' q am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate; injection E2 as ->; reflexivity).
    all: try (assert (Hu : usedX X s q am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
  Qed.

  Lemma tr_active sc : ltac2:(tb__ "0|0|
S0S3cS3bS6A1A1S28Vs';A1S28Vs;A1A3S6bVX;VR;Vs;Vsc;A4S6bVX';VR;Vs';Vsc;A4F_;F_;").
  Proof using EU.
    intros EA (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
    assert (EH : active_hd s' sc = active_hd s sc) by (unfold active_hd; rewrite EA; reflexivity).
    rewrite EH. split; [eapply ring_ok_ext; [intros; apply tr_alinks | exact Rg] |].
    split; [intros q a Hq; apply EU in Hq; apply Mem; exact Hq|].
    split; [intros q a Hq; apply EU in Hq; apply Full; exact Hq|].
    split; [intros q a Hq; apply EU in Hq; apply Q1; exact Hq|].
    intros q a Hq; apply EU in Hq; apply Q2; exact Hq.
  Qed.

  Theorem Inv_transfer : ltac2:(tb__ "0|0|
S76Vs';A1S77Vs';A1S74Vs';A1S72VX';Vs';A2S6fVX';VR;Vs';A3S70VX';VU';Vs';A3S61VX';VR;VU';Vs';A4F_;F_;F_;F_;F_;F_;").
  Proof using ER EU HI.
    intros C K A XO RG US.
    split; [exact C|]. split; [exact K|]. split; [exact A|].
    split; [exact XO|]. split; [apply tr_groups|]. split; [apply tr_laminar|]. split; [apply tr_maps|].
    split; [exact RG|]. split; [exact US|]. split; [apply tr_reserved | apply tr_partial].
  Qed.
End Transfer.

Lemma nth_slot_upd_slot am i j x : ltac2:(tb__ "0|1|
S57Z0M0Vi;A2S57G0Vj;A2S7eS5aVi;A1S41S13S14Vam;A1A2A2S0S13S10S19Vam;Vi;Vx;A3Vj;A2S3eS13L_;S5cVj;Vi;A2Vx;S10Vam;Vj;A2X3ex2A3F_;F_;F_;").
Proof.
  intros Hi Hj Hlen. unfold nth_slot, upd_slot. cbn [am_slots am_set_slots]. rewrite nth_lupd.
  destruct (j =? i) eqn:E.
  - apply Z.eqb_eq in E. subst j. rewrite Nat.eqb_refl.
    replace (Nat.ltb (Z.to_nat i) (length (am_slots am))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hlen.
  - replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. apply Z.eqb_neq in E. lia.
Qed.

Lemma flat_map_ext_In {A B} (f g : A -> list B) l : ltac2:(tb__ "0|1|
VA;S79VA;R1Vl;A3S0S3cVB;A1M0Vf;R2A1Vg;R2A1A3F_;Fa;S0G0S7aVA;VB;Vf;Vl;A4S7aVA;VB;Vg;Vl;A4A3F_;").
Proof.
  induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity).
  rewrite IH by (intros a Ha; apply H; right; exact Ha). reflexivity.
Qed.

Definition slot_block0 (am : ameta) (i : Z) : list (sptr * Z) := ltac2:(tb__ "0|3|
S3bScA1S3cS3aS6S39A2M0A1M1Lx;S11S10Vam;Vi;A2A1ScS12G1Lx;S18R1A1S45G0S40S6S39S1dS17Vam;Vi;A2S5bS1aS1cR1A1A2A2S1bR1A1A4S42G0A1M2A3G2X12x2Lfr;G2X3bx2").
Definition blocks_of0 (am : ameta) : list (sptr * Z) := ltac2:(tb__ "0|0|
S7aS39S3aS6S39A2S56Vam;A1S71Z0S59S8Vam;A1Z1A2A2A4").
Definition ucontrib0 (x : option mslot) : list (sptr * Z) := ltac2:(tb__ "0|4|
S3bS7A1S3cS3aS6S39A2M0A1M1Lx;Vx;S7S7G1Lm;R1S3bS6A1M2G2S42G0A1M3Lnext;Lprev;G3SeS53R1A1Lam;X7x3Lm;G3X3bx2").
Definition ublist0 (s : astate) : list (sptr * Z) := ltac2:(tb__ "0|0|
S7aS6S3aS6S39A2S6S55S60Vs;R1A2A1Lg;S5fVs;A1A4").

Lemma user_blocks_ublist0 s : ltac2:(tb__ "0|0|
S7bS6S5fVs;A1A2S0S3cS3aS6S39A2A1S69Vs;A1S54Vs;A1A3F_;").
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

Definition slot_block (g : sptr) (am : ameta) (i : Z) : list ublk := ltac2:(tb__ "0|4|
S3bScA1S3cS3aS3aS6S39A2M0G0A2M1A1M2Lx;S11S10Vam;Vi;A2A1ScS12G2Lx;S18R1A1S45G1S40G0G0S40S6S39S1dS17Vam;Vi;A2S5bS1aS1cR1A1A2A2S1bR1A1A4S40S6S39Vg;Vi;A4A4S42G1A1M3A3G3X12x2Lfr;G3X3bx2").

Definition blocks_of (g : sptr) (am : ameta) : list ublk := ltac2:(tb__ "0|1|
S7aS39S3aS3aS6S39A2M0G0A2S4eVg;Vam;A2S71Z0S59S8Vam;A1Z1A2A2A4").

Definition ucontrib (g : sptr) (x : option mslot) : list ublk := ltac2:(tb__ "0|5|
S3bS7A1S3cS3aS3aS6S39A2M0G0A2M1A1M2Lx;Vx;S7S7G2Lm;R1S3bS6A1M3G3S42G1A1M4Lnext;Lprev;G4SeS4aVg;R1A2Lam;X7x3Lm;G4X3bx2").

Definition ublist (s : astate) : list ublk := ltac2:(tb__ "0|1|
S7aS6S3aS3aS6S39A2M0G0A2S6S4bR1S60Vs;R1A2A2Lg;S5fVs;A1A4").

Lemma map_fst_blocks_of g am : ltac2:(tb__ "0|1|
S0S3cS3aS6S39A2M0A1S7cS3aG0G0A2G0S47G0G0A2S4aVg;Vam;A2A4S53Vam;A1A3").
Proof.
  unfold blocks_of, blocks_of0. induction (zseq 0 (am_last am + 1)) as [|i z IH]; [reflexivity|].
  simpl. rewrite map_app, IH. f_equal.
  unfold slot_block, slot_block0. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; reflexivity.
Qed.

Lemma map_fst_ucontrib g x : ltac2:(tb__ "0|1|
S0S3cS3aS6S39A2M0A1S7cS3aG0G0A2G0S47G0G0A2S4bVg;Vx;A2A4S55Vx;A1A3").
Proof. destruct x as [[| |am]|]; cbn [ucontrib ucontrib0 map]; try reflexivity. apply map_fst_blocks_of. Qed.

Lemma map_fst_ublist s : ltac2:(tb__ "0|1|
S0S3cS3aS6S39A2M0A1S7cS3aG0G0A2G0S47G0G0A2S4dVs;A1A4S54Vs;A1A3").
Proof.
  unfold ublist, ublist0. induction (keys s) as [|g k IH]; [reflexivity|]. simpl. rewrite map_app, IH, map_fst_ucontrib. reflexivity.
Qed.

Lemma user_blocks_ublist s : ltac2:(tb__ "0|1|
S7bS6S5fVs;A1A2S0S3cS3aS6S39A2M0A1S69Vs;A1S7cS3aG0G0A2G0S47G0G0A2S4dVs;A1A4A3F_;").
Proof. intros ND. rewrite map_fst_ublist. apply user_blocks_ublist0. exact ND. Qed.

Definition ub_same (s s' : astate) : Prop := ltac2:(tb__ "0|6|
S3S3cS6A1M0G0S1S0G0S5fVs';A1S3fS6S5fVs;A1M1R1A3A3S1S6S79S6R1R2A3S0S3cS3aS3aS6S39A2M2G2A2M3A1M4S4bR2S60Vs';R2A2A2M5S42G3A1A3F_;Fm;S6S79S6R1G1A3S0G4G5S4bR2S60Vs;R2A2A2A3F_;Fg;A2A2Lext;A2").

Lemma ub_same_refl s : ub_same s s.
Proof. exists []. rewrite app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.

Lemma ub_same_trans s1 s2 s3 : ltac2:(tb__ "0|0|
S4cVs1;Vs2;A2S4cVs2;Vs3;A2S4cVs1;Vs3;A2F_;F_;").
Proof.
  intros (e1 & K1 & Z1 & S1) (e2 & K2 & Z2 & S2). exists (e1 ++ e2). rewrite K2, K1, <- app_assoc. split; [reflexivity|]. split.
  - intros m Hm. apply in_app_iff in Hm as [Hm|Hm]; [|apply Z2; exact Hm].
    rewrite S2; [apply Z1; exact Hm|]. rewrite K1. apply in_app_iff. right. exact Hm.
  - intros g Hg. rewrite S2; [apply S1; exact Hg|]. rewrite K1. apply in_app_iff. left. exact Hg.
Qed.

Lemma flat_map_nil_In {A B} (f : A -> list B) l : ltac2:(tb__ "0|2|
VA;S79VA;R1Vl;A3S0S3cVB;A1M0Vf;R2A1S42VB;A1M1A3F_;Fa;S0G0S7aVA;VB;Vf;Vl;A4G1A3F_;").
Proof.
  induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). cbn. apply IH. intros a Ha. apply H. right. exact Ha.
Qed.

Lemma ub_same_ublist s s' : ltac2:(tb__ "0|1|
S4cVs;Vs';A2S0S3cS3aS3aS6S39A2M0G0A2A1S4dVs';A1S4dVs;A1A3F_;").
Proof.
  intros (ext & K & Zx & Sm). unfold ublist. rewrite K, flat_map_app.
  rewrite (flat_map_ext_In _ _ (keys s) Sm). rewrite (flat_map_nil_In _ ext Zx). apply app_nil_r.
Qed.

Lemma ub_same_user_blocks s s' : ltac2:(tb__ "0|0|
S7bS6S5fVs;A1A2S7bS6S5fVs';A1A2S4cVs;Vs';A2S0S3cS3aS6S39A2A1S69Vs';A1S69Vs;A1A3F_;F_;F_;").
Proof. intros N N' H. rewrite (user_blocks_ublist s N), (user_blocks_ublist s' N'). f_equal. apply ub_same_ublist. exact H. Qed.

Lemma ub_same_metas s s' : ltac2:(tb__ "0|0|
S0S3cS3aS6S7A2A1S1eVs';A1S1eVs;A1A3S4cVs;Vs';A2F_;").
Proof. intros E. exists []. unfold keys, MT. rewrite E, app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.

Lemma ub_same_upd_In s g x : ltac2:(tb__ "0|1|
S79S6Vg;S5fVs;A1A3S0S3cS3aS3aS6S39A2M0G0A2A1S4bVg;S3dS7Vx;A2A2S4bVg;S60Vs;Vg;A2A2A3S4cVs;S49Vg;Vx;Vs;A3A2F_;F_;").
Proof.
  intros Hg Hx. exists []. rewrite app_nil_r. split; [apply keys_upd_In; exact Hg|]. split; [intros m []|].
  intros q Hq. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; subst q; exact Hx | reflexivity].
Qed.

Lemma ub_same_upd_notIn s g x : ltac2:(tb__ "0|2|
S2S79S6Vg;S5fVs;A1A3A1S0S3cS3aS3aS6S39A2M0G0A2M1A1S4bVg;S3dS7Vx;A2A2S42G1A1A3S4cVs;S49Vg;Vx;Vs;A3A2F_;F_;").
Proof.
  intros Hg Hx. exists [g]. split; [apply keys_upd_notIn; exact Hg|]. split.
  - intros m [<-|[]]. rewrite MT_upd_same. exact Hx.
  - intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. exact (Hg Hq).
Qed.

Lemma blocks_of_ext g a b : ltac2:(tb__ "0|1|
S0S6SaVb;A1SaVa;A1A3S0S39S8Vb;A1S8Va;A1A3S0S39SbVb;A1SbVa;A1A3S0S39SdVb;A1SdVa;A1A3S0S3cS13A1S14Vb;A1S14Va;A1A3S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;Vb;A2S4aVg;Va;A2A3F_;F_;F_;F_;F_;").
Proof. intros E1 E2 E3 E4 E5. unfold blocks_of, slot_block, nth_slot, slot_start, stride_of. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.

Lemma blocks_of_links g p n am : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;S2bVp;Vn;Vam;A3A2S4aVg;Vam;A2A3").
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_masks g av fr ai am : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;S23Vai;S25Vfr;S24Vav;Vam;A2A2A2A2S4aVg;Vam;A2A3").
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_avail g av am : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;S24Vav;Vam;A2A2S4aVg;Vam;A2A3").
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_freed g fr am : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;S25Vfr;Vam;A2A2S4aVg;Vam;A2A3").
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_aidx g ai am : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4aVg;S23Vai;Vam;A2A2S4aVg;Vam;A2A3").
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma ucontrib_with_links g x p n : ltac2:(tb__ "0|1|
S0S3cS3aS3aS6S39A2M0G0A2A1S4bVg;S3dS7S37Vx;Vp;Vn;A3A2A2S4bVg;S3dS7Vx;A2A2A3").
Proof. destruct x; cbn; [reflexivity | reflexivity | apply blocks_of_links]. Qed.

Lemma blocks_of_frameless g am : ltac2:(tb__ "0|2|
S39S0S3bScA1S11S10Vam;R1A2A1S44ScA1A3Fj;S0S3cS3aS3aS6S39A2M0G0A2M1A1S4aVg;Vam;A2S42G1A1A3F_;").
Proof.
  intros H. unfold blocks_of. induction (zseq 0 (am_last am + 1)) as [|i t IH]; [reflexivity|]. cbn. unfold slot_block at 1. rewrite H. exact IH.
Qed.

Definition slotst_block (g : sptr) (am : ameta) (i : Z) (x : slotst) : list ublk := ltac2:(tb__ "0|4|
S3bScA1S3cS3aS3aS6S39A2M0G0A2M1A1M2Lx;S11Vx;A1ScS12G2Lx;S18R1A1S45G1S40G0G0S40S6S39S1dS17Vam;Vi;A2S5bS1aS1cR1A1A2A2S1bR1A1A4S40S6S39Vg;Vi;A4A4S42G1A1M3A3G3X12x2Lfr;G3X3bx2").

Lemma slot_block_upd_slot g am i x j : ltac2:(tb__ "0|3|
S57Z0M0Vi;A2S57G0Vj;A2S7eS5aVi;A1S41S13S14Vam;A1A2A2S0S3cS3aS3aS6S39A2M1G1A2A1M2S4eVg;S19Vam;Vi;Vx;A3Vj;A3S3eG2L_;S5cVj;Vi;A2S50Vg;Vam;Vi;Vx;A4S4eVg;Vam;Vj;A3X3ex2A3F_;F_;F_;").
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

Lemma blocks_of_upd_slot g am i x : ltac2:(tb__ "0|4|
S1S57Z0Vi;A2S57Vi;S8Vam;A1M0A2A2S0S43S41S13S14Vam;A1A2S5aS59G0Z1A2A1A3S3S3cS3aS3aS6S39A2M1G1A2M2A1M3G3S3G3G3S1S0G3S4aVg;Vam;A2S3fG2R2S3fG2S4eVg;Vam;Vi;A3R1A3A3A3S0G3S4aVg;S19Vam;Vi;Vx;A3A2S3fG2R2S3fG2S50Vg;Vam;Vi;Vx;A4R1A3A3A3A2Ll2;A2Ll1;A2F_;F_;").
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

Lemma blocks_of_upd_slot_same g am i x : ltac2:(tb__ "0|3|
S1S57Z0Vi;A2S57Vi;S8Vam;A1M0A2A2S0S43S41S13S14Vam;A1A2S5aS59G0Z1A2A1A3S0S3cS3aS3aS6S39A2M1G1A2A1M2S50Vg;Vam;Vi;Vx;A4S4eVg;Vam;Vi;A3A3S0G2S4aVg;S19Vam;Vi;Vx;A3A2S4aVg;Vam;A2A3F_;F_;F_;").
Proof.
  intros Hi Hlen E. destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & E1 & E2). rewrite E2, E, <- E1. reflexivity.
Qed.

Lemma ublist_split s g : ltac2:(tb__ "0|4|
S7bS6S5fVs;A1M0A2S79S6Vg;G0A3S3S3cS3aS3aS6S39A2M1G1A2M2A1M3G3S3G3G3S1S7S0G3S4dS49Vg;R1Vs;A3A1S3fG2R3S3fG2S4bVg;S3dS7R1A2A2R2A3A3A3Fx;S0G3S4dVs;A1S3fG2R2S3fG2S4bVg;S60Vs;Vg;A2A2R1A3A3A3A2LL2;A2LL1;A2F_;F_;").
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

Lemma ublist_upd_slot s g am i x : ltac2:(tb__ "0|4|
S7bS6S5fVs;A1A2S0S3bS7A1S60Vs;Vg;A2S3dS7S9Vam;A1A2A3S1S57Z0Vi;A2S57Vi;S8Vam;A1M0A2A2S0S43S41S13S14Vam;A1A2S5aS59G0Z1A2A1A3S3S3cS3aS3aS6S39A2M1G1A2M2A1M3G3S3G3G3S1S0G3S4dVs;A1S3fG2R2S3fG2S4eVg;Vam;Vi;A3R1A3A3A3S0G3S4dS49Vg;S9S19Vam;Vi;Vx;A3A1Vs;A3A1S3fG2R2S3fG2S50Vg;Vam;Vi;Vx;A4R1A3A3A3A2Ll2;A2Ll1;A2F_;F_;F_;F_;").
Proof.
  intros ND Mg Hi Hlen.
  destruct (ublist_split s g ND (MT_Some_In_keys _ _ _ Mg)) as (L1 & L2 & Hupd & Hs).
  destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & B1 & B2).
  exists (L1 ++ l1), (l2 ++ L2). rewrite Hs, Hupd, Mg. cbn [ucontrib]. rewrite B1, B2, <- !app_assoc. split; reflexivity.
Qed.
