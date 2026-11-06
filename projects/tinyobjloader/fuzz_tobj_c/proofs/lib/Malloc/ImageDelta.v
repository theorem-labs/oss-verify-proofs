(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "loc"; "LMem"; "footprint"; "image"; "user_blocks"; "MT"; "MCell"; "LCtx"; "keys"; "group_cells"; "slot_cells"; "CTX_active"; "CTX_bounces"; "VZ"; "active_hd"; "areas_cells"; "ctx_cells"; "mc_loc"; "meta_slot_cells"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "META_next"; "META_prev"; "VLo5"; "VP"; "optr"; "zseq"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "bool"; "option"; "length"; "Some"; "nil"; "app"; "andb"; "nat"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "padd"; "st_init_done"; "MUsed"; "st_metas"; "am_mem"; "am_aidx"; "am_last"; "am_maplen"; "astate"; "lupd"; "st_bounces"; "am_sc"; "am_slots"; "nth_slot"; "set_bounces"; "slot_start"; "slotst"; "st_active"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_brk"; "st_meta_alloc_shift"; "st_regions"; "st_usage"; "stride_of"; "zset"; "zupd"; "am_set_aidx"; "am_set_avail"; "am_set_freed"; "am_set_links"; "brkst"; "region"; "set_active"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "same_shape"; "delta"; "aidx_cell"; "meta_locs"; "set_hd"; "@Stdlib.Lists.List"; "In"; "NoDup"; "flat_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "slot_end"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "to_nat"; "mul"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.SetBounces"; "bounce_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.SetHd"; "active_cell"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocWfFrame MallocWfRepr ImageUpd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition same_shape (am am' : ameta) : Prop := ltac2:(tb__ "0|0|
S1S0S2eS34Vam';A1S34Vam;A1A3S1S0S21S36Vam';A1S36Vam;A1A3S1S0S21S3bVam';A1S3bVam;A1A3S1S0S21S37Vam';A1S37Vam;A1A3S0S22S40A1S3cVam';A1S3cVam;A1A3A2A2A2A2").

Lemma same_shape_refl am : same_shape am am. Proof. repeat split; reflexivity. Qed.
Lemma same_shape_links pr nx am : ltac2:(tb__ "0|0|
S53Vam;S4fVpr;Vnx;Vam;A3A2"). Proof. repeat split; reflexivity. Qed.
Lemma same_shape_avail v am : ltac2:(tb__ "0|0|
S53Vam;S4dVv;Vam;A2A2"). Proof. repeat split; reflexivity. Qed.
Lemma same_shape_freed v am : ltac2:(tb__ "0|0|
S53Vam;S4eVv;Vam;A2A2"). Proof. repeat split; reflexivity. Qed.
Lemma same_shape_aidx v am : ltac2:(tb__ "0|0|
S53Vam;S4cVv;Vam;A2A2"). Proof. repeat split; reflexivity. Qed.
Lemma same_shape_trans a b c : ltac2:(tb__ "0|0|
S53Va;Vb;A2S53Vb;Vc;A2S53Va;Vc;A2F_;F_;").
Proof. intros (A1&A2&A3&A4&A5) (B1&B2&B3&B4&B5). repeat split; congruence. Qed.

Lemma stride_same am am' : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S21S49Vam';A1S49Vam;A1A3F_;").
Proof. intros (E1&E2&E3&E4&E5). unfold stride_of, class_size. rewrite E2, E3, E4. reflexivity. Qed.
Lemma nth_slot_same am am' i : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S40S3dVam';Vi;A2S3dVam;Vi;A2A3F_;").
Proof. intros (E1&E2&E3&E4&E5). unfold nth_slot. rewrite E5. reflexivity. Qed.
Lemma slot_start_same am am' i : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S2eS3fVam';Vi;A2S3fVam;Vi;A2A3F_;").
Proof. intros H. unfold slot_start. rewrite (stride_same _ _ H). destruct H as (E1&_). rewrite E1. reflexivity. Qed.
Lemma slot_end_same am am' i : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S2eS5dVam';Vi;A2S5dVam;Vi;A2A3F_;").
Proof. intros H. unfold slot_end. rewrite (slot_start_same _ _ i H), (stride_same _ _ H). reflexivity. Qed.

Lemma slot_cells_same am am' i : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S22S3A1SeVam';Vi;A2SeVam;Vi;A2A3F_;").
Proof.
  intros H. unfold slot_cells. rewrite (slot_start_same _ _ i H), (nth_slot_same _ _ i H).
  destruct (ss_fr (nth_slot am i)) as [fr|]; [|reflexivity].
  unfold hdr_byte3, hdr_off16, rsv_code, reserved_of. rewrite (stride_same _ _ H). reflexivity.
Qed.

Lemma group_footer_cells_same am am' : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S0S22S3A1S5cVam';A1S5cVam;A1A3F_;").
Proof.
  intros H. unfold group_footer_cells, trailing_cell, trailing_loc. rewrite (stride_same _ _ H).
  pose proof H as (E1&E2&E3&E4&E5). rewrite E1, E2. f_equal.
  apply flat_map_ext_eq || idtac.
  induction (zseq 0 (am_last am + 1)) as [|i t IH]; [reflexivity|]. cbn [flat_map]. rewrite IH. f_equal.
  rewrite (nth_slot_same _ _ i H). destruct (ss_fr (nth_slot am i)) as [fr|]; [|reflexivity].
  unfold frame_footer_cells, frame_ptr, reserved_of. rewrite (slot_start_same _ _ i H), (slot_end_same _ _ i H), (stride_same _ _ H). reflexivity.
Qed.

Definition aidx_cell (am : ameta) : mcell := ltac2:(tb__ "0|2|
S25S3L_;S63S37Vam;A1Z0A2SaS5S30S34Vam;A1Z8A2A1M0U1S1dS35Vam;A1M1A1A3SaG0U4S11G1A1A3X25x2").

Lemma group_cells_eq g am : ltac2:(tb__ "0|0|
S0S22S3A1SdVg;Vam;A2S23S3SaS5S34Vam;A1A1U8S1eVg;A1A3S23S3S55Vam;A1S5aS21S3SeVam;A1S20Z0S5fS36Vam;A1Z1A2A2A4A3A3A3").
Proof. reflexivity. Qed.

Lemma group_cells_same_In g am am' c : ltac2:(tb__ "0|0|
S53Vam;Vam';A2S58S3Vc;SdVg;Vam';A2A3S2S58S3Vc;SdVg;Vam;A2A3S0S3Vc;S55Vam';A1A3A2F_;F_;").
Proof.
  intros H Hin. rewrite group_cells_eq in Hin. rewrite group_cells_eq.
  pose proof H as (E1&E2&E3&E4&E5).
  destruct Hin as [<-|[<-|Hin]].
  - left. left. rewrite E1. reflexivity.
  - right. reflexivity.
  - left. right. right. rewrite E2 in Hin. apply in_flat_map in Hin as [i [Hi Hc]]. apply in_flat_map. exists i. split; [exact Hi|].
    rewrite <- (slot_cells_same am am' i H). exact Hc.
Qed.

Section ShapeUpd.
  Variables (s : astate) (g : sptr) (am am' : ameta).
  Hypothesis ND : List.NoDup (keys s).
  Hypothesis Hg : ltac2:(tb__ "0|0|
S0S26S2fA1S9Vs;Vg;A2S28S2fS32Vam;A1A2A3").
  Hypothesis SH : same_shape am am'.
  Let s' : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S64Vg;S32Vam';A1Vs;A3").

  Lemma su_footprint : ltac2:(tb__ "0|0|
S0S22S24S4S21A2A1S6Vs';A1S6Vs;A1A3"). Proof using am' g. reflexivity. Qed.
  Lemma su_init : ltac2:(tb__ "0|0|
S0S25S31Vs';A1S31Vs;A1A3"). Proof using am' g. reflexivity. Qed.
  Lemma su_ctx : ltac2:(tb__ "0|0|
S0S22S3A1S14Vs';A1S14Vs;A1A3"). Proof using am' g. reflexivity. Qed.

  Lemma su_user_blocks : ltac2:(tb__ "0|0|
S0S22S24S2eS21A2A1S8Vs';A1S8Vs;A1A3").
  Proof using Hg ND SH.
    destruct (upd_used_metas s g am am' ND Hg) as (l1 & l2 & E1 & E2 & _).
    unfold user_blocks. fold s' in E2. rewrite E1, E2, !flat_map_app. cbn [flat_map]. f_equal. f_equal.
    cbn [snd]. pose proof SH as (_&E2'&_). rewrite E2'.
    induction (zseq 0 (am_last am + 1)) as [|i t IH]; [reflexivity|]. cbn [flat_map]. rewrite IH.
    rewrite (nth_slot_same _ _ i SH), (slot_start_same _ _ i SH). reflexivity.
  Qed.

  Lemma su_footers : ltac2:(tb__ "0|0|
S0S22S3A1S5bVs';A1S5bVs;A1A3").
  Proof using Hg ND SH.
    destruct (upd_used_metas s g am am' ND Hg) as (l1 & l2 & E1 & E2 & _).
    unfold footer_cells. fold s' in E2. rewrite E1, E2, !flat_map_app. cbn [flat_map snd].
    rewrite (group_footer_cells_same _ _ SH). reflexivity.
  Qed.

  Lemma su_image_In c : ltac2:(tb__ "0|0|
S58S3Vc;S7Vs';A1A3S2S58S3Vc;S7Vs;A1A3S2S58S3Vc;S16Vg;S28S2fS32Vam';A1A2A2A3S0S3Vc;S55Vam';A1A3A2A2F_;").
  Proof using Hg ND SH.
    intros Hin. destruct (upd_image_In s g am am' ND Hg c Hin) as [H|[H|H]]; [left; exact H | right; left; exact H |].
    destruct (group_cells_same_In g am am' c SH H) as [Ho|Ha]; [|right; right; exact Ha].
    left. apply (In_image_group s g am c); [|exact Ho]. exact (used_metas_g_old s g am am' ND Hg).
  Qed.
End ShapeUpd.

Definition set_hd (sc : Z) (v : option sptr) (s : astate) : astate := ltac2:(tb__ "0|0|
S52S39S26S2eA1S41Vs;A1S61Vsc;A1Vv;A4Vs;A2").

Lemma lupd_length {A} (l : list A) i v : ltac2:(tb__ "0|0|
S0S2cS27VA;S39VA;Vl;Vi;Vv;A4A2S27VA;Vl;A2A3").
Proof. revert i. induction l as [|x t IH]; intros [|i]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma nth_lupd {A} (l : list A) i v j d : ltac2:(tb__ "0|0|
S0VA;S5eVA;Vj;S39VA;Vl;Vi;Vv;A4Vd;A4S25VA;L_;S2bS65Vj;Vi;A2S66Vi;S27VA;Vl;A2A2A2Vv;S5eVA;Vj;Vl;Vd;A4X25x2A3").
Proof.
  revert i j. induction l as [|x t IH]; intros [|i] [|j]; cbn; try reflexivity.
  - destruct (Nat.eqb j i); reflexivity || (cbn; destruct j; reflexivity).
  - rewrite IH. destruct (Nat.eqb j i) eqn:E; cbn; [|reflexivity].
    destruct (Nat.ltb i (length t)) eqn:L, (Nat.ltb (S i) (S (length t))) eqn:L2; try reflexivity;
      apply Nat.ltb_lt in L || apply Nat.ltb_ge in L; apply Nat.ltb_lt in L2 || apply Nat.ltb_ge in L2; lia.
Qed.

Lemma areas_cells_metas t t' l : ltac2:(tb__ "0|0|
S0S22S24S2eS2fA2A1S33Vt;A1S33Vt';A1A3S0S22S3A1S13Vt;Vl;A2S13Vt';Vl;A2A3F_;").
Proof.
  intros E. induction l as [|a l IH]; [reflexivity|]. cbn [areas_cells]. rewrite IH. f_equal.
  unfold area_cells. rewrite E. reflexivity.
Qed.

Section SetHd.
  Variables (s : astate) (sc : Z) (v : option sptr).
  Let s' : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S57Vsc;Vv;Vs;A3").
  Lemma sh_footprint : ltac2:(tb__ "0|0|
S0S22S24S4S21A2A1S6Vs';A1S6Vs;A1A3"). Proof using sc v. reflexivity. Qed.
  Lemma sh_init : ltac2:(tb__ "0|0|
S0S25S31Vs';A1S31Vs;A1A3"). Proof using sc v. reflexivity. Qed.
  Lemma sh_metas : ltac2:(tb__ "0|0|
S0S22S24S2eS2fA2A1S33Vs';A1S33Vs;A1A3"). Proof using sc v. reflexivity. Qed.
  Lemma sh_user_blocks : ltac2:(tb__ "0|0|
S0S22S24S2eS21A2A1S8Vs';A1S8Vs;A1A3"). Proof using sc v. reflexivity. Qed.
  Lemma sh_footers : ltac2:(tb__ "0|0|
S0S22S3A1S5bVs';A1S5bVs;A1A3"). Proof using sc v. reflexivity. Qed.
  Lemma sh_MT q : ltac2:(tb__ "0|0|
S0S26S2fA1S9Vs';Vq;A2S9Vs;Vq;A2A3"). Proof using sc v. reflexivity. Qed.

  Definition active_cell (t : astate) (c : Z) : mcell := ltac2:(tb__ "0|0|
SaSbS5fSfS62Z8Vc;A2A2A1U8S1fS5eS26S2eA1S61Vc;A1S41Vt;A1S2dS2eA1A4A1A3").

  Lemma sh_image_In c : ltac2:(tb__ "0|0|
S60Z0Vsc;A2S58S3Vc;S7Vs';A1A3S2S58S3Vc;S7Vs;A1A3S0S3Vc;S68Vs';Vsc;A2A3A2F_;F_;").
  Proof using v.
    intros Hsc Hin. unfold image in *. change (st_areas s') with (st_areas s) in Hin.
    rewrite (areas_cells_metas s' s (st_areas s) eq_refl) in Hin. change (used_metas s') with (used_metas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. right. exact Hin. }
    unfold ctx_cells in Hin |- *.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_seq st_brk st_usage st_unmap_seq st_bounces st_active
      s' set_hd set_active] in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    apply in_map_iff in Hin as [k [Hk Hink]]. rewrite nth_lupd in Hk.
    destruct (Nat.eqb k (Z.to_nat sc) && Nat.ltb (Z.to_nat sc) (length (st_active s)))%bool eqn:E.
    - right. apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst k. unfold active_cell.
      change (st_active s') with (lupd (st_active s) (Z.to_nat sc) v). rewrite nth_lupd, Nat.eqb_refl, E2. cbn [andb].
      rewrite Z2Nat.id in Hk by lia. symmetry. exact Hk.
    - left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists k. auto.
  Qed.
End SetHd.

Section SetBounces.
  Variables (s : astate) (k : Z) (b : Z).
  Let s' : ltac2:(tb__ "0|0|
S38") := ltac2:(tb__ "0|0|
S3eS4aVk;Vb;S3aVs;A1A3Vs;A2").
  Lemma sb_footprint : ltac2:(tb__ "0|0|
S0S22S24S4S21A2A1S6Vs';A1S6Vs;A1A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_init : ltac2:(tb__ "0|0|
S0S25S31Vs';A1S31Vs;A1A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_metas : ltac2:(tb__ "0|0|
S0S22S24S2eS2fA2A1S33Vs';A1S33Vs;A1A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_user_blocks : ltac2:(tb__ "0|0|
S0S22S24S2eS21A2A1S8Vs';A1S8Vs;A1A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_footers : ltac2:(tb__ "0|0|
S0S22S3A1S5bVs';A1S5bVs;A1A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_MT q : ltac2:(tb__ "0|0|
S0S26S2fA1S9Vs';Vq;A2S9Vs;Vq;A2A3"). Proof using b k. reflexivity. Qed.
  Lemma sb_active_hd c : ltac2:(tb__ "0|0|
S0S26S2eA1S12Vs';Vc;A2S12Vs;Vc;A2A3"). Proof using b k. reflexivity. Qed.

  Definition bounce_cell (t : astate) (j : Z) : mcell := ltac2:(tb__ "0|0|
SaSbS5fS10Vj;A2A1U1S11S5eS21S61Vj;A1S3aVt;A1Z0A4A1A3").

  Lemma zupd_length l i x : ltac2:(tb__ "0|0|
S0S2cS27S21S4bVl;Vi;Vx;A3A2S27S21Vl;A2A3").
  Proof using . revert i. induction l as [|y t IH]; intros [|i]; cbn; try reflexivity. f_equal. apply IH. Qed.
  Lemma nth_zupd l i x j d : ltac2:(tb__ "0|0|
S0S21S5eS21Vj;S4bVl;Vi;Vx;A3Vd;A4S25S21L_;S2bS65Vj;Vi;A2S66Vi;S27S21Vl;A2A2A2Vx;S5eS21Vj;Vl;Vd;A4X25x2A3").
  Proof using .
    revert i j. induction l as [|y t IH]; intros [|i] [|j]; cbn; try reflexivity.
    - destruct (Nat.eqb j i); reflexivity || (cbn; destruct j; reflexivity).
    - rewrite IH. destruct (Nat.eqb j i) eqn:E; cbn; [|reflexivity].
      destruct (Nat.ltb i (length t)) eqn:L, (Nat.ltb (S i) (S (length t))) eqn:L2; try reflexivity;
        apply Nat.ltb_lt in L || apply Nat.ltb_ge in L; apply Nat.ltb_lt in L2 || apply Nat.ltb_ge in L2; lia.
  Qed.

  Lemma sb_image_In c : ltac2:(tb__ "0|0|
S60Z0Vk;A2S58S3Vc;S7Vs';A1A3S2S58S3Vc;S7Vs;A1A3S0S3Vc;S67Vs';Vk;A2A3A2F_;F_;").
  Proof using b.
    intros Hk Hin. unfold image in *. change (st_areas s') with (st_areas s) in Hin.
    rewrite (areas_cells_metas s' s (st_areas s) eq_refl) in Hin. change (used_metas s') with (used_metas s) in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    2:{ left. apply in_app_iff. right. exact Hin. }
    unfold ctx_cells in Hin |- *.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_seq st_brk st_usage st_unmap_seq st_bounces st_active
      s' set_bounces] in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_app_iff in Hin as [Hin|Hin].
    { left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    apply in_map_iff in Hin as [j [Hj Hinj]]. unfold zset in Hj. rewrite nth_zupd in Hj.
    destruct (Nat.eqb j (Z.to_nat k) && Nat.ltb (Z.to_nat k) (length (st_bounces s)))%bool eqn:E.
    - right. apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst j. unfold bounce_cell.
      change (st_bounces s') with (zset k b (st_bounces s)). unfold zset. rewrite nth_zupd, Nat.eqb_refl, E2. cbn [andb].
      rewrite Z2Nat.id in Hj by lia. symmetry. exact Hj.
    - left. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
      apply in_map_iff. exists j. auto.
  Qed.
End SetBounces.

Definition delta (s s' : astate) (locs : list loc) : Prop := ltac2:(tb__ "0|1|
S1S0S22S24S4S21A2A1S6Vs';A1S6Vs;A1A3S1S0S22S24S2eS21A2A1S8Vs';A1S8Vs;A1A3S1S0S25S31Vs';A1S31Vs;A1A3S1S0S22S2eA1M0S42Vs';A1S42Vs;A1A3S1S0S22S51A1S47Vs';A1S47Vs;A1A3S1S0S50S45Vs';A1S45Vs;A1A3S1S0G0ScVs';A1ScVs;A1A3S1S0S22S21A1S48Vs';A1S48Vs;A1A3S1S0S21S46Vs';A1S46Vs;A1A3S1S0S21S43Vs';A1S43Vs;A1A3S1S0S2eS44Vs';A1S44Vs;A1A3S3S58S3R1S2aS3S7Vs';A1S5bVs';A1A3A3S2S58S3R2S2aS3S7Vs;A1S5bVs;A1A3A3S58S4S15R2A1Vlocs;A3A2F_;Fc;A2A2A2A2A2A2A2A2A2A2A2").

Lemma delta_refl s : ltac2:(tb__ "0|0|
S54Vs;Vs;S29S4A1A3").
Proof. repeat split; try reflexivity. intros c Hc. left. exact Hc. Qed.

Lemma delta_trans s s' s'' l1 l2 : ltac2:(tb__ "0|0|
S54Vs;Vs';Vl1;A3S54Vs';Vs'';Vl2;A3S54Vs;Vs'';S2aS4Vl1;Vl2;A3A3F_;F_;").
Proof.
  intros (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9a&A9b&A10) (B1&B2&B3&B4&B5&B6&B7&B8&B9&B9a&B9b&B10).
  repeat split; try congruence.
  intros c Hc. destruct (B10 c Hc) as [H|H]; [|right; apply in_app_iff; right; exact H].
  destruct (A10 c H) as [H'|H']; [left; exact H' | right; apply in_app_iff; left; exact H'].
Qed.

Lemma delta_weaken s s' l1 l2 : ltac2:(tb__ "0|0|
S4S58S4R1Vl1;A3S58S4R2Vl2;A3F_;Fx;S54Vs;Vs';Vl1;A3S54Vs;Vs';Vl2;A3F_;F_;").
Proof.
  intros Hsub (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9a&A9b&A10). repeat split; try assumption.
  intros c Hc. destruct (A10 c Hc) as [H|H]; [left; exact H | right; apply Hsub; exact H].
Qed.

Definition meta_locs (g : sptr) : list loc := ltac2:(tb__ "0|0|
S23S4S5S30Vg;S1cA2A1S23S4S5S30Vg;S1bA2A1S23S4S5S30Vg;S1aA2A1S23S4S5S30Vg;S17A2A1S23S4S5S30Vg;S19A2A1S23S4S5S30Vg;S18A2A1S29S4A1A3A3A3A3A3A3").

Lemma meta_slot_cells_locs g x c : ltac2:(tb__ "0|0|
S58S3Vc;S16Vg;Vx;A2A3S58S4S15Vc;A1S56Vg;A1A3F_;").
Proof.
  unfold meta_slot_cells, meta_locs. destruct x as [[pr nx| |am]|]; cbn; intros H;
    repeat (destruct H as [<-|H]; [cbn; tauto|]); destruct H.
Qed.

Lemma delta_su s g am am' : ltac2:(tb__ "0|0|
S59S2eScVs;A1A2S0S26S2fA1S9Vs;Vg;A2S28S2fS32Vam;A1A2A3S53Vam;Vam';A2S54Vs;S64Vg;S32Vam';A1Vs;A3S23S4S5S30S34Vam;A1Z8A2A1S56Vg;A1A3A3F_;F_;F_;").
Proof.
  intros ND Hg SH. unfold delta.
  rewrite (su_user_blocks s g am am' ND Hg SH), (su_footers s g am am' ND Hg SH).
  repeat split; try reflexivity.
  - apply keys_upd_In. eapply MT_Some_In_keys. exact Hg.
  - intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
    destruct (su_image_In s g am am' ND Hg SH c Hc) as [H|[H|H]].
    + left. apply in_app_iff. left. exact H.
    + right. right. exact (meta_slot_cells_locs g _ c H).
    + right. left. subst c. unfold aidx_cell. destruct SH as (E1&_). rewrite E1. destruct (am_maplen am' =? 0); reflexivity.
Qed.

Lemma delta_sh s sc v : ltac2:(tb__ "0|0|
S60Z0Vsc;A2S54Vs;S57Vsc;Vv;Vs;A3S23S4SbS5fSfS62Z8Vsc;A2A2A1S29S4A1A3A3F_;").
Proof.
  intros Hsc. unfold delta. repeat split; try reflexivity.
  intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
  destruct (sh_image_In s sc v c Hsc Hc) as [H|H]; [left; apply in_app_iff; left; exact H|].
  right. subst c. left. reflexivity.
Qed.

Lemma delta_sb s k b : ltac2:(tb__ "0|0|
S60Z0Vk;A2S54Vs;S3eS4aVk;Vb;S3aVs;A1A3Vs;A2S23S4SbS5fS10Vk;A2A1S29S4A1A3A3F_;").
Proof.
  intros Hk. unfold delta. repeat split; try reflexivity.
  intros c Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
  destruct (sb_image_In s k b c Hk Hc) as [H|H]; [left; apply in_app_iff; left; exact H|].
  right. subst c. left. reflexivity.
Qed.

Lemma delta_su_keep s g am am' : ltac2:(tb__ "0|0|
S59S2eScVs;A1A2S0S26S2fA1S9Vs;Vg;A2S28S2fS32Vam;A1A2A3S53Vam;Vam';A2S0S21S35Vam';A1S35Vam;A1A3S54Vs;S64Vg;S32Vam';A1Vs;A3S56Vg;A1A3F_;F_;F_;F_;").
Proof.
  intros ND Hg SH Ea. pose proof (delta_su s g am am' ND Hg SH) as D.
  unfold delta in *. destruct D as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9a&A9b&A10). repeat split; try assumption.
  intros c Hc. destruct (A10 c Hc) as [H|[H|H]]; [left; exact H | | right; exact H].

  apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; rewrite <- (su_footers s g am am' ND Hg SH); exact Hc].
  destruct (su_image_In s g am am' ND Hg SH c Hc) as [Ho|[Hm|Hx]].
  - left. apply in_app_iff. left. exact Ho.
  - right. exact (meta_slot_cells_locs g _ c Hm).
  - left. apply in_app_iff. left. subst c.
    replace (aidx_cell am') with (aidx_cell am).
    + apply (In_image_group s g am); [exact (used_metas_g_old s g am am' ND Hg) |].
      rewrite group_cells_eq. right. left. reflexivity.
    + unfold aidx_cell. destruct SH as (E1&_&_&E4&_). rewrite E1, E4, Ea. reflexivity.
Qed.
