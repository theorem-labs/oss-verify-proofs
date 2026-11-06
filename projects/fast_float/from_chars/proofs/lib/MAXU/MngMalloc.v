(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfMalloc OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngImage.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mf_first (am : ameta) : Z := lowbit (am_avail am).
Definition mf_idx (am : ameta) : Z := ctz32 (mf_first am).
Definition mf_am1 (am : ameta) : ameta := am_set_avail (am_avail am - mf_first am) am.

(* [comment removed for export] *)
Definition ef_slackm (am : ameta) (n : Z) : Z := (stride_of am - IB - n) / UNIT.
Definition ef_offm (am : ameta) (n off0 : Z) : Z := ef_off (ef_slackm am n) off0.
Definition ef_rsvm (am : ameta) (n off : Z) : Z :=
  let reserved := stride_of am - IB - UNIT * off - n in if 5 <=? reserved then 5 else reserved.
Definition ef_hdrm (am : ameta) (idx n off : Z) : Z * Z :=
  if off =? 0 then (idx + ef_rsvm am n off * 32, (stride_of am * idx) / UNIT) else (224, off).
Definition ef_am (am : ameta) (idx n off : Z) : ameta :=
  upd_slot am idx (mkSlot (Some (ef_hdrm am idx n off)) (Some (mkFrame off n FUser))).
Definition ef_ptr (am : ameta) (idx off : Z) : sptr := padd (slot_start am idx) (UNIT * off).

(* [comment removed for export] *)
Definition s_mf (s : astate) (g : sptr) (am : ameta) (n off : Z) : astate :=
  set_meta s g (MUsed (ef_am (mf_am1 am) (mf_idx am) n off)).

(* [comment removed for export] *)
Definition ef_trace (am : ameta) (idx n ctr off0 : Z) : list (kreq * Z) :=
  if ef_slackm am n =? 0 then [] else match ss_hdr (nth_slot am idx) with Some _ => [] | None => [(KJunk (Z.land ctr 255), off0)] end.

Lemma stride_set_avail : forall am v, stride_of (am_set_avail v am) = stride_of am.
Proof. intros [] v. reflexivity. Qed.

Lemma nth_slot_set_avail : forall am v i, nth_slot (am_set_avail v am) i = nth_slot am i.
Proof. intros [] v i. reflexivity. Qed.

Lemma last_set_avail : forall am v, am_last (am_set_avail v am) = am_last am.
Proof. intros [] v. reflexivity. Qed.

Lemma slot_start_set_avail : forall am v i, slot_start (am_set_avail v am) i = slot_start am i.
Proof. intros [] v i. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ef_off_zero_slack : forall off0, 0 <= off0 -> ef_off 0 off0 = 0.
Proof.
  intros off0 H. unfold ef_off. destruct (off0 <=? 0) eqn:E; [apply Z.leb_le in E; lia|].
  cbv zeta. change (ef_mask 0) with 0. rewrite Z.land_0_r. reflexivity.
Qed.

Lemma mupdate_twice' : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn [mupdate].
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ef_off_model : forall sl a0,
  (if sl <? a0 then
     if sl <? Z.land a0 (Z.lor (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2))
                              (Z.shiftr (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2)) 4))
     then Z.land a0 (Z.lor (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2))
                              (Z.shiftr (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2)) 4)) - (sl + 1)
     else Z.land a0 (Z.lor (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2))
                              (Z.shiftr (Z.lor (Z.lor sl (Z.shiftr sl 1)) (Z.shiftr (Z.lor sl (Z.shiftr sl 1)) 2)) 4))
   else a0) = ef_off sl a0.
Proof.
  intros sl a0. unfold ef_off, ef_mask. cbv zeta.
  destruct (sl <? a0) eqn:E1; destruct (a0 <=? sl) eqn:E2; try reflexivity.
  - apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia.
  - apply Z.ltb_ge in E1. apply Z.leb_gt in E2. lia.
Qed.

Lemma ef_off_rng : forall sl a0, 0 <= sl -> 0 <= a0 <= 255 -> 0 <= ef_off sl a0 <= sl /\ ef_off sl a0 <= 255.
Proof.
  intros sl a0 Hsl Ha0. destruct (Z_lt_le_dec sl a0) as [C|C].
  - pose proof (mval_le sl a0 ltac:(lia) Ha0 C) as ML. rewrite masked_val in ML by lia. lia.
  - unfold ef_off. replace (a0 <=? sl) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.

Lemma set_metas_twice : forall v v' s, set_metas v (set_metas v' s) = set_metas v s.
Proof. intros v v' []. reflexivity. Qed.

Lemma st_metas_set_metas : forall v s, st_metas (set_metas v s) = v.
Proof. intros v []. reflexivity. Qed.

Section Yields.

#[using="Type"] Theorem malloc_fast_yields : forall s n g am off0,
  WF s -> 1 <= n < MMAP_THRESHOLD ->
  active_hd s (size_to_class n) = Some g -> MT s g = Some (MUsed am) -> am_avail am <> 0 ->
  0 <= off0 < 256 ->
  (forall h3 h16, ss_hdr (nth_slot am (mf_idx am)) = Some (h3, h16) ->
     ef_slackm am n <> 0 -> off0 = Z.land (if h3 =? 0 then st_mmap_counter s else h16 + 1) 255) ->
  yields (malloc n s) (ef_trace am (mf_idx am) n (st_mmap_counter s) off0)
         (Some (ef_ptr am (mf_idx am) (ef_offm am n off0)), s_mf s g am n (ef_offm am n off0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s n g am off0 HW Hn Hact HMT Hav Hoff0 Hhdr.
  unfold malloc. replace (size_overflows n) with false by (unfold size_overflows; symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold bind, get, ret. cbn [ibind].
  unfold active_hd in Hact. rewrite Hact. cbn [osptr_eqb andb]. rewrite Hact.
  unfold getm, bind, get, ret. cbn [ibind]. unfold MT in HMT. rewrite HMT. cbn [ibind].
  replace (am_avail am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hav).
  unfold setm, modify. cbn [ibind set_metas st_mmap_counter st_metas].
  unfold enframe, getm, bind, get, ret, mcheck. cbn [ibind set_metas st_mmap_counter st_metas].
  rewrite mlookup_mupdate_same. cbn [ibind].
  (* [comment removed for export] *)
  assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & Mabove2 & _).
  destruct (lowbit_spec (am_avail am) ltac:(lia)) as (k & Hk & Hlb & Hbit & Hlow).
  assert (Eidx : mf_idx am = k) by (unfold mf_idx, mf_first; rewrite Hlb; apply ctz32_bit; lia).
  assert (Hkl : k <= am_last am).
  { destruct (Z_le_gt_dec k (am_last am)) as [|Hg]; [assumption|]. rewrite (proj1 (Mabove k ltac:(lia))) in Hbit. discriminate. }
  change (ctz32 (lowbit (am_avail am))) with (mf_idx am). change (lowbit (am_avail am)) with (mf_first am).
  change (am_set_avail (am_avail am - mf_first am) am) with (mf_am1 am).
  unfold mf_am1 at 1. rewrite last_set_avail. rewrite Eidx.
  replace ((0 <=? k) && (k <=? am_last am)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  unfold ret. cbn [ibind].
  unfold mf_am1. rewrite !stride_set_avail, !nth_slot_set_avail.
  change ((stride_of am - IB - n) / UNIT) with (ef_slackm am n).
  assert (Sl0 : 0 <= ef_slackm am n).
  { pose proof (size_to_class_range n ltac:(lia)) as [Hsc0 Hfit0].
    destruct (head_used [] None U0 s (size_to_class n) g HW Hsc0 Hact) as (am' & Hu' & Hsa).
    assert (E' : am' = am) by (unfold usedX, MTX in Hu'; cbn [memb] in Hu'; unfold MT in Hu'; rewrite HMT in Hu'; injection Hu'; auto).
    subst am'.
    pose proof (avail_bit_not_undersized [] None U0 s g am k HW Hux ltac:(lia) ltac:(lia) ltac:(rewrite Z.lor_spec, Hbit; reflexivity)) as Hus.
    rewrite Hsa in Hus. unfold ef_slackm, UNIT, IB in *. apply Z.div_pos; lia. }
  unfold ef_trace.
  destruct (ef_slackm am n =? 0) eqn:ES; [|destruct (ss_hdr (nth_slot am k)) as [[h3 h16]|] eqn:EH].
  - cbn [ibind]. rewrite ef_off_model. unfold massert. apply Z.eqb_eq in ES. rewrite ES.
    rewrite (ef_off_zero_slack 0) by lia. cbn -[set_metas mupdate].
    replace (ef_offm am n off0) with 0 by (unfold ef_offm; rewrite ES; symmetry; apply ef_off_zero_slack; lia).
    apply (f_equal2 pair); [f_equal; unfold ef_ptr; rewrite slot_start_set_avail; reflexivity|].
    unfold s_mf, set_meta. rewrite st_metas_set_metas, mupdate_twice', set_metas_twice. f_equal. f_equal. f_equal.
    unfold ef_am, ef_hdrm, ef_rsvm, mf_am1. rewrite Eidx, stride_set_avail. reflexivity.
  - apply Z.eqb_neq in ES. rewrite <- (Hhdr h3 h16 ltac:(rewrite Eidx; exact EH) ES). cbn [ibind]. rewrite ef_off_model. unfold massert.
    pose proof (ef_off_rng (ef_slackm am n) off0 Sl0 ltac:(lia)) as (OR1 & OR2).
    replace (ef_off (ef_slackm am n) off0 <=? ef_slackm am n) with true by (symmetry; apply Z.leb_le; lia).
    cbn -[set_metas mupdate].
    change (ef_off (ef_slackm am n) off0) with (ef_offm am n off0).
    apply (f_equal2 pair); [f_equal; unfold ef_ptr; rewrite slot_start_set_avail; reflexivity|].
    unfold s_mf, set_meta. rewrite st_metas_set_metas, mupdate_twice', set_metas_twice. f_equal. f_equal. f_equal.
    unfold ef_am, ef_hdrm, ef_rsvm, mf_am1. rewrite Eidx, stride_set_avail. reflexivity.
  - unfold askz. cbn [ibind yields]. split; [reflexivity|]. split; [cbn; lia|].
    rewrite (Z.mod_small off0 256) by lia. rewrite ef_off_model. unfold massert.
    pose proof (ef_off_rng (ef_slackm am n) off0 Sl0 ltac:(lia)) as (OR1 & OR2).
    replace (ef_off (ef_slackm am n) off0 <=? ef_slackm am n) with true by (symmetry; apply Z.leb_le; lia).
    cbn -[set_metas mupdate].
    change (ef_off (ef_slackm am n) off0) with (ef_offm am n off0).
    apply (f_equal2 pair); [f_equal; unfold ef_ptr; rewrite slot_start_set_avail; reflexivity|].
    unfold s_mf, set_meta. rewrite st_metas_set_metas, mupdate_twice', set_metas_twice. f_equal. f_equal. f_equal.
    unfold ef_am, ef_hdrm, ef_rsvm, mf_am1. rewrite Eidx, stride_set_avail. reflexivity.
Qed.

End Yields.
