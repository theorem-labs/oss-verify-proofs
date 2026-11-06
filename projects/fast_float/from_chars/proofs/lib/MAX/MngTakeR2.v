(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngImage MngSurgery MngCtx MngTake MngOwn MngMalloc MngTakeRepr AXF_efbz AXF_efmem
  MngGeoX MngGM MngTakeR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section TR.
Variables (L : layout) (g : sptr) (am : ameta) (k n off : Z).

Local Abbreviation am2 := (ef_am am k n off).
Local Abbreviation hdr := (ef_hdrm am k n off).
Local Abbreviation fr := (mkFrame off n FUser).

(* [comment removed for export] *)
Definition tr_cnew : list mcell :=
  [MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ (fst hdr));
   MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ (snd hdr))]
  ++ (if off =? 0 then []
      else [MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-4))) 1 (VZ 0);
            MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-3))) 1 (VZ (hdr_byte3 am2 k fr));
            MCell (LMem (padd (padd (slot_start am k) (UNIT * off)) (-2))) 2 (VZ (hdr_off16 am2 k fr))]).

(* [comment removed for export] *)
Definition tr_mnew : list mcell :=
  let e := slot_end am2 k in
  let r := frame_rsv am2 fr in
  (if 0 <? r then [MCell (LMem (padd e (- r))) 1 (VZ 0)] else [])
  ++ (if 5 <=? r then [MCell (LMem (padd e (-4))) 4 (VZ r); MCell (LMem (padd e (-5))) 1 (VZ 0)] else []).

#[using="Type"] Lemma tr_am2_facts : am_mem am2 = am_mem am /\ stride_of am2 = stride_of am /\ am_last am2 = am_last am /\
  (forall j, j <> k -> 0 <= j -> 0 <= k -> nth_slot am2 j = nth_slot am j) /\
  (0 <= k <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
     nth_slot am2 k = mkSlot (Some hdr) (Some fr)) /\
  meta_bits am2 = meta_bits am /\ am_prev am2 = am_prev am /\ am_next am2 = am_next am /\ am_freed am2 = am_freed am /\
  am_avail am2 = am_avail am /\ slot_start am2 k = slot_start am k /\ am_maplen am2 = am_maplen am /\ am_aidx am2 = am_aidx am.
Proof. LiaFast.lf_pins LiaFast.u0.
  unfold ef_am, upd_slot. destruct am. cbn. repeat split; try reflexivity.
  - intros j Hj Hj0 Hk0. unfold nth_slot. cbn. rewrite nth_lupd_other; [reflexivity|]. lia.
  - intros Hk Hl. unfold nth_slot. cbn. rewrite nth_lupd_same; [reflexivity|]. cbn in Hl. rewrite Hl. lia.
Qed.

(* [comment removed for export] *)
Section Cells.
Variables (m2 : word -> option byte) (sz : Z).
Local Abbreviation stv := (loc_addr L (LMem (slot_start am k))).
Local Abbreviation memv := (loc_addr L (LMem (am_mem am))).

Hypothesis Esz : 16 * sz = stride_of am.
Hypothesis Rst : 17 <= stv <= 2^63 - 1.
Hypothesis Rend : stv + 16 * sz <= 2^63.
Hypothesis Roff : 0 <= off <= 255.
Hypothesis Rn : 1 <= n.
Hypothesis Fit : n + 4 + 16 * off <= 16 * sz.
Hypothesis Hk0 : 0 <= k.

Local Abbreviation mE := (efb_mem m2 k n memv sz stv off).

#[using="Type"] Lemma tr_Est : stv = memv + 16 + stride_of am * k.
Proof. LiaFast.lf_pins LiaFast.u0. unfold slot_start. rewrite loc_padd. unfold UNIT. ring. Qed.

#[using="Esz"] Lemma tr_rsv_code_eq : forall (am' : ameta) fr', stride_of am' = stride_of am -> fr_off fr' = off -> fr_n fr' = n ->
  rsv_code am' fr' = efb_code (efb_rsv sz n off).
Proof. LiaFast.lf_pins (fun (Esz : LiaFast.U) => LiaFast.u0).
  intros am' fr' E1 E2 E3. unfold rsv_code, efb_code, efb_rsv. rewrite E1, E2, E3, <- Esz. unfold UNIT, IB.
  destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:A; [apply Z.eqb_eq in A; rewrite A; reflexivity|].
  apply Z.eqb_neq in A. destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:B.
  - apply Z.ltb_lt in B. replace (5 <=? 16 * sz - 4 - 16 * off - n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - apply Z.ltb_ge in B. replace (5 <=? 16 * sz - 4 - 16 * off - n) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

#[using="Esz"] Lemma tr_ef_rsvm_eq : ef_rsvm am n off = efb_code (efb_rsv sz n off).
Proof. LiaFast.lf_pins (fun (Esz : LiaFast.U) => LiaFast.u0). unfold ef_rsvm. exact (tr_rsv_code_eq am (mkFrame off n FUser) eq_refl eq_refl eq_refl). Qed.

#[using="sz Esz"] Lemma tr_off16_eq : (stv + 16 * off - memv - 16) / 16 = (stride_of am * k) / UNIT + off.
Proof. LiaFast.lf_pins (fun (sz Esz : LiaFast.U) => LiaFast.u0).
  rewrite tr_Est. rewrite <- Esz. unfold UNIT.
  replace (memv + 16 + 16 * sz * k + 16 * off - memv - 16) with ((sz * k + off) * 16) by ring.
  replace (16 * sz * k) with ((sz * k) * 16) by ring. rewrite !Z.div_mul by lia. reflexivity.
Qed.

#[using="Esz Rst Rend Roff Rn Fit"] Theorem tr_cnew_holds : Forall (cell_holds L (bview SEGS mE)) tr_cnew.
Proof. LiaFast.lf_pins (fun (Esz Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  unfold tr_cnew. apply Forall_app. split.
  - constructor; [|constructor; [|constructor]].
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      unfold ef_hdrm. destruct (off =? 0) eqn:E0; cbn [fst snd].
      * apply Z.eqb_eq in E0. pose proof (efb_mem_p3 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P3.
        rewrite E0 in P3 at 2. replace (stv + 16 * 0 - 3) with (stv + -3 + Z.of_nat 0) in P3 by lia. rewrite P3.
        f_equal. unfold efb_code'. rewrite tr_ef_rsvm_eq. f_equal. ring.
      * apply Z.eqb_neq in E0. destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (H3 & _ & _).
        replace (stv + -3 + Z.of_nat 0) with (stv - 3) by lia. exact H3.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. intros j Hj.
      unfold ef_hdrm. destruct (off =? 0) eqn:E0; cbn [fst snd].
      * apply Z.eqb_eq in E0. pose proof (efb_mem_p2 m2 k n memv sz stv off Rst Rend Roff Rn Fit j Hj) as P2.
        replace (stv + 16 * off - 2 + Z.of_nat j) with (stv + -2 + Z.of_nat j) in P2 by lia. rewrite P2.
        f_equal. rewrite tr_off16_eq, E0, Z.add_0_r. reflexivity.
      * apply Z.eqb_neq in E0. destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (_ & H2 & _).
        replace (stv + -2 + Z.of_nat j) with (stv - 2 + Z.of_nat j) by lia. exact (H2 j Hj).
  - destruct (off =? 0) eqn:E0; [constructor|]. apply Z.eqb_neq in E0.
    destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (_ & _ & H4).
    pose proof (efb_mem_p3 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P3.
    pose proof (efb_mem_p2 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P2.
    pose proof tr_am2_facts as (_ & Es2 & _).
    constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (stv + UNIT * off + -4 + Z.of_nat 0) with (stv + 16 * off - 4) by (unfold UNIT; lia). exact H4.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (stv + UNIT * off + -3 + Z.of_nat 0) with (stv + 16 * off - 3) by (unfold UNIT; lia). rewrite P3.
      f_equal. unfold hdr_byte3. cbv iota.
      rewrite (tr_rsv_code_eq am2 (mkFrame off n FUser) Es2 eq_refl eq_refl). reflexivity.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj.
      replace (stv + UNIT * off + -2 + Z.of_nat j) with (stv + 16 * off - 2 + Z.of_nat j) by (unfold UNIT; lia). rewrite (P2 j Hj).
      f_equal. unfold hdr_off16. rewrite Es2. cbn [fr_off]. rewrite tr_off16_eq. reflexivity.
Qed.

#[using="Esz Rst Rend Roff Rn Fit"] Theorem tr_mnew_holds : Forall (cell_holds L (bview SEGS mE)) tr_mnew.
Proof. LiaFast.lf_pins (fun (Esz Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  pose proof tr_am2_facts as (_ & Es2 & _ & _ & _ & _ & _ & _ & _ & _ & Est2 & _).
  assert (Ee : loc_addr L (LMem (slot_end am2 k)) = stv + 16 * sz - 4).
  { unfold slot_end. rewrite loc_padd, Est2, Es2, <- Esz. unfold IB. ring. }
  assert (Er : frame_rsv am2 (mkFrame off n FUser) = efb_rsv sz n off).
  { unfold frame_rsv, efb_rsv. cbn [fr_off fr_n]. rewrite Es2, <- Esz. unfold UNIT, IB. ring. }
  unfold tr_mnew. cbv zeta. rewrite Er. apply Forall_app. split.
  - destruct (0 <? efb_rsv sz n off) eqn:E1; [|constructor]. apply Z.ltb_lt in E1.
    constructor; [|constructor].
    unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Ee. intros j Hj. assert (j = 0%nat) as -> by lia.
    replace (stv + 16 * sz - 4 + - efb_rsv sz n off + Z.of_nat 0) with (stv + 16 * off + n) by (unfold efb_rsv; lia).
    apply efb_mem_rsv1; [exact Rst | exact Rend | exact Roff | exact Rn | exact Fit | lia].
  - destruct (5 <=? efb_rsv sz n off) eqn:E5; [|constructor]. apply Z.leb_le in E5.
    destruct (efb_mem_rsv5 m2 k n memv sz stv off Rst Rend Roff Rn E5) as (H5 & H4).
    constructor; [|constructor; [|constructor]].
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Ee. intros j Hj. exact (H4 j Hj).
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Ee. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (stv + 16 * sz - 4 + -5 + Z.of_nat 0) with (stv + 16 * sz - 4 - 5) by lia. exact H5.
Qed.
End Cells.

(* [comment removed for export] *)
Section Repr.
Variables (s : astate) (R : option (sptr * Z)) (U : Z -> Z).
Hypothesis HI : Inv [] R U s.
Hypothesis Hux : usedX [] s g am.
Hypothesis Hk : 0 <= k <= am_last am.
Hypothesis Hfree : ss_fr (nth_slot am k) = None.

Local Abbreviation s' := (set_meta s g (MUsed am2)).
Local Abbreviation stv := (loc_addr L (LMem (slot_start am k))).

#[using="R U HI Hux Hk"] Lemma tr_cnew_in : forall c, In c tr_cnew -> In c (image s').
Proof. LiaFast.lf_pins (fun (R U HI Hux Hk : LiaFast.U) => LiaFast.u0).
  intros c Hc.
  pose proof tr_am2_facts as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est & Eml & Eai).
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  pose proof (inv_groups HI g am Hux) as G. pose proof G as (Gm & _). destruct Gm as (_ & _ & Mlen & _).
  pose proof (KS_of_Inv [] R U s HI) as KS.
  apply (In_image_setm_new s g am am2 c KS HMT).
  unfold tr_cnew in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct Hc as [<-|[<-|[]]].
    + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
      unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
      cbn [fst snd app In]. tauto.
    + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
      unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
      cbn [fst snd app In]. tauto.
  - destruct (off =? 0) eqn:E0; [destruct Hc|].
    right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
    unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr fr_off]. rewrite E0.
    apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

#[using="R U HI Hux Hk Hfree"] Theorem reserved_slot_repr : forall (m m' : byteview),
  repr L s m -> WF s' ->
  (forall x, ~ (stv - 3 <= x < stv + stride_of am - 4) -> m' x = m x) ->
  (forall x, m x <> None -> m' x <> None) ->
  Forall (cell_holds L m') tr_cnew ->
  repr L s' m'.
Proof. LiaFast.lf_pins (fun (R U HI Hux Hk Hfree : LiaFast.U) => LiaFast.u0).
  intros m m' HR HW' BV BM HNew.
  pose proof tr_am2_facts as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est & Eml & Eai).
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  pose proof (inv_groups HI g am Hux) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & _). destruct Gm as (_ & _ & Mlen & _).
  pose proof (KS_of_Inv [] R U s HI) as KS.
  pose proof HR as (HL & HC & HFM).
  assert (HL' : layout_ok L s') by (apply layout_ok_set_meta; exact HL).
  assert (NewIn : forall c, In c tr_cnew -> In c (image s')).
  { intros c Hc. apply (In_image_setm_new s g am am2 c KS HMT).
    unfold tr_cnew in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - destruct Hc as [<-|[<-|[]]].
      + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
        unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
        cbn [fst snd app In]. tauto.
      + right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
        unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr]. rewrite (surjective_pairing hdr).
        cbn [fst snd app In]. tauto.
    - destruct (off =? 0) eqn:E0; [destruct Hc|].
      right. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [apply In_zseq; lia|].
      unfold slot_cells. rewrite (Ek Hk Mlen), Est. cbn [ss_hdr ss_fr fr_off]. rewrite E0.
      apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
  apply (repr_from_pre L s s' m m' tr_cnew HR HL').
  - rewrite footprint_set_meta. apply Forall_forall. intros rg Hrg x Hx. apply BM. exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - (* [comment removed for export] *)
    intros c Hc. destruct (cov_setm s g am am2 c KS HMT Hc) as [H1|[H2|H3]]; [left; exact H1| |].
    + left. apply (In_image_used s g am _ KS HMT). left. unfold meta_slot_cells in H2 |- *. rewrite Ep, Enx, Em, Eav, Ef, Eb in H2. exact H2.
    + unfold group_cells in H3. rewrite Em in H3. apply in_app_iff in H3 as [H3|H3].
      * left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. left.
        rewrite Eml, Eai in H3. exact H3.
      * apply in_flat_map in H3 as [j [Hj Hcj]]. rewrite El in Hj. apply In_zseq in Hj.
        destruct (Z.eq_dec j k) as [->|Hjk].
        -- unfold slot_cells in Hcj. rewrite (Ek Hk Mlen), Est in Hcj. cbn [ss_hdr ss_fr] in Hcj.
           apply in_app_iff in Hcj as [Hcj|Hcj].
           ++ left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
              exists k. split; [apply In_zseq; lia|]. unfold slot_cells. apply in_app_iff. left. exact Hcj.
           ++ right. apply in_app_iff in Hcj as [Hcj|Hcj].
              ** unfold tr_cnew. rewrite (surjective_pairing hdr) in Hcj. cbn [fst snd] in Hcj.
                 destruct Hcj as [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity].
              ** cbn [fr_off] in Hcj. unfold tr_cnew. apply in_app_iff. right. exact Hcj.
        -- left. apply (In_image_used s g am _ KS HMT). right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
           exists j. split; [apply In_zseq; lia|].
           unfold slot_cells in Hcj |- *. rewrite (Eoth j Hjk ltac:(lia) ltac:(lia)) in Hcj.
           assert (Estj : slot_start am2 j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
           rewrite Estj in Hcj. exact Hcj.
  - exact HNew.
  - (* [comment removed for export] *)
    intros c a Hc' Hc Hn Ha. apply BV. intros Hsl.
    destruct (Z_lt_le_dec a (loc_addr L (LMem (slot_start am k)))) as [Lt|Ge].
    + assert (C3 : In (MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ (fst hdr))) tr_cnew) by (unfold tr_cnew; left; reflexivity).
      assert (C16 : In (MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ (snd hdr))) tr_cnew) by (unfold tr_cnew; right; left; reflexivity).
      destruct (Z_lt_le_dec a (loc_addr L (LMem (slot_start am k)) - 2)) as [A3|A16].
      * assert (Hne : c <> MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ (fst hdr))) by (intros ->; exact (Hn C3)).
        pose proof (image_pair_disjoint s' L _ _ HW' HL' Hc' (NewIn _ C3) Hne) as D.
        unfold ranges_disjoint, cell_range, in_rng in *. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in *. rewrite loc_padd in D. lia.
      * assert (Hne : c <> MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ (snd hdr))) by (intros ->; exact (Hn C16)).
        pose proof (image_pair_disjoint s' L _ _ HW' HL' Hc' (NewIn _ C16) Hne) as D.
        unfold ranges_disjoint, cell_range, in_rng in *. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in *. rewrite loc_padd in D. lia.
    + destruct (In_dec mcell_eq_dec c (slot_cells am k)) as [Hk'|Hk'].
      * unfold slot_cells in Hk'. rewrite Hfree in Hk'. rewrite app_nil_r in Hk'.
        unfold cell_range, in_rng in Ha. cbn [fst snd] in Ha.
        apply in_app_iff in Hk' as [Hk'|Hk'].
        -- destruct Hk' as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Ha. rewrite loc_padd in Ha. lia.
        -- destruct (ss_hdr (nth_slot am k)) as [[h3 h16]|]; [|destruct Hk'].
           destruct Hk' as [<-|[<-|[]]]; cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Ha; rewrite loc_padd in Ha; lia.
      * pose proof (image_outside_free_slot_R R U s L c g am k HI HL Hux Hk Hfree Hc Hk') as D.
        unfold ranges_disjoint, cell_range, free_slot_range, in_rng in D, Ha. cbn [fst snd] in D, Ha.
        lia.
  - intros c Hc. apply image_cell_width with (s := s'). exact Hc.
Qed.

#[using="R U HI Hux Hk Hfree"] Theorem reserved_slot_markers : forall (m m' : byteview),
  repr L s m -> markers_hold L s m ->
  (forall x, ~ (stv - 3 <= x < stv + stride_of am - 4) -> m' x = m x) ->
  Forall (cell_holds L m') tr_mnew ->
  markers_hold L s' m'.
Proof. LiaFast.lf_pins (fun (R U HI Hux Hk Hfree : LiaFast.U) => LiaFast.u0).
  intros m m' HR HM BV HNew.
  pose proof tr_am2_facts as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est & Eml & Eai).
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  pose proof (inv_groups HI g am Hux) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & _ & Gsl & _). destruct Gm as (Mlast & _ & Mlen & _).
  pose proof HR as (HL & HC & HFM). pose proof HL as (_ & _ & Ldisj & Lrng).
  assert (Eloc : forall r, loc_addr L (LMem r) = ly_reg L (prid r) + poff r) by (intros [rr oo]; reflexivity).
  (* [comment removed for export] *)
  assert (OLD : forall c, In c (markers s) -> cell_holds L m' c).
  { intros c Hc. pose proof (proj1 (Forall_forall _ _) HM c Hc) as Hh.
    assert (W1 : (1 <= mc_w c)%nat).
    { unfold markers in Hc. apply in_flat_map in Hc as [[g2 a2] [_ Hc]]. cbn [snd] in Hc. unfold meta_markers in Hc.
      apply in_app_iff in Hc as [Hc|[<-|[]]]; [|cbn; lia].
      apply in_flat_map in Hc as [i [_ Hc]]. destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct Hc].
      destruct (fr_kind f); [|destruct Hc]. unfold marker_cells in Hc. destruct Hc as [<-|Hc]; [cbn; lia|].
      apply in_app_iff in Hc as [Hc|Hc]; [destruct (0 <? _); [destruct Hc as [<-|[]]; cbn; lia | destruct Hc]|].
      destruct (5 <=? _); [destruct Hc as [<-|[<-|[]]]; cbn; lia | destruct Hc]. }
    apply (cell_holds_frame L m m' c W1 Hh). intros x Hx. apply BV. intros Hsl.
    pose proof (markers_outside_free_slot_R R U s L c g am k HI HL Hux Hk Hfree Hc) as D.
    unfold ranges_disjoint, cell_range, free_slot_range, in_rng in *. cbn [fst snd] in *. lia. }
  (* [comment removed for export] *)
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  assert (ND' : List.NoDup (keys s')).
  { unfold keys, set_meta. cbn [st_metas set_metas]. rewrite map_fst_mupdate_In; [exact ND|].
    apply (mlookup_In_keys (st_metas s) g (MUsed am)). exact HMT. }
  assert (UM : forall h a, In (h, a) (used_metas s) <-> MT s h = Some (MUsed a)) by (intros h a; exact (used_metas_iff s h a ND)).
  apply Forall_forall. intros c Hc.
  destruct (In_markers_inv _ c Hc) as [(h & a & j & f & Hfr' & Kf & Hc') | (h & a & Hua & ->)].
  - destruct (in_frames_inv _ _ _ _ _ Hfr') as (Hua & Hj & Hfj).
    apply (used_metas_iff _ h a ND') in Hua. unfold MT, set_meta in Hua. cbn [st_metas set_metas] in Hua.
    destruct (sptr_eq_dec h g) as [->|Hhg].
    + rewrite mlookup_mupdate_same in Hua. injection Hua as <-.
      destruct (Z.eq_dec j k) as [->|Hjk].
      * rewrite (Ek Hk Mlen) in Hfj. cbn [ss_fr] in Hfj. injection Hfj as <-.
        unfold marker_cells in Hc'. destruct Hc' as [<-|Hc'].
        -- (* [comment removed for export] *)
           assert (Ese : slot_end am2 k = slot_end am k).
           { unfold slot_end. rewrite Es, Est. reflexivity. }
           rewrite Ese.
           destruct (Z.eq_dec k (am_last am)) as [Eql|Nql].
           ++ rewrite Eql. apply OLD. change (MCell (LMem (slot_end am (am_last am))) 1 (VZ 0)) with (gend_cell am).
              apply (In_gend s g am). apply UM. exact HMT.
           ++ (* [comment removed for export] *)
              set (ck := MCell (LMem (padd (slot_start am (k + 1)) (-4))) 1 (VZ 0)).
              assert (Cin : In ck (image s)).
              { apply (In_image_used s g am _ (KS_of_Inv [] R U s HI) HMT). right. unfold group_cells. apply in_app_iff. right.
                apply in_flat_map. exists (k + 1). split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity. }
              assert (Eck : padd (slot_start am (k + 1)) (-4) = slot_end am k).
              { apply sptr_eq_parts; [rewrite prid_padd, prid_slot_start; unfold slot_end; rewrite prid_padd, prid_slot_start; reflexivity|].
                unfold slot_end. rewrite !poff_padd, !poff_slot_start. unfold IB. ring. }
              assert (Hck : cell_holds L m ck) by exact (proj1 (Forall_forall _ _) HC ck Cin).
              unfold ck in Hck. rewrite Eck in Hck.
              apply (cell_holds_frame L m m' (MCell (LMem (slot_end am k)) 1 (VZ 0)) ltac:(cbn; lia) Hck).
              intros x Hx. unfold in_rng, cell_range in Hx. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat] in Hx.
              assert (Ex : x = loc_addr L (LMem (slot_end am k))) by lia. subst x.
              apply BV.
              unfold slot_end. rewrite loc_padd. unfold IB. lia.
        -- apply (proj1 (Forall_forall _ _) HNew). exact Hc'.
      * apply OLD. rewrite El in Hj. apply (In_markers s g am j f c).
        -- unfold frames. apply in_flat_map. exists (g, am). split; [apply UM; exact HMT|].
           apply in_flat_map. exists j. split; [apply In_zseq; lia|]. rewrite <- (Eoth j Hjk ltac:(lia) ltac:(lia)), Hfj. left. reflexivity.
        -- exact Kf.
        -- unfold marker_cells, slot_end, frame_rsv in *. rewrite Es in Hc'.
           assert (Estj : slot_start am2 j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
           rewrite Estj in Hc'. exact Hc'.
    + rewrite mlookup_mupdate_other in Hua by exact Hhg. apply OLD. apply (In_markers s h a j f c); [|exact Kf | exact Hc'].
      unfold frames. apply in_flat_map. exists (h, a). split; [apply UM; exact Hua|].
      apply in_flat_map. exists j. split; [apply In_zseq; lia|]. rewrite Hfj. left. reflexivity.
  - apply (used_metas_iff _ h a ND') in Hua. unfold MT, set_meta in Hua. cbn [st_metas set_metas] in Hua.
    apply OLD. destruct (sptr_eq_dec h g) as [->|Hhg].
    + rewrite mlookup_mupdate_same in Hua. injection Hua as <-.
      replace (gend_cell am2) with (gend_cell am).
      * apply (In_gend s g am). apply UM. exact HMT.
      * unfold gend_cell, slot_end. rewrite El, Es. unfold slot_start. rewrite Em, Es. reflexivity.
    + rewrite mlookup_mupdate_other in Hua by exact Hhg. apply (In_gend s h a). apply UM. exact Hua.
Qed.

(* [comment removed for export] *)
#[using="R U HI Hux Hk Hfree"] Theorem reserved_slot_cover : forall c, In c (image s) ->
  In c (image s') \/ exists c', In c' tr_cnew /\ cell_range L c' = cell_range L c.
Proof. LiaFast.lf_pins (fun (R U HI Hux Hk Hfree : LiaFast.U) => LiaFast.u0).
  intros c Hc.
  pose proof tr_am2_facts as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est & Eml & Eai).
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  pose proof (inv_groups HI g am Hux) as G. pose proof G as (Gm & _). destruct Gm as (_ & _ & Mlen & _).
  pose proof (KS_of_Inv [] R U s HI) as KS.
  destruct (image_setm_ks s g am am2 KS HMT) as (U' & P1 & P2).
  apply (Permutation_in c P1) in Hc. apply in_app_iff in Hc as [Hu|Hc].
  { left. apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. left. exact Hu. }
  apply in_app_iff in Hc as [Hm|Hg].
  { left. apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. right. apply in_app_iff. left.
    unfold meta_slot_cells in Hm |- *. rewrite Ep, Enx, Em, Eav, Ef, Eb. exact Hm. }
  unfold group_cells in Hg. apply in_app_iff in Hg as [Hh|Hs].
  { left. apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. right. apply in_app_iff. right.
    unfold group_cells. apply in_app_iff. left. rewrite Em, Eml, Eai. exact Hh. }
  apply in_flat_map in Hs as [j [Hj Hcj]]. apply In_zseq in Hj.
  destruct (Z.eq_dec j k) as [->|Hjk].
  - unfold slot_cells in Hcj. rewrite Hfree in Hcj. rewrite app_nil_r in Hcj. apply in_app_iff in Hcj as [Hc4|Hch].
    + left. apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. right. apply in_app_iff. right.
      unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [rewrite El; apply In_zseq; lia|].
      unfold slot_cells. rewrite Est. apply in_app_iff. left. exact Hc4.
    + right. destruct (ss_hdr (nth_slot am k)) as [[h3 h16]|]; [|destruct Hch].
      destruct Hch as [<-|[<-|[]]].
      * exists (MCell (LMem (padd (slot_start am k) (-3))) 1 (VZ (fst hdr))). split; [unfold tr_cnew; left; reflexivity | reflexivity].
      * exists (MCell (LMem (padd (slot_start am k) (-2))) 2 (VZ (snd hdr))). split; [unfold tr_cnew; right; left; reflexivity | reflexivity].
  - left. apply (Permutation_in c (Permutation_sym P2)). apply in_app_iff. right. apply in_app_iff. right.
    unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists j. split; [rewrite El; apply In_zseq; lia|].
    unfold slot_cells in Hcj |- *. rewrite (Eoth j Hjk ltac:(lia) ltac:(lia)).
    assert (Estj : slot_start am2 j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
    rewrite Estj. exact Hcj.
Qed.

(* [comment removed for export] *)
#[using="R U HI Hux Hk Hfree"] Theorem reserved_slot_blocks : forall b, In b (user_blocks s) -> In b (user_blocks s').
Proof. LiaFast.lf_pins (fun (R U HI Hux Hk Hfree : LiaFast.U) => LiaFast.u0).
  intros b Hb.
  pose proof tr_am2_facts as (Em & Es & El & Eoth & Ek & Eb & Ep & Enx & Ef & Eav & Est & Eml & Eai).
  pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  assert (ND' : List.NoDup (keys s')).
  { unfold keys, set_meta. cbn [st_metas set_metas]. rewrite map_fst_mupdate_In; [exact ND|].
    apply (mlookup_In_keys (st_metas s) g (MUsed am)). exact HMT. }
  destruct (in_user_blocks_inv s b Hb) as (h & ah & j & f & Hh & Hj & Hf & Kf & ->).
  apply (used_metas_iff s h ah ND) in Hh.
  unfold user_blocks. apply in_flat_map.
  destruct (sptr_eq_dec h g) as [->|Hhg].
  - unfold MT in HMT, Hh. rewrite HMT in Hh. injection Hh as <-.
    exists (g, am2). split; [apply (used_metas_iff s' g am2 ND'); apply MT_set_same|]. cbn [snd].
    apply in_flat_map. exists j. split; [rewrite El; apply In_zseq; lia|].
    destruct (Z.eq_dec j k) as [->|Hjk]; [rewrite Hfree in Hf; discriminate|].
    rewrite (Eoth j Hjk ltac:(lia) ltac:(lia)), Hf, Kf.
    assert (Estj : slot_start am2 j = slot_start am j) by (unfold slot_start; rewrite Em, Es; reflexivity).
    rewrite Estj. left. reflexivity.
  - exists (h, ah). split; [apply (used_metas_iff s' h ah ND'); rewrite MT_set_other by exact Hhg; exact Hh|]. cbn [snd].
    apply in_flat_map. exists j. split; [apply In_zseq; lia|]. rewrite Hf, Kf. left. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="g R U HI Hux Hk Hfree"] Theorem reserved_slot_owned : forall x, layout_ok L s ->
  stv - 3 <= x < stv + stride_of am - 4 -> in_footprint L s x /\ ~ in_user_block L s x.
Proof. LiaFast.lf_pins (fun (g R U HI Hux Hk Hfree : LiaFast.U) => LiaFast.u0). intros x HL Hx. exact (free_slot_owned_R R U s L g am k x HI HL Hux Hk Hfree Hx). Qed.
End Repr.
End TR.
