(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngTake.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngOwn MngMalloc MngTakeRepr AXF_efbz AXF_efmem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem free_slot_outside_blocks : forall s L g am k b,
  WF s -> layout_ok L s -> usedX [] s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  In b (user_blocks s) -> ranges_disjoint (block_range L b) (free_slot_range L am k).
Proof.
  intros s L g am k b HW HL Hg Hk Hfr Hb.
  destruct (in_user_blocks_inv s b Hb) as (h & ah & j & f & Hh & Hj & Hf & Kf & ->).
  apply (used_metas_usedX s h ah HW) in Hh as Uh.
  pose proof (inv_groups HW h ah Uh) as (_ & _ & Gslh & _). pose proof (Gslh j Hj) as (_ & _ & T3). rewrite Hf in T3.
  destruct T3 as (_ & _ & (Nf & Of & Ff & _) & _).
  pose proof (slot_in_span [] None U0 s HW h ah j Uh Hj) as [SJ1 SJ2].
  pose proof (slot_in_span [] None U0 s HW g am k Hg Hk) as [SK1 SK2].
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW h ah Uh)) as Sh.
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hg)) as Sg.
  unfold ranges_disjoint, block_range, free_slot_range, frame_ptr. cbn [fst snd].
  rewrite (loc_padd L (slot_start ah j) (UNIT * fr_off f)).
  assert (Eloc : forall r, loc_addr L (LMem r) = ly_reg L (prid r) + poff r) by (intros [rr oo]; reflexivity).
  rewrite !Eloc. rewrite !prid_slot_start.
  destruct (Nat.eq_dec (prid (am_mem am)) (prid (am_mem ah))) as [Er|Er].
  - rewrite Er.
    assert (D : poff (slot_start am k) + stride_of am <= poff (slot_start ah j) \/
                poff (slot_start ah j) + stride_of ah <= poff (slot_start am k)).
    { destruct (sptr_eq_dec g h) as [<-|Hgh].
      - pose proof (usedX_fun _ _ _ _ _ Hg Uh) as <-. destruct (Z.eq_dec k j) as [->|Hkj]; [rewrite Hfr in Hf; discriminate|].
        exact (same_group_starts am k j Hkj Sg).
      - destruct (inv_laminar HW g am h ah Hg Uh Hgh Er) as [D | [I | I]].
        + unfold spans_disjoint in D. unfold group_extent, UNIT, IB in *. lia.
        + destruct (inside_slot_start [] None U0 s HW _ _ _ _ _ Hg Uh Hk I) as (j0 & fr0 & Hj0 & Hfj & Hkj & A & B).
          destruct (Z.eq_dec j0 j) as [->|Hji]; [rewrite Hf in Hfj; injection Hfj as <-; rewrite Kf in Hkj; discriminate|].
          destruct (same_group_starts ah j0 j Hji Sh); unfold UNIT in *; lia.
        + destruct (inside_slot_start [] None U0 s HW _ _ _ _ _ Uh Hg Hj I) as (j0 & fr0 & Hj0 & Hfj & Hkj & A & B).
          destruct (Z.eq_dec j0 k) as [->|Hji]; [rewrite Hfr in Hfj; discriminate|].
          destruct (same_group_starts am j0 k Hji Sg); unfold UNIT in *; lia. }
    unfold UNIT, IB in *. lia.
  - destruct (used_group_region [] None U0 s g am HW Hg) as (rgG & _ & _ & _ & HoG & _).
    destruct (used_group_region [] None U0 s h ah HW Uh) as (rgH & _ & _ & _ & HoH & _).
    destruct (regions_apart s L am ah g h (poff (slot_start am k) - 3) (stride_of am - 1) (poff (slot_start ah j) + UNIT * fr_off f) (fr_n f) HW HL Hg Uh Er)
      as [D|D].
    + unfold UNIT in *. lia.
    + unfold group_extent, UNIT, IB in *. lia.
    + unfold UNIT in *. lia.
    + unfold group_extent, UNIT, IB in *. lia.
    + unfold UNIT, IB in *. lia.
    + unfold UNIT, IB in *. lia.
Qed.

Theorem free_slot_owned : forall s L g am k x,
  WF s -> layout_ok L s -> usedX [] s g am -> 0 <= k <= am_last am -> ss_fr (nth_slot am k) = None ->
  loc_addr L (LMem (slot_start am k)) - 3 <= x < loc_addr L (LMem (slot_start am k)) + stride_of am - 4 ->
  in_footprint L s x /\ ~ in_user_block L s x.
Proof.
  intros s L g am k x HW HL Hg Hk Hfr Hx. split.
  - destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    pose proof (slot_in_span [] None U0 s HW g am k Hg Hk) as [SK1 SK2].
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [apply footprint_region_In; assumption|].
    cbn [fst snd]. change (loc_addr L (LMem (SP (prid (am_mem am)) 0))) with (ly_reg L (prid (am_mem am)) + 0).
    assert (Eloc : loc_addr L (LMem (slot_start am k)) = ly_reg L (prid (am_mem am)) + poff (slot_start am k)).
    { rewrite <- (prid_slot_start am k). destruct (slot_start am k). reflexivity. }
    rewrite Eloc in Hx. unfold group_extent, UNIT, IB in *. lia.
  - intros (b & Hb & Hxb). pose proof (free_slot_outside_blocks s L g am k b HW HL Hg Hk Hfr Hb) as D.
    unfold ranges_disjoint, block_range, free_slot_range in D. cbn [fst snd] in D. lia.
Qed.

Theorem image_owned : forall s L c x, WF s -> layout_ok L s -> In c (image s) ->
  loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) ->
  in_footprint L s x /\ ~ in_user_block L s x.
Proof.
  intros s L c x HW HL Hc Hx. split.
  - destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl). exists rg. split; [exact Hrg|].
    unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. lia.
  - intros (b & Hb & Hxb). pose proof (image_outside_user_blocks s L c b HW HL Hc Hb) as D.
    unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Cells.
Variables (L : layout) (g : sptr) (am : ameta) (n off0 : Z) (m2 : word -> option byte) (sz : Z).

Local Notation k := (mf_idx am).
Local Notation off := (ef_offm am n off0).
Local Notation stv := (loc_addr L (LMem (slot_start am (mf_idx am)))).
Local Notation memv := (loc_addr L (LMem (am_mem am))).
Local Notation Gv := (loc_addr L (LMem g)).

Hypothesis Esz : 16 * sz = stride_of am.
Hypothesis Rst : 17 <= stv <= 2^63 - 1.
Hypothesis Rend : stv + 16 * sz <= 2^63.
Hypothesis Roff : 0 <= off <= 255.
Hypothesis Rn : 1 <= n.
Hypothesis Fit : n + 4 + 16 * off <= 16 * sz.
Hypothesis Hk0 : 0 <= k.

Local Notation mE := (efb_mem m2 (mf_idx am) n memv sz stv (ef_offm am n off0)).

#[using="Type"] Lemma Est' : stv = memv + 16 + stride_of am * k.
Proof. LiaFast.lf_pins LiaFast.u0. unfold slot_start. rewrite loc_padd. unfold UNIT. ring. Qed.

#[using="Esz"] Lemma rsv_code_eq : forall (am' : ameta) fr, stride_of am' = stride_of am -> fr_off fr = off -> fr_n fr = n ->
  rsv_code am' fr = efb_code (efb_rsv sz n off).
Proof. LiaFast.lf_pins (fun (Esz : LiaFast.U) => LiaFast.u0).
  intros am' fr E1 E2 E3. unfold rsv_code, efb_code, efb_rsv. rewrite E1, E2, E3, <- Esz. unfold UNIT, IB.
  destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:A; [apply Z.eqb_eq in A; rewrite A; reflexivity|].
  apply Z.eqb_neq in A. destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:B.
  - apply Z.ltb_lt in B. replace (5 <=? 16 * sz - 4 - 16 * off - n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - apply Z.ltb_ge in B. replace (5 <=? 16 * sz - 4 - 16 * off - n) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

#[using="Esz"] Lemma ef_rsvm_eq : ef_rsvm (mf_am1 am) n off = efb_code (efb_rsv sz n off).
Proof. LiaFast.lf_pins (fun (Esz : LiaFast.U) => LiaFast.u0).
  unfold ef_rsvm, mf_am1. rewrite stride_set_avail. exact (rsv_code_eq am (mkFrame off n FUser) eq_refl eq_refl eq_refl).
Qed.

#[using="sz Esz"] Lemma off16_eq : (stv + 16 * off - memv - 16) / 16 = (stride_of am * k) / UNIT + off.
Proof. LiaFast.lf_pins (fun (sz Esz : LiaFast.U) => LiaFast.u0).
  rewrite Est'. rewrite <- Esz. unfold UNIT.
  replace (memv + 16 + 16 * sz * k + 16 * off - memv - 16) with ((sz * k + off) * 16) by ring.
  replace (16 * sz * k) with ((sz * k) * 16) by ring. rewrite !Z.div_mul by lia. reflexivity.
Qed.

#[using="Esz Rst Rend Roff Rn Fit"] Theorem efb_cnew :
  (forall j, (j < 4)%nat -> bview SEGS m2 (Gv + 24 + Z.of_nat j) = Some (le_byte (am_avail am - mf_first am) 4 j)) ->
  0 <= Gv + 24 -> Gv + 28 <= 2^64 -> (Gv + 28 <= stv - 3 \/ stv + 16 * sz - 4 <= Gv + 24) ->
  Forall (cell_holds L (bview SEGS mE)) (mf_cnew g am n off0).
Proof. LiaFast.lf_pins (fun (Esz Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros AV G0 G1 DJ.
  pose proof (efb_mem_out m2 k n memv sz stv off Rst Rend Roff Rn Fit) as OUT.
  unfold mf_cnew. apply Forall_app. split.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. unfold META_avail. intros j Hj.
      rewrite OUT by lia. exact (AV j Hj).
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      unfold mf_hdr, ef_hdrm. destruct (off =? 0) eqn:E0; cbn [fst snd].
      * apply Z.eqb_eq in E0. pose proof (efb_mem_p3 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P3.
        rewrite E0 in P3 at 2. replace (stv + 16 * 0 - 3) with (stv + -3 + Z.of_nat 0) in P3 by lia. rewrite P3.
        f_equal. unfold efb_code'. rewrite ef_rsvm_eq. f_equal. ring.
      * apply Z.eqb_neq in E0. destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (H3 & _ & _).
        replace (stv + -3 + Z.of_nat 0) with (stv - 3) by lia. exact H3.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. intros j Hj.
      unfold mf_hdr, ef_hdrm. destruct (off =? 0) eqn:E0; cbn [fst snd].
      * apply Z.eqb_eq in E0. pose proof (efb_mem_p2 m2 k n memv sz stv off Rst Rend Roff Rn Fit j Hj) as P2.
        replace (stv + 16 * off - 2 + Z.of_nat j) with (stv + -2 + Z.of_nat j) in P2 by lia. rewrite P2.
        f_equal. rewrite off16_eq. unfold mf_am1. rewrite stride_set_avail, E0, Z.add_0_r. reflexivity.
      * apply Z.eqb_neq in E0. destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (_ & H2 & _).
        replace (stv + -2 + Z.of_nat j) with (stv - 2 + Z.of_nat j) by lia. exact (H2 j Hj).
  - destruct (off =? 0) eqn:E0; [constructor|]. apply Z.eqb_neq in E0.
    destruct (efb_mem_hdr m2 k n memv sz stv off Rst Rend Roff Rn Fit E0) as (_ & _ & H4).
    pose proof (efb_mem_p3 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P3.
    pose proof (efb_mem_p2 m2 k n memv sz stv off Rst Rend Roff Rn Fit) as P2.
    pose proof (am2_facts am n off0) as (_ & Es2 & _).
    constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (stv + UNIT * off + -4 + Z.of_nat 0) with (stv + 16 * off - 4) by (unfold UNIT; lia). exact H4.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj. assert (j = 0%nat) as -> by lia.
      replace (stv + UNIT * off + -3 + Z.of_nat 0) with (stv + 16 * off - 3) by (unfold UNIT; lia). rewrite P3.
      f_equal. unfold hdr_byte3. replace (fr_kind (mf_fr am n off0)) with FUser by reflexivity. cbv iota.
      rewrite (rsv_code_eq (mf_am2 am n off0) (mf_fr am n off0) Es2 eq_refl eq_refl). reflexivity.
    + unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num]. rewrite !loc_padd. intros j Hj.
      replace (stv + UNIT * off + -2 + Z.of_nat j) with (stv + 16 * off - 2 + Z.of_nat j) by (unfold UNIT; lia). rewrite (P2 j Hj).
      f_equal. unfold hdr_off16. rewrite Es2. unfold mf_fr. cbn [fr_off]. rewrite off16_eq. reflexivity.
Qed.

#[using="Esz Rst Rend Roff Rn Fit"] Theorem efb_mnew : Forall (cell_holds L (bview SEGS mE)) (mf_mnew am n off0).
Proof. LiaFast.lf_pins (fun (Esz Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  pose proof (am2_facts am n off0) as (_ & Es2 & _ & _ & _ & _ & _ & _ & _ & _ & Est2).
  assert (Ee : loc_addr L (LMem (slot_end (mf_am2 am n off0) k)) = stv + 16 * sz - 4).
  { unfold slot_end. rewrite loc_padd, Est2, Es2, <- Esz. unfold IB. ring. }
  assert (Er : frame_rsv (mf_am2 am n off0) (mf_fr am n off0) = efb_rsv sz n off).
  { unfold frame_rsv, efb_rsv, mf_fr. cbn [fr_off fr_n]. rewrite Es2, <- Esz. unfold UNIT, IB. ring. }
  unfold mf_mnew. cbv zeta. rewrite Er. apply Forall_app. split.
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
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EFRAW.
Variables (m : word -> option byte) (idx n mem sz st off : Z).
Hypothesis Rst : 17 <= st <= 2^63 - 1.
Hypothesis Rend : st + 16 * sz <= 2^63.
Hypothesis Roff : 0 <= off <= 255.
Hypothesis Rn : 1 <= n.
Hypothesis Fit : n + 4 + 16 * off <= 16 * sz.

Ltac wout' := rewrite MngWb.wbytes_out by (unfold word_to_le_bytes; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat]; rewrite ?u_wa_small by lia; lia).

#[using="Rst Rend Roff Rn Fit"] Lemma efb_mem_out_raw : forall x, 0 <= x < 2^64 -> ~ (st - 3 <= x < st + 16 * sz - 4) ->
  efb_mem m idx n mem sz st off (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Rst Rend Roff Rn Fit : LiaFast.U) => LiaFast.u0).
  intros x Hx Hno. unfold efb_mem, efb_rsv, le. cbv zeta.
  wout'.
  assert (TAIL : forall mm, mm (wa x) = m (wa x) ->
            wbytes (wbytes mm (wa (st + 16 * off - 3)) (word_to_le_bytes 1 (wa idx)))
                   (wa (st + 16 * off - 2)) (word_to_le_bytes 2 (wa ((st + 16 * off - mem - 16) / 16))) (wa x) = m (wa x)).
  { intros mm Hmm. wout'. wout'. exact Hmm. }
  assert (HEAD : (if off =? 0 then m else wbytes (wbytes (wbytes m (wa (st - 3)) (word_to_le_bytes 1 (wa 224))) (wa (st - 2)) (word_to_le_bytes 2 (wa off)))
                                (wa (st + 16 * off - 4)) (word_to_le_bytes 1 (wa 0))) (wa x) = m (wa x)).
  { destruct (off =? 0) eqn:Eo; [reflexivity|]. apply Z.eqb_neq in Eo. wout'. wout'. wout'. reflexivity. }
  destruct (16 * sz - 4 - 16 * off - n =? 0) eqn:E0.
  - apply TAIL. exact HEAD.
  - apply Z.eqb_neq in E0. destruct (16 * sz - 4 - 16 * off - n <? 5) eqn:E5.
    + wout'. apply TAIL. exact HEAD.
    + apply Z.ltb_ge in E5. wout'. wout'. wout'. apply TAIL. exact HEAD.
Qed.
End EFRAW.
