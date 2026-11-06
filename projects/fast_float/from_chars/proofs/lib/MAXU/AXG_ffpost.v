(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngImage MngHeap MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXF_ff3.
Import AX2S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition fast_slot (am : ameta) (i : Z) (fr : frame) : slotst :=
  if fr_off fr =? 0 then mkSlot (Some (255, 0)) None else mkSlot (ss_hdr (nth_slot am i)) None.

Definition fast_meta (am : ameta) (i : Z) (fr : frame) : ameta :=
  am_set_freed (am_freed am + bit i) (upd_slot am i (fast_slot am i fr)).

Definition s_fast (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : astate :=
  set_meta s g (MUsed (fast_meta am i fr)).

Lemma mupdate_twice : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn [mupdate].
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma free_fast_itree : forall s g am i fr,
  WF s -> In (g, am, i, fr) (frames s) ->
  am_freed am <> 0 -> Z.lor (am_freed am) (am_avail am) + bit i <> ones (am_last am) ->
  free (Some (frame_ptr am i fr)) s = IRet (tt, s_fast s g am i fr).
Proof.
  intros s g am i fr HW HF Hf0 Hnall.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hasrt & Hff).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  assert (Mg : mlookup (st_metas s) g = Some (MUsed am)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu).
  unfold free, find_frame, getm, release_slot, setm, modify, massert, bind, ret, get.
  cbn [ibind fst snd]. rewrite Hff. cbn [ibind fst snd].
  rewrite Mg. cbn [ibind fst snd].
  unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd]. rewrite Hfri.
  assert (Hm : Z.land (Z.lor (am_freed am) (am_avail am)) (bit i) = 0).
  { unfold allocated in *. pose proof (inv_groups HW g am (proj1 (used_metas_usedX s g am HW) Hu)) as (_ & _ & Gsl & _).
    pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (Hal & _).
    unfold allocated in Hal. apply negb_true_iff in Hal.
    apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0. unfold bit.
    destruct (Z.eq_dec j i) as [->|Hne].
    - rewrite Z.lor_comm, Hal. reflexivity.
    - rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
  rewrite Hm. cbn [Z.eqb ibind fst snd].
  replace (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am))) with true
    by (symmetry; apply andb_true_intro; split; apply negb_true_iff, Z.eqb_neq; assumption).
  unfold getm, get, bind, ret, setm, modify. cbn [ibind fst snd set_metas st_metas].
  rewrite mlookup_mupdate_same. cbn [ibind fst snd set_metas st_metas].
  rewrite mupdate_twice. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_vaddi : forall (w : word) k, 0 <= bv_unsigned w + k < 2^64 -> bv_unsigned (v_addi w k) = bv_unsigned w + k.
Proof. intros w k H. unfold v_addi. apply u_small. exact H. Qed.

Section Mem.
Variable segs : list Segment.
Variables (m : word -> option byte) (regs : bvmap 5 word) (p G fnew : Z).
Hypothesis Hsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47.
Hypothesis Hp : 3 <= p <= 2^63.
Hypothesis HG : 0 <= G + 28 <= 2^63.
Hypothesis HpG : p <= G + 28 \/ G + 32 <= p - 3.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_vaddi, ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.

#[using="Hsp Hp HG"] Lemma ff3_mem_out : forall x, 0 <= x < 2^64 ->
  ~ (bv_unsigned (getr regs 2) - 40 <= x < bv_unsigned (getr regs 2)) -> ~ (p - 3 <= x < p) -> ~ (G + 28 <= x < G + 32) ->
  ff3_mem m regs p G fnew (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp Hp HG : LiaFast.U) => LiaFast.u0).
  intros x Hx H1 H2 H3. unfold ff3_mem. do 8 peel. reflexivity.
Qed.

#[using="Hp HG HpG"] Lemma ff3_mem_p3 : ff3_mem m regs p G fnew (wa (p - 3)) = Some (Z_to_bv 8 255).
Proof. LiaFast.lf_pins (fun (Hp HG HpG : LiaFast.U) => LiaFast.u0).
  unfold ff3_mem. do 2 peel. rewrite wbytes_at_wa0 by (cbn; lia). reflexivity.
Qed.

#[using="Hp HG HpG"] Lemma ff3_mem_p2 : forall k, (k < 2)%nat -> ff3_mem m regs p G fnew (wa (p - 2 + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hp HG HpG : LiaFast.U) => LiaFast.u0).
  intros k Hk. unfold ff3_mem. peel. rewrite wbytes_at_wa by (cbn; lia). destruct k as [|[|k]]; [reflexivity | reflexivity | lia].
Qed.

#[using="HG"] Lemma ff3_mem_G28 : forall k, (k < 4)%nat -> ff3_mem m regs p G fnew (wa (G + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa fnew)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0).
  intros k Hk. unfold ff3_mem. apply wbytes_at_wa; cbn; lia.
Qed.
End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_cells : forall L (l : list mcell), pairwise ranges_disjoint (map (cell_range L) l) ->
  (forall c, In c l -> (1 <= mc_w c)%nat) -> List.NoDup l.
Proof.
  intros L l. induction l as [|c t IH]; intros HP HW; [constructor|]. cbn [map pairwise] in HP. destruct HP as [H1 H2].
  constructor.
  - intros Hin. pose proof (H1 _ (in_map (cell_range L) _ _ Hin)) as D. unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D.
    pose proof (HW c (or_introl eq_refl)). lia.
  - apply IH; [exact H2|]. intros c' Hc'. apply HW. right. exact Hc'.
Qed.

Lemma nodup_image : forall L s, WF s -> layout_ok L s -> List.NoDup (image s).
Proof. intros L s HW HL. apply (nodup_cells L); [apply image_cells_disjoint; assumption | apply image_cell_width]. Qed.

Lemma nodup_app_disj {A} (l1 l2 : list A) x : List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a t IH]; intros ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|a' t' Hn Ht]; subst.
  destruct H1 as [<-|H1].
  - apply Hn. apply in_app_iff. right. exact H2.
  - exact (IH Ht H1 H2).
Qed.

Lemma cell_neq_off : forall q q' w w' v v', poff q <> poff q' -> MCell (LMem q) w v <> MCell (LMem q') w' v'.
Proof. intros q q' w w' v v' H E. injection E as E1 _ _. apply H. rewrite E1. reflexivity. Qed.

(* [comment removed for export] *)
Lemma slot_cells_span : forall am j c, 16 <= stride_of am ->
  (forall fr, ss_fr (nth_slot am j) = Some fr -> 0 <= fr_off fr /\ 0 <= fr_n fr /\ UNIT * fr_off fr + fr_n fr <= stride_of am - IB) ->
  In c (slot_cells am j) ->
  exists q, mc_loc c = LMem q /\ prid q = prid (slot_start am j) /\
    poff (slot_start am j) - 4 <= poff q <= poff (slot_start am j) + stride_of am - 6.
Proof.
  intros am j c Hs Hfit Hc. unfold slot_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct Hc as [<-|[]]. exists (padd (slot_start am j) (-4)). rewrite prid_padd, poff_padd. repeat split; lia.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (ss_hdr (nth_slot am j)) as [[h3 h16]|]; [|destruct Hc].
      destruct Hc as [<-|[<-|[]]]; [exists (padd (slot_start am j) (-3)) | exists (padd (slot_start am j) (-2))];
        rewrite prid_padd, poff_padd; repeat split; lia.
    + destruct (ss_fr (nth_slot am j)) as [fr|] eqn:Ef; [|destruct Hc].
      destruct (Hfit fr eq_refl) as (H1 & H2 & H3). unfold UNIT, IB in H3.
      destruct (fr_off fr =? 0); [destruct Hc|].
      destruct Hc as [<-|[<-|[<-|[]]]];
        [exists (padd (padd (slot_start am j) (UNIT * fr_off fr)) (-4)) | exists (padd (padd (slot_start am j) (UNIT * fr_off fr)) (-3))
        | exists (padd (padd (slot_start am j) (UNIT * fr_off fr)) (-2))];
        rewrite !prid_padd, !poff_padd; unfold UNIT; repeat split; lia.
Qed.

Section Post.
Variable segs : list Segment.

#[using="Type"] Theorem free_fast_repr : forall L s (regs : bvmap 5 word) m g am i fr,
  WF s -> repr L s (bview segs m) -> In (g, am, i, fr) (frames s) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  repr L (s_fast s g am i fr)
    (bview segs (ff3_mem m regs (loc_addr L (LMem (frame_ptr am i fr))) (loc_addr L (LMem g)) (am_freed am + 2 ^ i))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m g am i fr HW HR HF Rsp HFP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & _ & Hland & Hasrt & Hff).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  destruct HR as (HL & HC & HFM).
  set (p := frame_ptr am i fr) in *.
  set (pa := loc_addr L (LMem p)). set (G := loc_addr L (LMem g)).
  (* [comment removed for export] *)
  assert (FP : forall c, In c (image s) -> 1 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= bv_unsigned (getr regs 2) - 1024).
  { intros c Hc. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
    pose proof (proj2 (proj2 (proj2 HL)) rg Hrg) as R. pose proof (HFP rg Hrg) as S.
    unfold range_incl, cell_range, crange in *. cbn [fst snd] in *. lia. }
  pose proof (FP _ Ch3) as F3. pose proof (FP _ Ch16) as F16. pose proof (FP _ Cfr) as FF.
  cbn [mc_loc mc_w] in F3, F16, FF. rewrite !loc_padd in F3, F16, FF. fold p in F3, F16. fold pa G in F3, F16, FF. unfold META_freed in FF.
  assert (D3F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))))
                                (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch3 | exact Cfr | intro E; injection E; intros; discriminate]. }
  assert (D16F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))))
                                 (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch16 | exact Cfr | intro E; injection E; intros; discriminate]. }
  unfold ranges_disjoint, cell_range in D3F, D16F. cbn [mc_loc mc_w fst snd] in D3F, D16F. rewrite !loc_padd in D3F, D16F.
  fold p in D3F, D16F. fold pa G in D3F, D16F. unfold META_freed in D3F, D16F.
  assert (HpG : pa <= G + 28 \/ G + 32 <= pa - 3) by (clear - D3F D16F; lia).
  set (m' := ff3_mem m regs pa G (am_freed am + 2 ^ i)).
  assert (BV : forall x, ~ (bv_unsigned (getr regs 2) - 40 <= x < bv_unsigned (getr regs 2)) -> ~ (pa - 3 <= x < pa) ->
                         ~ (G + 28 <= x < G + 32) -> bview segs m' x = bview segs m x).
  { intros x H1 H2 H3. destruct (Z_lt_le_dec x 0) as [Hn|Hn]; [unfold bview; replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia); reflexivity|].
    destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx]; [|unfold bview; replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia); reflexivity].
    apply bview_ext. unfold m'. apply (ff3_mem_out m regs pa G _ Rsp); [lia | lia | lia | exact H1 | exact H2 | exact H3]. }
  assert (Hst : loc_addr L (LMem (slot_start am i)) = pa - 16 * fr_off fr).
  { unfold pa, p, frame_ptr. rewrite loc_padd. unfold UNIT. ring. }
  assert (WR3 : bview segs m' (pa - 3) = Some 255).
  { rewrite (bview_some_byte segs m' (pa - 3) (Z_to_bv 8 255) ltac:(lia)); [reflexivity|]. unfold m'. apply ff3_mem_p3; first [exact HpG | lia]. }
  assert (WR2 : forall k, (k < 2)%nat -> bview segs m' (pa - 2 + Z.of_nat k) = Some 0).
  { intros k Hk. rewrite (bview_some_byte segs m' (pa - 2 + Z.of_nat k) (Z_to_bv 8 0) ltac:(lia)); [reflexivity|]. unfold m'. apply ff3_mem_p2; first [exact HpG | exact Hk | lia]. }
  assert (WRF : forall k, (k < 4)%nat -> bview segs m' (G + 28 + Z.of_nat k) = Some (le_byte (am_freed am + bit i) 4 k)).
  { intros k Hk. rewrite (bview_some_byte segs m' (G + 28 + Z.of_nat k) (nth k (word_to_le_bytes 4 (wa (am_freed am + 2 ^ i))) (Z_to_bv 8 0)) ltac:(lia)).
    - f_equal. rewrite le_byte_Z_to_le_bytes by lia. unfold bit. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      unfold le_byte. rewrite Z.mod_mod by lia. reflexivity.
    - unfold m'. apply ff3_mem_G28; first [exact Hk | lia]. }
  apply (repr_update L s (s_fast s g am i fr) (bview segs m) (bview segs m')
           [MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr)); MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr));
            MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))]
           (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am + bit i))
            :: (if fr_off fr =? 0 then [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ 255);
                                       MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ 0)] else []))
           HW (conj HL (conj HC HFM))).
  - exact HL.
  - change (footprint (s_fast s g am i fr)) with (footprint s). apply Forall_forall. intros rg Hrg x Hx.
    pose proof (proj1 (Forall_forall _ _) HFM rg Hrg x Hx) as Hm. pose proof (HFP rg Hrg) as Hb.
    destruct (Z_lt_le_dec x (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec x pa) as [A2|A2]].
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
    + destruct (Z.eq_dec x (pa - 3)) as [->|Hne]; [rewrite WR3; discriminate|].
      replace x with (pa - 2 + Z.of_nat (Z.to_nat (x - (pa - 2)))) by lia. rewrite WR2 by lia. discriminate.
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
  - intros c [<-|[<-|[<-|[]]]]; assumption.
  - intros c Hc.
    assert (Mg : MT s g = Some (MUsed am)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu).
    destruct (image_setm s g am (fast_meta am i fr) HW Mg) as (U & P1 & P2).
    pose proof (Permutation_NoDup P1 (nodup_image L s HW HL)) as ND.
    apply (Permutation_in c P2) in Hc.
    apply (used_metas_usedX s g am HW) in Hu as Hux.
    pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & _).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hux)) as Sp.
    pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
    destruct FOK as (Fn & Foff & Ffit & _).
    assert (Epoff : poff p = poff (slot_start am i) + 16 * fr_off fr) by (unfold p, frame_ptr; rewrite poff_padd; reflexivity).
    assert (Eprid : prid p = prid (slot_start am i)) by (unfold p, frame_ptr; apply prid_padd).
    assert (InS : forall c0, In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am) -> In c0 (image s)).
    { intros c0 H0. apply (Permutation_in c0 (Permutation_sym P1)). apply in_app_iff. right. exact H0. }
    apply in_app_iff in Hc as [HU|Hc].
    + left. split; [apply (Permutation_in c (Permutation_sym P1)); apply in_app_iff; left; exact HU|].
      intros HCo. apply (nodup_app_disj U _ c ND HU).
      assert (HGCi : forall c0, In c0 (slot_cells am i) -> In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am)).
      { intros c0 H0. apply in_app_iff. right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
        exists i. split; [apply In_zseq; lia | exact H0]. }
      destruct HCo as [<-|[<-|[<-|[]]]].
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-3)) with (padd (slot_start am i) (-3)).
           ++ left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. left. reflexivity.
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-2)) with (padd (slot_start am i) (-2)).
           ++ right. left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. right. left. reflexivity.
      * apply in_app_iff. left. unfold meta_slot_cells. right. right. right. right. left. reflexivity.
    + apply in_app_iff in Hc as [HMS|HGC].
      * unfold meta_slot_cells in HMS. cbn [fast_meta am_set_freed upd_slot am_set_slots am_prev am_next am_mem am_avail am_freed] in HMS.
        assert (EB : meta_bits (fast_meta am i fr) = meta_bits am) by reflexivity.
        assert (MSi : forall c0, In c0 (meta_slot_cells g (Some (MUsed am))) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. left. exact H0. }
        destruct HMS as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
        -- left. split; [apply MSi; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; try (inversion E; fail).
           revert E. apply cell_neq_off. rewrite !poff_padd. unfold META_avail, META_freed. lia.
        -- right. left. reflexivity.
        -- left. rewrite EB. split; [apply MSi; right; right; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
      * pose proof (NoDup_app_remove_l _ _ ND) as ND2.
        assert (C3MS : In (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) (meta_slot_cells g (Some (MUsed am)))).
        { unfold meta_slot_cells. right. right. right. right. left. reflexivity. }
        assert (NC3 : forall c0, In c0 (group_cells g am) -> c0 <> MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))).
        { intros c0 H0 E. subst c0. exact (nodup_app_disj _ _ _ ND2 C3MS H0). }
        assert (GCi : forall c0, In c0 (group_cells g am) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. right. exact H0. }
        destruct Gm as (Mlast & _ & Mlen & _).
        assert (Hsl : forall j, 0 <= j -> nth_slot (fast_meta am i fr) j = if j =? i then fast_slot am i fr else nth_slot am j).
        { intros j Hj. unfold fast_meta. change (nth_slot (am_set_freed (am_freed am + bit i) (upd_slot am i (fast_slot am i fr))) j)
            with (nth_slot (upd_slot am i (fast_slot am i fr)) j). apply nth_slot_upd_slot; [lia | exact Hj | rewrite Mlen; lia]. }
        unfold group_cells in HGC. apply in_app_iff in HGC as [HH|HSC].
        -- (* [comment removed for export] *)
           change (am_mem (fast_meta am i fr)) with (am_mem am) in HH. change (am_maplen (fast_meta am i fr)) with (am_maplen am) in HH.
           change (am_aidx (fast_meta am i fr)) with (am_aidx am) in HH.
           left. split; [apply GCi; unfold group_cells; apply in_app_iff; left; exact HH|].
           assert (HG0 : In c (group_cells g am)) by (unfold group_cells; apply in_app_iff; left; exact HH).
           destruct (am_maplen am =? 0); cbn in HH; destruct HH as [<-|[<-|[]]]; intros [E|[E|[E|[]]]];
             first [inversion E; fail | exact (NC3 _ HG0 E) | exact (NC3 _ HG0 (eq_sym E))].
        -- apply in_flat_map in HSC as (j & Hj & Hcj). apply In_zseq in Hj.
           change (am_last (fast_meta am i fr)) with (am_last am) in Hj.
           assert (GCj : forall j0 c0, 0 <= j0 <= am_last am -> In c0 (slot_cells am j0) -> In c0 (group_cells g am)).
           { intros j0 c0 Hj0 H0. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists j0. split; [apply In_zseq; lia | exact H0]. }
           destruct (Z.eq_dec j i) as [->|Hne].
           ++ assert (Es : slot_cells (fast_meta am i fr) i =
                            MCell (LMem (padd (slot_start am i) (-4))) 1 (VZ 0)
                            :: match ss_hdr (fast_slot am i fr) with
                               | Some (h3, h16) => [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ h3); MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ h16)]
                               | None => [] end).
              { unfold slot_cells. rewrite (Hsl i ltac:(lia)), Z.eqb_refl. unfold fast_slot.
                destruct (fr_off fr =? 0); cbn [ss_hdr ss_fr app]; rewrite ?app_nil_r; reflexivity. }
              rewrite Es in Hcj. destruct Hcj as [<-|Hcj].
              ** left. split; [apply GCi, (GCj i); [lia | left; reflexivity]|].
                 intros [E|[E|[E|[]]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff; clear - Foff; unfold UNIT in *; lia.
              ** unfold fast_slot in Hcj. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
                 --- cbn [ss_hdr] in Hcj. right. replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0).
                     destruct Hcj as [<-|[<-|[]]]; [right; left; reflexivity | right; right; left; reflexivity].
                 --- cbn [ss_hdr] in Hcj. left.
                     assert (Hin : In c (slot_cells am i)).
                     { unfold slot_cells. apply in_app_iff. right. apply in_app_iff. left. exact Hcj. }
                     split; [apply GCi, (GCj i); [lia | exact Hin]|].
                     destruct (ss_hdr (nth_slot am i)) as [[h3' h16']|]; [|destruct Hcj].
                     intros [E|[E|[E|[]]]]; try (inversion E; fail);
                       destruct Hcj as [<-|[<-|[]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff;
                       clear - Foff E0; unfold UNIT in *; lia.
           ++ assert (Es : slot_cells (fast_meta am i fr) j = slot_cells am j).
              { unfold slot_cells. rewrite (Hsl j ltac:(lia)). replace (j =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
              rewrite Es in Hcj. left. split; [apply GCi, (GCj j); [lia | exact Hcj]|].
              pose proof (Gsl j ltac:(lia)) as (_ & _ & T3).
              assert (Hfit : forall fr0, ss_fr (nth_slot am j) = Some fr0 -> 0 <= fr_off fr0 /\ 0 <= fr_n fr0 /\ UNIT * fr_off fr0 + fr_n fr0 <= stride_of am - IB).
              { intros fr0 E0. rewrite E0 in T3. destruct T3 as (_ & _ & (N0 & O0 & F0 & _) & _). lia. }
              destruct (slot_cells_span am j c Sp Hfit Hcj) as (q & Eq & Hq1 & Hq2).
              pose proof (same_group_starts am i j ltac:(lia) Sp) as SGS.
              intros [E|[E|[E|[]]]].
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** exact (NC3 c (GCj j c ltac:(lia) Hcj) (eq_sym E)).
  - constructor.
    + intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. fold G. unfold META_freed. rewrite WRF by exact Hk. reflexivity.
    + destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0]; [|constructor].
      constructor; [|constructor; [|constructor]].
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0. destruct k as [|k]; [|cbn in Hk; lia].
        replace (pa - 16 * 0 + -3 + Z.of_nat 0) with (pa - 3) by ring. rewrite WR3. reflexivity.
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0.
        replace (pa - 16 * 0 + -2 + Z.of_nat k) with (pa - 2 + Z.of_nat k) by ring. rewrite WR2 by exact Hk.
        destruct k as [|[|k]]; [reflexivity | reflexivity | cbn in Hk; lia].
  - intros a Ha.
    destruct (Z_lt_le_dec a (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec a pa) as [A2|A2]].
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (bv_unsigned (getr regs 2) - 40)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (bv_unsigned (getr regs 2) - 40)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
    + left. destruct (Z.eq_dec a (pa - 3)) as [->|Hne].
      * exists (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))). split; [left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
      * exists (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))). split; [right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (bv_unsigned (getr regs 2) - 40)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (bv_unsigned (getr regs 2) - 40)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
Qed.

#[using="Type"] Theorem freed_slot_repr : forall L s m m' g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> In (g, am, i, fr) (frames s) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     ~ (loc_addr L (LMem g) + 28 <= x < loc_addr L (LMem g) + 32) -> bview segs m' x = bview segs m x) ->
  bview segs m' (loc_addr L (LMem (frame_ptr am i fr)) - 3) = Some 255 ->
  (forall k, (k < 2)%nat -> bview segs m' (loc_addr L (LMem (frame_ptr am i fr)) - 2 + Z.of_nat k) = Some 0) ->
  (forall k, (k < 4)%nat -> bview segs m' (loc_addr L (LMem g) + 28 + Z.of_nat k) = Some (le_byte (am_freed am + bit i) 4 k)) ->
  repr L (s_fast s g am i fr) (bview segs m').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr spz HW HR HF HFP BV WR3 WR2 WRF.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & _ & Hland & Hasrt & Hff).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  destruct HR as (HL & HC & HFM).
  set (p := frame_ptr am i fr) in *.
  set (pa := loc_addr L (LMem p)) in *. set (G := loc_addr L (LMem g)) in *.
  (* [comment removed for export] *)
  assert (FP : forall c, In c (image s) -> 1 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= spz - 1024).
  { intros c Hc. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
    pose proof (proj2 (proj2 (proj2 HL)) rg Hrg) as R. pose proof (HFP rg Hrg) as S.
    unfold range_incl, cell_range, crange in *. cbn [fst snd] in *. lia. }
  pose proof (FP _ Ch3) as F3. pose proof (FP _ Ch16) as F16. pose proof (FP _ Cfr) as FF.
  cbn [mc_loc mc_w] in F3, F16, FF. rewrite !loc_padd in F3, F16, FF. fold p in F3, F16. fold pa G in F3, F16, FF. unfold META_freed in FF.
  assert (D3F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))))
                                (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch3 | exact Cfr | intro E; injection E; intros; discriminate]. }
  assert (D16F : ranges_disjoint (cell_range L (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))))
                                 (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch16 | exact Cfr | intro E; injection E; intros; discriminate]. }
  unfold ranges_disjoint, cell_range in D3F, D16F. cbn [mc_loc mc_w fst snd] in D3F, D16F. rewrite !loc_padd in D3F, D16F.
  fold p in D3F, D16F. fold pa G in D3F, D16F. unfold META_freed in D3F, D16F.
  assert (Hst : loc_addr L (LMem (slot_start am i)) = pa - 16 * fr_off fr).
  { unfold pa, p, frame_ptr. rewrite loc_padd. unfold UNIT. ring. }
  apply (repr_update L s (s_fast s g am i fr) (bview segs m) (bview segs m')
           [MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr)); MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr));
            MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))]
           (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am + bit i))
            :: (if fr_off fr =? 0 then [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ 255);
                                       MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ 0)] else []))
           HW (conj HL (conj HC HFM))).
  - exact HL.
  - change (footprint (s_fast s g am i fr)) with (footprint s). apply Forall_forall. intros rg Hrg x Hx.
    pose proof (proj1 (Forall_forall _ _) HFM rg Hrg x Hx) as Hm. pose proof (HFP rg Hrg) as Hb.
    destruct (Z_lt_le_dec x (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec x pa) as [A2|A2]].
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
    + destruct (Z.eq_dec x (pa - 3)) as [->|Hne]; [rewrite WR3; discriminate|].
      replace x with (pa - 2 + Z.of_nat (Z.to_nat (x - (pa - 2)))) by lia. rewrite WR2 by lia. discriminate.
    + destruct (Z_lt_le_dec x (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec x (G + 32)) as [B2|B2]].
      * rewrite BV by lia. exact Hm.
      * replace x with (G + 28 + Z.of_nat (Z.to_nat (x - (G + 28)))) by lia. rewrite WRF by lia. discriminate.
      * rewrite BV by lia. exact Hm.
  - intros c [<-|[<-|[<-|[]]]]; assumption.
  - intros c Hc.
    assert (Mg : MT s g = Some (MUsed am)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu).
    destruct (image_setm s g am (fast_meta am i fr) HW Mg) as (U & P1 & P2).
    pose proof (Permutation_NoDup P1 (nodup_image L s HW HL)) as ND.
    apply (Permutation_in c P2) in Hc.
    apply (used_metas_usedX s g am HW) in Hu as Hux.
    pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & _).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hux)) as Sp.
    pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
    destruct FOK as (Fn & Foff & Ffit & _).
    assert (Epoff : poff p = poff (slot_start am i) + 16 * fr_off fr) by (unfold p, frame_ptr; rewrite poff_padd; reflexivity).
    assert (Eprid : prid p = prid (slot_start am i)) by (unfold p, frame_ptr; apply prid_padd).
    assert (InS : forall c0, In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am) -> In c0 (image s)).
    { intros c0 H0. apply (Permutation_in c0 (Permutation_sym P1)). apply in_app_iff. right. exact H0. }
    apply in_app_iff in Hc as [HU|Hc].
    + left. split; [apply (Permutation_in c (Permutation_sym P1)); apply in_app_iff; left; exact HU|].
      intros HCo. apply (nodup_app_disj U _ c ND HU).
      assert (HGCi : forall c0, In c0 (slot_cells am i) -> In c0 (meta_slot_cells g (Some (MUsed am)) ++ group_cells g am)).
      { intros c0 H0. apply in_app_iff. right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
        exists i. split; [apply In_zseq; lia | exact H0]. }
      destruct HCo as [<-|[<-|[<-|[]]]].
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-3)) with (padd (slot_start am i) (-3)).
           ++ left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. left. reflexivity.
      * apply HGCi. unfold slot_cells. rewrite Hfri. apply in_app_iff. right. apply in_app_iff.
        destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
        -- left. rewrite (Hhdr E0). replace (padd p (-2)) with (padd (slot_start am i) (-2)).
           ++ right. left. reflexivity.
           ++ unfold p, frame_ptr. rewrite E0. destruct (slot_start am i). cbn. f_equal. lia.
        -- right. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). right. right. left. reflexivity.
      * apply in_app_iff. left. unfold meta_slot_cells. right. right. right. right. left. reflexivity.
    + apply in_app_iff in Hc as [HMS|HGC].
      * unfold meta_slot_cells in HMS. cbn [fast_meta am_set_freed upd_slot am_set_slots am_prev am_next am_mem am_avail am_freed] in HMS.
        assert (EB : meta_bits (fast_meta am i fr) = meta_bits am) by reflexivity.
        assert (MSi : forall c0, In c0 (meta_slot_cells g (Some (MUsed am))) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. left. exact H0. }
        destruct HMS as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
        -- left. split; [apply MSi; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
        -- left. split; [apply MSi; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; try (inversion E; fail).
           revert E. apply cell_neq_off. rewrite !poff_padd. unfold META_avail, META_freed. lia.
        -- right. left. reflexivity.
        -- left. rewrite EB. split; [apply MSi; right; right; right; right; right; left; reflexivity|]. intros [E|[E|[E|[]]]]; inversion E.
      * pose proof (NoDup_app_remove_l _ _ ND) as ND2.
        assert (C3MS : In (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) (meta_slot_cells g (Some (MUsed am)))).
        { unfold meta_slot_cells. right. right. right. right. left. reflexivity. }
        assert (NC3 : forall c0, In c0 (group_cells g am) -> c0 <> MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))).
        { intros c0 H0 E. subst c0. exact (nodup_app_disj _ _ _ ND2 C3MS H0). }
        assert (GCi : forall c0, In c0 (group_cells g am) -> In c0 (image s)).
        { intros c0 H0. apply InS. apply in_app_iff. right. exact H0. }
        destruct Gm as (Mlast & _ & Mlen & _).
        assert (Hsl : forall j, 0 <= j -> nth_slot (fast_meta am i fr) j = if j =? i then fast_slot am i fr else nth_slot am j).
        { intros j Hj. unfold fast_meta. change (nth_slot (am_set_freed (am_freed am + bit i) (upd_slot am i (fast_slot am i fr))) j)
            with (nth_slot (upd_slot am i (fast_slot am i fr)) j). apply nth_slot_upd_slot; [lia | exact Hj | rewrite Mlen; lia]. }
        unfold group_cells in HGC. apply in_app_iff in HGC as [HH|HSC].
        -- (* [comment removed for export] *)
           change (am_mem (fast_meta am i fr)) with (am_mem am) in HH. change (am_maplen (fast_meta am i fr)) with (am_maplen am) in HH.
           change (am_aidx (fast_meta am i fr)) with (am_aidx am) in HH.
           left. split; [apply GCi; unfold group_cells; apply in_app_iff; left; exact HH|].
           assert (HG0 : In c (group_cells g am)) by (unfold group_cells; apply in_app_iff; left; exact HH).
           destruct (am_maplen am =? 0); cbn in HH; destruct HH as [<-|[<-|[]]]; intros [E|[E|[E|[]]]];
             first [inversion E; fail | exact (NC3 _ HG0 E) | exact (NC3 _ HG0 (eq_sym E))].
        -- apply in_flat_map in HSC as (j & Hj & Hcj). apply In_zseq in Hj.
           change (am_last (fast_meta am i fr)) with (am_last am) in Hj.
           assert (GCj : forall j0 c0, 0 <= j0 <= am_last am -> In c0 (slot_cells am j0) -> In c0 (group_cells g am)).
           { intros j0 c0 Hj0 H0. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists j0. split; [apply In_zseq; lia | exact H0]. }
           destruct (Z.eq_dec j i) as [->|Hne].
           ++ assert (Es : slot_cells (fast_meta am i fr) i =
                            MCell (LMem (padd (slot_start am i) (-4))) 1 (VZ 0)
                            :: match ss_hdr (fast_slot am i fr) with
                               | Some (h3, h16) => [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ h3); MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ h16)]
                               | None => [] end).
              { unfold slot_cells. rewrite (Hsl i ltac:(lia)), Z.eqb_refl. unfold fast_slot.
                destruct (fr_off fr =? 0); cbn [ss_hdr ss_fr app]; rewrite ?app_nil_r; reflexivity. }
              rewrite Es in Hcj. destruct Hcj as [<-|Hcj].
              ** left. split; [apply GCi, (GCj i); [lia | left; reflexivity]|].
                 intros [E|[E|[E|[]]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff; clear - Foff; unfold UNIT in *; lia.
              ** unfold fast_slot in Hcj. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
                 --- cbn [ss_hdr] in Hcj. right. replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0).
                     destruct Hcj as [<-|[<-|[]]]; [right; left; reflexivity | right; right; left; reflexivity].
                 --- cbn [ss_hdr] in Hcj. left.
                     assert (Hin : In c (slot_cells am i)).
                     { unfold slot_cells. apply in_app_iff. right. apply in_app_iff. left. exact Hcj. }
                     split; [apply GCi, (GCj i); [lia | exact Hin]|].
                     destruct (ss_hdr (nth_slot am i)) as [[h3' h16']|]; [|destruct Hcj].
                     intros [E|[E|[E|[]]]]; try (inversion E; fail);
                       destruct Hcj as [<-|[<-|[]]]; try (inversion E; fail); revert E; apply cell_neq_off; rewrite !poff_padd; fold p; rewrite Epoff;
                       clear - Foff E0; unfold UNIT in *; lia.
           ++ assert (Es : slot_cells (fast_meta am i fr) j = slot_cells am j).
              { unfold slot_cells. rewrite (Hsl j ltac:(lia)). replace (j =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
              rewrite Es in Hcj. left. split; [apply GCi, (GCj j); [lia | exact Hcj]|].
              pose proof (Gsl j ltac:(lia)) as (_ & _ & T3).
              assert (Hfit : forall fr0, ss_fr (nth_slot am j) = Some fr0 -> 0 <= fr_off fr0 /\ 0 <= fr_n fr0 /\ UNIT * fr_off fr0 + fr_n fr0 <= stride_of am - IB).
              { intros fr0 E0. rewrite E0 in T3. destruct T3 as (_ & _ & (N0 & O0 & F0 & _) & _). lia. }
              destruct (slot_cells_span am j c Sp Hfit Hcj) as (q & Eq & Hq1 & Hq2).
              pose proof (same_group_starts am i j ltac:(lia) Sp) as SGS.
              intros [E|[E|[E|[]]]].
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** rewrite <- E in Eq. cbn [mc_loc] in Eq. injection Eq as Eq. rewrite <- Eq in Hq2. rewrite poff_padd in Hq2.
                 fold p in Hq2. rewrite Epoff in Hq2. clear - Hq2 SGS Foff Ffit Fn. unfold UNIT, IB in *. lia.
              ** exact (NC3 c (GCj j c ltac:(lia) Hcj) (eq_sym E)).
  - constructor.
    + intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd. fold G. unfold META_freed. rewrite WRF by exact Hk. reflexivity.
    + destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0]; [|constructor].
      constructor; [|constructor; [|constructor]].
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0. destruct k as [|k]; [|cbn in Hk; lia].
        replace (pa - 16 * 0 + -3 + Z.of_nat 0) with (pa - 3) by ring. rewrite WR3. reflexivity.
      * intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, Hst, E0.
        replace (pa - 16 * 0 + -2 + Z.of_nat k) with (pa - 2 + Z.of_nat k) by ring. rewrite WR2 by exact Hk.
        destruct k as [|[|k]]; [reflexivity | reflexivity | cbn in Hk; lia].
  - intros a Ha.
    destruct (Z_lt_le_dec a (pa - 3)) as [A1|A1]; [| destruct (Z_lt_le_dec a pa) as [A2|A2]].
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
    + left. destruct (Z.eq_dec a (pa - 3)) as [->|Hne].
      * exists (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))). split; [left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
      * exists (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))). split; [right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold pa. lia.
    + destruct (Z_lt_le_dec a (G + 28)) as [B1|B1]; [| destruct (Z_lt_le_dec a (G + 32)) as [B2|B2]].
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
      * left. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [right; right; left; reflexivity|].
        unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. fold G. unfold META_freed. lia.
      * destruct (Z_lt_le_dec a (spz - 1024)) as [C1|C1].
        -- exfalso. apply Ha. apply BV; lia.
        -- right. intros (rg & Hrg & Hin). pose proof (HFP rg Hrg). lia.
Qed.
End Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma user_slots_disjoint : forall s g1 a1 i1 f1 g2 a2 i2 f2,
  WF s -> usedX [] s g1 a1 -> usedX [] s g2 a2 -> 0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
  ss_fr (nth_slot a1 i1) = Some f1 -> fr_kind f1 = FUser -> ss_fr (nth_slot a2 i2) = Some f2 -> fr_kind f2 = FUser ->
  (g1 <> g2 \/ i1 <> i2) -> prid (am_mem a1) = prid (am_mem a2) ->
  poff (slot_start a1 i1) + stride_of a1 <= poff (slot_start a2 i2) \/
  poff (slot_start a2 i2) + stride_of a2 <= poff (slot_start a1 i1).
Proof.
  intros s g1 a1 i1 f1 g2 a2 i2 f2 HW U1 U2 Hi1 Hi2 F1 K1 F2 K2 Hne Er.
  pose proof (inv_groups HW g1 a1 U1) as G1. pose proof (inv_groups HW g2 a2 U2) as G2.
  pose proof (stride_pos _ _ _ _ _ G1) as S1. pose proof (stride_pos _ _ _ _ _ G2) as S2.
  destruct (sptr_eq_dec g1 g2) as [<-|Hg].
  - pose proof (usedX_fun _ _ _ _ _ U1 U2) as <-. destruct Hne as [Hne|Hne]; [exfalso; exact (Hne eq_refl)|].
    exact (same_group_starts a1 i1 i2 Hne S1).
  - pose proof (slot_in_span [] None U0 s HW g1 a1 i1 U1 Hi1) as [L1 H1].
    pose proof (slot_in_span [] None U0 s HW g2 a2 i2 U2 Hi2) as [L2 H2].
    destruct (inv_laminar HW g1 a1 g2 a2 U1 U2 Hg Er) as [D | [I | I]].
    + unfold spans_disjoint, group_extent in D. unfold group_extent, UNIT, IB in *. lia.
    + destruct (inside_slot_start [] None U0 s HW _ _ _ _ _ U1 U2 Hi1 I) as (j & fr & Hj & Hfj & Hkj & A & B).
      destruct (Z.eq_dec j i2) as [->|Hji]; [rewrite F2 in Hfj; injection Hfj as <-; rewrite K2 in Hkj; discriminate|].
      destruct (same_group_starts a2 j i2 Hji S2); unfold UNIT in *; lia.
    + destruct (inside_slot_start [] None U0 s HW _ _ _ _ _ U2 U1 Hi2 I) as (j & fr & Hj & Hfj & Hkj & A & B).
      destruct (Z.eq_dec j i1) as [->|Hji]; [rewrite F1 in Hfj; injection Hfj as <-; rewrite K1 in Hkj; discriminate|].
      destruct (same_group_starts a1 j i1 Hji S1); unfold UNIT in *; lia.
Qed.

(* [comment removed for export] *)
Lemma marker_cells_span : forall am i fr c, 0 <= fr_off fr -> 0 <= fr_n fr -> UNIT * fr_off fr + fr_n fr <= stride_of am - IB ->
  In c (marker_cells am i fr) ->
  exists q, mc_loc c = LMem q /\ prid q = prid (slot_start am i) /\
    poff (slot_start am i) + UNIT * fr_off fr + fr_n fr <= poff q /\ poff q + Z.of_nat (mc_w c) <= poff (slot_start am i) + stride_of am - IB + 1.
Proof.
  intros am i fr c H0 H1 H2 Hc. unfold marker_cells, slot_end, frame_rsv in Hc. unfold UNIT, IB in *.
  destruct Hc as [<-|Hc].
  - exists (padd (slot_start am i) (stride_of am - 4)). cbn [mc_loc mc_w]. rewrite prid_padd, poff_padd. repeat split; lia.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (0 <? stride_of am - 4 - 16 * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.ltb_lt in E.
      destruct Hc as [<-|[]]. exists (padd (padd (slot_start am i) (stride_of am - 4)) (- (stride_of am - 4 - 16 * fr_off fr - fr_n fr))).
      cbn [mc_loc mc_w]. rewrite !prid_padd, !poff_padd. repeat split; lia.
    + destruct (5 <=? stride_of am - 4 - 16 * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.leb_le in E.
      destruct Hc as [<-|[<-|[]]];
        [exists (padd (padd (slot_start am i) (stride_of am - 4)) (-4)) | exists (padd (padd (slot_start am i) (stride_of am - 4)) (-5))];
        cbn [mc_loc mc_w]; rewrite !prid_padd, !poff_padd; repeat split; lia.
Qed.

Section PostM.
Variable segs : list Segment.


(* [comment removed for export] *)
#[using="Type"] Lemma gend_vs_user_slot : forall s h a g am i fr,
  WF s -> usedX [] s h a -> usedX [] s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> prid (am_mem a) = prid (am_mem am) ->
  UNIT * fr_off fr + fr_n fr <= stride_of am - IB -> 0 <= fr_off fr -> 0 <= fr_n fr ->
  poff (slot_start a (am_last a)) + stride_of a - IB + 1 <= poff (slot_start am i) - 3 \/
  poff (slot_start am i) + UNIT * fr_off fr + fr_n fr <= poff (slot_start a (am_last a)) + stride_of a - IB.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s h a g am i fr HW Ua Ug Hi F K Er Ffit Fo Fn.
  pose proof (inv_groups HW h a Ua) as Ga. pose proof (inv_groups HW g am Ug) as Gg.
  pose proof (stride_pos _ _ _ _ _ Ga) as Sa. pose proof (stride_pos _ _ _ _ _ Gg) as Sg.
  pose proof Ga as ((Mla & _) & _). pose proof Gg as ((Mlg & _) & _).
  destruct (sptr_eq_dec h g) as [<-|Hg].
  - pose proof (usedX_fun _ _ _ _ _ Ua Ug) as <-. right.
    rewrite !poff_slot_start. assert (stride_of a * i <= stride_of a * am_last a) by nia. unfold UNIT, IB in *. lia.
  - pose proof (slot_in_span [] None U0 s HW h a (am_last a) Ua ltac:(lia)) as [L1 H1].
    pose proof (slot_in_span [] None U0 s HW g am i Ug Hi) as [L2 H2].
    destruct (inv_laminar HW h a g am Ua Ug Hg Er) as [D | [I | I]].
    + unfold spans_disjoint, group_extent in D. rewrite !poff_slot_start in *. unfold group_extent, UNIT, IB in *.
      assert (stride_of a * am_last a + stride_of a = stride_of a * (am_last a + 1)) by ring.
      destruct D as [D|D]; [left | right]; lia.
    + destruct (inside_slot_start [] None U0 s HW h a (am_last a) g am Ua Ug ltac:(lia) I) as (j & fr' & Hj & Hfj & Hkj & A & B).
      destruct (Z.eq_dec j i) as [->|Hji]; [rewrite F in Hfj; injection Hfj as <-; rewrite K in Hkj; discriminate|].
      destruct (same_group_starts am j i Hji Sg); unfold UNIT, IB in *; [left | right]; lia.
    + destruct (inside_slot_start [] None U0 s HW g am i h a Ug Ua Hi I) as (j & fr' & Hj & Hfj & Hkj & A & B).
      right. rewrite !poff_slot_start in *. assert (stride_of a * j <= stride_of a * am_last a) by nia.
      unfold UNIT, IB in *. lia.
Qed.

#[using="Type"] Theorem freed_slot_markers_gen : forall L s m m' g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> markers_hold L s (bview segs m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     (forall a, In a (st_areas s) -> ~ (loc_addr L (LMem a) <= x < loc_addr L (LMem a) + 4096)) ->
     ~ (ly_ctx L <= x < ly_ctx L + CTX_SIZE) -> bview segs m' x = bview segs m x) ->
  markers_hold L (s_fast s g am i fr) (bview segs m').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr spz HW HR HM HF Hk HFP BV.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & (a0 & k0 & Ha0 & Hk0 & Hga & _) & Hland & _ & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  pose proof HR as (HL & HC & HFM).
  pose proof HL as (_ & _ & Ldisj & Lrng).
  set (p := frame_ptr am i fr) in *. set (pa := loc_addr L (LMem p)) in *. set (G := loc_addr L (LMem g)) in *.
  (* [comment removed for export] *)
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
  destruct FOK as (Fn & Foff & Ffit & _).
  pose proof (inv_areas HW) as (AND & AOK & _).
  destruct (AOK a0 Ha0) as (ra & oa & rga & Ea & Oal & Opg & Hra & Hla & Hofit & Hkind).
  assert (FA : In (LMem a0, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a1 => (LMem a1, PGSZ))); exact Ha0).
  assert (EG : G = loc_addr L (LMem a0) + 24 + 40 * k0) by (unfold G; rewrite Hga, loc_padd; unfold AREA_HDR, META_SIZE; ring).
  (* [comment removed for export] *)
  apply Forall_forall. intros c Hc.
  assert (ND' : List.NoDup (keys (s_fast s g am i fr))).
  { unfold keys, s_fast, set_meta. cbn [st_metas set_metas]. rewrite map_fst_mupdate_In.
    - exact (proj1 (inv_keys HW)).
    - apply (mlookup_In_keys (st_metas s) g (MUsed am)). apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hu. }
  assert (Eloc : forall r, loc_addr L (LMem r) = ly_reg L (prid r) + poff r) by (intros [rr oo]; reflexivity).
  assert (Hpa : pa = ly_reg L (prid (am_mem am)) + poff (slot_start am i) + 16 * fr_off fr).
  { unfold pa, p, frame_ptr. rewrite Eloc, prid_padd, poff_padd, prid_slot_start. unfold UNIT. ring. }
  destruct (In_markers_inv _ c Hc) as [(h & a & j & f & Hfr' & Kf & Hc') | (h & a & Hua & ->)].
  2:{ (* [comment removed for export] *)
    apply (used_metas_iff _ h a ND') in Hua. unfold MT, s_fast, set_meta in Hua. cbn [st_metas set_metas] in Hua.
    assert (Ha' : exists a', usedX [] s h a' /\ gend_cell a = gend_cell a').
    { destruct (sptr_eq_dec h g) as [->|Hhg].
      - rewrite mlookup_mupdate_same in Hua. injection Hua as <-. exists am. split; [exact Hux | reflexivity].
      - rewrite mlookup_mupdate_other in Hua by exact Hhg. exists a. split; [apply usedX_intro; [reflexivity | exact Hua] | reflexivity]. }
    destruct Ha' as (a' & Hua' & ->).
    assert (Hheld : cell_holds L (bview segs m) (gend_cell a')).
    { apply (proj1 (Forall_forall _ _) HM). apply (In_gend s h a'). apply (used_metas_usedX s h a' HW). exact Hua'. }
    pose proof (inv_groups HW h a' Hua') as (Gm' & _ & _ & _).
    destruct Gm' as (Mlast' & _).
    destruct (used_group_region [] None U0 s h a' HW Hua') as (rgH & HrH & HkH & HlH & Ho0H & HextH & _).
    assert (FH : In (LMem (SP (prid (am_mem a')) 0), rg_len rgH) (footprint s)) by (apply footprint_region_In; assumption).
    destruct (used_group_region [] None U0 s g am HW Hux) as (rgG & HrG & HkG & HlG & Ho0G & HextG & _).
    assert (FG : In (LMem (SP (prid (am_mem am)) 0), rg_len rgG) (footprint s)) by (apply footprint_region_In; assumption).
    pose proof (slot_in_span [] None U0 s HW h a' (am_last a') Hua' ltac:(lia)) as [SL1 SL2].
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW h a' Hua')) as Sa'.
    pose proof (slot_in_span [] None U0 s HW g am i Hux Hi) as [SI1 SI2].
    assert (Bx : forall x, in_rng (cell_range L (gend_cell a')) x ->
               x = ly_reg L (prid (am_mem a')) + poff (slot_start a' (am_last a')) + stride_of a' - IB).
    { intros x Hx. unfold in_rng, cell_range, gend_cell, slot_end in Hx. cbn [mc_loc mc_w fst snd] in Hx.
      rewrite Eloc, prid_padd, poff_padd, prid_slot_start in Hx. clear - Hx. unfold IB in *. lia. }
    apply (cell_holds_frame L (bview segs m) (bview segs m') (gend_cell a') ltac:(cbn; lia) Hheld).
    intros x Hx. pose proof (Bx x Hx) as ->. apply BV.
    - pose proof (HFP _ FH) as SpH. cbn [fst snd loc_addr] in SpH. unfold group_extent, UNIT, IB in *. clear - SpH SL1 SL2 HextH Ho0H Sa'.
      lia.
    - destruct (Nat.eq_dec (prid (am_mem a')) (prid (am_mem am))) as [Er|Er].
      + destruct (gend_vs_user_slot s h a' g am i fr HW Hua' Hux Hi Hfri Hk Er Ffit ltac:(clear - Foff; lia) Fn) as [D|D];
          rewrite <- Er in Hpa; clear - D Hpa Fn Foff; unfold UNIT, IB in *; lia.
      + destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FH FG ltac:(intro E; injection E; intros; contradiction)) as [D|D];
          unfold ranges_disjoint in D; cbn [crange fst snd loc_addr] in D;
          pose proof (HFP _ FG) as SpG; cbn [fst snd loc_addr] in SpG; unfold group_extent, UNIT, IB in *;
          clear - D Hpa Foff Ffit Fn SI1 SI2 HextG Ho0G SL1 SL2 HextH Ho0H Sa'; lia.
    - intros a1 Ha1 Hx1.
      destruct (AOK a1 Ha1) as (ra1 & oa1 & rga1 & Ea1 & Oal1 & Opg1 & Hra1 & Hla1 & Hofit1 & Hkind1).
      assert (FA1 : In (LMem a1, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a2 => (LMem a2, PGSZ))); exact Ha1).
      assert (Hne : (LMem a1, PGSZ) <> (LMem (SP (prid (am_mem a')) 0), rg_len rgH)).
      { rewrite Ea1. intro E. injection E as E1 E2. clear - E2 Opg1. unfold PGSZ in *. lia. }
      destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA1 FH Hne) as [D|D];
        unfold ranges_disjoint in D; cbn [crange fst snd] in D; rewrite (Eloc (SP (prid (am_mem a')) 0)) in D; cbn [prid poff] in D;
        clear - D Hx1 SL1 SL2 HextH Ho0H Sa'; unfold METAS_PER_AREA, PGSZ, group_extent, UNIT, IB in *; lia.
    - intros Hx1. assert (FC : In (LCtx 0, CTX_SIZE) (footprint s)) by (left; reflexivity).
      assert (Hne : (LCtx 0, CTX_SIZE) <> (LMem (SP (prid (am_mem a')) 0), rg_len rgH)) by discriminate.
      destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FC FH Hne) as [D|D];
        unfold ranges_disjoint in D; cbn [crange fst snd] in D; change (loc_addr L (LCtx 0)) with (ly_ctx L + 0) in D;
        rewrite (Eloc (SP (prid (am_mem a')) 0)) in D; cbn [prid poff] in D;
        clear - D Hx1 SL1 SL2 HextH Ho0H Sa'; unfold CTX_SIZE, group_extent, UNIT, IB in *; lia. }
  destruct (in_frames_inv _ _ _ _ _ Hfr') as (Hu' & Hj' & Hf').
  apply (used_metas_iff _ h a ND') in Hu'. unfold MT, s_fast, set_meta in Hu'. cbn [st_metas set_metas] in Hu'.
  (* [comment removed for export] *)
  assert (Hfr0 : exists a', In (h, a', j, f) (frames s) /\ marker_cells a j f = marker_cells a' j f /\ usedX [] s h a' /\
                   0 <= j <= am_last a' /\ ss_fr (nth_slot a' j) = Some f /\ (h <> g \/ j <> i)).
  { destruct (sptr_eq_dec h g) as [->|Hhg].
    - rewrite mlookup_mupdate_same in Hu'. injection Hu' as <-.
      destruct Gm as (Mlast & _ & Mlen & _).
      assert (Hsl : nth_slot (fast_meta am i fr) j = if j =? i then fast_slot am i fr else nth_slot am j).
      { unfold fast_meta. change (nth_slot (am_set_freed (am_freed am + bit i) (upd_slot am i (fast_slot am i fr))) j)
          with (nth_slot (upd_slot am i (fast_slot am i fr)) j). apply nth_slot_upd_slot; [lia | lia | rewrite Mlen; lia]. }
      rewrite Hsl in Hf'. destruct (Z.eqb_spec j i) as [->|Hji].
      + unfold fast_slot in Hf'. destruct (fr_off fr =? 0); discriminate.
      + exists am. split; [apply frames_intro; [exact HW | apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu | exact Hj' | exact Hf']|].
        split; [reflexivity|]. split; [exact Hux|]. split; [exact Hj'|]. split; [exact Hf'|]. right. exact Hji.
    - rewrite mlookup_mupdate_other in Hu' by exact Hhg.
      assert (Hua : usedX [] s h a) by (apply usedX_intro; [reflexivity | exact Hu']).
      exists a. split; [apply frames_intro; [exact HW | exact Hu' | exact Hj' | exact Hf']|].
      split; [reflexivity|]. split; [exact Hua|]. split; [exact Hj'|]. split; [exact Hf'|]. left. exact Hhg. }
  destruct Hfr0 as (a' & Hfrs & Emk & Hua' & Hj0 & Hf0 & Hdist).
  rewrite Emk in Hc'.
  assert (Hheld : cell_holds L (bview segs m) c) by exact (proj1 (Forall_forall _ _) HM c (In_markers s h a' j f c Hfrs Kf Hc')).
  pose proof (inv_groups HW h a' Hua') as (_ & _ & Gsl' & _).
  pose proof (Gsl' j Hj0) as (_ & _ & T3). rewrite Hf0 in T3. destruct T3 as (_ & _ & (N0 & O0 & F0 & _) & _).
  destruct (marker_cells_span a' j f c ltac:(lia) N0 F0 Hc') as (q & Eq & Hq1 & Hq2 & Hq3).
  destruct (used_group_region [] None U0 s h a' HW Hua') as (rgH & HrH & HkH & HlH & Ho0H & HextH & _).
  assert (FH : In (LMem (SP (prid (am_mem a')) 0), rg_len rgH) (footprint s)) by (apply footprint_region_In; assumption).
  destruct (used_group_region [] None U0 s g am HW Hux) as (rgG & HrG & HkG & HlG & Ho0G & HextG & _).
  assert (FG : In (LMem (SP (prid (am_mem am)) 0), rg_len rgG) (footprint s)) by (apply footprint_region_In; assumption).
  pose proof (slot_in_span [] None U0 s HW h a' j Hua' Hj0) as [SL1 SL2].
  pose proof (slot_in_span [] None U0 s HW g am i Hux Hi) as [SI1 SI2].
  assert (Hcq : forall x, in_rng (cell_range L c) x ->
             ly_reg L (prid (am_mem a')) + poff (slot_start a' j) <= x < ly_reg L (prid (am_mem a')) + poff (slot_start a' j) + stride_of a' - 3).
  { intros x Hx. unfold in_rng, cell_range in Hx. rewrite Eq, Eloc, Hq1, prid_slot_start in Hx. cbn [fst snd] in Hx.
    clear - Hx Hq2 Hq3 O0 N0. unfold UNIT, IB in *. lia. }
  assert (Hw1 : (1 <= mc_w c)%nat).
  { clear - Hc'. unfold marker_cells in Hc'. destruct Hc' as [<-|Hc']; [cbn; lia|].
    apply in_app_iff in Hc' as [Hc'|Hc'].
    - destruct (0 <? _); [destruct Hc' as [<-|[]]; cbn; lia | destruct Hc'].
    - destruct (5 <=? _); [destruct Hc' as [<-|[<-|[]]]; cbn; lia | destruct Hc']. }
  apply (cell_holds_frame L (bview segs m) (bview segs m') c Hw1 Hheld).
  intros x Hx. pose proof (Hcq x Hx) as Bx. apply BV.
  - (* [comment removed for export] *)
    pose proof (HFP _ FH) as SpH. cbn [fst snd loc_addr] in SpH. unfold group_extent, UNIT, IB in *. clear - Bx SpH SL2 HextH Ho0H.
    lia.
  - (* [comment removed for export] *)
    destruct (Nat.eq_dec (prid (am_mem a')) (prid (am_mem am))) as [Er|Er].
    + destruct (user_slots_disjoint s h a' j f g am i fr HW Hua' Hux Hj0 Hi Hf0 Kf Hfri Hk Hdist Er) as [D|D];
        rewrite Er in Bx; clear - Bx D Hpa Foff Ffit Fn; unfold UNIT, IB in *; lia.
    + destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FH FG ltac:(intro E; injection E; intros; contradiction)) as [D|D];
        unfold ranges_disjoint in D; cbn [crange fst snd loc_addr] in D;
        pose proof (HFP _ FG) as SpG; cbn [fst snd loc_addr] in SpG; unfold group_extent, UNIT, IB in *;
        clear - Bx D Hpa Foff Ffit Fn SI1 SI2 HextG Ho0G SL1 SL2 HextH Ho0H; lia.
  - (* [comment removed for export] *)
    intros a1 Ha1 Hx1.
    destruct (AOK a1 Ha1) as (ra1 & oa1 & rga1 & Ea1 & Oal1 & Opg1 & Hra1 & Hla1 & Hofit1 & Hkind1).
    assert (FA1 : In (LMem a1, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a2 => (LMem a2, PGSZ))); exact Ha1).
    assert (Hne : (LMem a1, PGSZ) <> (LMem (SP (prid (am_mem a')) 0), rg_len rgH)).
    { rewrite Ea1. intro E. injection E as E1 E2. clear - E2 Opg1. unfold PGSZ in *. lia. }
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA1 FH Hne) as [D|D];
      unfold ranges_disjoint in D; cbn [crange fst snd] in D; rewrite (Eloc (SP (prid (am_mem a')) 0)) in D; cbn [prid poff] in D;
      clear - Bx D Hx1 SL1 SL2 HextH Ho0H; unfold METAS_PER_AREA, PGSZ, group_extent, UNIT, IB in *; lia.
  - (* [comment removed for export] *)
    intros Hx1. assert (FC : In (LCtx 0, CTX_SIZE) (footprint s)) by (left; reflexivity).
    assert (Hne : (LCtx 0, CTX_SIZE) <> (LMem (SP (prid (am_mem a')) 0), rg_len rgH)) by discriminate.
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FC FH Hne) as [D|D];
      unfold ranges_disjoint in D; cbn [crange fst snd] in D; change (loc_addr L (LCtx 0)) with (ly_ctx L + 0) in D;
      rewrite (Eloc (SP (prid (am_mem a')) 0)) in D; cbn [prid poff] in D;
      clear - Bx D Hx1 SL1 SL2 HextH Ho0H; unfold CTX_SIZE, group_extent, UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem freed_slot_markers : forall L s m m' g am i fr (spz : Z),
  WF s -> repr L s (bview segs m) -> markers_hold L s (bview segs m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  (forall x, ~ (spz - 1024 <= x < spz) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
     ~ (loc_addr L (LMem g) + 28 <= x < loc_addr L (LMem g) + 32) -> bview segs m' x = bview segs m x) ->
  markers_hold L (s_fast s g am i fr) (bview segs m').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr spz HW HR HM HF Hk HFP BV.
  apply (freed_slot_markers_gen L s m m' g am i fr spz HW HR HM HF Hk HFP).
  intros x H1 H2 H3 H4. apply BV; [exact H1 | exact H2 |].
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (a0 & k0 & Ha0 & Hk0 & Hga & _) & _).
  intros Hx. apply (H3 a0 Ha0). rewrite Hga, loc_padd in Hx. unfold AREA_HDR, META_SIZE in Hx. clear - Hx Hk0. unfold METAS_PER_AREA in *. lia.
Qed.

End PostM.
