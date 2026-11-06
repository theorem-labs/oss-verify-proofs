(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngHeap MngSurgery AXG_ffpost MngExc MngNtfPre MngNtfC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition rel_meta (am : ameta) (i : Z) (fr : frame) : ameta := upd_slot am i (fast_slot am i fr).
Definition s_rel (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : astate := set_meta s g (MUsed (rel_meta am i fr)).

(* [comment removed for export] *)
Definition s_unm (s : astate) (r : nat) : astate :=
  set_regions (lupd (st_regions s) r (mkRegion RkMap (rg_len (nth r (st_regions s) (mkRegion RkMap 0 [] false))) [] false)) s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_ntf_unfold : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  free (Some (frame_ptr am i fr)) s =
  bind (nontrivial_free NEST_FUEL g i)
       (fun mi => match mi with
                  | Some (r, len) => _ <- ask (KMunmap r len) ;; upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false)
                  | None => ret tt
                  end) (s_rel s g am i fr).
Proof.
  intros s g am i fr HW HF Hnt.
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
  replace (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am))) with false.
  2:{ symmetry. destruct Hnt as [E|E]; [rewrite E; reflexivity|]. rewrite E, Z.eqb_refl. apply andb_false_r. }
  reflexivity.
Qed.

Lemma free_ntf_none : forall s g am i fr s', WF s -> In (g, am, i, fr) (frames s) ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  nontrivial_free NEST_FUEL g i (s_rel s g am i fr) = IRet (None, s') ->
  free (Some (frame_ptr am i fr)) s = IRet (tt, s').
Proof. intros s g am i fr s' HW HF Hnt E. rewrite (free_ntf_unfold s g am i fr HW HF Hnt). unfold bind. rewrite E. reflexivity. Qed.

Lemma free_ntf_some : forall s g am i fr s' r len, WF s -> In (g, am, i, fr) (frames s) ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  nontrivial_free NEST_FUEL g i (s_rel s g am i fr) = IRet (Some (r, len), s') ->
  free (Some (frame_ptr am i fr)) s = IAsk (KMunmap r len) s' (fun _ => IRet (tt, s_unm s' r)).
Proof.
  intros s g am i fr s' r len HW HF Hnt E. rewrite (free_ntf_unfold s g am i fr HW HF Hnt). unfold bind. rewrite E.
  cbn [ibind]. unfold ask, upd_region, modify, bind. cbn [ibind]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rel_Inv : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  Inv [] (Some (g, i)) U0 (s_rel s g am i fr) /\ usedX [] (s_rel s g am i fr) g (rel_meta am i fr).
Proof.
  intros s g am i fr HW HF Kfr. destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  assert (Ux : usedX [] s g am) by exact (proj1 (used_metas_usedX s g am HW) Hu).
  pose proof (release_slot_spec [] U0 s g i am fr (fun r => Inv [] (Some (g, i)) U0 (snd r)) HW Ux Hi Hfri Kfr (fun s' x _ _ HI' => HI')) as A.
  assert (Mg : mlookup (st_metas s) g = Some (MUsed am)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Hu).
  unfold release_slot, getm, setm, modify, get, bind, ret in A. cbn [ibind fst snd] in A. rewrite Mg in A. cbn [ibind fst snd] in A. rewrite Hfri in A.
  split; [exact A|]. apply usedX_intro; [reflexivity | apply MT_set_same].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rel_extra (L : layout) (am : ameta) (i : Z) (fr : frame) : list (Z * Z) :=
  if fr_off fr =? 0 then [] else
  let p := padd (slot_start am i) (UNIT * fr_off fr) in
  map (cell_range L) [MCell (LMem (padd p (-4))) 1 (VZ 0); MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr));
                      MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))].

Lemma fm_sub : forall {A} (cr : mcell -> Z * Z) (f g : A -> list mcell) (l : list A) (i : A) (ex : list (Z * Z)),
  List.NoDup l -> In i l -> (forall x, In x l -> x <> i -> f x = g x) -> Permutation (map cr (g i)) (map cr (f i) ++ ex) ->
  Permutation (map cr (flat_map g l)) (map cr (flat_map f l) ++ ex).
Proof.
  intros A cr f g l i ex ND Hi Hfg Hp. destruct (in_split i l Hi) as (l1 & l2 & ->).
  pose proof (NoDup_remove _ _ _ ND) as [ND' Hn].
  rewrite !flat_map_app'. cbn [flat_map].
  replace (flat_map g l1) with (flat_map f l1).
  2:{ apply flat_map_ext_in'. intros x Hx. apply Hfg; [apply in_app_iff; left; exact Hx | intros ->; apply Hn; apply in_app_iff; left; exact Hx]. }
  replace (flat_map g l2) with (flat_map f l2).
  2:{ apply flat_map_ext_in'. intros x Hx. apply Hfg; [apply in_app_iff; right; right; exact Hx | intros ->; apply Hn; apply in_app_iff; right; exact Hx]. }
  rewrite !map_app. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_tail; exact Hp|]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma NoDup_zseq' : forall lo n, List.NoDup (zseq lo n).
Proof.
  intros lo n. unfold zseq. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros x y _ _ E. lia.
Qed.

Lemma msc_upd_slot : forall q am i x, meta_slot_cells q (Some (MUsed (upd_slot am i x))) = meta_slot_cells q (Some (MUsed am)).
Proof. intros q am i x. destruct am; reflexivity. Qed.

Theorem rel_RS : forall L s g am i fr, WF s -> In (g, am, i, fr) (frames s) ->
  Permutation (map (cell_range L) (image s)) (map (cell_range L) (image (s_rel s g am i fr)) ++ rel_extra L am i fr).
Proof.
  intros L s g am i fr HW HF. destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  assert (Mg : MT s g = Some (MUsed am)) by exact (proj1 (used_metas_iff s g am (proj1 (inv_keys HW))) Hu).
  destruct (image_setm_ks s g am (rel_meta am i fr) (KS_of_WF s HW) Mg) as (U & P1 & P2).
  eapply Permutation_trans; [apply Permutation_map; exact P1|].
  eapply Permutation_trans; [|apply Permutation_app_tail; apply Permutation_map; apply Permutation_sym; exact P2].
  rewrite !map_app. rewrite <- !app_assoc. apply Permutation_app_head.
  unfold rel_meta at 1. rewrite msc_upd_slot. apply Permutation_app_head.
  pose proof (upd_slot_fields am i (fast_slot am i fr)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
  assert (Fa : am_aidx (upd_slot am i (fast_slot am i fr)) = am_aidx am) by (destruct am; reflexivity).
  pose proof (inv_groups HW g am (proj1 (used_metas_usedX s g am HW) Hu)) as ((_ & _ & Mlen & _) & _ & Gsl & _).
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat) by (rewrite Mlen; lia).
  unfold group_cells. unfold rel_meta. rewrite Fm, Fl, Fml, Fa. rewrite !map_app, <- app_assoc. apply Permutation_app_head.
  apply (fm_sub (cell_range L) (slot_cells (upd_slot am i (fast_slot am i fr))) (slot_cells am) _ i).
  - apply NoDup_zseq'.
  - apply In_zseq. lia.
  - intros j Hj Hne. apply In_zseq in Hj. unfold slot_cells. rewrite Fss, nth_slot_upd_slot by (first [lia | exact Hlen]).
    replace (j =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
  - pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (_ & _ & _ & Hhdr).
    unfold slot_cells at 2. rewrite Fss, nth_slot_upd_slot by (first [lia | exact Hlen]). rewrite Z.eqb_refl.
    unfold rel_extra, fast_slot, slot_cells. rewrite Hfri.
    destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
    + rewrite (Hhdr E0). cbn [ss_hdr ss_fr app map]. rewrite ?app_nil_r. apply Permutation_refl.
    + cbn [ss_hdr ss_fr]. rewrite ?app_nil_r. rewrite !map_app, <- ?app_assoc. apply Permutation_app_head. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rel_cnew (am : ameta) (i : Z) (fr : frame) : list mcell :=
  if fr_off fr =? 0 then [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ 255); MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ 0)] else [].

Section RX.
Variable segs : list Segment.

#[using="Type"] Theorem rel_repr_x : forall L s (m m' : word -> option byte) g am i fr (lo : Z),
  WF s -> repr L s (bview segs m) -> In (g, am, i, fr) (frames s) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= lo) ->
  (forall x, bview segs m x <> None -> bview segs m' x <> None) ->
  (forall x, x < lo -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) -> bview segs m' x = bview segs m x) ->
  bview segs m' (loc_addr L (LMem (frame_ptr am i fr)) - 3) = Some 255 ->
  (forall k, (k < 2)%nat -> bview segs m' (loc_addr L (LMem (frame_ptr am i fr)) - 2 + Z.of_nat k) = Some 0) ->
  repr_x L (s_rel s g am i fr) (bview segs m') [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m m' g am i fr lo HW HR HF HFP Hgrow BV W3 W2.
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  assert (Mg : MT s g = Some (MUsed am)) by exact (proj1 (used_metas_iff s g am (proj1 (inv_keys HW))) Hu).
  assert (HK : KS s) by exact (KS_of_WF s HW).
  pose proof HR as (HL & HC & HFM).
  pose proof (repr_x_of_repr L s _ HW HR) as HRX.
  pose proof (rel_RS L s g am i fr HW HF) as P.
  assert (HPW : PW L s) by exact (image_cells_disjoint s L HW HL).
  assert (HRS : RS L (s_rel s g am i fr) s) by (exists (rel_extra L am i fr); exact P).
  pose proof (upd_slot_fields am i (fast_slot am i fr)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
  assert (Fa : am_aidx (upd_slot am i (fast_slot am i fr)) = am_aidx am) by (destruct am; reflexivity).
  pose proof (inv_groups HW g am (proj1 (used_metas_usedX s g am HW) Hu)) as ((_ & _ & Mlen & _) & _ & Gsl & _).
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat) by (rewrite Mlen; lia).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfri in S3. destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & Hhdr).
  set (pa := loc_addr L (LMem (frame_ptr am i fr))) in *.
  assert (Epa : pa = loc_addr L (LMem (slot_start am i)) + UNIT * fr_off fr) by (unfold pa, frame_ptr; rewrite loc_padd; reflexivity).
  (* [comment removed for export] *)
  assert (LOW : forall c, In c (image (s_rel s g am i fr)) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= lo).
  { intros c Hc. destruct (RS_range L _ s c HRS Hc) as (c0 & H0 & E0). destruct (image_in_footprint s L c0 HW HL H0) as (rg & Hrg & Hincl).
    pose proof (HFP rg Hrg) as B. unfold range_incl, cell_range, crange in *. injection E0 as E1 E2. cbn [fst snd] in *. lia. }
  apply (repr_x_step L s (s_rel s g am i fr) (bview segs m) (bview segs m') [] [] (rel_cnew am i fr) HRX).
  - exact (layout_ok_set_meta L s g _ HL).
  - exact (PW_of_RS L _ s HPW HRS).
  - change (footprint (s_rel s g am i fr)) with (footprint s). apply Forall_forall. intros rg Hrg x Hx. apply Hgrow. exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - intros c Hc. unfold s_rel in Hc. destruct (cov_setm s g am (rel_meta am i fr) c HK Mg Hc) as [H1|[H1|H1]].
    + left. split; [exact H1 | intros []].
    + left. split; [|intros []]. apply (In_image_used s g am c HK Mg). left. unfold rel_meta in H1. rewrite msc_upd_slot in H1. exact H1.
    + unfold group_cells, rel_meta in H1. rewrite Fm, Fl, Fml, Fa in H1. apply in_app_iff in H1 as [H1|H1].
      * left. split; [|intros []]. apply (In_image_used s g am c HK Mg). right. unfold group_cells. apply in_app_iff. left. exact H1.
      * apply in_flat_map in H1 as (j & Hj & Hcj). apply In_zseq in Hj. unfold slot_cells in Hcj. rewrite Fss in Hcj.
        rewrite nth_slot_upd_slot in Hcj by (first [lia | exact Hlen]).
        assert (GCj : forall c0, In c0 (slot_cells am j) -> In c0 (image s)).
        { intros c0 H0. apply (In_image_used s g am c0 HK Mg). right. unfold group_cells. apply in_app_iff. right. apply in_flat_map.
          exists j. split; [apply In_zseq; lia | exact H0]. }
        destruct (Z.eqb_spec j i) as [->|Hne].
        -- unfold fast_slot in Hcj. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
           ++ cbn [ss_hdr ss_fr app] in Hcj. rewrite ?app_nil_r in Hcj. destruct Hcj as [<-|Hcj].
              ** left. split; [|intros []]. apply GCj. unfold slot_cells. left. reflexivity.
              ** right. left. unfold rel_cnew. replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0). exact Hcj.
           ++ cbn [ss_hdr ss_fr app] in Hcj. rewrite ?app_nil_r in Hcj. left. split; [|intros []]. apply GCj. unfold slot_cells.
              destruct Hcj as [<-|Hcj]; [left; reflexivity | right; cbn [app]; apply in_app_iff; left; exact Hcj].
        -- left. split; [|intros []]. apply GCj. unfold slot_cells. exact Hcj.
  - intros c Hc. unfold rel_cnew in Hc. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0]; [|destruct Hc].
    apply (In_image_setm_new s g am (rel_meta am i fr) c HK Mg). right. unfold group_cells, rel_meta. rewrite Fm, Fl, Fml, Fa.
    apply in_app_iff. right. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
    unfold slot_cells. rewrite Fss, nth_slot_upd_slot by (first [lia | exact Hlen]). rewrite Z.eqb_refl. unfold fast_slot.
    replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0). cbn [ss_hdr ss_fr app]. right. exact Hc.
  - unfold rel_cnew. destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0]; [|constructor].
    rewrite E0, Z.mul_0_r, Z.add_0_r in Epa.
    constructor; [|constructor; [|constructor]].
    + intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, <- Epa. destruct k as [|k]; [|cbn in Hk; lia].
      replace (pa + -3 + Z.of_nat 0) with (pa - 3) by ring. rewrite W3. reflexivity.
    + intros k Hk. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_padd, <- Epa.
      replace (pa + -2 + Z.of_nat k) with (pa - 2 + Z.of_nat k) by ring. rewrite W2 by (cbn in Hk; lia).
      destruct k as [|[|k]]; [reflexivity | reflexivity | cbn in Hk; lia].
  - intros a Ha. destruct (Z_lt_le_dec a lo) as [A1|A1].
    + destruct (decide (pa - 3 <= a < pa)) as [A2|A2]; [|exfalso; apply Ha; apply BV; [exact A1 | exact A2]].
      destruct (Z.eqb_spec (fr_off fr) 0) as [E0|E0].
      * left. rewrite E0, Z.mul_0_r, Z.add_0_r in Epa. unfold rel_cnew. replace (fr_off fr =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0).
        destruct (Z.eq_dec a (pa - 3)) as [->|Hne].
        -- exists (MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ 255)). split; [left; reflexivity|].
           unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_padd, <- Epa. lia.
        -- exists (MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ 0)). split; [right; left; reflexivity|].
           unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd, <- Epa. lia.
      * right. intros c Hc _ Hin.
        assert (HPWp : pairwise ranges_disjoint (map (cell_range L) (image (s_rel s g am i fr)) ++ rel_extra L am i fr)).
        { apply (pairwise_perm ranges_disjoint _ _ ranges_disjoint_sym' P). exact HPW. }
        unfold rel_extra in HPWp. replace (fr_off fr =? 0) with false in HPWp by (symmetry; apply Z.eqb_neq; exact E0).
        set (p := padd (slot_start am i) (UNIT * fr_off fr)) in HPWp.
        assert (Ep : loc_addr L (LMem p) = pa) by (unfold p, pa, frame_ptr; reflexivity).
        pose proof (image_cell_width _ c Hc) as W1.
        assert (Hc' : In (cell_range L c) (map (cell_range L) (image (s_rel s g am i fr)))) by (apply in_map; exact Hc).
        destruct (Z.eq_dec a (pa - 3)) as [->|Hne].
        -- pose proof (pairwise_In_app ranges_disjoint _ _ HPWp (cell_range L c) (cell_range L (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))))
              Hc' ltac:(apply in_map; right; left; reflexivity)) as D.
           unfold ranges_disjoint, cell_range, in_rng in *. cbn [fst snd mc_loc mc_w] in *. rewrite loc_padd, Ep in D. lia.
        -- pose proof (pairwise_In_app ranges_disjoint _ _ HPWp (cell_range L c) (cell_range L (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))))
              Hc' ltac:(apply in_map; right; right; left; reflexivity)) as D.
           unfold ranges_disjoint, cell_range, in_rng in *. cbn [fst snd mc_loc mc_w Z.of_nat Pos.of_succ_nat] in *. rewrite loc_padd, Ep in D. lia.
    + right. intros c Hc _ Hin. pose proof (LOW c Hc) as B. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
Qed.
End RX.
