(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngHeap MngSurgery MngNtfPre MngGeoX MngLt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXG_ffpost MngMeta MngGeo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section GX.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.
Hypothesis HXU : XNU X s.

#[using="HXU"] Lemma usedX_of_MT : forall q a, MT s q = Some (MUsed a) -> usedX X s q a.
Proof. LiaFast.lf_pins (fun (HXU : LiaFast.U) => LiaFast.u0).
  intros q a E. apply usedX_intro; [|exact E]. destruct (memb q X) eqn:M; [|reflexivity].
  exfalso. exact (HXU q (memb_In' q X M) a E).
Qed.

#[using="R U HI"] Lemma ufacts_X : forall q a, usedX X s q a -> 16 <= stride_of a /\ 0 <= am_last a <= 31 /\ 0 <= poff (am_mem a).
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros q a Hu. pose proof (stride_pos _ _ _ _ _ (inv_groups HI q a Hu)) as S.
  pose proof (inv_groups HI q a Hu) as ((Gl & _) & _). destruct (used_group_region X R U s q a HI Hu) as (rg & _ & _ & _ & Ho & _). lia.
Qed.

#[using="R U HI"] Lemma ext28_X : forall q a, usedX X s q a -> 28 <= group_extent a.
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0). intros q a Hu. destruct (ufacts_X q a Hu) as (S & L & _). unfold group_extent, UNIT, IB. nia. Qed.





(* [comment removed for export] *)
#[using="R U HI"] Theorem adjacency_impossible_X : forall h ah q aq, usedX X s h ah -> usedX X s q aq -> h <> q ->
  prid (am_mem ah) = prid (am_mem aq) -> poff (am_mem ah) + group_extent ah = poff (am_mem aq) -> False.
Proof. LiaFast.lf_pins (fun (R U HI : LiaFast.U) => LiaFast.u0).
  intros h ah q aq Uh Uq Hne Er Eo.
  destruct (ufacts_X h ah Uh) as (Sh & Lh & Oh). destruct (ufacts_X q aq Uq) as (Sq & Lq & Oq).
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI h ah Uh)) as Xh.
  pose proof (inv_groups HI q aq Uq) as (_ & _ & _ & _ & Gmp & Gns).
  destruct (Z.eq_dec (am_maplen aq) 0) as [Hml|Hml].
  2:{ destruct (used_group_region X R U s q aq HI Uq) as (rg & _ & _ & _ & _ & _ & Z0). rewrite (Z0 ltac:(pose proof (inv_groups HI q aq Uq) as (_ & Gml & _); lia)) in Eo. lia. }
  destruct (Gns Hml) as (_ & p & ap & k & fr & Up & Hk & Hfr & Kfr & Emem & _ & _ & _).
  destruct (ufacts_X p ap Up) as (Sp & Lp & Op).
  pose proof (f_equal poff Emem) as Eoq. pose proof (f_equal prid Emem) as Erq. rewrite prid_slot_start in Erq.
  pose proof (st_last ah) as ELh.
  destruct (sptr_eq_dec h p) as [<-|Hhp].
  - pose proof (usedX_fun _ _ _ _ _ Up Uh) as ->.
    pose proof (st_mono ah k (am_last ah) ltac:(lia) ltac:(lia)) as M. unfold IB in ELh. lia.
  - assert (Erp : prid (am_mem ah) = prid (am_mem ap)) by congruence.
    pose proof (slot_in_span X R U s HI p ap k Up Hk) as [SP1 SP2].
    destruct (inv_laminar HI h ah p ap Uh Up Hhp Erp) as [D | [I | I]].
    + unfold spans_disjoint in D. unfold UNIT, IB in *. lia.
    + destruct (inside_slot_start X R U s HI h ah (am_last ah) p ap Uh Up ltac:(lia) I) as (j & fr' & Hj & _ & _ & A & B).
      destruct (Z.eq_dec k j) as [->|Hkj]; [unfold UNIT, IB in *; lia|].
      destruct (same_group_starts ap k j Hkj Sp); unfold UNIT, IB in *; lia.
    + destruct (inside_slot_start X R U s HI p ap k h ah Up Uh Hk I) as (j & fr' & Hj & _ & _ & A & B).
      pose proof (st_mono ah j (am_last ah) ltac:(lia) ltac:(lia)) as M. unfold UNIT, IB in *. lia.
Qed.

(* [comment removed for export] *)
#[using="X R U HI HXU"] Theorem markers_vs_hdr_X : forall c q aq, In c (markers s) -> MT s q = Some (MUsed aq) ->
  exists qc, mc_loc c = LMem qc /\
    (prid qc <> prid (am_mem aq) \/ poff qc + Z.of_nat (mc_w c) <= poff (am_mem aq) \/ poff (am_mem aq) + 12 <= poff qc).
Proof. LiaFast.lf_pins (fun (X R U HI HXU : LiaFast.U) => LiaFast.u0).
  intros c q aq Hc Mq.
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  assert (Uq : usedX X s q aq) by (exact (usedX_of_MT q aq Mq)).
  destruct (ufacts_X q aq Uq) as (Sq & Lq & Oq).
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI q aq Uq)) as Xq.
  destruct (In_markers_inv s c Hc) as [(h & ah & j & fr & HF & Kfr & Hc') | (h & ah & Hu & ->)].
  - destruct (in_frames_inv s h ah j fr HF) as (Hu & Hj & Hfr).
    assert (Uh : usedX X s h ah) by (exact (usedX_of_MT h ah (proj1 (used_metas_iff s h ah ND) Hu))).
    destruct (ufacts_X h ah Uh) as (Sh & Lh & Oh).
    pose proof (inv_groups HI h ah Uh) as (_ & _ & Gsl & _). pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & _).
    destruct (marker_cells_span ah j fr c ltac:(lia) N0 F0 Hc') as (qc & Eq & Hq1 & Hq2 & Hq3).
    exists qc. split; [exact Eq|].
    destruct (Nat.eq_dec (prid qc) (prid (am_mem aq))) as [Erc|Erc]; [|left; exact Erc]. right.
    rewrite Hq1, prid_slot_start in Erc.
    pose proof (slot_in_span X R U s HI h ah j Uh Hj) as [SJ1 SJ2].
    destruct (sptr_eq_dec h q) as [<-|Hhq].
    + pose proof (usedX_fun _ _ _ _ _ Uq Uh) as ->. right. unfold UNIT, IB in *. lia.
    + destruct (inv_laminar HI h ah q aq Uh Uq Hhq Erc) as [D | [I | I]].
      * unfold spans_disjoint in D. destruct D as [D|D]; [|right; unfold UNIT, IB in *; lia].
        destruct (Z.eq_dec (poff (am_mem ah) + group_extent ah) (poff (am_mem aq))) as [E|E].
        -- exfalso. exact (adjacency_impossible_X h ah q aq Uh Uq Hhq Erc E).
        -- left. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start X R U s HI h ah j q aq Uh Uq Hj I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (slot_in_span X R U s HI q aq k Uq Hk) as [SK1 _]. right. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start X R U s HI q aq 0 h ah Uq Uh ltac:(lia) I) as (k & fr' & Hk & Hfr' & Kfr' & A & B).
        pose proof (poff_slot_start aq 0) as E0. rewrite Z.mul_0_r in E0.
        destruct (Z.eq_dec k j) as [->|Hkj].
        -- exfalso. rewrite Hfr in Hfr'. injection Hfr' as <-. rewrite Kfr in Kfr'. discriminate.
        -- destruct (same_group_starts ah k j Hkj Sh); unfold UNIT, IB in *; lia.
  - assert (Uh : usedX X s h ah) by (exact (usedX_of_MT h ah (proj1 (used_metas_iff s h ah ND) Hu))).
    destruct (ufacts_X h ah Uh) as (Sh & Lh & Oh).
    exists (slot_end ah (am_last ah)). split; [reflexivity|]. unfold gend_cell. cbn [mc_w Z.of_nat Pos.of_succ_nat].
    unfold slot_end. rewrite prid_padd, poff_padd, prid_slot_start. pose proof (st_last ah) as EL.
    destruct (Nat.eq_dec (prid (am_mem ah)) (prid (am_mem aq))) as [Erc|Erc]; [|left; exact Erc]. right.
    pose proof (ext28_X h ah Uh) as Xh. pose proof (ext28_X q aq Uq) as Xq'.
    destruct (sptr_eq_dec h q) as [<-|Hhq].
    + pose proof (usedX_fun _ _ _ _ _ Uq Uh) as ->. right. unfold IB in *. lia.
    + destruct (inv_laminar HI h ah q aq Uh Uq Hhq Erc) as [D | [I | I]].
      * unfold spans_disjoint in D. destruct D as [D|D]; [|right; unfold IB in *; lia].
        destruct (Z.eq_dec (poff (am_mem ah) + group_extent ah) (poff (am_mem aq))) as [E|E].
        -- exfalso. exact (adjacency_impossible_X h ah q aq Uh Uq Hhq Erc E).
        -- left. unfold IB in *. lia.
      * destruct (inside_slot_start X R U s HI h ah (am_last ah) q aq Uh Uq ltac:(lia) I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (slot_in_span X R U s HI q aq k Uq Hk) as [SK1 _]. right. unfold UNIT, IB in *. lia.
      * destruct (inside_slot_start X R U s HI q aq 0 h ah Uq Uh ltac:(lia) I) as (k & fr' & Hk & _ & _ & A & B).
        pose proof (poff_slot_start aq 0) as E0. rewrite Z.mul_0_r in E0.
        destruct (Z.eq_dec k (am_last ah)) as [->|Hkj]; [right; unfold UNIT, IB in *; lia|].
        destruct (same_group_starts ah k (am_last ah) Hkj Sh); unfold UNIT, IB in *; lia.
Qed.

End GX.
