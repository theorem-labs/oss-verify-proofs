(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "mul"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "loc"; "mc_loc"; "mc_w"; "Inv"; "frame_ptr"; "usedX"; "group_extent"; "used_metas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "ameta"; "frame"; "sptr"; "padd"; "poff"; "IB"; "am_mem"; "fr_n"; "stride_of"; "FUser"; "UNIT"; "am_last"; "fkind"; "fr_kind"; "fr_off"; "nth_slot"; "slot_start"; "ss_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "group_footer_cells"; "footer_cells"; "frame_footer_cells"; "reserved_of"; "@Corelib.Init.Datatypes"; "option"; "Some"; "nat"; "pair"; "prod"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain MallocFooter.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma In_group_footer_cells X R U s g am c : ltac2:(tb__ "0|1|
S11VX;VR;VU;Vs;A4S13VX;Vs;Vg;Vam;A4SbScVc;S28Vam;A1A3S7SaSaS5S6SeSfVc;A1SdS19S1cVam;A1R1A2A1A3S5S0Z0R1A2S5S0S1R1S2S10Vc;A1M0A1A2S1S14Vam;A1S1bA2A2S8S6S2eG0U0A3A1A2A2A2Ld;A2F_;F_;F_;").
Proof.
  intros HI Hu Hin. pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Glast & _) & _ & Gsl & _).
  assert (Ess : forall i d, padd (slot_start am i) d = padd (am_mem am) (UNIT + stride_of am * i + d)).
  { intros i d. unfold slot_start. destruct (am_mem am); cbn. f_equal. lia. }
  assert (Efp : forall i fr d, padd (frame_ptr am i fr) d = padd (am_mem am) (UNIT + stride_of am * i + UNIT * fr_off fr + d)).
  { intros i fr d. unfold frame_ptr, slot_start. destruct (am_mem am); cbn. f_equal. lia. }
  assert (Ese : forall i d, padd (slot_end am i) d = padd (am_mem am) (UNIT + stride_of am * i + (stride_of am - IB) + d)).
  { intros i d. unfold slot_end, slot_start. destruct (am_mem am); cbn. f_equal. lia. }
  unfold group_footer_cells in Hin. destruct Hin as [<- | Hin].
  -
    exists (UNIT + stride_of am * (am_last am + 1) - IB). cbn [trailing_cell mc_loc mc_w Z.of_nat Pos.of_succ_nat].
    unfold trailing_loc. split; [reflexivity|]. unfold group_extent, UNIT, IB in *. split; [nia|]. split; [lia|]. discriminate.
  - apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
    destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hin].
    pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
    assert (Hi0 : 0 <= stride_of am * i) by nia.
    assert (Hi1 : stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    unfold frame_footer_cells in Hin. destruct (fr_kind fr); [|destruct Hin].
    apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
    + destruct (0 <? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er. unfold reserved_of in Er.
      destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Efp.
      eexists. split; [reflexivity|]. unfold group_extent, UNIT, IB in *. split; [lia|]. split; [lia|]. discriminate.
    + destruct (5 <=? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.leb_le in Er. unfold reserved_of in Er.
      destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite Ese.
      eexists. split; [reflexivity|]. unfold group_extent, UNIT, IB in *. split; [lia|]. split; [lia|]. discriminate.
    + destruct (5 <? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er. unfold reserved_of in Er.
      destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Ese.
      eexists. split; [reflexivity|]. unfold group_extent, UNIT, IB in *. split; [lia|]. split; [lia|]. discriminate.
Qed.

Lemma In_footer_cells_inv s c : ltac2:(tb__ "0|0|
SbScVc;S29Vs;A1A3S7S18S18S7S16S16S5SbS30S18S16A2S2fS18S16R2R1A4S15Vs;A1A3SbScVc;S28R1A1A3A2Lam;A2Lg;A2F_;").
Proof.
  intros Hin. unfold footer_cells in Hin. apply in_flat_map in Hin as [[g am] [Hg Hc]]. exists g, am. auto.
Qed.

Theorem footer_in_footprint : footer_in_footprint_stmt.
Proof.
  intros s L c HW HL Hin.
  destruct (In_footer_cells_inv s c Hin) as (g & am & Hg & Hc).
  apply (used_metas_usedX s g am HW) in Hg.
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
  destruct (In_group_footer_cells [] None U0 s g am c HW Hg Hc) as (d & E & Hd & Hw & _).
  exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [apply footprint_region_In; assumption|].
  unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. lia.
Qed.

Lemma frame_footer_above_block am i fr c : ltac2:(tb__ "0|3|
S0Z10S1eVam;A1A2S0Z0M0S1dVfr;A1M1A2S0G0S2bVam;Vfr;A2M2A2SbScVc;S2aVam;Vi;Vfr;A3A3S7SaSaS5S6SeSfVc;A1SdS19S12Vam;Vi;Vfr;A3R1A2A1A3S5S0G1R1A2S0S1R1S2S10Vc;A1A1A2S1G1G2A2A2A2A2Ld;A2F_;F_;F_;F_;").
Proof.
  intros Sp Hn Hr Hin.
  assert (Ese : forall d, padd (slot_end am i) d = padd (frame_ptr am i fr) (fr_n fr + reserved_of am fr + d)).
  { intros d. unfold slot_end, frame_ptr, slot_start, reserved_of. destruct (am_mem am); cbn. f_equal. lia. }
  unfold frame_footer_cells in Hin. destruct (fr_kind fr); [|destruct Hin].
  apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - destruct (0 <? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. eexists. split; [reflexivity|]. lia.
  - destruct (5 <=? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.leb_le in Er.
    destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite Ese. eexists. split; [reflexivity|]. lia.
  - destruct (5 <? reserved_of am fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Ese. eexists. split; [reflexivity|]. lia.
Qed.

Lemma footer_cells_vs_body X R U s g am J lo hi c : ltac2:(tb__ "0|6|
S11VX;VR;VU;Vs;A4S13VX;Vs;Vg;Vam;A4S5S0Z0M0VJ;A2S0VJ;S21Vam;A1A2A2SbScVc;S28Vam;A1A3S0S1S1aS26Vam;VJ;A2A1M1S3S20S2cS17A1M2SaLx;S27S25Vam;VJ;A2A1M3S17S24R1A1Lf;G0X2cx2A2A2Vlo;A2S0Vhi;S4S1G1S1eVam;A1A2S1bA2A2S17S6G2G3S2dS17R1A2A3S6S22S23R2A1S1fA3S0Vhi;S1S1aS12Vam;VJ;R3A3A1S1dR3A1A2A2F_;F_;Ff;S7SaSaS5S6SeSfVc;A1SdS19S1cVam;A1M4R1A2A1A3S9S0S1S1S1aG4A1R1A2M5S2S10Vc;A1A1A2Vlo;A2S0Vhi;G5A2A2A2Ld;A2F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu HJ Hin Hlo Hhi Huser.
  pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _ & Gsl & _).
  rewrite poff_slot_start in Hlo, Hhi.
  assert (Hoff0 : 0 <= match ss_fr (nth_slot am J) with Some f => fr_off f | None => 0 end).
  { pose proof (Gsl J HJ) as (_ & _ & S3). destruct (ss_fr (nth_slot am J)) as [f|]; [|lia]. destruct S3 as (_ & _ & (_ & O & _) & _). lia. }
  assert (HJ1 : stride_of am * J + stride_of am <= stride_of am * (am_last am + 1)) by nia.
  unfold group_footer_cells in Hin. destruct Hin as [<- | Hin].
  -
    exists (UNIT + stride_of am * (am_last am + 1) - IB). cbn [trailing_cell mc_loc mc_w Z.of_nat Pos.of_succ_nat].
    unfold trailing_loc. split; [reflexivity|]. right. unfold UNIT, IB in *. lia.
  - apply in_flat_map in Hin as [k [Hk Hin]]. apply In_zseq in Hk.
    destruct (ss_fr (nth_slot am k)) as [fk|] eqn:Efk; [|destruct Hin].
    pose proof (Gsl k ltac:(lia)) as (_ & _ & S3). rewrite Efk in S3. destruct S3 as (_ & _ & (Nk & Ok & Bk & _) & _).
    assert (Hrk : 0 <= reserved_of am fk) by (unfold reserved_of; lia).
    destruct (frame_footer_above_block am k fk c Sp Nk Hrk Hin) as (d0 & E0 & Lo0 & Hi0).
    exists (UNIT + stride_of am * k + UNIT * fr_off fk + d0). split.
    { rewrite E0. unfold frame_ptr, slot_start. destruct (am_mem am); cbn. f_equal. f_equal. lia. }
    assert (Hk0 : 0 <= stride_of am * k) by nia.
    destruct (Z_lt_dec k J) as [Hlt | Hge]; [|destruct (Z_lt_dec J k) as [Hgt | Heq]].
    +
      left. assert (stride_of am * k + stride_of am <= stride_of am * J) by nia.
      unfold reserved_of, UNIT, IB in *. lia.
    +
      right. assert (stride_of am * J + stride_of am <= stride_of am * k) by nia.
      unfold UNIT, IB in *. lia.
    + assert (k = J) as -> by lia. right. rewrite Efk in Hlo.
      destruct (fr_kind fk) eqn:Ekind.
      * specialize (Huser fk Efk Ekind). unfold frame_ptr in Huser. rewrite poff_padd, poff_slot_start in Huser.
        unfold UNIT, IB in *. lia.
      *
        unfold frame_footer_cells in Hin. rewrite Ekind in Hin. destruct Hin.
Qed.

Theorem footer_outside_user_blocks : footer_outside_user_blocks_stmt.
Proof.
  intros s L c b HW HL Hc Hb. pose proof HL as (_ & _ & PW & _).
  destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
  apply (used_metas_usedX s g am HW) in Hg.
  pose proof (inv_groups HW g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  assert (BI : range_incl (block_range L (frame_ptr am i fr, fr_n fr)) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
  { pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (A1 & A2 & A3).
    pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
    unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
    unfold frame_ptr, slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia. }

  assert (VIA : forall e, In e (footprint s) -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg) ->
            range_incl (cell_range L c) (crange L e) -> ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
  { intros e He Hne Hincl.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR Hne) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact Hincl | exact BI].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact BI | exact Hincl]. }
  destruct (In_footer_cells_inv s c Hc) as (g' & am' & Hg' & Hcc).
  apply (used_metas_usedX s g' am' HW) in Hg'.
  destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
  2:{ destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
      destruct (In_group_footer_cells [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw & _).
      apply (VIA (LMem (SP (prid (am_mem am')) 0), rg_len rg')); [apply footprint_region_In; assumption | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep) |].
      unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. lia. }

  assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
            (poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (frame_ptr am i fr) \/
             poff (frame_ptr am i fr) + fr_n fr <= poff (am_mem am') + d) ->
            ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
  { intros d E D. unfold cell_range, block_range, ranges_disjoint, loc_addr. rewrite E. cbn [fst snd].
    unfold frame_ptr, slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
  pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (A1 & A2 & A3).
  destruct (sptr_eq_dec g' g) as [->|Hne].
  + pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
    destruct (footer_cells_vs_body [] None U0 s g am i (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HW Hg Hi Hcc
                ltac:(rewrite Hfr; unfold frame_ptr; rewrite poff_padd; lia) A2) as (d & E & D).
    { intros f Hf _. rewrite Hfr in Hf. injection Hf as <-. lia. }
    exact (GOAL d E D).
  + pose proof (extent_pos _ _ _ _ _ (inv_groups HW g' am' Hg')) as Pa'.
    destruct (inv_laminar HW g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
    * destruct (In_group_footer_cells [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw & _). apply (GOAL d E).
      pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
      unfold spans_disjoint in Dj. unfold frame_ptr in *. rewrite poff_padd in *. unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
    *
      destruct (In_group_footer_cells [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw & _). apply (GOAL d E).
      destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
      destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
      pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
      rewrite Mem0, poff_slot_start in Lo0, Hi0.
      unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
      destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
    *
      destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
      pose proof (inv_groups HW g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
      destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
      pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
      destruct (footer_cells_vs_body [] None U0 s g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HW Hg' Hj' Hcc) as (d & E & D).
      -- rewrite Hfr', Off'. rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
      -- rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
      -- intros f Hf Hkf. rewrite Hfr' in Hf. injection Hf as <-. rewrite Hk' in Hkf. discriminate.
      -- exact (GOAL d E D).
Qed.
