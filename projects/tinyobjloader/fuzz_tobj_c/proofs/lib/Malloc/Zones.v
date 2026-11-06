(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "frame"; "sptr"; "am_mem"; "prid"; "IB"; "nth_slot"; "padd"; "poff"; "ss_fr"; "slot_start"; "am_last"; "region"; "stride_of"; "UNIT"; "fkind"; "fr_kind"; "FUser"; "RkMap"; "SP"; "fr_n"; "fr_off"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "FGroup"; "slotst"; "ss_hdr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "mul"; "of_nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LMem"; "loc"; "MCell"; "VZ"; "ranges_disjoint"; "usedX"; "crange"; "footprint"; "group_extent"; "mc_loc"; "mc_w"; "range_incl"; "cell_range"; "frame_ptr"; "image"; "loc_addr"; "region_of"; "user_blocks"; "WF"; "block_range"; "hdr_byte3"; "hdr_off16"; "ly_reg"; "slot_cells"; "sval"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "pair"; "cons"; "nil"; "bool"; "nat"; "true"; "app"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones"; "zone_range"; "zone_hi"; "zone_lo"; "off_zone"; "own_hdr"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "frame_footer_cells"; "group_footer_cells"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfSurgery MallocWfGeom MallocWfRepr MallocWfMain
  MallocWfGroup MallocFooter MallocFooterLemmas.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zone_lo (am : ameta) (j : Z) : Z := ltac2:(tb__ "0|0|
S24SdSfVam;Vj;A2A1Z3A2").
Definition zone_hi (am : ameta) (j : Z) : Z := ltac2:(tb__ "0|0|
S24S23SdSfVam;Vj;A2A1S12Vam;A1A2SaA2").

Definition own_hdr (am : ameta) (j : Z) : list mcell := ltac2:(tb__ "0|9|
SfVam;Vj;A2S7SbVam;Vj;A2S20S4cS28S43S45S5S5A2M0A1S4dS28A1M1Lx;S21R1A1G0G0G1Lp;R1S5S5S47S28S2bS29ScR5N3M2A2A1U1M3S2cR2A1A3S47S28S2bS29ScR5N2M4A2A1U2M5S2cR1A1A3S48S28A1M6A3A3Lh16;Lh3;X45x1Lp;G6X43x2S43S6A1G1Lx;SeR1A1S6S49G1L_;S27S1aR1A1M7Z0M8A2G6ScR3S25S13G7A2A2S7S47S28S2bS29ScR1N4A2A1G3S2cG8A1A3S47S28S2bS29ScR1G2A2A1G3S2cS3dVam;Vj;R2A3A1A3S47S28S2bS29ScR1G4A2A1G5S2cS3eVam;Vj;R2A3A1A3G6A3A3A3Tp;X49x2Lfr;G6X43x2A3Tsl;Tst;").

Definition off_zone (am : ameta) (j : Z) (p : sptr) (w : Z) : Prop := ltac2:(tb__ "0|1|
S0S4aS9Vp;A1S9S8Vam;A1A1A3S2S22S23SdVp;A1M0Vw;A2S50Vam;Vj;A2A2S22S4fVam;Vj;A2G0A2A2F_;").

Lemma slot_cells_own am j c : ltac2:(tb__ "0|0|
S42S28Vc;S40Vam;Vj;A2A3S2S0S28Vc;S2bS29ScSfVam;Vj;A2N4A2A1U1S2cZ0A1A3A3S42S28Vc;S52Vam;Vj;A2A3A2F_;").
Proof.
  intros Hin. unfold slot_cells in Hin. unfold own_hdr.
  apply in_app_iff in Hin as [Hin|Hin]; [destruct Hin as [<-|[]]; left; reflexivity|].
  right. apply in_app_iff. apply in_app_iff in Hin as [Hin|Hin].
  - left. destruct (ss_hdr (nth_slot am j)) as [[h3 h16]|]; [exact Hin | destruct Hin].
  - right. destruct (ss_fr (nth_slot am j)) as [fr|]; [|destruct Hin].
    destruct (fr_off fr =? 0); [destruct Hin | exact Hin].
Qed.

Lemma LMem_inj a b : ltac2:(tb__ "0|0|
S0S2aS29Va;A1S29Vb;A1A3S0S7Va;Vb;A3F_;").
Proof. intros H. injection H. auto. Qed.

Lemma loc_eq_dec (a b : loc) : ltac2:(tb__ "0|1|
S53S0S2aVa;Vb;A3M0S4G0A1A2").
Proof. decide equality; try apply Z.eq_dec. apply sptr_eq_dec. Defined.

Lemma sval_eq_dec (a b : sval) : ltac2:(tb__ "0|1|
S53S0S41Va;Vb;A3M0S4G0A1A2").
Proof. decide equality; try apply Z.eq_dec. apply sptr_eq_dec. Defined.

Lemma mcell_eq_dec (a b : mcell) : ltac2:(tb__ "0|1|
S53S0S28Va;Vb;A3M0S4G0A1A2").
Proof. decide equality; [apply sval_eq_dec | apply Nat.eq_dec | apply loc_eq_dec]. Defined.

Lemma footer_cell_bound s g am c : ltac2:(tb__ "0|0|
S3bVs;A1S2eS48S7A1Vs;Vg;Vam;A4S42S28Vc;S56Vam;A1A3S3S5S5S1S0S2aS32Vc;A1S29ScS8Vam;A1R1A2A1A3S1S22Z0R1A2S22S23R1S26S33Vc;A1A1A2S23S31Vam;A1Z1A2A2A2A2Ld;A2F_;F_;F_;").
Proof.
  intros HW Hu Hc.
  destruct (In_group_footer_cells [] None U0 s g am c HW Hu Hc) as (d & E & Hd & Hw & _).
  exists d. split; [exact E|]. split; [exact Hd|].
  pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  unfold group_footer_cells in Hc. destruct Hc as [<- | Hc].
  - cbn [trailing_cell mc_loc mc_w] in E |- *. unfold trailing_loc in E.
    assert (d = UNIT + stride_of am * (am_last am + 1) - IB) as ->.
    { apply LMem_inj in E. pose proof (f_equal poff E) as Eo. rewrite !poff_padd in Eo. lia. }
    unfold group_extent. lia.
  - apply in_flat_map in Hc as [k [Hk Hc]]. apply In_zseq in Hk.
    destruct (ss_fr (nth_slot am k)) as [fk|] eqn:Efk; [|destruct Hc].
    pose proof (Gsl k ltac:(lia)) as (_ & _ & S3). rewrite Efk in S3. destruct S3 as (_ & _ & (Nk & Ok & Bk & _) & _).
    assert (Hrk : 0 <= reserved_of am fk) by (unfold reserved_of; lia).
    destruct (frame_footer_above_block am k fk c Sp Nk Hrk Hc) as (d0 & E0 & Lo0 & Hi0).
    rewrite E in E0. apply LMem_inj in E0. pose proof (f_equal poff E0) as Eo. unfold frame_ptr in Eo. rewrite !poff_padd, poff_slot_start in Eo.
    assert (stride_of am * k + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    unfold group_extent, reserved_of, UNIT, IB in *. lia.
Qed.

Section Zone.
  Variables (s : astate) (g : sptr) (am : ameta) (j : Z).
  Hypothesis HW : WF s.
  Hypothesis Hu : ltac2:(tb__ "0|0|
S2eS48S7A1Vs;Vg;Vam;A4").
  Hypothesis Hj : ltac2:(tb__ "0|0|
S1S22Z0Vj;A2S22Vj;S10Vam;A1A2A2").
  Hypothesis Hng : ltac2:(tb__ "0|0|
S6S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S0S14S15R2A1S16A3F_;Ffr;").

  Lemma Zgeom : ltac2:(tb__ "0|6|
S1S22Z10S12Vam;A1M0A2S1S22Z0M1SdS8Vam;A1A1M2A2S1S0S5S50Vam;Vj;A2S24S23S23G2S13A2S25G0Vj;A2M3A2M4Z3A2A3S1S0S5S4fVam;Vj;A2S24S23G4G0A2SaA2A3S1S22G1G3A2S1S22S23G3G0A2S25G0S23S10Vam;A1Z1A2A2M5A2S0S5S31Vam;A1S24S23S13G5A2SaA2A3A2A2A2A2A2A2").
  Proof using HW Hj Hu.
    pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    destruct (used_group_region [] None U0 s g am HW Hu) as (rg & _ & _ & _ & Ho & _).
    unfold zone_lo, zone_hi. rewrite !poff_slot_start. unfold group_extent.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [nia|]. split; [nia|]. reflexivity.
  Qed.

  Lemma other_slot_off k : ltac2:(tb__ "0|1|
S1S22Z0Vk;A2S22Vk;S10Vam;A1A2A2S4S0S5Vk;Vj;A3A1S2S22S23S24S23SdSfVam;Vk;A2A1M0S12Vam;A1A2SaA2Z1A2S50Vam;Vj;A2A2S22S4fVam;Vj;A2S24G0SaA2A2A2F_;F_;").
  Proof using HW Hj Hu.
    intros Hk Hne. pose proof Zgeom as (Sp & _ & Ezlo & Ezhi & _). rewrite Ezlo, Ezhi. rewrite poff_slot_start.
    assert (k < j \/ j < k) as [H|H] by lia.
    - left. assert (stride_of am * k + stride_of am <= stride_of am * j) by nia. unfold UNIT, IB in *. lia.
    - right. assert (stride_of am * j + stride_of am <= stride_of am * k) by nia. unfold UNIT, IB in *. lia.
  Qed.

  Lemma other_group_cases g' am' : ltac2:(tb__ "0|8|
S2eS48S7A1Vs;Vg';Vam';A4S4S0S7Vg';Vg;A3A1S0S4aS9S8Vam';A1M0A1S9S8Vam;A1A1A3S2S2S22S23S23SdG0A1M1S31Vam';A1A2M2Z1A2S50Vam;Vj;A2M3A2S22S4fVam;Vj;A2M4G1A2A2S2S3S5S5S1S1S22Z0M5R1A2S22R1S10Vam;A1A2A2S1S4S0S5R1Vj;A3A1S1S22SdSfVam;R1A2A1M6G1A2S22G2S24S23G6S12Vam;A1A2SaA2A2A2A2A2Lj0;A2S3S5S5S3S6S6S1S1S22G5R2A2S22R2S10Vam';A1A2A2S1S0S43S6A1SeSbVam';R2A2A1S44S6R1A2A3S1S0S14S15R1A1S1fA3S1S0S5S1aR1A1G5A3S1S22SdSfVam';R2A2A1M7G3A2S22G4S24S23G7S12Vam';A1A2SaA2A2A2A2A2A2A2LfrJ;A2LJ;A2A2A2F_;F_;F_;").
  Proof using HW Hj Hng Hu.
    intros Hu' Hne Hr. pose proof Zgeom as (Sp & Ho & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    pose proof (inv_groups HW g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'.
    pose proof (extent_pos _ _ _ _ _ G') as Ep'.
    destruct (inv_laminar HW g' am' g am Hu' Hu Hne Hr) as [D | [I | I]].
    - left. unfold spans_disjoint in D. destruct D as [D|D].
      + left.

        pose proof (used_group_aligned [] None U0 s HW _ g am Hu (PeanoNat.Nat.le_refl _)) as M16.
        pose proof (used_group_aligned [] None U0 s HW _ g' am' Hu' (PeanoNat.Nat.le_refl _)) as M16'.
        pose proof (stride_mod16 _ _ _ _ _ _ HW Hu') as S16'.
        apply Z.div_exact in M16; [|lia]. apply Z.div_exact in M16'; [|lia]. apply Z.div_exact in S16'; [|lia].
        set (q := stride_of am' / 16) in *. set (m1 := poff (am_mem am) / 16) in *. set (m2 := poff (am_mem am') / 16) in *.
        clearbody q m1 m2.
        rewrite Ezlo. unfold group_extent in D |- *. rewrite M16, M16', S16' in *. unfold UNIT, IB in *. nia.
      + right. rewrite Ezhi. rewrite Eext in D. unfold UNIT, IB in *. lia.
    - right; left. destruct I as (j0 & fr0 & c & ac & Hj0r & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi & Fit).
      exists j0. split; [exact Hj0r|]. split.
      { intros ->. rewrite (Hng fr0 Hfr0) in Hk0. discriminate. }
      pose proof (f_equal poff Memc) as Eo.
      destruct (fgroup_frame [] None U0 s HW g am j0 fr0 Hu Hj0r Hfr0 Hk0) as [Fn _].
      lia.
    - right; right. destruct I as (J & frJ & c & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi & Fit).
      exists J, frJ. destruct (fgroup_frame [] None U0 s HW g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
      repeat (split; [assumption|]). pose proof (f_equal poff Memc) as Eo.
      rewrite Ezlo, Ezhi. rewrite Eext in Hi. unfold UNIT, IB in *. lia.
  Qed.

  Theorem zone_image c p : ltac2:(tb__ "0|0|
S42S28Vc;S37Vs;A1A3S0S2aS32Vc;A1S29Vp;A1A3S2S42S28Vc;S52Vam;Vj;A2A3S51Vam;Vj;Vp;S26S33Vc;A1A1A4A2F_;F_;").
  Proof using HW Hj Hng Hu.
    intros Hin Hloc.
    destruct (in_dec mcell_eq_dec c (own_hdr am j)) as [Hown|Hown]; [left; exact Hown | right]. intros Hr. pose proof Zgeom as (Sp & Ho & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    destruct (In_image_inv s c Hin) as [Hc | [(a & next & Ha & Hc) | (g' & am' & Hg' & Hc)]].
    - destruct (In_ctx_cells s c Hc) as (off & E & _). rewrite Hloc in E. discriminate.
    -
      exfalso. destruct (In_area_cells s a next c Hc) as (d & E & _). rewrite Hloc in E. injection E as ->.
      rewrite prid_padd in Hr.
      pose proof (inv_areas HW) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & _ & Hra & _ & _ & Hkind).
      destruct (used_group_region [] None U0 s g am HW Hu) as (rg & Hrg & Hk & _).
      subst a. cbn [prid] in Hr. subst ra. rewrite Hrg in Hra. injection Hra as ->. rewrite Hk in Hkind. exact Hkind.
    - apply (used_metas_usedX s g' am' HW) in Hg'.
      destruct (sptr_eq_dec g' g) as [->|Hne].
      + pose proof (usedX_fun _ _ _ _ _ Hg' Hu) as ->.
        unfold group_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
        *
          rewrite Ezlo. left.
          destruct Hc as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hloc |- *.
          -- injection Hloc as <-. unfold UNIT. lia.
          -- destruct (am_maplen am =? 0); cbn [mc_loc mc_w] in Hloc |- *; injection Hloc as <-; rewrite poff_padd; unfold UNIT; lia.
        * apply in_flat_map in Hc as [k [Hk Hc]]. apply In_zseq in Hk.
          destruct (Z.eq_dec k j) as [->|Hkj].
          --
             destruct (slot_cells_own am j c Hc) as [-> | Hown']; [|exfalso; exact (Hown Hown')].
             cbn [mc_loc mc_w] in Hloc |- *. injection Hloc as <-. rewrite poff_padd. rewrite Ezlo, poff_slot_start. left. lia.
          -- destruct (In_slot_cells [] None U0 s g am k c HW Hu ltac:(lia) Hc) as (d & E & Lo & Hiw & _).
             rewrite Hloc in E. injection E as ->. rewrite poff_padd.
             destruct (other_slot_off k ltac:(lia) Hkj) as [X|X]; rewrite poff_slot_start in X; [left|right]; lia.
      + assert (Hr' : prid (am_mem am') = prid (am_mem am)).
        { destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hc) as (d & E & _). rewrite Hloc in E. injection E as ->.
          rewrite prid_padd in Hr. exact Hr. }
        destruct (other_group_cases g' am' Hg' Hne Hr') as [D | [(j0 & Hj0r & Hj0ne & Lo & Hi) | (J & frJ & HJ & HfrJ & HkJ & OffJ & Lo & Hi)]].
        * destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
          rewrite Hloc in E. injection E as ->. rewrite poff_padd. destruct D; [left|right]; lia.
        * destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
          rewrite Hloc in E. injection E as ->. rewrite poff_padd.
          destruct (other_slot_off j0 Hj0r Hj0ne) as [X|X]; [left|right]; unfold UNIT, IB in *; lia.
        * destruct (group_cells_vs_body [] None U0 s g' am' J (zone_lo am j) (zone_hi am j) c HW Hg' HJ Hc
                      ltac:(rewrite HfrJ, OffJ; lia) Hi) as (d & E & D).
          rewrite Hloc in E. injection E as ->. rewrite poff_padd. exact D.
  Qed.

  Theorem zone_footer c p : ltac2:(tb__ "0|0|
S42S28Vc;S54Vs;A1A3S0S2aS32Vc;A1S29Vp;A1A3S2S3S6S6S1S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S42S28Vc;S55Vam;Vj;R1A3A3A2Lfr;A2S51Vam;Vj;Vp;S26S33Vc;A1A1A4A2F_;F_;").
  Proof using HW Hj Hng Hu.
    intros Hin Hloc.
    destruct (Nat.eq_dec (prid p) (prid (am_mem am))) as [Hr|Hr]; [| right; intros H; exfalso; exact (Hr H)].
    pose proof Zgeom as (Sp & Ho & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    destruct (In_footer_cells_inv s c Hin) as (g' & am' & Hg' & Hc).
    apply (used_metas_usedX s g' am' HW) in Hg'.
    destruct (sptr_eq_dec g' g) as [->|Hne].
    - pose proof (usedX_fun _ _ _ _ _ Hg' Hu) as ->.
      pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _).
      unfold group_footer_cells in Hc. destruct Hc as [<- | Hc].
      +
        right. intros _.
        cbn [trailing_cell mc_loc mc_w] in Hloc |- *. injection Hloc as <-. unfold trailing_loc. rewrite poff_padd.
        right. rewrite Ezhi. unfold UNIT, IB in *. lia.
      + apply in_flat_map in Hc as [k [Hk Hc]]. apply In_zseq in Hk.
        destruct (ss_fr (nth_slot am k)) as [fk|] eqn:Efk; [|destruct Hc].
        destruct (Z.eq_dec k j) as [->|Hkj].
        * left. exists fk. split; [exact Efk | exact Hc].
        * right. intros _.
          pose proof (Gsl k ltac:(lia)) as (_ & _ & S3). rewrite Efk in S3. destruct S3 as (_ & _ & (Nk & Ok & Bk & _) & _).
          assert (Hrk : 0 <= reserved_of am fk) by (unfold reserved_of; lia).
          destruct (frame_footer_above_block am k fk c Sp Nk Hrk Hc) as (d0 & E0 & Lo0 & Hi0).
          rewrite Hloc in E0. injection E0 as ->. unfold frame_ptr. rewrite !poff_padd.
          destruct (other_slot_off k ltac:(lia) Hkj) as [X|X]; [left|right]; unfold reserved_of, UNIT, IB in *; lia.
    - right. intros _.
      assert (Hr' : prid (am_mem am') = prid (am_mem am)).
      { destruct (In_group_footer_cells [] None U0 s g' am' c HW Hg' Hc) as (d & E & _). rewrite Hloc in E. injection E as ->.
        rewrite prid_padd in Hr. exact Hr. }
      destruct (other_group_cases g' am' Hg' Hne Hr') as [D | [(j0 & Hj0r & Hj0ne & Lo & Hi) | (J & frJ & HJ & HfrJ & HkJ & OffJ & Lo & Hi)]].
      + destruct (footer_cell_bound s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
        rewrite Hloc in E. injection E as ->. rewrite poff_padd. destruct D; [left|right]; unfold IB in *; lia.
      + destruct (footer_cell_bound s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
        rewrite Hloc in E. injection E as ->. rewrite poff_padd.
        destruct (other_slot_off j0 Hj0r Hj0ne) as [X|X]; [left|right]; unfold IB in *; lia.
      + destruct (footer_cells_vs_body [] None U0 s g' am' J (zone_lo am j) (zone_hi am j) c HW Hg' HJ Hc
                    ltac:(rewrite HfrJ, OffJ; lia) Hi
                    ltac:(intros f Hf Hkf; rewrite HfrJ in Hf; injection Hf as <-; rewrite HkJ in Hkf; discriminate)) as (d & E & D).
        rewrite Hloc in E. injection E as ->. rewrite poff_padd. exact D.
  Qed.

  Theorem zone_block q n : ltac2:(tb__ "0|0|
S42S45S7S5A2S46S7S5Vq;Vn;A4S3aVs;A1A3S2S3S6S6S1S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S1S0S7Vq;S36Vam;Vj;R1A3A3S0S5Vn;S19R1A1A3A2A2Lfr;A2S51Vam;Vj;Vq;Vn;A4A2F_;").
  Proof using HW Hj Hng Hu.
    intros Hin.
    destruct (Nat.eq_dec (prid q) (prid (am_mem am))) as [Hr|Hr]; [| right; intros H; exfalso; exact (Hr H)].
    pose proof Zgeom as (Sp & Ho & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    destruct (in_user_blocks_inv s _ Hin) as (g' & am' & k & f & Hg' & Hk & Hf & Hkf & E). injection E as -> ->.
    apply (used_metas_usedX s g' am' HW) in Hg'.
    pose proof (block_in_slot s g' am' k f HW Hg' Hk Hf) as (B1 & B2 & B3).
    destruct (sptr_eq_dec g' g) as [->|Hne].
    - pose proof (usedX_fun _ _ _ _ _ Hg' Hu) as ->.
      destruct (Z.eq_dec k j) as [->|Hkj].
      { left. exists f. auto. }
      right. intros _.
      destruct (other_slot_off k Hk Hkj) as [X|X]; [left|right]; unfold IB in *; lia.
    - right. intros _.
      assert (Hr' : prid (am_mem am') = prid (am_mem am)).
      { unfold frame_ptr, slot_start in Hr. rewrite !prid_padd in Hr. exact Hr. }
      pose proof (slot_in_span [] None U0 s HW g' am' k Hg' Hk) as [S1 S2].
      destruct (other_group_cases g' am' Hg' Hne Hr') as [D | [(j0 & Hj0r & Hj0ne & Lo & Hi) | (J & frJ & HJ & HfrJ & HkJ & OffJ & Lo & Hi)]].
      + destruct D; [left|right]; unfold IB, UNIT in *; lia.
      + destruct (other_slot_off j0 Hj0r Hj0ne) as [X|X]; [left|right]; unfold IB, UNIT in *; lia.
      +
        destruct (Z.eq_dec k J) as [->|HkJ'].
        { rewrite HfrJ in Hf. injection Hf as ->. rewrite HkJ in Hkf. discriminate. }
        pose proof (stride_pos _ _ _ _ _ (inv_groups HW g' am' Hg')) as Sp'.
        destruct (same_group_starts am' k J HkJ' Sp') as [X|X]; [left|right]; unfold IB, UNIT in *; lia.
  Qed.
End Zone.

Definition zone_range (L : layout) (am : ameta) (j : Z) : Z * Z := ltac2:(tb__ "0|2|
S46S5S5S24S23S23S38VL;S29S8Vam;A1A1A2S13A2S25S12Vam;A1M0Vj;A2A2Z3M1A2S23S24G0SaA2G1A2A4").

Lemma zone_range_eq L am j : ltac2:(tb__ "0|1|
S0S45S5S5A2S4eVL;Vam;Vj;A3S46S5S5S23S3fVL;S9S8Vam;A1A1A2S50Vam;Vj;A2M0A2S24S4fVam;Vj;A2G0A2A4A3").
Proof.
  unfold zone_range, zone_lo, zone_hi, loc_addr. rewrite poff_slot_start. destruct (am_mem am) as [r o]. cbn [prid poff].
  f_equal; lia.
Qed.

Section ZoneAddr.
  Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (j : Z).
  Hypothesis HW : WF s.
  Hypothesis HL : layout_ok L s.
  Hypothesis Hu : ltac2:(tb__ "0|0|
S2eS48S7A1Vs;Vg;Vam;A4").
  Hypothesis Hj : ltac2:(tb__ "0|0|
S1S22Z0Vj;A2S22Vj;S10Vam;A1A2A2").
  Hypothesis Hng : ltac2:(tb__ "0|0|
S6S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S0S14S15R2A1S16A3F_;Ffr;").

  Lemma zone_entry : ltac2:(tb__ "0|2|
S3S11S11S1S0S43S11A1S39Vs;S9S8Vam;A1A1M0A2S44S11R1A2A3S1S0S1eS1bR1A1S17A3S1S0S49S1dR1A1S4bA3S1S42S45S2aS5A2S46S2aS5S29S18G0Z0A2A1S1cR1A1A4M1S30Vs;A1A3S34S4eVL;Vam;Vj;A3S2fVL;G1A2A2A2A2A2A2Lrg;A2").
  Proof using HW Hj Hu.
    destruct (used_group_region [] None U0 s g am HW Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    exists rg. repeat (split; [assumption|]). split; [apply footprint_region_In; assumption|].
    pose proof (Zgeom s g am j HW Hu Hj) as (Sp & _ & Ezlo & Ezhi & Hj0 & Hj1 & Eext).
    rewrite zone_range_eq. unfold range_incl, crange, loc_addr. cbn [fst snd]. rewrite Ezlo, Ezhi.
    unfold UNIT, IB in *. lia.
  Qed.

  Lemma off_zone_addr p w : ltac2:(tb__ "0|0|
S22Z0Vw;A2S51Vam;Vj;Vp;Vw;A4S0S4aS9Vp;A1S9S8Vam;A1A1A3S2dS46S5S5S38VL;S29Vp;A1A2Vw;A4S4eVL;Vam;Vj;A3A2F_;F_;F_;").
  Proof using .
    intros Hw Hoz Hr. specialize (Hoz Hr). rewrite zone_range_eq.
    unfold ranges_disjoint, loc_addr. destruct p as [r o]. cbn [fst snd prid poff] in *. subst r. lia.
  Qed.

  Lemma other_entry_addr e (rng : Z * Z) rg : ltac2:(tb__ "0|2|
S42S45S2aS5A2M0Ve;S30Vs;A1A3S34Vrng;S2fVL;Ve;A2A2S0S43S11A1S39Vs;S9S8Vam;A1A1M1A2S44S11Vrg;A2A3S0S1eS1bVrg;A1S17A3S0S49S1dVrg;A1S4bA3S4S0G0Ve;S46S2aS5S29S18G1Z0A2A1S1cVrg;A1A4A3A1S2dVrng;S4eVL;Vam;Vj;A3A2F_;F_;F_;F_;F_;F_;").
  Proof using HL HW Hj Hu.
    intros He Hincl Hr Hk Hl Hne. pose proof HL as (_ & _ & PW & _).
    destruct zone_entry as (rg' & Hr' & _ & _ & InR & ZI). rewrite Hr in Hr'. injection Hr' as <-.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR Hne) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact Hincl | exact ZI].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact ZI | exact Hincl].
  Qed.

  Theorem zone_image_addr c : ltac2:(tb__ "0|0|
S42S28Vc;S37Vs;A1A3S2S42S28Vc;S52Vam;Vj;A2A3S2dS35VL;Vc;A2S4eVL;Vam;Vj;A3A2A2F_;").
  Proof using HL HW Hj Hng Hu.
    intros Hin.
    destruct (in_dec mcell_eq_dec c (own_hdr am j)) as [Hown|Hown]; [left; exact Hown | right].
    destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    destruct (In_image_inv s c Hin) as [Hc | [(a & next & Ha & Hc) | (g' & am' & Hg' & Hc)]].
    - destruct (In_ctx_cells s c Hc) as (off & E & Ho' & Hw).
      apply (other_entry_addr (LCtx 0, CTX_SIZE) _ rg); [left; reflexivity | | exact Hr | exact Hk | exact Hl | discriminate].
      unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
    - destruct (In_area_cells s a next c Hc) as (d & E & Hd & Hw).
      pose proof (inv_areas HW) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
      apply (other_entry_addr (LMem a, PGSZ) _ rg); [| | exact Hr | exact Hk | exact Hl |].
      + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
      + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
      + rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
    - apply (used_metas_usedX s g' am' HW) in Hg'.
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
      + destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
        destruct (zone_image s g am j HW Hu Hj Hng c _ Hin E) as [Hown' | Hoz]; [exfalso; exact (Hown Hown')|].
        unfold cell_range. rewrite E.
        apply off_zone_addr; [lia | exact Hoz | rewrite prid_padd; exact Hsame].
      + destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
        destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hc) as (d & E & Hd & Hw).
        apply (other_entry_addr (LMem (SP (prid (am_mem am')) 0), rg_len rg') _ rg);
          [apply footprint_region_In; assumption | | exact Hr | exact Hk | exact Hl | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep)].
        unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia.
  Qed.

  Theorem zone_footer_addr c : ltac2:(tb__ "0|0|
S42S28Vc;S54Vs;A1A3S2S3S6S6S1S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S42S28Vc;S55Vam;Vj;R1A3A3A2Lfr;A2S2dS35VL;Vc;A2S4eVL;Vam;Vj;A3A2A2F_;").
  Proof using HL HW Hj Hng Hu.
    intros Hin.
    destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    destruct (In_footer_cells_inv s c Hin) as (g' & am' & Hg' & Hc).
    apply (used_metas_usedX s g' am' HW) in Hg'.
    destruct (In_group_footer_cells [] None U0 s g' am' c HW Hg' Hc) as (d & E & Hd & Hw & _).
    destruct (zone_footer s g am j HW Hu Hj Hng c _ Hin E) as [Hown | Hoz]; [left; exact Hown | right].
    destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
    - unfold cell_range. rewrite E.
      apply off_zone_addr; [lia | exact Hoz | rewrite prid_padd; exact Hsame].
    - destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
      apply (other_entry_addr (LMem (SP (prid (am_mem am')) 0), rg_len rg') _ rg);
        [apply footprint_region_In; assumption | | exact Hr | exact Hk | exact Hl | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep)].
      unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. lia.
  Qed.

  Theorem zone_block_addr q n : ltac2:(tb__ "0|1|
S42S45S7S5A2S46S7S5Vq;Vn;A4M0S3aVs;A1A3S2S3S6S6S1S0S43S6A1SeSbVam;Vj;A2A1S44S6R1A2A3S1S0S7Vq;S36Vam;Vj;R1A3A3S0S5Vn;S19R1A1A3A2A2Lfr;A2S2dS3cVL;G0A2S4eVL;Vam;Vj;A3A2A2F_;").
  Proof using HL HW Hj Hng Hu.
    intros Hin.
    destruct zone_entry as (rg & Hr & Hk & Hl & InR & ZI).
    destruct (in_user_blocks_inv s _ Hin) as (g' & am' & k & f & Hg' & Hk' & Hf & Hkf & E). injection E as Eq En.
    apply (used_metas_usedX s g' am' HW) in Hg'.
    destruct (zone_block s g am j HW Hu Hj Hng q n Hin) as [Hown | Hoz]; [left; exact Hown | right].
    destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
    - unfold block_range. cbn [fst snd].
      pose proof (block_in_slot s g' am' k f HW Hg' Hk' Hf) as (_ & _ & B3).
      apply off_zone_addr; [subst; exact B3 | exact Hoz | rewrite Eq; unfold frame_ptr, slot_start; rewrite !prid_padd; exact Hsame].
    - destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
      pose proof (block_in_slot s g' am' k f HW Hg' Hk' Hf) as (B1 & B2 & B3).
      pose proof (slot_in_span [] None U0 s HW g' am' k Hg' Hk') as [S1 S2].
      apply (other_entry_addr (LMem (SP (prid (am_mem am')) 0), rg_len rg') _ rg);
        [apply footprint_region_In; assumption | | exact Hr | exact Hk | exact Hl | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep)].
      unfold block_range, crange, range_incl, loc_addr. rewrite Eq, En. cbn [fst snd].
      unfold frame_ptr, slot_start in *. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB, UNIT in *. lia.
  Qed.

  Lemma zone_in_footprint : ltac2:(tb__ "0|1|
S3S45S2aS5A2M0G0S1S42G0R1S30Vs;A1A3S34S4eVL;Vam;Vj;A3S2fVL;R1A2A2A2Lrg;A2").
  Proof using HW Hj Hu. destruct zone_entry as (rg & _ & _ & _ & InR & ZI). eexists. split; [exact InR | exact ZI]. Qed.
End ZoneAddr.
