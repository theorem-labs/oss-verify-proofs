(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "Inv"; "image"; "usedX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "frame"; "am_last"; "nth_slot"; "slot_start"; "ss_fr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Init.Datatypes"; "None"; "app"; "option"; "@Corelib.Init.Logic"; "False"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocWfGeom MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FSZ.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S1VX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.

  Theorem free_slot_zone q aq j c : ltac2:(tb__ "0|0|
S3VX;Vs;Vq;Vaq;A4SeS9Z0Vj;A2S9Vj;S5Vaq;A1A2A2SfScS4A1S8S6Vaq;Vj;A2A1SaS4A1A3S13S0Vc;SbS0S2Vs;A1S10Vs;A1A3A3S12VL;Vc;S11VL;S7Vaq;Vj;A2A2Z8A4SdF_;F_;F_;F_;F_;").
  Proof using HI HL HX.
    intros Hu Hj Hfr Hin Hm.
    pose proof (inv_groups HI q aq Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof (extent_pos _ _ _ _ _ G) as EP0.
    pose proof G as ((Glast & _) & _).
    pose proof (poff_slot_start aq j) as PS.
    assert (SJ : 0 <= stride_of aq * j /\ stride_of aq * (j + 1) <= stride_of aq * (am_last aq + 1)) by nia.
    assert (EXT : poff (slot_start aq j) + stride_of aq - IB <= poff (am_mem aq) + group_extent aq).
    { rewrite PS. unfold group_extent, UNIT, IB in *. nia. }
    destruct (used_group_region X R U s q aq HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as ER.
    assert (AS : addr_of L (slot_start aq j) = ly_reg L (prid (am_mem aq)) + poff (slot_start aq j)).
    { unfold addr_of, loc_addr, slot_start. destruct (am_mem aq) as [r o]. cbn [padd prid poff]. reflexivity. }
    assert (ZI : range_incl (addr_of L (slot_start aq j), 8) (crange L (e_reg (prid (am_mem aq)) rg))).
    { unfold range_incl, crange, e_reg. cbn [fst snd]. unfold loc_addr. rewrite AS, PS. unfold group_extent, UNIT, IB in *. nia. }
    destruct (cell_cases X R U s HI HX c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g' & am' & Hu' & Hc)]].
    - refine (meet_entries s L HL c e_ctx _ _ _ (e_ctx_In s) ER _ (ctx_cell_in s L c Hc) ZI Hm). discriminate.
    - refine (meet_entries s L HL c (e_area a') _ _ _ (e_area_In s a' Ha') ER _ (area_cell_in s L a' next c Hc) ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin X R U s HI a' Ha') as Z0. rewrite Ea in Z0. exact (Z0 eq_refl).
    -
      destruct Hm as (kk & Hkk & Hmk). rewrite AS in Hmk.
      assert (OWN : forall lo hi, (exists d, mc_loc c = LMem (padd (am_mem am') d) /\ (poff (am_mem am') + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am') + d)) ->
                    prid (am_mem am') = prid (am_mem aq) -> lo <= poff (slot_start aq j) -> poff (slot_start aq j) + 8 <= hi -> False).
      { intros lo hi (d & E & D) Ep Hlo Hhi. rewrite E in Hmk. unfold loc_addr in Hmk.
        destruct (am_mem am') as [r' o'] eqn:Em'. cbn [padd prid poff] in *. rewrite Ep in Hmk. lia. }
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem aq))) as [Ep | Np].
      2:{ destruct (group_cell_in X R U s L HI g' am' c Hu' Hc) as (rg' & Hr' & Hk' & Hl' & ER' & RI' & _).
          refine (meet_entries s L HL c (e_reg (prid (am_mem am')) rg') _ _ _ ER' ER _ RI' ZI ltac:(exists kk; split; [exact Hkk | rewrite AS; exact Hmk])).
          unfold e_reg. intros E2. injection E2 as Er _. exact (Np Er). }
      destruct (sptr_eq_dec g' q) as [-> | Hne].
      +
        pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
        assert (B1 : poff (slot_start aq j) + UNIT * match ss_fr (nth_slot aq j) with Some f => fr_off f | None => 0 end <= poff (slot_start aq j)).
        { rewrite Hfr. rewrite Z.mul_0_r, Z.add_0_r. apply Z.le_refl. }
        assert (B2 : poff (slot_start aq j) + 8 <= poff (slot_start aq j) + stride_of aq - IB) by (unfold IB in *; lia).
        apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + 8)); [| exact Ep | lia | lia].
        destruct Hc as [Hc | Hc].
        * exact (group_cells_vs_body X R U s q aq j _ _ c HI Hu Hj Hc B1 B2).
        * exact (footer_cells_vs_body X R U s q aq j _ _ c HI Hu Hj Hc B1 B2 ltac:(intros f Hf; rewrite Hfr in Hf; discriminate Hf)).
      + pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'. pose proof (extent_pos _ _ _ _ _ G') as EP1.
        destruct (group_cell_in X R U s L HI g' am' c Hu' Hc) as (_ & _ & _ & _ & _ & _ & (d & E & Hd & Hw)).
        destruct (inv_laminar HI g' am' q aq Hu' Hu Hne Ep) as [D | [I | I]].
        *
          apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + 8)); [| exact Ep | lia | lia].
          exists d. split; [exact E|]. unfold spans_disjoint in D. rewrite PS. unfold group_extent, UNIT, IB in *. nia.
        *
          destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi & Fit).
          assert (Hjj : j0 <> j) by (intros ->; rewrite Hfr in Hfr0; discriminate).
          destruct (fgroup_frame X R U s HI q aq j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
          apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + 8)); [| exact Ep | lia | lia].
          exists d. split; [exact E|]. rewrite PS.
          assert (CASE : j0 + 1 <= j \/ j + 1 <= j0) by lia.
          destruct CASE as [C|C]; [assert (stride_of aq * (j0 + 1) <= stride_of aq * j) by nia | assert (stride_of aq * (j + 1) <= stride_of aq * j0) by nia];
            unfold group_extent, UNIT, IB in *; nia.
        *
          destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi & Fit).
          destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo.
          assert (B1 : poff (slot_start am' J) + UNIT * match ss_fr (nth_slot am' J) with Some f => fr_off f | None => 0 end <= poff (slot_start aq j)).
          { rewrite HfrJ, Off, <- Eo, PS. unfold UNIT in *. nia. }
          assert (B2 : poff (slot_start aq j) + 8 <= poff (slot_start am' J) + stride_of am' - IB).
          { rewrite <- Eo. rewrite PS. unfold group_extent, UNIT, IB in *. nia. }
          apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + 8)); [| exact Ep | lia | lia].
          destruct Hc as [Hc | Hc].
          -- exact (group_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2).
          -- exact (footer_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2
                      ltac:(intros f Hf Hkf; rewrite HfrJ in Hf; injection Hf as <-; rewrite HkJ in Hkf; discriminate Hkf)).
  Qed.
End FSZ.
