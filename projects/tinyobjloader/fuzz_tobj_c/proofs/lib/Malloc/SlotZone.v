(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "add"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "usedX"; "LMem"; "MCell"; "VZ"; "image"; "Inv"; "alloc_owned"; "group_extent"; "loc"; "mc_loc"; "mc_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "am_last"; "frame"; "IB"; "nth_slot"; "padd"; "slot_start"; "stride_of"; "ss_fr"; "UNIT"; "am_mem"; "ss_hdr"; "@Corelib.Init.Datatypes"; "option"; "None"; "app"; "Some"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfRepr MallocWfGeom MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout Zones2 ImageDelta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section SZ.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S11VX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.

  Theorem frameless_slot_zone_full q aq j c : ltac2:(tb__ "0|0|
ScVX;Vs;Vq;Vaq;A4S6S1Z0Vj;A2S1Vj;S17Vaq;A1A2A2S7S22S18A1S1eS1aVaq;Vj;A2A1S23S18A1A3S2aSbVc;S24SbS10Vs;A1S2bVs;A1A3A3S2dVL;Vc;S29VL;S1cVaq;Vj;A2A2S2S1dVaq;A1S19A2A4SaF_;F_;F_;F_;F_;").
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
    assert (ZI : range_incl (addr_of L (slot_start aq j), stride_of aq - IB) (crange L (e_reg (prid (am_mem aq)) rg))).
    { unfold range_incl, crange, e_reg. cbn [fst snd]. unfold loc_addr. rewrite AS, PS. unfold group_extent, UNIT, IB in *. nia. }
    destruct (cell_cases X R U s HI HX c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g' & am' & Hu' & Hc)]].
    - refine (meet_entries s L HL c e_ctx _ _ _ (e_ctx_In s) ER _ (ctx_cell_in s L c Hc) ZI Hm). discriminate.
    - refine (meet_entries s L HL c (e_area a') _ _ _ (e_area_In s a' Ha') ER _ (area_cell_in s L a' next c Hc) ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin X R U s HI a' Ha') as Z0. rewrite Ea in Z0. exact (Z0 eq_refl).
    - destruct Hm as (kk & Hkk & Hmk). rewrite AS in Hmk.
      assert (OWN : forall lo hi, (exists d, mc_loc c = LMem (padd (am_mem am') d) /\ (poff (am_mem am') + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am') + d)) ->
                    prid (am_mem am') = prid (am_mem aq) -> lo <= poff (slot_start aq j) -> poff (slot_start aq j) + (stride_of aq - IB) <= hi -> False).
      { intros lo hi (d & E & D) Ep Hlo Hhi. rewrite E in Hmk. unfold loc_addr in Hmk.
        destruct (am_mem am') as [r' o'] eqn:Em'. cbn [padd prid poff] in *. rewrite Ep in Hmk. lia. }
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem aq))) as [Ep | Np].
      2:{ destruct (group_cell_in X R U s L HI g' am' c Hu' Hc) as (rg' & Hr' & Hk' & Hl' & ER' & RI' & _).
          refine (meet_entries s L HL c (e_reg (prid (am_mem am')) rg') _ _ _ ER' ER _ RI' ZI ltac:(exists kk; split; [exact Hkk | rewrite AS; exact Hmk])).
          unfold e_reg. intros E2. injection E2 as Er _. exact (Np Er). }
      destruct (sptr_eq_dec g' q) as [-> | Hne].
      + pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
        assert (B1 : poff (slot_start aq j) + UNIT * match ss_fr (nth_slot aq j) with Some f => fr_off f | None => 0 end <= poff (slot_start aq j)).
        { rewrite Hfr. rewrite Z.mul_0_r, Z.add_0_r. apply Z.le_refl. }
        assert (B2 : poff (slot_start aq j) + (stride_of aq - IB) <= poff (slot_start aq j) + stride_of aq - IB) by lia.
        apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + (stride_of aq - IB))); [| exact Ep | lia | lia].
        destruct Hc as [Hc | Hc].
        * exact (group_cells_vs_body X R U s q aq j _ _ c HI Hu Hj Hc B1 B2).
        * exact (footer_cells_vs_body X R U s q aq j _ _ c HI Hu Hj Hc B1 B2 ltac:(intros f Hf; rewrite Hfr in Hf; discriminate Hf)).
      + pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'. pose proof (extent_pos _ _ _ _ _ G') as EP1.
        destruct (group_cell_in X R U s L HI g' am' c Hu' Hc) as (_ & _ & _ & _ & _ & _ & (d & E & Hd & Hw)).
        destruct (inv_laminar HI g' am' q aq Hu' Hu Hne Ep) as [D | [I | I]].
        * apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + (stride_of aq - IB))); [| exact Ep | lia | lia].
          exists d. split; [exact E|]. unfold spans_disjoint in D. rewrite PS. unfold group_extent, UNIT, IB in *. nia.
        * destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi & Fit).
          assert (Hjj : j0 <> j) by (intros ->; rewrite Hfr in Hfr0; discriminate).
          destruct (fgroup_frame X R U s HI q aq j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
          apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + (stride_of aq - IB))); [| exact Ep | lia | lia].
          exists d. split; [exact E|]. rewrite PS.
          assert (CASE : j0 + 1 <= j \/ j + 1 <= j0) by lia.
          destruct CASE as [C|C]; [assert (stride_of aq * (j0 + 1) <= stride_of aq * j) by nia | assert (stride_of aq * (j + 1) <= stride_of aq * j0) by nia];
            unfold group_extent, UNIT, IB in *; nia.
        * destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi & Fit).
          destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo.
          assert (B1 : poff (slot_start am' J) + UNIT * match ss_fr (nth_slot am' J) with Some f => fr_off f | None => 0 end <= poff (slot_start aq j)).
          { rewrite HfrJ, Off, <- Eo, PS. unfold UNIT in *. nia. }
          assert (B2 : poff (slot_start aq j) + (stride_of aq - IB) <= poff (slot_start am' J) + stride_of am' - IB).
          { rewrite <- Eo. rewrite PS. unfold group_extent, UNIT, IB in *. nia. }
          apply (OWN (poff (slot_start aq j)) (poff (slot_start aq j) + (stride_of aq - IB))); [| exact Ep | lia | lia].
          destruct Hc as [Hc | Hc].
          -- exact (group_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2).
          -- exact (footer_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2
                      ltac:(intros f Hf Hkf; rewrite HfrJ in Hf; injection Hf as <-; rewrite HkJ in Hkf; discriminate Hkf)).
  Qed.

  Lemma footer_cells_fine q aq c : ltac2:(tb__ "0|3|
ScVX;Vs;Vq;Vaq;A4S2aSbVc;S2cVaq;A1A3S8S0S0S6S7S14S15Vc;A1SdS1bS20Vaq;A1R1A2A1A3S9S6S7S0R1S13Vaq;A1A3S7S26S16Vc;A1M0U1A3A2S8S0S0S6S6S1Z0R1A2S1R1S17Vaq;A1A2A2S6S1S3S1fS4S1dVaq;A1M1R1A2A2M2R2A2S1S3R2S5G0A1A2S2S3G2G1A2S19A2A2A2A2Li;A2A2A2Ld;A2F_;F_;").
  Proof using HI.
    intros Hu Hin. pose proof (inv_groups HI q aq Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    pose proof G as ((Glast & _) & _ & Gsl & _).
    assert (Efp : forall i fr d, padd (frame_ptr aq i fr) d = padd (am_mem aq) (UNIT + stride_of aq * i + UNIT * fr_off fr + d)).
    { intros i fr d. unfold frame_ptr, slot_start. destruct (am_mem aq); cbn. f_equal. lia. }
    assert (Ese : forall i d, padd (slot_end aq i) d = padd (am_mem aq) (UNIT + stride_of aq * i + (stride_of aq - IB) + d)).
    { intros i d. unfold slot_end, slot_start. destruct (am_mem aq); cbn. f_equal. lia. }
    unfold group_footer_cells in Hin. destruct Hin as [<- | Hin].
    - exists (UNIT + stride_of aq * (am_last aq + 1) - IB). cbn [trailing_cell mc_loc mc_w]. unfold trailing_loc. split; [reflexivity|]. left. unfold group_extent. split; [lia | reflexivity].
    - apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
      destruct (ss_fr (nth_slot aq i)) as [fr|] eqn:Efr; [|destruct Hin].
      pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
      unfold frame_footer_cells in Hin. destruct (fr_kind fr); [|destruct Hin].
      apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
      + destruct (0 <? reserved_of aq fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er. unfold reserved_of in Er.
        destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Efp.
        eexists. split; [reflexivity|]. right. exists i. unfold UNIT, IB in *. split; [lia|]. split; lia.
      + destruct (5 <=? reserved_of aq fr) eqn:Er; [|destruct Hin]. apply Z.leb_le in Er. unfold reserved_of in Er.
        destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite Ese.
        eexists. split; [reflexivity|]. right. exists i. unfold UNIT, IB in *. split; [lia|]. split; lia.
      + destruct (5 <? reserved_of aq fr) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er. unfold reserved_of in Er.
        destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Ese.
        eexists. split; [reflexivity|]. right. exists i. unfold UNIT, IB in *. split; [lia|]. split; lia.
  Qed.

  Theorem slot_hdr_zone q aq j c : ltac2:(tb__ "0|3|
ScVX;Vs;Vq;Vaq;A4S6S1Z0Vj;A2S1Vj;S17Vaq;A1A2A2S2aSbVc;S24SbS10Vs;A1S2bVs;A1A3A3S2dVL;Vc;S2S29VL;S1cVaq;Vj;A2M0A2Z3M1A2G1A4S8S0S0S8S0S0S6S7S22S28S0S0A2M2A1S21S1aVaq;Vj;A2A1S25G2S27S0S0R2R1A4A2A3S9S7SbVc;SeSdS1bG0N3A2A1U1SfR2A1A3A3S7SbVc;SeSdS1bG0N2A2A1U2SfR1A1A3A3A2A2Lh16;A2Lh3;A2F_;F_;F_;F_;").
  Proof using HI HL HX.
    intros Hu Hj Hin Hm.
    pose proof (inv_groups HI q aq Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof (extent_pos _ _ _ _ _ G) as EP0.
    pose proof G as ((Glast & _) & _ & Gsl & _).
    pose proof (poff_slot_start aq j) as PS.
    assert (SJ : 0 <= stride_of aq * j /\ stride_of aq * (j + 1) <= stride_of aq * (am_last aq + 1)) by nia.
    destruct (used_group_region X R U s q aq HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as ER.
    assert (AS : addr_of L (slot_start aq j) = ly_reg L (prid (am_mem aq)) + poff (slot_start aq j)).
    { unfold addr_of, loc_addr, slot_start. destruct (am_mem aq) as [r o]. cbn [padd prid poff]. reflexivity. }
    assert (ZI : range_incl (addr_of L (slot_start aq j) - 3, 3) (crange L (e_reg (prid (am_mem aq)) rg))).
    { unfold range_incl, crange, e_reg. cbn [fst snd]. unfold loc_addr. rewrite AS, PS. unfold group_extent, UNIT, IB in *. nia. }
    destruct (cell_cases X R U s HI HX c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g' & am' & Hu' & Hc)]].
    - exfalso. refine (meet_entries s L HL c e_ctx _ _ _ (e_ctx_In s) ER _ (ctx_cell_in s L c Hc) ZI Hm). discriminate.
    - exfalso. refine (meet_entries s L HL c (e_area a') _ _ _ (e_area_In s a' Ha') ER _ (area_cell_in s L a' next c Hc) ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin X R U s HI a' Ha') as Z0. rewrite Ea in Z0. exact (Z0 eq_refl).
    - destruct Hm as (kk & Hkk & Hmk). rewrite AS in Hmk.

      assert (OWN : forall lo hi, (exists d, mc_loc c = LMem (padd (am_mem am') d) /\ (poff (am_mem am') + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am') + d)) ->
                    prid (am_mem am') = prid (am_mem aq) -> lo <= poff (slot_start aq j) - 3 -> poff (slot_start aq j) <= hi -> False).
      { intros lo hi (d & E & D) Ep Hlo Hhi. rewrite E in Hmk. unfold loc_addr in Hmk.
        destruct (am_mem am') as [r' o'] eqn:Em'. cbn [padd prid poff] in *. rewrite Ep in Hmk. lia. }
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem aq))) as [Ep | Np].
      2:{ exfalso. destruct (group_cell_in X R U s L HI g' am' c Hu' Hc) as (rg' & Hr' & Hk' & Hl' & ER' & RI' & _).
          refine (meet_entries s L HL c (e_reg (prid (am_mem am')) rg') _ _ _ ER' ER _ RI' ZI ltac:(exists kk; split; [exact Hkk | rewrite AS; exact Hmk])).
          unfold e_reg. intros E2. injection E2 as Er _. exact (Np Er). }
      destruct (sptr_eq_dec g' q) as [-> | Hne].
      +
        pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
        assert (Ess : forall i d, padd (slot_start aq i) d = padd (am_mem aq) (UNIT + stride_of aq * i + d)).
        { intros i d. unfold slot_start. destruct (am_mem aq); cbn. f_equal. lia. }
        destruct Hc as [Hc | Hc].
        * rewrite (ImageDelta.group_cells_eq q aq) in Hc. destruct Hc as [<- | [<- | Hc]].
          -- exfalso. apply (OWN (poff (am_mem aq) + 8) (poff (slot_start aq j))); [|exact Ep| rewrite PS; unfold UNIT; lia | lia].
             exists 0. cbn [mc_loc mc_w]. split; [destruct (am_mem aq) as [r0 o0]; cbn; rewrite Z.add_0_r; reflexivity|]. left. lia.
          -- exfalso. apply (OWN (poff (am_mem aq) + 12) (poff (slot_start aq j))); [|exact Ep| rewrite PS; unfold UNIT; lia | lia].
             unfold ImageDelta.aidx_cell. destruct (am_maplen aq =? 0); cbn [mc_loc mc_w]; exists 8; (split; [reflexivity|]); left; lia.
          -- apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi.
             destruct (In_slot_cells X R U s q aq i c HI Hu ltac:(lia) Hc) as (d & E & Lo & Hiw & Fine).
             destruct (Z.eq_dec i j) as [-> | NE].
             ++
                unfold slot_cells in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
                ** exfalso. destruct Hc as [<-|[]]. apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia].
                   rewrite Ess. cbn [mc_loc mc_w]. eexists. split; [reflexivity|]. left. rewrite PS. lia.
                ** destruct (ss_hdr (nth_slot aq j)) as [[h3 h16]|]; [|destruct Hc]. exists h3, h16. split; [reflexivity|].
                   destruct Hc as [<-|[<-|[]]]; [left | right]; reflexivity.
                ** exfalso. destruct (ss_fr (nth_slot aq j)) as [fr|] eqn:Efr; [|destruct Hc]. destruct (fr_off fr =? 0) eqn:E0; [destruct Hc|]. apply Z.eqb_neq in E0.
                   pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
                   destruct Fine as [Fine | (fr' & Efr' & Ho' & Lo' & Hi')]; [apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia] |].
                   +++ exfalso.
                       assert (Ess2 : forall dd, padd (padd (slot_start aq j) (UNIT * fr_off fr)) dd = padd (am_mem aq) (UNIT + stride_of aq * j + UNIT * fr_off fr + dd)).
                       { intros dd. unfold slot_start. destruct (am_mem aq); cbn. f_equal. lia. }
                       destruct Hc as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w] in E, Fine; rewrite Ess2 in E; injection E as E'; pose proof (f_equal poff E') as E''; rewrite !poff_padd in E''; unfold UNIT, IB in *; lia.
                   +++ apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia].
                       exists d. split; [exact E|]. right. rewrite PS. unfold UNIT, IB in *. nia.
             ++ exfalso. assert (CASE : i + 1 <= j \/ j + 1 <= i) by lia.
                destruct CASE as [Cij|Cij].
                ** apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. left. rewrite PS.
                   assert (stride_of aq * (i + 1) <= stride_of aq * j) by nia. unfold UNIT, IB in *. nia.
                ** apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. right. rewrite PS.
                   assert (stride_of aq * (j + 1) <= stride_of aq * i) by nia. unfold UNIT, IB in *. nia.
        * exfalso. destruct (footer_cells_fine q aq c Hu Hc) as (d & E & [[Ed Ew] | (i & Hi & Lo & Hiw)]).
          -- apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. right. rewrite PS, Ed.
             unfold group_extent, UNIT, IB in *. nia.
          -- destruct (Z_lt_dec i j) as [Cij|Cij].
             ++ apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. left. rewrite PS.
                assert (stride_of aq * (i + 1) <= stride_of aq * j) by nia. unfold UNIT, IB in *. nia.
             ++ apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. right. rewrite PS.
                assert (stride_of aq * j <= stride_of aq * i) by nia. unfold UNIT, IB in *. nia.
      +
        exfalso.
        pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'. pose proof (extent_pos _ _ _ _ _ G') as EP1. pose proof G' as ((Glast' & _) & _).

        assert (CEND : exists d, mc_loc c = LMem (padd (am_mem am') d) /\ 0 <= d /\ (d + Z.of_nat (mc_w c) <= group_extent am' \/ (d = group_extent am' /\ mc_w c = 1%nat))).
        { destruct Hc as [Hc|Hc].
          - destruct (In_group_cells_span X R U s g' am' c HI Hu' Hc) as (d & E & D0 & D1). exists d. auto.
          - destruct (footer_cells_fine g' am' c Hu' Hc) as (d & E & [[Ed Ew] | (i & Hi & Lo & Hiw)]).
            + exists d. split; [exact E|]. split; [rewrite Ed; lia|]. right. auto.
            + exists d. split; [exact E|]. assert (0 <= stride_of am' * i) by nia. assert (stride_of am' * (i + 1) <= stride_of am' * (am_last am' + 1)) by nia.
              split; [unfold UNIT in *; lia|]. left. unfold group_extent, UNIT, IB in *. nia. }
        destruct CEND as (d & E & D0 & DE).
        destruct (inv_laminar HI g' am' q aq Hu' Hu Hne Ep) as [D | [I | I]].
        * unfold spans_disjoint in D. destruct D as [D|D].
          -- apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. left. rewrite PS.
             destruct DE as [DE | [-> Ew]]; [|rewrite Ew; cbn [Z.of_nat Pos.of_succ_nat]]; unfold group_extent, UNIT, IB in *; nia.
          -- apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. right. rewrite PS.
             unfold group_extent, UNIT, IB in *. nia.
        *
          destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi & Fit).
          destruct (fgroup_frame X R U s HI q aq j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
          destruct (Z_lt_dec j0 j) as [Cj|Cj].
          -- apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. left. rewrite PS.
             assert (stride_of aq * (j0 + 1) <= stride_of aq * j) by nia.
             destruct DE as [DE | [-> Ew]]; [|rewrite Ew; cbn [Z.of_nat Pos.of_succ_nat]]; unfold group_extent, UNIT, IB in *; nia.
          -- apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [|exact Ep|lia|lia]. exists d. split; [exact E|]. right. rewrite PS.
             assert (stride_of aq * j <= stride_of aq * j0) by nia. unfold group_extent, UNIT, IB in *. nia.
        *
          destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi & Fit).
          destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo.
          assert (B1 : poff (slot_start am' J) + UNIT * match ss_fr (nth_slot am' J) with Some f => fr_off f | None => 0 end <= poff (slot_start aq j) - 3).
          { rewrite HfrJ, Off, <- Eo, PS. unfold UNIT in *. nia. }
          assert (B2 : poff (slot_start aq j) <= poff (slot_start am' J) + stride_of am' - IB).
          { rewrite <- Eo. rewrite PS. unfold group_extent, UNIT, IB in *. nia. }
          apply (OWN (poff (slot_start aq j) - 3) (poff (slot_start aq j))); [| exact Ep | lia | lia].
          destruct Hc as [Hc | Hc].
          -- exact (group_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2).
          -- exact (footer_cells_vs_body X R U s g' am' J _ _ c HI Hu' HJ Hc B1 B2
                      ltac:(intros f Hf Hkf; rewrite HfrJ in Hf; injection Hf as <-; rewrite HkJ in Hkf; discriminate Hkf)).
  Qed.

  Theorem frameless_slot_owned q aq j x : ltac2:(tb__ "0|1|
ScVX;Vs;Vq;Vaq;A4S6S1Z0Vj;A2S1Vj;S17Vaq;A1A2A2S7S22S18A1S1eS1aVaq;Vj;A2A1S23S18A1A3S6S1S2S29VL;S1cVaq;Vj;A2A2M0Z4A2Vx;A2S1Vx;S2S3G0S1dVaq;A1A2S19A2A2A2S12VL;Vs;Vx;A3F_;F_;F_;F_;").
  Proof using HI HL HX.
    intros Hu Hj Hfr Hx.
    pose proof (inv_groups HI q aq Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof (extent_pos _ _ _ _ _ G) as EP0.
    pose proof G as ((Glast & _) & _).
    pose proof (poff_slot_start aq j) as PS.
    assert (SJ : 0 <= stride_of aq * j /\ stride_of aq * j + stride_of aq <= stride_of aq * (am_last aq + 1)).
    { split; [apply Z.mul_nonneg_nonneg; lia|]. replace (stride_of aq * j + stride_of aq) with (stride_of aq * (j + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
    destruct (used_group_region X R U s q aq HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as ER.
    assert (AS : addr_of L (slot_start aq j) = ly_reg L (prid (am_mem aq)) + poff (slot_start aq j)).
    { unfold addr_of, loc_addr, slot_start. destruct (am_mem aq) as [r o]. cbn [padd prid poff]. reflexivity. }
    assert (AM : forall am', prid (am_mem am') = prid (am_mem aq) -> addr_of L (am_mem am') = ly_reg L (prid (am_mem aq)) + poff (am_mem am')).
    { intros am' Ep. unfold addr_of, loc_addr. destruct (am_mem am') as [r' o']. cbn [prid poff] in *. rewrite Ep. reflexivity. }
    split.
    - exists (LMem (SP (prid (am_mem aq)) 0), rg_len rg). split; [exact ER|]. cbn [fst snd]. unfold loc_addr. cbn [prid poff].
      rewrite AS, PS in Hx. unfold group_extent, UNIT, IB in *. nia.
    - intros (b & Hb & Hxb). cbn [fst snd] in Hxb. change (loc_addr L (LMem (fst b))) with (addr_of L (fst b)) in Hxb.
      destruct (user_block_in_group X R U s L HI HX b Hb) as (g' & am' & i & fr & Hu' & Hi & Hfr' & Hk' & Eb & B1 & B2 & B3 & B4).
      pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'. pose proof (extent_pos _ _ _ _ _ G') as EP1.
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem aq))) as [Ep | Np].
      2:{
          destruct (used_group_region X R U s g' am' HI Hu') as (rg' & Hr' & Hk'' & Hl' & Ho' & Hext' & _).
          pose proof (footprint_region_In s _ _ Hr' Hk'' Hl') as ER'.
          pose proof (fp_disjoint s L HL _ _ ER' ER ltac:(intros E; injection E as E1 _; exact (Np E1))) as D.
          unfold ranges_disjoint, crange in D. cbn [fst snd] in D. unfold loc_addr in D. cbn [prid poff] in D.
          assert (A' : addr_of L (am_mem am') = ly_reg L (prid (am_mem am')) + poff (am_mem am')).
          { unfold addr_of, loc_addr. destruct (am_mem am') as [r' o']. cbn [prid poff]. reflexivity. }
          rewrite A' in B1, B2, B4. rewrite AS, PS in Hx. unfold group_extent, UNIT, IB in *. nia. }
      rewrite (AM am' Ep) in B1, B2, B4. rewrite AS, PS in Hx.
      destruct (sptr_eq_dec g' q) as [-> | Hne].
      +
        pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
        assert (Hij : i <> j) by (intros ->; rewrite Hfr in Hfr'; discriminate).
        assert (CASE : i + 1 <= j \/ j + 1 <= i) by lia.
        destruct CASE as [C|C]; [assert (stride_of aq * (i + 1) <= stride_of aq * j) by nia | assert (stride_of aq * (j + 1) <= stride_of aq * i) by nia];
          unfold group_extent, UNIT, IB in *; nia.
      + destruct (inv_laminar HI g' am' q aq Hu' Hu Hne Ep) as [D | [I | I]].
        * unfold spans_disjoint in D. unfold group_extent, UNIT, IB in *. nia.
        *
          destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hhi & Fit).
          destruct (fgroup_frame X R U s HI q aq j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
          assert (Hjj : j0 <> j) by (intros ->; rewrite Hfr in Hfr0; discriminate).
          assert (Qi : 0 <= stride_of am' * i /\ stride_of am' * i + stride_of am' <= stride_of am' * (am_last am' + 1)).
          { split; [apply Z.mul_nonneg_nonneg; lia|]. replace (stride_of am' * i + stride_of am') with (stride_of am' * (i + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
          assert (CASE : stride_of aq * j0 + stride_of aq <= stride_of aq * j \/ stride_of aq * j + stride_of aq <= stride_of aq * j0).
          { assert (C : j0 + 1 <= j \/ j + 1 <= j0) by lia. destruct C as [C|C]; [left | right];
              [replace (stride_of aq * j0 + stride_of aq) with (stride_of aq * (j0 + 1)) by lia | replace (stride_of aq * j + stride_of aq) with (stride_of aq * (j + 1)) by lia];
              apply Z.mul_le_mono_nonneg_l; lia. }
          unfold group_extent, UNIT, IB in *.
          set (Tm' := stride_of am' * (am_last am' + 1)) in *. set (Ti := stride_of am' * i) in *.
          set (Tm := stride_of aq * (am_last aq + 1)) in *. set (T0 := stride_of aq * j0) in *. set (Tj := stride_of aq * j) in *.
          set (Tc := stride_of ac * (am_last ac + 1)) in *.
          clearbody Tm' Ti Tm T0 Tj Tc. subst b. cbn [fst snd] in *. lia.
        *
          destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hhi & Fit).
          destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
          pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
          assert (HiJ : i <> J) by (intros ->; rewrite HfrJ in Hfr'; injection Hfr' as <-; rewrite HkJ in Hk'; discriminate Hk').
          assert (QJ : 0 <= stride_of am' * J /\ stride_of am' * J + stride_of am' <= stride_of am' * (am_last am' + 1)).
          { split; [apply Z.mul_nonneg_nonneg; lia|]. replace (stride_of am' * J + stride_of am') with (stride_of am' * (J + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
          assert (Qi : 0 <= stride_of am' * i /\ stride_of am' * i + stride_of am' <= stride_of am' * (am_last am' + 1)).
          { split; [apply Z.mul_nonneg_nonneg; lia|]. replace (stride_of am' * i + stride_of am') with (stride_of am' * (i + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
          assert (CASE : stride_of am' * i + stride_of am' <= stride_of am' * J \/ stride_of am' * J + stride_of am' <= stride_of am' * i).
          { assert (C : i + 1 <= J \/ J + 1 <= i) by lia. destruct C as [C|C]; [left | right];
              [replace (stride_of am' * i + stride_of am') with (stride_of am' * (i + 1)) by lia | replace (stride_of am' * J + stride_of am') with (stride_of am' * (J + 1)) by lia];
              apply Z.mul_le_mono_nonneg_l; lia. }
          unfold group_extent, UNIT, IB in *.
          set (Tm' := stride_of am' * (am_last am' + 1)) in *. set (Ti := stride_of am' * i) in *. set (TJ := stride_of am' * J) in *.
          set (Tm := stride_of aq * (am_last aq + 1)) in *. set (Tj := stride_of aq * j) in *.
          set (Tc := stride_of ac * (am_last ac + 1)) in *.
          clearbody Tm' Ti TJ Tm Tj Tc. subst b. cbn [fst snd] in *. lia.
  Qed.
End SZ.
