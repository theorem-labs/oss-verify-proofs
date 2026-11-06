(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "padd"; "METAS_PER_AREA"; "META_SIZE"; "AREA_HDR"; "SP"; "mlookup"; "st_areas"; "st_metas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "area_cells"; "LMem"; "MCell"; "loc_addr"; "Inv"; "VSec"; "VZ"; "areas_cells"; "crange"; "image"; "meta_slot_cells"; "optr"; "range_incl"; "@Stdlib.Lists.List"; "In"; "NoDup"; "last"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone"; "succ_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "e_area"; "@Corelib.Init.Datatypes"; "app"; "cons"; "nil"; "option"; "None"; "Some"; "list"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfGeom MallocWfRepr MallocWfSurgery
  MallocLemmasRing MallocLayout MallocFooter MallocFooterLemmas Zones FpLaws Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint succ_in (l : list sptr) (a : sptr) : option sptr :=
  match l with
  | [] => None
  | b :: t => if sptr_eqb b a then hd_error t else succ_in t a
  end.

Lemma succ_in_app_last l p : ltac2:(tb__ "0|0|
S1bS17S0Vp;Vl;A3A1S1aS24S0A1S1eS21S0Vl;S22S0Vp;S23S0A1A3A3Vp;A2S25S0A1A3F_;").
Proof.
  induction l as [|b t IH]; intros Hn; cbn [succ_in app].
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb b p) eqn:E.
    + exfalso. apply sptr_eqb_eq in E. apply Hn. left. exact E.
    + apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma succ_in_app_prev l p d : ltac2:(tb__ "0|1|
S1bS1aS27S0A1Vl;S23S0A1M0A3A1S18S0Vl;A2S1aS24S0A1S1eS21S0Vl;S22S0Vp;G0A3A3S19S0Vl;Vd;A3A2S26S0Vp;A2A3F_;F_;").
Proof.
  induction l as [|b t IH]; intros Hne ND; [exfalso; exact (Hne eq_refl)|].
  inversion ND as [|b' t' Hb Ht]; subst. cbn [succ_in app].
  destruct t as [|c t'].
  - cbn [last]. rewrite sptr_eqb_refl. reflexivity.
  - change (last (b :: c :: t') d) with (last (c :: t') d).
    destruct (sptr_eqb b (last (c :: t') d)) eqn:E.
    + exfalso. apply sptr_eqb_eq in E. apply Hb. rewrite E. apply MallocLemmasRing.In_last. discriminate.
    + apply IH; [discriminate | exact Ht].
Qed.

Lemma succ_in_app_old l p a : ltac2:(tb__ "0|0|
S17S0Va;Vl;A3S1bS1aS0Va;S19S0Vl;S5U0Z0A2A3A3A1S18S0Vl;A2S1aS24S0A1S1eS21S0Vl;S22S0Vp;S23S0A1A3A3Va;A2S1eVl;Va;A2A3F_;F_;F_;").
Proof.
  induction l as [|b t IH]; intros Ha Hl ND; [destruct Ha|].
  inversion ND as [|b' t' Hb Ht]; subst. cbn [succ_in app].
  destruct (sptr_eqb b a) eqn:E.
  - apply sptr_eqb_eq in E. subst b. destruct t as [|c t']; [exfalso; apply Hl; reflexivity | reflexivity].
  - apply sptr_eqb_neq in E. destruct Ha as [->|Ha]; [exfalso; exact (E eq_refl)|].
    apply IH; [exact Ha | | exact Ht].
    intros El. apply Hl. destruct t as [|c t']; [destruct Ha | exact El].
Qed.

Lemma In_areas_cells_succ s l c : ltac2:(tb__ "0|0|
S18S0Vl;A2S17S9Vc;S11Vs;Vl;A2A3S1dS0S0S1cS17S0R1Vl;A3S17S9Vc;SaVs;R1S1eVl;R1A2A3A3A2La;A2F_;F_;").
Proof.
  induction l as [|a t IH]; intros ND Hin; cbn [areas_cells] in Hin; [destruct Hin|].
  inversion ND as [|a' t' Ha Ht]; subst.
  apply in_app_iff in Hin as [Hin|Hin].
  - exists a. split; [left; reflexivity|]. cbn [succ_in]. rewrite sptr_eqb_refl. exact Hin.
  - destruct (IH Ht Hin) as (b & Hb & Hc). exists b. split; [right; exact Hb|]. cbn [succ_in].
    destruct (sptr_eqb a b) eqn:E; [|exact Hc].
    exfalso. apply sptr_eqb_eq in E. subst a. exact (Ha Hb).
Qed.

Section AZ.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
SeVX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.

  Theorem area_zone a c lo n : ltac2:(tb__ "0|1|
S17S0Va;S7Vs;A1M0A3S17S9Vc;S21S9S13Vs;A1S2eVs;A1A3A3S16S28S2dS2dVlo;Vn;A4S12VL;S20Va;A1A2A2S1fVL;Vc;Vlo;Vn;A4S17S9Vc;SaVs;Va;S1eG0Va;A2A3A3F_;F_;F_;F_;").
  Proof using HI HL HX.
    intros Ha Hin ZI Hm. pose proof (inv_areas HI) as (AND & _).
    pose proof (e_area_In s a Ha) as EA.
    apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hc|Hin].
      + exfalso. refine (meet_entries s L HL c (e_ctx) (e_area a) _ _ (e_ctx_In s) EA _ (ctx_cell_in s L c Hc) ZI Hm). discriminate.
      + apply in_app_iff in Hin as [Hin|Hin].
        * destruct (In_areas_cells_succ s (st_areas s) c AND Hin) as (a' & Ha' & Hc).
          destruct (sptr_eq_dec a' a) as [->|Hne]; [exact Hc|].
          exfalso. refine (meet_entries s L HL c (e_area a') (e_area a) _ _ (e_area_In s a' Ha') EA _ (area_cell_in s L a' _ c Hc) ZI Hm).
          unfold e_area. intros E. injection E as E'. exact (Hne E').
        * exfalso. apply in_flat_map in Hin as [[g am] [Hg Hc]]. cbn [fst snd] in Hc.
          pose proof (proj1 (used_iff X R U s HI HX g am) Hg) as Hu.
          destruct (group_cell_in X R U s L HI g am c Hu (or_introl Hc)) as (rg & Hr & Hkd & Hl & ER & RI & _).
          refine (meet_entries s L HL c (e_reg (prid (am_mem am)) rg) (e_area a) _ _ ER EA _ RI ZI Hm).
          unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin X R U s HI a Ha) as Z0. rewrite <- Ea in Z0. exact (Z0 eq_refl).
    - exfalso. destruct (In_footer_cells_inv s c Hin) as (g & am & Hg & Hc).
      pose proof (proj1 (used_iff X R U s HI HX g am) Hg) as Hu.
      destruct (group_cell_in X R U s L HI g am c Hu (or_intror Hc)) as (rg & Hr & Hkd & Hl & ER & RI & _).
      refine (meet_entries s L HL c (e_reg (prid (am_mem am)) rg) (e_area a) _ _ ER EA _ RI ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin X R U s HI a Ha) as Z0. rewrite <- Ea in Z0. exact (Z0 eq_refl).
  Qed.

  Lemma area_cells_next_word a next c : ltac2:(tb__ "0|1|
S17S9Vc;SaVs;Va;Vnext;A3A3S1fVL;Vc;S29SdVL;SbVa;A1A2Z8M0A2G0A4S1aS9Vc;ScSbS1Va;G0A2A1U8S15Vnext;A1A3A3F_;F_;").
  Proof using .
    intros Hc (j & Hj & Hm). unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - cbn in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; [exfalso | reflexivity | exfalso];
        cbn [mc_loc mc_w] in Hm, Hj; unfold loc_addr in Hm; destruct a as [r o]; cbn [padd] in Hm; lia.
    - exfalso. apply in_flat_map in Hc as [k' [Hk' Hc]]. apply in_seq in Hk'.
      destruct (In_meta_slot_cells _ _ _ Hc) as (d & E & Hd & Hw). rewrite E in Hm. unfold loc_addr in Hm. destruct a as [r o]. cbn [padd] in Hm.
      unfold AREA_HDR, META_SIZE in *. lia.
  Qed.

  Lemma area_cells_check_word a next c : ltac2:(tb__ "0|1|
S17S9Vc;SaVs;Va;Vnext;A3A3S1fVL;Vc;SdVL;SbVa;A1M0A2Z8A4S1aS9Vc;ScG0U8SfA3A3F_;F_;").
  Proof using .
    intros Hc (j & Hj & Hm). unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - cbn in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; [reflexivity | exfalso | exfalso];
        cbn [mc_loc mc_w] in Hm, Hj; unfold loc_addr in Hm; destruct a as [r o]; cbn [padd] in Hm; lia.
    - exfalso. apply in_flat_map in Hc as [k' [Hk' Hc]]. apply in_seq in Hk'.
      destruct (In_meta_slot_cells _ _ _ Hc) as (d & E & Hd & Hw). rewrite E in Hm. unfold loc_addr in Hm. destruct a as [r o]. cbn [padd] in Hm.
      unfold AREA_HDR, META_SIZE in *. lia.
  Qed.

  Lemma area_cells_nslots_word a next c : ltac2:(tb__ "0|1|
S17S9Vc;SaVs;Va;Vnext;A3A3S1fVL;Vc;S29SdVL;SbVa;A1A2Z10M0A2Z8A4S1aS9Vc;ScSbS1Va;G0A2A1U4S10S2A1A3A3F_;F_;").
  Proof using .
    intros Hc (j & Hj & Hm). unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - cbn in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; [exfalso | exfalso | reflexivity];
        cbn [mc_loc mc_w] in Hm, Hj; unfold loc_addr in Hm; destruct a as [r o]; cbn [padd] in Hm; lia.
    - exfalso. apply in_flat_map in Hc as [k' [Hk' Hc]]. apply in_seq in Hk'.
      destruct (In_meta_slot_cells _ _ _ Hc) as (d & E & Hd & Hw). rewrite E in Hm. unfold loc_addr in Hm. destruct a as [r o]. cbn [padd] in Hm.
      unfold AREA_HDR, META_SIZE in *. lia.
  Qed.

  Lemma area_cells_slot a next k c : ltac2:(tb__ "0|1|
S1cS2aZ0Vk;A2S2bVk;S2A2A2S17S9Vc;SaVs;Va;Vnext;A3A3S1fVL;Vc;S2fVL;S1Va;S29S4S2cS3Vk;A2A2A2M0A2S3A4S17S9Vc;S14G0S6S8Vs;A1G0A2A2A3F_;F_;F_;").
  Proof using . apply (area_cells_meet s L). Qed.
End AZ.
