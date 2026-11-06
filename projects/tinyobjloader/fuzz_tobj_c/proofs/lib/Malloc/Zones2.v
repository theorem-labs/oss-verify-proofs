(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LCtx"; "image"; "loc"; "usedX"; "MCell"; "crange"; "mc_w"; "mc_loc"; "range_incl"; "VZ"; "cell_range"; "ctx_cells"; "keys"; "CTX_SIZE"; "footprint"; "ly_ctx"; "CTX_active"; "LMem"; "group_extent"; "CTX_bounces"; "MT"; "area_cells"; "group_cells"; "loc_addr"; "meta_slot_cells"; "optr"; "active_hd"; "alloc_owned"; "ranges_disjoint"; "user_blocks"; "CTX_seq"; "CTX_unmap_seq"; "CTX_usage"; "Inv"; "VLo5"; "block_range"; "frame_ptr"; "region_of"; "used_metas"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "False"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "to_nat"; "eqb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "META_SIZE"; "am_mem"; "ameta"; "padd"; "IB"; "frame"; "region"; "st_areas"; "AREA_HDR"; "METAS_PER_AREA"; "PGSZ"; "mslot"; "st_bounces"; "FUser"; "MFree"; "MRaw"; "RkMap"; "SP"; "UNIT"; "am_aidx"; "am_last"; "am_maplen"; "fkind"; "fr_kind"; "fr_n"; "mlookup"; "nth_slot"; "poff"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "ss_fr"; "st_active"; "st_metas"; "st_unmap_seq"; "st_usage"; "stride_of"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "ledger_ok"; "mc_img_hi"; "mc_img_lo"; "topL"; "vm_ok"; "@Corelib.Init.Datatypes"; "nat"; "app"; "prod"; "pair"; "option"; "Some"; "bool"; "None"; "fst"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "@Corelib.Lists.ListDef"; "nth"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.Z2"; "aidx_cell"; "e_area"; "e_ctx"; "e_reg"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfFrame MallocWfGeom MallocWfRepr MallocWfSurgery
  MallocLayout MallocFooter MallocFooterLemmas Zones FpLaws ImageUpd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition xraw (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|3|
S39S0S39R1VX;A3S2cS2aS6cS45A1M0S16Vs;R2A2M1S6dS45S49A2A3S2aG0G1S6dS45S48S6fS39A1M2G2A2A2A3A2F_;Fq;").

Lemma xraw_nil s : xraw [] s.
Proof. intros q []. Qed.

Definition cmeets (L : layout) (c : mcell) (lo n : Z) : Prop := ltac2:(tb__ "0|1|
S2bS68S68S29S77R1S8Vc;A1A2S29S31Vlo;S30S19VL;S9Vc;A1A2S33R1A1A2M0A2S32G0S30Vlo;Vn;A2A2A2A2Lk;A2").

Lemma In_ctx_cells_cases s c : ltac2:(tb__ "0|8|
S0S1Vc;SdVs;A1A3S2cS2bS61S61S29S2aS4S9Vc;A1S2R1A1A3S29S31Z0M0R1A2S29S2cS31S30R1S33S8Vc;A1A1A2M1S12A2S31S20R1A2A2S31G1SfA2A2A2A2Lo;A2S2cS2bS68S68S29S77R1U30A2M2S2aS1Vc;S6S2S30S12S34Z8S33R1A1M3A2M4A2A1U8M5S1bS76S6cS39A1R1S5cVs;A1S6fS39A1A4A1A3A3A2Lk;A2S2cS2bS68S68S29G2S2aS1Vc;S6S2S30S22G4A2A1G5SbS76S61R1S5fVs;A1G0A4A1A3A3A2Lk;A2S2cS2bS68S68S29S77R1U20A2M6S2aS1Vc;S6S2S30S21G3A2A1U1M7SbS76S61R1S5eVs;A1G0A4A1A3A3A2Lk;A2S2bS68S68S29G6S2aS1Vc;S6S2S30S15G3A2A1G7SbS76S61R1S46Vs;A1G0A4A1A3A3A2Lk;A2A2A2A2A2F_;").
Proof.
  intros Hin. unfold ctx_cells in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  - left. unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
      CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas,
      CTX_seq, CTX_brk, CTX_active, CTX_SIZE in *.
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_w]; eexists; (split; [reflexivity|]); cbn; lia.
  - apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]].
    + right; left. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + right; right; left. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + right; right; right; left. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + right; right; right; right. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
Qed.

Lemma ctx_cells_at_active s c sc o : ltac2:(tb__ "0|2|
S29S31Z0Vsc;A2S32Vsc;Z30A2A2S0S1Vc;SdVs;A1A3S2aS4S9Vc;A1S2Vo;A1A3S32Vo;S30S30S12S34Z8M0Vsc;A2A2M1G0A2A2S32G1S30Vo;S33S8Vc;A1A1A2A2S2aS1Vc;S6S2G1A1U8S1bS1cVs;Vsc;A2A1A3A3F_;F_;F_;F_;F_;").
Proof.
  intros Hsc Hin Ho O1 O2.
  destruct (In_ctx_cells_cases s c Hin) as [(o' & E & H0 & H1 & H2) | [(k & Hk & ->) | [(k & Hk & ->) | [(k & Hk & ->) | (k & Hk & ->)]]]];
    [rewrite Ho in E; injection E as <-; unfold CTX_active, CTX_seq, CTX_SIZE in *; lia | ..];
    cbn [mc_loc mc_w] in Ho, O2; injection Ho as Eo; unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *; try lia.
  assert (Z.of_nat k = sc) as <- by lia. unfold active_hd. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma ctx_cells_at_bounce s c k o : ltac2:(tb__ "0|2|
S29S31Z0M0Vk;A2S32Vk;Z20A2A2S0S1Vc;SdVs;A1A3S2aS4S9Vc;A1S2Vo;A1A3S32Vo;S30S30S15Vk;A2M1Z1A2A2S32G1S30Vo;S33S8Vc;A1A1A2A2S2aS1Vc;S6S2G1A1U1SbS76S61S36Vk;A1S46Vs;A1G0A4A1A3A3F_;F_;F_;F_;F_;").
Proof.
  intros Hk Hin Ho O1 O2.
  destruct (In_ctx_cells_cases s c Hin) as [(o' & E & H0 & H1 & H2) | [(k' & Hk' & ->) | [(k' & Hk' & ->) | [(k' & Hk' & ->) | (k' & Hk' & ->)]]]];
    [rewrite Ho in E; injection E as <-; unfold CTX_active, CTX_bounces, CTX_seq, CTX_SIZE in *; lia | ..];
    cbn [mc_loc mc_w] in Ho, O2; injection Ho as Eo; unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *; try lia.
  assert (Z.of_nat k' = k) as <- by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Section Z2.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S23VX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Hypothesis HL : layout_ok L s.
  Variables (Cz : mconsts) (vmz : VmMaps).

  Lemma used_iff g am : ltac2:(tb__ "0|0|
S2fS0S6aS39S3cA2S6bS39S3cVg;Vam;A4S28Vs;A1A3S5VX;Vs;Vg;Vam;A4A2").
  Proof using HI HX.
    rewrite (used_metas_iff s g am (proj1 (inv_keys HI))). unfold usedX, MTX. split; intros H.
    - destruct (memb g X) eqn:E; [|exact H]. exfalso.
      assert (Hin : In g X).
      { unfold memb in E. apply existsb_exists in E as (y & Hy & Ey). apply sptr_eqb_eq in Ey. subst y. exact Hy. }
      destruct (HX g Hin) as [M|M]; rewrite M in H; discriminate.
    - destruct (memb g X); [discriminate | exact H].
  Qed.

  Definition e_ctx : loc * Z := ltac2:(tb__ "0|0|
S6bS4S61S2Z0A1SfA4").
  Definition e_area (a : sptr) : loc * Z := ltac2:(tb__ "0|0|
S6bS4S61S13Va;A1S44A4").
  Definition e_reg (k : nat) (rg : region) : loc * Z := ltac2:(tb__ "0|0|
S6bS4S61S13S4bVk;Z0A2A1S58Vrg;A1A4").

  Lemma e_ctx_In : In e_ctx (footprint s). Proof using . left. reflexivity. Qed.
  Lemma e_area_In a : ltac2:(tb__ "0|0|
S0S39Va;S41Vs;A1A3S0S6aS4S61A2S79Va;A1S10Vs;A1A3F_;").
  Proof using . intros Ha. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. Qed.

  Lemma fp_disjoint e1 e2 : ltac2:(tb__ "0|2|
S0S6aS4S61A2M0Ve1;S10Vs;A1M1A3S0G0Ve2;G1A3S2dS2aG0Ve1;Ve2;A3A1S1eS7VL;Ve1;A2S7VL;Ve2;A2A2F_;F_;F_;").
  Proof using HL.
    intros H1 H2 Hne. pose proof HL as (_ & _ & PW & _).
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) e1 e2 PW H1 H2 Hne) as [D|D]; [exact D|].
    unfold ranges_disjoint in *. lia.
  Qed.

  Lemma area_not_origin a : ltac2:(tb__ "0|0|
S0S39Va;S41Vs;A1A3S2dS2aS61S55Va;A1Z0A3A1F_;").
  Proof using HI.
    intros Ha. pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rg & -> & _ & Ho & _).
    cbn [poff]. unfold PGSZ in Ho. lia.
  Qed.

  Lemma ctx_cell_in c : ltac2:(tb__ "0|0|
S0S1Vc;SdVs;A1A3SaScVL;Vc;A2S7VL;S7aA2A2F_;").
  Proof using .
    intros Hc. destruct (In_ctx_cells s c Hc) as (off & E & Ho & Hw).
    unfold cell_range, crange, range_incl, e_ctx, loc_addr. rewrite E. cbn [fst snd]. lia.
  Qed.

  Lemma area_cell_in a next c : ltac2:(tb__ "0|0|
S0S1Vc;S17Vs;Va;Vnext;A3A3SaScVL;Vc;A2S7VL;S79Va;A1A2A2F_;").
  Proof using .
    intros Hc. destruct (In_area_cells s a next c Hc) as (d & E & Hd & Hw).
    unfold cell_range, crange, range_incl, e_area, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  Qed.

  Lemma group_cell_in g am c : ltac2:(tb__ "0|3|
S5VX;Vs;Vg;Vam;A4S2cS0S1Vc;S18Vg;Vam;A2A3S0S1Vc;S74Vam;A1A3A2S2bS40S40S29S2aS6cS40A1S27Vs;S56S3bVam;A1M0A1M1A2S6dS40R1A2A3S29S2aS5aS57R1A1S4aA3S29S2aS6eS59R1A1S72A3S29S0S6aS4S61A2S7bG1R1A2M2S10Vs;A1A3S29SaScVL;Vc;A2S7VL;G2A2A2S2bS61S61S29S2aS4S9Vc;A1S13S3dG0R1A2A1A3S29S31Z0R1A2S31S30R1S33S8Vc;A1A1A2S30S14Vam;A1S3eA2A2A2A2Ld;A2A2A2A2A2A2Lrg;A2F_;F_;").
  Proof using HI.
    intros Hu Hc.
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    assert (D : exists d, mc_loc c = LMem (padd (am_mem am) d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= group_extent am + IB).
    { destruct Hc as [Hc|Hc].
      - exact (In_group_cells X R U s g am c HI Hu Hc).
      - destruct (In_group_footer_cells X R U s g am c HI Hu Hc) as (d & E & Hd & Hw & _). exists d. auto. }
    exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
    split; [|exact D]. destruct D as (d & E & Hd & Hw).
    unfold cell_range, crange, range_incl, e_reg, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. lia.
  Qed.

  Lemma cell_cases c : ltac2:(tb__ "0|1|
S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S2cS0S1Vc;SdVs;A1A3S2cS2bS39S39S2bS6cS39A1M0G0S29S0S39R2S41Vs;A1A3S0S1Vc;S17Vs;R2R1A3A3A2Lnext;A2La;A2S2bS39S39S2bS3cS3cS29S5VX;Vs;R2R1A4S2cS0S1Vc;S18R2R1A2A3S0S1Vc;S74R1A1A3A2A2Lam;A2Lg;A2A2A2F_;").
  Proof using HI HX.
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - destruct (In_image_inv s c Hin) as [H|[H|(g & am & Hg & Hc)]]; [left; exact H | right; left; exact H |].
      right; right. exists g, am. split; [apply used_iff; exact Hg | left; exact Hc].
    - destruct (In_footer_cells_inv s c Hin) as (g & am & Hg & Hc).
      right; right. exists g, am. split; [apply used_iff; exact Hg | right; exact Hc].
  Qed.

  Lemma meet_entries c e1 e2 lo n : ltac2:(tb__ "0|2|
S0S6aS4S61A2M0Ve1;S10Vs;A1M1A3S0G0Ve2;G1A3S2dS2aG0Ve1;Ve2;A3A1SaScVL;Vc;A2S7VL;Ve1;A2A2SaS6bS61S61Vlo;Vn;A4S7VL;Ve2;A2A2S75VL;Vc;Vlo;Vn;A4S2eF_;F_;F_;F_;F_;F_;").
  Proof using HL.
    intros H1 H2 Hne I1 I2 (k & Hk & Hm).
    pose proof (fp_disjoint e1 e2 H1 H2 Hne) as D.
    unfold range_incl, cell_range, ranges_disjoint in *. cbn [fst snd] in *. lia.
  Qed.

  Lemma key_area q : ltac2:(tb__ "0|0|
S0S39Vq;SeVs;A1A3S2bS39S39S2bS61S61S29S0S39R2S41Vs;A1A3S29S29S31Z0R1A2S32R1S43A2A2S2aS39Vq;S3dR2S30S42S34S3aR1A2A2A2A3A2A2Lk;A2La;A2F_;").
  Proof using HI.
    intros Hq. pose proof (inv_keys HI) as (_ & KP & _).
    destruct (KP q Hq) as (a & k & Ha & Hk & E). exists a, k. split; [exact Ha|]. split; [|exact E].
    unfold handed in Hk. destruct (sptr_eqb a _).
    - pose proof (inv_keys HI) as (_ & _ & _ & _ & Hc). lia.
    - lia.
  Qed.

  Lemma meta_zone_in_area q a k : ltac2:(tb__ "0|0|
S2aS39Vq;S3dVa;S30S42S34S3aVk;A2A2A2A3S29S31Z0Vk;A2S32Vk;S43A2A2SaS6bS61S61S62VL;Vq;A2S3aA4S7VL;S79Va;A1A2A2F_;F_;").
  Proof using .
    intros -> Hk. unfold range_incl, crange, e_area, addr_of, loc_addr. destruct a as [r o]. cbn [fst snd padd].
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
  Qed.

  Lemma area_cells_meet a next k c : ltac2:(tb__ "0|1|
S29S31Z0Vk;A2S32Vk;S43A2A2S0S1Vc;S17Vs;Va;Vnext;A3A3S75VL;Vc;S62VL;S3dVa;S30S42S34S3aVk;A2A2A2M0A2S3aA4S0S1Vc;S1aG0S53S5dVs;A1G0A2A2A3F_;F_;F_;").
  Proof using .
    intros Hk Hc (j & Hj & Hm).
    unfold addr_of, loc_addr in Hm. destruct a as [r o]. cbn [padd] in Hm.
    unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    - exfalso. cbn in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w loc_addr padd] in Hm, Hj;
        unfold AREA_HDR, META_SIZE in *; lia.
    - apply in_flat_map in Hc as [k' [Hk' Hc]]. apply in_seq in Hk'.
      destruct (In_meta_slot_cells _ _ _ Hc) as (d & E & Hd & Hw). rewrite E in Hm. cbn [loc_addr padd] in Hm.
      assert (Z.of_nat k' = k) as <-.
      { unfold AREA_HDR, META_SIZE, METAS_PER_AREA in *. nia. }
      cbn [padd]. exact Hc.
  Qed.

  Theorem meta_zone q c : ltac2:(tb__ "0|0|
S0S39Vq;SeVs;A1A3S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S75VL;Vc;S62VL;Vq;A2S3aA4S0S1Vc;S1aVq;S16Vs;Vq;A2A2A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hq Hin Hm. destruct (key_area q Hq) as (a & k & Ha & Hk & Eq).
    pose proof (meta_zone_in_area q a k Eq Hk) as ZI. pose proof (e_area_In a Ha) as EA.
    destruct (cell_cases c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g & am & Hu & Hc)]].
    - exfalso. refine (meet_entries c e_ctx (e_area a) _ _ e_ctx_In EA _ (ctx_cell_in c Hc) ZI Hm). discriminate.
    - destruct (sptr_eq_dec a' a) as [->|Hne].
      + rewrite Eq. unfold MT. apply (area_cells_meet a next k c Hk Hc). rewrite <- Eq. exact Hm.
      + exfalso. refine (meet_entries c (e_area a') (e_area a) _ _ (e_area_In a' Ha') EA _ (area_cell_in a' next c Hc) ZI Hm).
        unfold e_area. intros E. injection E as E'. exact (Hne E').
    - exfalso. destruct (group_cell_in g am c Hu Hc) as (rg & Hr & Hkd & Hl & ER & RI & _).
      refine (meet_entries c (e_reg (prid (am_mem am)) rg) (e_area a) _ _ ER EA _ RI ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin a Ha) as Z0. rewrite <- Ea in Z0. exact (Z0 eq_refl).
  Qed.

  Definition aidx_cell (am : ameta) : mcell := ltac2:(tb__ "0|2|
S6eS1L_;S37S4fVam;A1Z0A2S6S13S3dS3bVam;A1Z8A2A1M0U1S24S4dVam;A1M1A1A3S6G0U4SbG1A1A3X6ex2").

  Lemma aidx_cell_In g am : ltac2:(tb__ "0|0|
S5VX;Vs;Vg;Vam;A4S0S1S78Vam;A1S3Vs;A1A3F_;").
  Proof using HI HX.
    intros Hu. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map.
    exists (g, am). split; [apply used_iff; exact Hu|]. cbn [fst snd]. unfold group_cells, aidx_cell. right. left.
    destruct (am_maplen am =? 0); reflexivity.
  Qed.

  Lemma own_cells_aidx g am c : ltac2:(tb__ "0|0|
S5VX;Vs;Vg;Vam;A4S2cS0S1Vc;S18Vg;Vam;A2A3S0S1Vc;S74Vam;A1A3A2S75VL;Vc;S30S62VL;S3bVam;A1A2Z8A2Z1A4S2aS1Vc;S78Vam;A1A3F_;F_;F_;").
  Proof using HI.
    intros Hu Hc (j & Hj & Hm).
    pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    unfold addr_of, loc_addr in Hm.
    destruct Hc as [Hc|Hc].
    - unfold group_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
      + destruct Hc as [<-|[<-|[]]].
        * exfalso. cbn [mc_loc mc_w loc_addr] in Hm, Hj. lia.
        * unfold aidx_cell. destruct (am_maplen am =? 0); reflexivity.
      + exfalso. apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi.
        destruct (In_slot_cells X R U s g am i c HI Hu ltac:(lia) Hc) as (d & E & Lo & _).
        rewrite E in Hm. destruct (am_mem am) as [r o]. cbn [loc_addr padd] in Hm.
        assert (0 <= stride_of am * i) by nia. unfold UNIT, IB in *. lia.
    - exfalso. unfold group_footer_cells in Hc. destruct Hc as [<-|Hc].
      + cbn [trailing_cell mc_loc mc_w] in Hm, Hj. unfold trailing_loc in Hm. destruct (am_mem am) as [r o]. cbn [loc_addr padd] in Hm.
        pose proof G as ((Glast & _) & _). assert (stride_of am <= stride_of am * (am_last am + 1)) by nia. unfold UNIT, IB in *. lia.
      + apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi.
        destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hc].
        pose proof G as (_ & _ & Gsl & _). pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3.
        destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
        unfold frame_footer_cells in Hc. destruct (fr_kind fr); [|destruct Hc].
        assert (0 <= stride_of am * i) by nia.
        apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
        * destruct (0 <? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]].
          cbn [mc_loc mc_w] in Hm, Hj. unfold frame_ptr, slot_start in Hm. destruct (am_mem am) as [r o]. cbn [loc_addr padd] in Hm.
          unfold UNIT, IB in *. lia.
        * destruct (5 <=? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]].
          cbn [mc_loc mc_w] in Hm, Hj. unfold slot_end, slot_start in Hm. destruct (am_mem am) as [r o]. cbn [loc_addr padd] in Hm.
          unfold UNIT, IB in *. lia.
        * destruct (5 <? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]].
          cbn [mc_loc mc_w] in Hm, Hj. unfold slot_end, slot_start in Hm. destruct (am_mem am) as [r o]. cbn [loc_addr padd] in Hm.
          unfold UNIT, IB in *. lia.
  Qed.

  Theorem aidx_zone g am c : ltac2:(tb__ "0|0|
S5VX;Vs;Vg;Vam;A4S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S75VL;Vc;S30S62VL;S3bVam;A1A2Z8A2Z1A4S2aS1Vc;S78Vam;A1A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hu Hin Hm.
    pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof (extent_pos _ _ _ _ _ G) as Ep.
    assert (E28 : 28 <= group_extent am).
    { unfold group_extent. pose proof G as ((Glast & _) & _). assert (stride_of am <= stride_of am * (am_last am + 1)) by nia.
      unfold UNIT, IB. lia. }
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hk Hl) as ER.
    assert (ZI : range_incl (addr_of L (am_mem am) + 8, 1) (crange L (e_reg (prid (am_mem am)) rg))).
    { unfold range_incl, crange, e_reg, addr_of, loc_addr. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *.
      unfold IB in Hext. lia. }
    destruct (cell_cases c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g' & am' & Hu' & Hc)]].
    - exfalso. refine (meet_entries c e_ctx _ _ _ e_ctx_In ER _ (ctx_cell_in c Hc) ZI Hm). discriminate.
    - exfalso. refine (meet_entries c (e_area a') _ _ _ (e_area_In a' Ha') ER _ (area_cell_in a' next c Hc) ZI Hm).
      unfold e_reg, e_area. intros E. injection E as Ea _. pose proof (area_not_origin a' Ha') as Z0. rewrite Ea in Z0. exact (Z0 eq_refl).
    - destruct (sptr_eq_dec g' g) as [->|Hne].
      + pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->. exact (own_cells_aidx g am c Hu Hc Hm).
      + exfalso. destruct (group_cell_in g' am' c Hu' Hc) as (rg' & Hr' & Hk' & Hl' & ER' & RI' & (d & E & Hd & Hw)).
        destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Ep'|Np].
        *
          destruct Hm as (j & Hj & Hm). rewrite E in Hm. unfold addr_of, loc_addr in Hm.
          destruct (am_mem am') as [r' o'] eqn:Em'. destruct (am_mem am) as [r o] eqn:Em. cbn [padd prid poff] in *. subst r'.
          pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'.
          destruct (inv_laminar HI g' am' g am Hu' Hu Hne ltac:(rewrite Em', Em; reflexivity)) as [D | [I | I]].
          -- unfold spans_disjoint in D. rewrite Em', Em in D. cbn [poff] in D.
             pose proof (extent_pos _ _ _ _ _ G') as Ep'.
             unfold IB in *. lia.
          --
             destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi & Fit).
             rewrite Em' in Lo. rewrite Memc in Lo. rewrite poff_slot_start, Em in Lo. cbn [poff] in Lo.
             assert (0 <= stride_of am * j0) by nia. unfold UNIT in *. lia.
          --
             destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi & Fit).
             destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
             pose proof (inv_groups HI cc ac Uc) as Gc. pose proof (extent_pos _ _ _ _ _ Gc) as Epc.
             assert (BODY : forall c', In c' (group_cells g' am') \/ In c' (group_footer_cells am') ->
                       exists d', mc_loc c' = LMem (padd (am_mem am') d') /\
                         (poff (am_mem am') + d' + Z.of_nat (mc_w c') <= o + 8 \/ o + 9 <= poff (am_mem am') + d')).
             { intros c' Hc'. rewrite Em in Lo, Hi. cbn [poff] in Lo, Hi.
               assert (B1 : poff (slot_start am' J) + UNIT * match ss_fr (nth_slot am' J) with Some f => fr_off f | None => 0 end <= o + 8).
               { rewrite HfrJ, Off, <- Memc. unfold UNIT. lia. }
               assert (B2 : o + 9 <= poff (slot_start am' J) + stride_of am' - IB).
               { rewrite <- Memc. lia. }
               assert (B3 : forall f, ss_fr (nth_slot am' J) = Some f -> fr_kind f = FUser -> o + 9 <= poff (frame_ptr am' J f) + fr_n f).
               { intros f Hf Hkf. rewrite HfrJ in Hf. injection Hf as <-. rewrite HkJ in Hkf. discriminate. }
               destruct Hc' as [Hc'|Hc'].
               - exact (group_cells_vs_body X R U s g' am' J (o + 8) (o + 9) c' HI Hu' HJ Hc' B1 B2).
               - exact (footer_cells_vs_body X R U s g' am' J (o + 8) (o + 9) c' HI Hu' HJ Hc' B1 B2 B3). }
             destruct (BODY c Hc) as (d' & E' & D'). rewrite E in E'. apply LMem_inj in E'. pose proof (f_equal poff E') as Eo.
             rewrite Em' in Eo, D'. cbn [padd poff] in Eo, D'. lia.
        * refine (meet_entries c (e_reg (prid (am_mem am')) rg') _ _ _ ER' ER _ RI' ZI Hm).
          unfold e_reg. intros E2. injection E2 as Er _. exact (Np Er).
  Qed.

  Lemma meta_ranges_disjoint q q' : ltac2:(tb__ "0|3|
S0S39Vq;SeVs;A1M0A3S0S39Vq';G0A3S2dS2aS39Vq;Vq';A3A1S2cS31S30S62VL;Vq;A2M1S3aA2S62VL;Vq';A2M2A2S31S30G2S3aA2G1A2A2F_;F_;F_;").
  Proof using HI HL.
    intros Hq Hq' Hne.
    destruct (key_area q Hq) as (a & k & Ha & Hk & Eq). destruct (key_area q' Hq') as (a' & k' & Ha' & Hk' & Eq').
    destruct (sptr_eq_dec a a') as [<-|Hna].
    - assert (k <> k') by (intros <-; apply Hne; rewrite Eq, Eq'; reflexivity).
      rewrite Eq, Eq'. unfold addr_of, loc_addr. destruct a as [r o]. cbn [padd].
      unfold AREA_HDR, META_SIZE in *. nia.
    - pose proof (fp_disjoint (e_area a) (e_area a') (e_area_In a Ha) (e_area_In a' Ha')
                    ltac:(unfold e_area; intros E; injection E as E'; exact (Hna E'))) as D.
      pose proof (meta_zone_in_area q a k Eq Hk) as I1. pose proof (meta_zone_in_area q' a' k' Eq' Hk') as I2.
      unfold ranges_disjoint, range_incl in *. cbn [fst snd] in *. lia.
  Qed.

  Lemma meta_vs_group q g am d : ltac2:(tb__ "0|2|
S0S39Vq;SeVs;A1A3S5VX;Vs;Vg;Vam;A4S29S31Z0Vd;A2S32Vd;S30S14Vam;A1S3eA2A2A2S2cS31S30S62VL;Vq;A2M0S3aA2S30S62VL;S3bVam;A1A2Vd;A2M1A2S31S30G1Z1A2G0A2A2F_;F_;F_;").
  Proof using HI HL.
    intros Hq Hu Hd.
    destruct (key_area q Hq) as (a & k & Ha & Hk & Eq). pose proof (meta_zone_in_area q a k Eq Hk) as I1.
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hkd Hl) as ER.
    pose proof (fp_disjoint (e_area a) (e_reg (prid (am_mem am)) rg) (e_area_In a Ha) ER) as D.
    specialize (D ltac:(unfold e_area, e_reg; intros E; injection E as Ea _; pose proof (area_not_origin a Ha) as Z0; rewrite Ea in Z0; exact (Z0 eq_refl))).
    unfold ranges_disjoint, range_incl, crange, e_area, e_reg, addr_of, loc_addr in *.
    destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. lia.
  Qed.

  Lemma used_mem_addr_ne g1 a1 g2 a2 : ltac2:(tb__ "0|0|
S5VX;Vs;Vg1;Va1;A4S5VX;Vs;Vg2;Va2;A4S2dS2aS39Vg1;Vg2;A3A1S2dS2aS61S62VL;S3bVa1;A1A2S62VL;S3bVa2;A1A2A3A1F_;F_;F_;").
  Proof using HI HL.
    intros Hu1 Hu2 Hne E.
    pose proof (inv_groups HI g1 a1 Hu1) as G1. pose proof (inv_groups HI g2 a2 Hu2) as G2.
    pose proof (extent_pos _ _ _ _ _ G1) as E1. pose proof (extent_pos _ _ _ _ _ G2) as E2.
    pose proof (stride_pos _ _ _ _ _ G1) as S1. pose proof (stride_pos _ _ _ _ _ G2) as S2.
    destruct (used_group_region X R U s g1 a1 HI Hu1) as (rg1 & Hr1 & Hk1 & Hl1 & Ho1 & Hext1 & _).
    destruct (used_group_region X R U s g2 a2 HI Hu2) as (rg2 & Hr2 & Hk2 & Hl2 & Ho2 & Hext2 & _).
    destruct (Nat.eq_dec (prid (am_mem a1)) (prid (am_mem a2))) as [Ep|Np].
    - destruct (inv_laminar HI g1 a1 g2 a2 Hu1 Hu2 Hne Ep) as [D|[I|I]].
      + unfold spans_disjoint in D. unfold addr_of, loc_addr in E.
        destruct (am_mem a1) as [r1 o1], (am_mem a2) as [r2 o2]. cbn [prid poff] in *. subst r2. lia.
      + destruct I as (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mc & Memc & Lo & Hi & Fit).
        pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
        assert (0 <= stride_of a2 * j) by nia.
        unfold addr_of, loc_addr in E. destruct (am_mem a1) as [r1 o1], (am_mem a2) as [r2 o2]. cbn [prid poff] in *. subst r2.
        unfold UNIT in *. lia.
      + destruct I as (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mc & Memc & Lo & Hi & Fit).
        pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
        assert (0 <= stride_of a1 * j) by nia.
        unfold addr_of, loc_addr in E. destruct (am_mem a1) as [r1 o1], (am_mem a2) as [r2 o2]. cbn [prid poff] in *. subst r2.
        unfold UNIT in *. lia.
    - pose proof (fp_disjoint _ _ (footprint_region_In s _ _ Hr1 Hk1 Hl1) (footprint_region_In s _ _ Hr2 Hk2 Hl2)
                    ltac:(intros EE; injection EE as Er _; exact (Np Er))) as D.
      unfold ranges_disjoint, crange, addr_of, loc_addr in *.
      destruct (am_mem a1) as [r1 o1], (am_mem a2) as [r2 o2]. cbn [fst snd prid poff] in *. unfold IB in *. lia.
  Qed.

  Lemma key_range q : ltac2:(tb__ "0|3|
S0S39Vq;SeVs;A1A3S67VL;Vs;Vvmz;A3S63VCz;Vvmz;A2S29S31S44S62VL;Vq;A2M0A2S29S31S30G0S3aA2M1S66VL;A1A2S29S2cS31G1S65VCz;A1A2S31S64VCz;A1G0A2A2S2cS31S30S11VL;A1M2SfA2G0A2S31G1G2A2A2A2A2A2F_;F_;F_;").
  Proof using HI HL.
    intros Hq HV HLG. destruct (key_area q Hq) as (a & k & Ha & Hk & Eq). pose proof (meta_zone_in_area q a k Eq Hk) as I1.
    pose proof (FpLaws.fp_mem_range Cz L s vmz a PGSZ HV HLG (e_area_In a Ha) ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
    pose proof (fp_disjoint e_ctx (e_area a) e_ctx_In (e_area_In a Ha) ltac:(discriminate)) as D.
    unfold ranges_disjoint, range_incl, crange, e_ctx, e_area, addr_of, loc_addr in *. destruct a as [r o]. cbn [fst snd padd] in *.
    unfold META_SIZE, PGSZ in *. lia.
  Qed.

  Lemma group_range g am : ltac2:(tb__ "0|3|
S5VX;Vs;Vg;Vam;A4S67VL;Vs;Vvmz;A3S63VCz;Vvmz;A2S29S31S44S62VL;S3bVam;A1A2M0A2S29S31S30S30G0S14Vam;A1A2S3eA2M1S66VL;A1A2S29S2cS31G1S65VCz;A1A2S31S64VCz;A1G0A2A2S2cS31S30S11VL;A1M2SfA2G0A2S31G1G2A2A2A2A2A2F_;F_;F_;").
  Proof using HI HL.
    intros Hu HV HLG.
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hkd Hl) as ER.
    pose proof (extent_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Ep.
    pose proof (FpLaws.fp_mem_range Cz L s vmz _ _ HV HLG ER ltac:(unfold IB in Hext; lia)) as (A1 & A2 & A3).
    pose proof (fp_disjoint e_ctx _ e_ctx_In ER ltac:(discriminate)) as D.
    unfold ranges_disjoint, range_incl, crange, e_ctx, e_reg, addr_of, loc_addr in *. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *.
    lia.
  Qed.

  Theorem ctx_zone c off n : ltac2:(tb__ "0|1|
S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S31Z0Voff;A2S31S30Voff;Vn;A2M0SfA2S75VL;Vc;S30S11VL;A1Voff;A2Vn;A4S29S0S1Vc;SdVs;A1A3S2bS61S61S29S2aS4S9Vc;A1S2R1A1A3S29S32R1G0A2S32Voff;S30R1S33S8Vc;A1A1A2A2A2A2Lo;A2A2F_;F_;F_;F_;").
  Proof using HI HL HX.
    intros Hin Ho Hn Hm.
    assert (ZI : range_incl (ly_ctx L + off, n) (crange L e_ctx)).
    { unfold range_incl, crange, e_ctx, loc_addr. cbn [fst snd]. lia. }
    destruct (cell_cases c Hin) as [Hc | [(a' & next & Ha' & Hc) | (g' & am' & Hu' & Hc)]].
    - split; [exact Hc|]. destruct (In_ctx_cells s c Hc) as (o & E & Ho' & Hw). exists o. split; [exact E|].
      destruct Hm as (k & Hk & Hm). rewrite E in Hm. unfold loc_addr in Hm. lia.
    - exfalso. refine (meet_entries c (e_area a') e_ctx _ _ (e_area_In a' Ha') e_ctx_In _ (area_cell_in a' next c Hc) ZI Hm). discriminate.
    - exfalso. destruct (group_cell_in g' am' c Hu' Hc) as (rg' & _ & _ & _ & ER' & RI' & _).
      refine (meet_entries c _ e_ctx _ _ ER' e_ctx_In _ RI' ZI Hm). discriminate.
  Qed.

  Lemma ctx_active_cell c sc : ltac2:(tb__ "0|2|
S29S31Z0Vsc;A2S32Vsc;Z30A2A2S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S75VL;Vc;S30S11VL;A1S30S12S34Z8M0Vsc;A2A2M1A2G0A4S2aS1Vc;S6S2G1A1U8S1bS1cVs;Vsc;A2A1A3A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hsc Hin Hm.
    destruct (ctx_zone c (CTX_active + 8 * sc) 8 Hin ltac:(unfold CTX_active; lia) ltac:(unfold CTX_active, CTX_SIZE; lia) Hm)
      as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_active s c sc o Hsc Hc E O1 O2).
  Qed.

  Lemma ctx_bounce_cell c k : ltac2:(tb__ "0|2|
S29S31Z0M0Vk;A2S32Vk;Z20A2A2S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S75VL;Vc;S30S11VL;A1S30S15Vk;A2M1A2Z1A4S2aS1Vc;S6S2G1A1U1SbS76S61S36Vk;A1S46Vs;A1G0A4A1A3A3F_;F_;F_;").
  Proof using HI HL HX.
    intros Hk Hin Hm.
    destruct (ctx_zone c (CTX_bounces + k) 1 Hin ltac:(unfold CTX_bounces; lia) ltac:(unfold CTX_bounces, CTX_SIZE; lia) Hm)
      as [Hc (o & E & O1 & O2)].
    exact (ctx_cells_at_bounce s c k o Hk Hc E O1 O2).
  Qed.

  Lemma meta_cells_in_imageI q c : ltac2:(tb__ "0|0|
S0S39Vq;SeVs;A1A3S0S1Vc;S1aVq;S16Vs;Vq;A2A2A3S0S1Vc;S3Vs;A1A3F_;F_;").
  Proof using HI.
    intros Hq Hc. destruct (key_area q Hq) as (a & k & Ha & Hk & Eq).
    unfold image. apply in_app_iff. right. apply in_app_iff. left.
    apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next. unfold area_cells. apply in_app_iff. right.
    apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|].
    rewrite Z2Nat.id by lia. rewrite <- Eq. exact Hc.
  Qed.

  Lemma user_block_in_group b : ltac2:(tb__ "0|8|
S0S6aS39S61A2M0Vb;S1fVs;A1A3S2bS39S39S2bS3cS3cS2bS61S61S2bS3fS3fS29S5VX;Vs;R4R3A4S29S29S31Z0M1R2A2S31R2S4eR3A1A2A2S29S2aS6cS3fA1S5bS54R3R2A2A1S6dS3fR1A2A3S29S2aS50S51R1A1S47A3S29S2aG0Vb;S6bS39S61S26R3R2R1A3S52R1A1A4A3S29S31S30S30S62VL;S3bR3A1A2M2S4cA2S34S60R3A1M3R2A2A2M4S62VL;S70S39S61Vb;A3A2M5A2S29S31S30G5S71S39S61Vb;A3M6A2S38S30G4G3A2S3eA2M7A2S29S31G1G6A2S31G7S30G2S14R3A1A2A2A2A2A2A2A2A2A2A2Lfr;A2Li;A2Lam;A2Lg;A2F_;").
  Proof using HI HX.
    intros Hb. destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & Eb).
    apply used_iff in Hg. exists g, am, i, fr. split; [exact Hg|]. split; [exact Hi|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Eb|].
    pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
    pose proof G as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
    rewrite Eb. cbn [fst snd]. unfold addr_of, loc_addr, frame_ptr, slot_start. destruct (am_mem am) as [r o]. cbn [padd].
    assert (0 <= stride_of am * i) by nia. assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    unfold group_extent, UNIT, IB in *. lia.
  Qed.

  Lemma image_outside_user_blocksI c b : ltac2:(tb__ "0|0|
S0S1Vc;S3Vs;A1A3S0S6aS39S61A2Vb;S1fVs;A1A3S1eScVL;Vc;A2S25VL;Vb;A2A2F_;F_;").
  Proof using HI HL HX.
    intros Hc Hb.
    destruct (user_block_in_group b Hb) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    pose proof (footprint_region_In s _ _ Hr Hkd Hl) as ER.
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as SpB. assert (Hsi : 0 <= stride_of am * i) by nia.
    assert (BI : range_incl (block_range L b) (crange L (e_reg (prid (am_mem am)) rg))).
    { unfold range_incl, block_range, crange, e_reg. rewrite Eb. cbn [fst snd]. rewrite Eb in B1, B2, B3. cbn [fst snd] in B1, B2, B3.
      unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *.
      unfold IB, UNIT in *. lia. }
    destruct (In_image_inv s c Hc) as [Hcx | [(a & next & Ha & Hca) | (g' & am' & Hg' & Hcg)]].
    - pose proof (fp_disjoint e_ctx _ e_ctx_In ER ltac:(discriminate)) as D. pose proof (ctx_cell_in c Hcx) as RI.
      unfold ranges_disjoint, range_incl, e_reg, e_ctx, e_area, crange in *. cbn [fst snd] in *. lia.
    - pose proof (fp_disjoint (e_area a) _ (e_area_In a Ha) ER) as D.
      specialize (D ltac:(unfold e_area, e_reg; intros E; injection E as Ea _; pose proof (area_not_origin a Ha) as Z0; rewrite Ea in Z0; exact (Z0 eq_refl))).
      pose proof (area_cell_in a next c Hca) as RI. unfold ranges_disjoint, range_incl, e_reg, e_ctx, e_area, crange in *. cbn [fst snd] in *. lia.
    - apply used_iff in Hg'. rename Hg' into Hu'.
      destruct (group_cell_in g' am' c Hu' (or_introl Hcg)) as (rg' & Hr' & Hk' & Hl' & ER' & RI' & (d & E & Hd & Hw)).
      destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Ep|Np].
      +
        destruct (sptr_eq_dec g' g) as [->|Hne].
        * pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
          destruct (group_cells_vs_body X R U s g am i (addr_of L (fst b) - ly_reg L (prid (am_mem am))) (addr_of L (fst b) + snd b - ly_reg L (prid (am_mem am))) c HI Hu Hi Hcg) as (d2 & E2 & D2).
          -- rewrite Hfr. rewrite Eb. cbn [fst]. unfold addr_of, loc_addr, frame_ptr, slot_start. destruct (am_mem am) as [r o]. cbn [padd prid poff]. lia.
          -- rewrite Eb in B2 |- *. cbn [fst snd] in *. rewrite poff_slot_start. unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
             destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. lia.
          -- unfold ranges_disjoint, cell_range, block_range. rewrite E2. rewrite Eb. cbn [fst snd].
             rewrite Eb in D2. cbn [fst snd] in D2. unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
             destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. lia.
        * destruct (inv_laminar HI g' am' g am Hu' Hu Hne Ep) as [Dj | [I | I]].
          -- unfold spans_disjoint in Dj. unfold ranges_disjoint, cell_range, block_range. rewrite E. rewrite Eb. cbn [fst snd].
             rewrite Eb in B1, B2. cbn [fst snd] in B1, B2.
             destruct (In_group_cells_span X R U s g' am' c HI Hu' Hcg) as (d2 & E2 & Hd2 & Hw2).
             rewrite E in E2. apply LMem_inj in E2. pose proof (f_equal poff E2) as Eo. rewrite !poff_padd in Eo.
             unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
             destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. unfold UNIT, IB in *. lia.
          --
             destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo & Hi' & Fit).
             assert (Hj0i : j0 <> i) by (intros ->; rewrite Hfr in Hfr0; injection Hfr0 as ->; rewrite Hk in Hk0; discriminate).
             pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
             destruct (fgroup_frame X R U s HI g am j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn0 Off0].
             pose proof (f_equal poff Memc) as Eo. rewrite poff_slot_start in Eo.
             unfold ranges_disjoint, cell_range, block_range. rewrite E. rewrite Eb. cbn [fst snd]. rewrite Eb in B1, B2. cbn [fst snd] in B1, B2.
             unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
             destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'.
             assert (i < j0 \/ j0 < i) as [LT|LT] by lia.
             ++ assert (stride_of am * i + stride_of am <= stride_of am * j0) by nia. unfold UNIT, IB in *. lia.
             ++ assert (stride_of am * j0 + stride_of am <= stride_of am * i) by nia.
                pose proof (inv_groups HI cc ac Uc) as Gc. unfold group_extent in *. unfold UNIT, IB in *. nia.
          --
             destruct I as (J & frJ & cc & ac & HJ & HfrJ & HkJ & Uc & Mc & Memc & Lo & Hi' & Fit).
             destruct (fgroup_frame X R U s HI g' am' J frJ Hu' HJ HfrJ HkJ) as [Fn Off].
             pose proof (f_equal poff Memc) as Eo.
             rewrite Eb in B1, B2. cbn [fst snd] in B1, B2.
             destruct (group_cells_vs_body X R U s g' am' J (addr_of L (frame_ptr am i fr) - ly_reg L (prid (am_mem am')))
                         (addr_of L (frame_ptr am i fr) + fr_n fr - ly_reg L (prid (am_mem am'))) c HI Hu' HJ Hcg) as (d2 & E2 & D2).
             ++ rewrite HfrJ, Off, <- Memc. unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
                destruct (am_mem ac) as [rc oc], (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. unfold UNIT in *. lia.
             ++ rewrite <- Memc. unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
                destruct (am_mem ac) as [rc oc], (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'.
                unfold group_extent in *. unfold UNIT, IB in *. lia.
             ++ unfold ranges_disjoint, cell_range, block_range. rewrite E2. rewrite Eb. cbn [fst snd].
                unfold addr_of, loc_addr in *. unfold frame_ptr, slot_start in *.
                destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia.
      + pose proof (fp_disjoint _ _ ER' ER ltac:(intros E2; injection E2 as Er _; exact (Np Er))) as D.
        unfold ranges_disjoint, range_incl, e_reg, e_ctx, e_area, crange in *. cbn [fst snd] in *. lia.
  Qed.

  Lemma image_cell_owned c : ltac2:(tb__ "0|0|
S0S1Vc;S3Vs;A1A3S68S77R1S8Vc;A1A2S1dVL;Vs;S30S19VL;S9Vc;A1A2S33R2A1A2A3F_;Fj;F_;").
  Proof using HI HL HX.
    intros Hc j Hj. split.
    - destruct (In_image_inv s c Hc) as [Hcx | [(a & next & Ha & Hca) | (g & am & Hg & Hcg)]].
      + exists e_ctx. split; [apply e_ctx_In|]. pose proof (ctx_cell_in c Hcx) as RI. unfold range_incl, cell_range, crange, e_ctx in *. cbn [fst snd] in *. lia.
      + exists (e_area a). split; [apply e_area_In; exact Ha|]. pose proof (area_cell_in a next c Hca) as RI.
        unfold range_incl, cell_range, crange, e_area in *. cbn [fst snd] in *. lia.
      + apply used_iff in Hg. destruct (group_cell_in g am c Hg (or_introl Hcg)) as (rg & _ & _ & _ & ER & RI & _).
        eexists. split; [exact ER|]. unfold range_incl, cell_range, crange, e_reg in *. cbn [fst snd] in *. lia.
    - intros (b & Hb & Hx). pose proof (image_outside_user_blocksI c b Hc Hb) as D.
      unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. lia.
  Qed.

  Lemma cell_in_footprintI c : ltac2:(tb__ "0|1|
S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S2bS6aS4S61A2M0G0S29S0G0R1S10Vs;A1A3SaScVL;Vc;A2S7VL;R1A2A2A2Lrg;A2F_;").
  Proof using HI HX.
    intros Hin. destruct (cell_cases c Hin) as [Hc | [(a & next & Ha & Hca) | (g & am & Hu & Hcg)]].
    - exists e_ctx. split; [apply e_ctx_In | apply ctx_cell_in; exact Hc].
    - exists (e_area a). split; [apply e_area_In; exact Ha | apply (area_cell_in a next); exact Hca].
    - destruct (group_cell_in g am c Hu Hcg) as (rg & _ & _ & _ & ER & RI & _). eexists. split; [exact ER | exact RI].
  Qed.

  Lemma cell_w_posI c : ltac2:(tb__ "0|0|
S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S77U0S8Vc;A1A2F_;").
  Proof using .
    intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [apply (ImageUpd.image_cell_w s c Hin)|].
    destruct (In_footer_cells_inv s c Hin) as (g & am & Hg & Hc). exact (ImageUpd.footer_cell_w am c Hc).
  Qed.

  Lemma cell_spanI c : ltac2:(tb__ "0|1|
S0S1Vc;S69S1S3Vs;A1S73Vs;A1A3A3S29S32Z0S19VL;S9Vc;A1A2M0A2S32S30G0S33S8Vc;A1A1A2S35Z2Z3fA2A2A2F_;").
  Proof using HI HL HX.
    intros Hin. destruct (cell_in_footprintI c Hin) as (rg & Hrg & [I1 I2]).
    pose proof HL as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    unfold cell_range in I1, I2. cbn [fst snd] in I1, I2. lia.
  Qed.

  Lemma owned_spanI x : ltac2:(tb__ "0|0|
S1dVL;Vs;Vx;A3S29S32Z0Vx;A2S32Vx;S35Z2Z3fA2A2A2F_;").
  Proof using HL.
    intros [(rg & Hrg & Hx) _]. pose proof HL as (_ & _ & _ & POS). destruct (POS rg Hrg) as [P1 P2].
    unfold crange in P1, P2. cbn [fst snd] in P1, P2. lia.
  Qed.

End Z2.
