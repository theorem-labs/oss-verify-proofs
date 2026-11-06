(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap.KM"; "km_a"; "km_s'"; "km_n"; "km_vm'"; "km_m'"; "inK"; "km_e"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "byteview_of"; "range_in_maps"; "holds"; "mc_img_hi"; "mc_img_lo"; "topL"; "statics_ok"; "vm_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "region"; "PGSZ"; "sptr"; "rg_live"; "st_regions"; "RkMap"; "mkRegion"; "rg_len"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_brk"; "st_init_done"; "st_meta_alloc_shift"; "st_metas"; "st_usage"; "RkBrk"; "SP"; "am_maplen"; "am_mem"; "ameta"; "brkst"; "lupd"; "mslot"; "prid"; "rg_kind"; "rkind"; "set_regions"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "app"; "nat"; "bool"; "Some"; "pair"; "true"; "cons"; "fst"; "snd"; "false"; "length"; "nil"; "None"; "@Stdlib.Lists.List"; "In"; "flat_map"; "NoDup"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "region_of"; "loc"; "footprint"; "cell_holds"; "image"; "mcell"; "pairwise"; "crange"; "keys"; "loc_addr"; "ly_reg"; "user_blocks"; "Inv"; "LMem"; "mc_loc"; "mc_w"; "ranges_disjoint"; "usedX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_maps"; "vm_noaccess"; "vm_brk"; "vm_reserved"; "vm_start_brk"; "map_remove"; "maps_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "wok_of"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "owned_mapped"; "reprO"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "in_range"; "unmap_range"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfMeta MallocWfGeom MallocWfRepr MallocWfGroup MallocLayout MallocFooter
  MallocIface MallocIfaceI MallocLaws Contract FpLaws Zones2 MapsWf WalkArith ImageDelta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma pairwise_app_drop {A} (Rr : A -> A -> Prop) (u v : list A) (x : A) : ltac2:(tb__ "0|0|
S54VA;VRr;S3bVA;Vu;S41VA;Vx;Vv;A3A3A3S54VA;VRr;S3bVA;Vu;Vv;A3A3F_;").
Proof.
  revert v. induction u as [|h u IH]; intros v Hp; cbn in *.
  - exact (proj2 Hp).
  - destruct Hp as [H1 H2]. split; [|exact (IH v H2)].
    intros y Hy. apply H1. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
Qed.

Lemma flat_map_exteq {A B} (F F' : A -> list B) (l : list A) : ltac2:(tb__ "0|1|
VA;S48VA;R1Vl;A3S0S39VB;A1M0VF';R2A1VF;R2A1A3F_;Fk;S0G0S49VA;VB;VF';Vl;A4S49VA;VB;VF;Vl;A4A3F_;").
Proof.
  induction l as [|h t IH]; intros HF; [reflexivity|]. cbn. rewrite (HF h ltac:(left; reflexivity)), IH; [reflexivity|].
  intros k Hk. apply HF. right. exact Hk.
Qed.

Lemma flat_map_remove {A B} (F F' : A -> list B) (l : list A) (x : A) : ltac2:(tb__ "0|1|
S4aVA;Vl;A2S48VA;Vx;Vl;A3VA;S48VA;R1Vl;A3S2S0VA;R2Vx;A3A1S0S39VB;A1M0VF';R3A1VF;R3A1A3F_;F_;Fk;S3G0G0S3G0G0S1S0G0S49VA;VB;VF;Vl;A4S3bVB;R2S3bVB;VF;Vx;A1R1A3A3A3S0G0S49VA;VB;VF';Vl;A4S3bVB;R2S3bVB;VF';Vx;A1R1A3A3A3A2Ll2;A2Ll1;A2F_;F_;F_;").
Proof.
  induction l as [|h t IH]; intros ND Hin HF; [destruct Hin|].
  inversion ND as [|h' t' Hh Ht]; subst. cbn.
  destruct Hin as [->|Hin].
  - exists [], (flat_map F t). split; [reflexivity|]. cbn. f_equal.
    apply flat_map_exteq. intros k Hk. apply HF; [right; exact Hk|]. intros ->. exact (Hh Hk).
  - destruct (IH Ht Hin ltac:(intros k Hk Hne; apply HF; [right; exact Hk | exact Hne])) as (l1 & l2 & E1 & E2).
    exists (F h ++ l1), l2. rewrite E1, E2. rewrite (HF h ltac:(left; reflexivity) ltac:(intros ->; exact (Hh Hin))).
    rewrite !app_assoc. split; reflexivity.
Qed.

Section KM.
  Variables (segs : list Segment) (C : mconsts).
  Hypothesis HS : statics_in_image C.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
  Variables (m : word -> option byte) (vm : VmMaps) (r : nat) (rg : region).
  Hypothesis HMI : ltac2:(tb__ "0|0|
S6fVC;VX;VR;VU;S6eVs;VL;A2S67Vsegs;Vm;A2S68Vsegs;Vm;A2Vvm;A8").
  Hypothesis HXr : xraw X s.
  Hypothesis HRr : ltac2:(tb__ "0|0|
S0S3aS1cA1S4eVs;Vr;A2S3eS1cVrg;A2A3").
  Hypothesis HRk : rg_kind rg = RkMap.
  Hypothesis HRl : rg_live rg = true.
  Hypothesis Hno : ltac2:(tb__ "0|0|
S1eS30S5fVX;Vs;R2R1A4SfZ0S2eR2A1A2S2S0S3cS34S2fR3A1A1Vr;A3A1F_;F_;Fa;Fq;").
  Hypothesis Hinit : st_init_done s = true.

  Definition km_a : Z := ly_reg L r.
  Definition km_n : Z := rg_len rg.
  Definition km_s' : astate := ltac2:(tb__ "0|0|
S37S32S1cS20Vs;A1Vr;S22S21S7S46ScA1S44A4A4Vs;A2").
  Definition km_m' : word -> option byte := ltac2:(tb__ "0|0|
S72Vm;S13S5A1S13S7A1A3").
  Definition km_vm' : VmMaps := ltac2:(tb__ "0|0|
S70Vvm;S13S5A1S13S7A1A3").

  Let HI : Inv X R U s := mig_I HMI.
  Let HL : layout_ok L s := mig_layout HMI.
  Let HV : vm_ok L s vm := mig_vm HMI.
  Let HLG : ledger_ok C vm := mig_ledger HMI.
  Let HMW : maps_wf vm := mig_maps HMI.

  Definition km_e : loc * Z := ltac2:(tb__ "0|0|
S3fS4fScS5bS2dVr;Z0A2A1S7A4").
  Lemma e_In : In km_e (footprint s). Proof using HRk HRl HRr. exact (footprint_region_In s r rg HRr HRk HRl). Qed.
  Lemma e_crange : ltac2:(tb__ "0|0|
S0S38ScScA2S55VL;SbA2S3fScScS5S7A4A3"). Proof using . unfold crange, km_e, km_a. cbn [fst snd loc_addr]. rewrite Z.add_0_r. reflexivity. Qed.

  Lemma a_range : ltac2:(tb__ "0|0|
S1SdS1dS5A2S1SdSeS5S7A2S19VL;A1A2SdS1dS7A2A2A2").
  Proof using HRl HRr HV.
    pose proof HV as (_ & _ & _ & _ & _ & _ & V7 & V8 & _).
    pose proof (V8 r rg HRr HRl) as [A B]. pose proof (V7 r rg HRr HRl) as Cn. unfold km_a, km_n. lia.
  Qed.
  Lemma a64 : ltac2:(tb__ "0|1|
S1SdZ0M0S5A2S1SfSeS5S7A2S11Z2Z40A2A2SfG0S7A2A2A2").
  Proof using HRl HRr HV. pose proof a_range. top_ranges. unfold PGSZ in *. lia. Qed.
  Lemma Ua : ltac2:(tb__ "0|0|
S0ScS4cQ40S13S5A1A2S5A3"). Proof using HRl HRr HV. unfold wz. apply u64. pose proof a64. lia. Qed.
  Lemma Un : ltac2:(tb__ "0|0|
S0ScS4cQ40S13S7A1A2S7A3"). Proof using HRl HRr HV. unfold wz. apply u64. pose proof a64. lia. Qed.

  Lemma entry_In : ltac2:(tb__ "0|1|
S48S38S4bQ40A1M0G0A2S3fG0G0S13S5A1S13S7A1A4S60Vvm;A1A3").
  Proof using HRk HRl HRr HV. pose proof HV as (V1 & _). exact (V1 r rg HRr HRl HRk). Qed.

  Lemma a_off_image : ltac2:(tb__ "0|0|
S4SdSeS5S7A2S18VC;A1A2SdS17VC;A1S5A2A2").
  Proof using HLG HRk HRl HRr HV. pose proof (HLG _ entry_In) as (_ & _ & G). cbn [fst snd] in G. rewrite Ua, Un in G. exact G. Qed.

  Lemma s'_fields : ltac2:(tb__ "0|2|
S1S0S39S1eA1M0S24S6A1S24Vs;A1A3S1S0S39S38S1eS33A2A1S2aS6A1S2aVs;A1A3S1S0S31S27S6A1S27Vs;A1A3S1S0S3dS28S6A1S28Vs;A1A3S1S0S39ScA1S2bS6A1S2bVs;A1A3S1S0ScS29S6A1S29Vs;A1A3S1S0ScS25S6A1S25Vs;A1A3S1S0S1eS26S6A1S26Vs;A1A3S1S0S3cS45S1cS20S6A1A2S45S1cS20Vs;A1A2A3S1S0S39S53A1M1S52S6A1S52Vs;A1A3S1S0G1S6aS6A1S6aVs;A1A3S1S0S39S38S1eScA2A1S59S6A1S59Vs;A1A3S0G0S56S6A1S56Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HMI HRr HXr Hinit Hno.
    assert (EI : image km_s' = image s).
    { unfold image. rewrite (areas_cells_metas km_s' s) by reflexivity. unfold km_s'. destruct s; reflexivity. }
    rewrite EI. unfold km_s'. destruct s; cbn. repeat split; try reflexivity. apply length_lupd.
  Qed.

  Lemma region_of'_other k : ltac2:(tb__ "0|0|
S2S0S3cVk;Vr;A3A1S0S3aS1cA1S4eS6Vk;A2S4eVs;Vk;A2A3F_;").
  Proof using . intros Hne. unfold km_s'. rewrite region_of_upd. replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact Hne). reflexivity. Qed.
  Lemma region_of'_r : ltac2:(tb__ "0|0|
S0S3aS1cA1S4eS6Vr;A2S3eS1cS22S21S7S46ScA1S44A4A2A3").
  Proof using HRr.
    unfold km_s'. rewrite region_of_upd. rewrite Nat.eqb_refl.
    replace (Nat.ltb r (length (st_regions s))) with true by (symmetry; apply Nat.ltb_lt; eapply region_of_lt; exact HRr). reflexivity.
  Qed.
  Lemma live'_live k rg' : ltac2:(tb__ "0|2|
S0S3aS1cA1M0S4eS6Vk;A2S3eS1cVrg';A2M1A3S0S3dS1fVrg';A1S40A3S1S2S0S3cVk;Vr;A3A1S0G0S4eVs;Vk;A2G1A3A2F_;F_;").
  Proof using HRr.
    intros H HRl'. destruct (Nat.eq_dec k r) as [->|Hne].
    - rewrite region_of'_r in H. injection H as <-. discriminate HRl'.
    - split; [exact Hne|]. rewrite <- (region_of'_other k Hne). exact H.
  Qed.

  Lemma HI' : ltac2:(tb__ "0|0|
S5aVX;VR;VU;S6A4").
  Proof using HI HRk HRr Hno. unfold km_s', km_n. exact (Inv_kill_map X R U s r rg HI HRr HRk Hno). Qed.
  Lemma HXr' : xraw X km_s'.
  Proof using HMI HRr HXr Hinit Hno. unfold xraw, MT, mlookup in *. rewrite (proj1 (proj2 s'_fields)). exact HXr. Qed.

  Lemma footprint_split : ltac2:(tb__ "0|2|
S3S39S38S4fScA2M0A1M1G1S3G1G1S1S0G1S50Vs;A1S3bG0R2S41G0SbR1A3A3A3S0G1S50S6A1S3bG0R2R1A3A3A2Ll2;A2Ll1;A2").
  Proof using HMI HRk HRl HRr HXr Hinit Hno.
    unfold footprint. rewrite (proj1 s'_fields). rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 s'_fields))))))))).
    set (F := fun k => match region_of s k with Some rg0 => match rg_kind rg0 with RkMap => if rg_live rg0 then [(LMem (SP k 0), rg_len rg0)] else [] | _ => [] end | None => [] end).
    set (F' := fun k => match region_of km_s' k with Some rg0 => match rg_kind rg0 with RkMap => if rg_live rg0 then [(LMem (SP k 0), rg_len rg0)] else [] | _ => [] end | None => [] end).
    destruct (flat_map_remove F F' (seq 0 (length (st_regions s))) r) as (l1 & l2 & E1 & E2).
    - apply seq_NoDup.
    - apply in_seq. pose proof (region_of_lt _ _ _ HRr). lia.
    - intros k _ Hne. unfold F, F'. rewrite (region_of'_other k Hne). reflexivity.
    - change (flat_map ?g (seq 0 (length (st_regions s)))) with (flat_map F (seq 0 (length (st_regions s)))) at 1.
      rewrite E1. change (flat_map ?g (seq 0 (length (st_regions s)))) with (flat_map F' (seq 0 (length (st_regions s)))).
      rewrite E2.
      assert (EF : F r = [km_e]) by (unfold F; rewrite HRr, HRk, HRl; reflexivity).
      assert (EF' : F' r = []) by (unfold F'; rewrite region_of'_r; reflexivity).
      rewrite EF, EF'. cbn [app].
      exists ((LCtx 0, CTX_SIZE) :: map (fun a : sptr => (LMem a, PGSZ)) (st_areas s) ++ l1), l2.
      cbn [app]. rewrite <- !app_assoc. split; reflexivity.
  Qed.

  Lemma pairwise_mid {A} (Rr : A -> A -> Prop) (u v : list A) (x y : A) : ltac2:(tb__ "0|0|
S54VA;VRr;S3bVA;Vu;S41VA;Vx;Vv;A3A3A3S48VA;Vy;S3bVA;Vu;Vv;A3A3S4VRr;Vy;Vx;A2VRr;Vx;Vy;A2A2F_;F_;").
  Proof using .
    revert v. induction u as [|h u IH]; intros v Hp Hy; cbn in *.
    - right. exact (proj1 Hp y Hy).
    - destruct Hp as [H1 H2]. destruct Hy as [<-|Hy].
      + left. apply H1. apply in_app_iff. right. left. reflexivity.
      + exact (IH v H2 Hy).
  Qed.

  Lemma footprint'_old e : ltac2:(tb__ "0|1|
S48S38S4fScA2M0Ve;S50S6A1A3S1S48G0Ve;S50Vs;A1A3S5eS55VL;Ve;A2S3fScScS5S7A4A2A2F_;").
  Proof using HL HRk HRl HRr HXr Hinit Hno.
    destruct footprint_split as (l1 & l2 & E1 & E2). rewrite E1, E2. intros Hin.
    split; [apply in_app_iff in Hin as [H|H]; apply in_app_iff; [left; exact H | right; right; exact H]|].
    pose proof HL as (_ & _ & PW & _). rewrite E1, map_app in PW. cbn [map] in PW. rewrite <- e_crange.
    destruct (pairwise_mid ranges_disjoint (map (crange L) l1) (map (crange L) l2) (crange L km_e) (crange L e) PW
                ltac:(rewrite <- map_app; apply in_map; exact Hin)) as [D|D]; [exact D|].
    unfold ranges_disjoint in *. lia.
  Qed.

  Lemma e_not_In' : ltac2:(tb__ "0|0|
S2S48S38S4fScA2SbS50S6A1A3A1").
  Proof using HL HRk HRl HRr HV HXr Hinit Hno.
    intros Hin. destruct (footprint'_old km_e Hin) as [_ D]. rewrite e_crange in D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    pose proof a64. lia.
  Qed.

  Lemma HL' : layout_ok L km_s'.
  Proof using HL HRk HRl HRr HXr Hinit Hno.
    pose proof HL as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [|split].
    - intros k rg' HRk' HRl'. destruct (live'_live k rg' HRk' HRl') as [_ H]. exact (A2 k rg' H HRl').
    - destruct footprint_split as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in A3. rewrite map_app in *. cbn [map] in A3.
      exact (pairwise_app_drop _ _ _ _ A3).
    - intros e He. exact (A4 e (proj1 (footprint'_old e He))).
  Qed.

  Lemma Hbounded' : bounded km_s'.
  Proof using HMI HRr HXr Hinit Hno.
    pose proof (mig_bounded HMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in *.
    pose proof s'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & _).
    unfold bounded, usage_of in *. rewrite F1, F5, F6, F7, F8, F9. auto.
  Qed.

  Definition inK (x : Z) : Prop := ltac2:(tb__ "0|0|
S1SdS5Vx;A2SfVx;SeS5S7A2A2A2").

  Lemma m'_at x : ltac2:(tb__ "0|2|
S0S3aS4bQ8A1M0A1M1S9Vx;A1S3dG1L_;S71S13S5A1S13S7A1Vx;A3S47G0A1Vm;Vx;A1X3dx2A3").
  Proof using . unfold km_m'. apply unmap_range_at. Qed.
  Lemma m'_out x : ltac2:(tb__ "0|1|
S1SdZ0Vx;A2SfVx;S11Z2Z40A2A2A2S2SaVx;A1A1S0S3aS4bQ8A1A1S9S4dQ40Vx;A2M0A1Vm;G0A1A3F_;F_;").
  Proof using HRl HRr HV.
    intros Hx NK. rewrite m'_at. unfold in_range. rewrite Ua, Un, u64 by lia.
    destruct (km_a <=? x) eqn:E1; destruct (x <? km_a + km_n) eqn:E2; cbn [andb]; try reflexivity.
    exfalso. apply NK. apply Z.leb_le in E1. apply Z.ltb_lt in E2. unfold inK. lia.
  Qed.

  Let bv0 : byteview := ltac2:(tb__ "0|0|
S14S67Vsegs;Vm;A2S68Vsegs;Vm;A2A2").
  Let rv0 : byteview := ltac2:(tb__ "0|0|
S14S67Vsegs;Vm;A2S4bQ40A1S40L_;A2").
  Let bv1 : byteview := ltac2:(tb__ "0|0|
S14S67Vsegs;S9A2S68Vsegs;S9A2A2").
  Let rv1 : byteview := ltac2:(tb__ "0|0|
S14S67Vsegs;S9A2S4bQ40A1S40L_;A2").

  Lemma views_out x : ltac2:(tb__ "0|1|
S2SaVx;A1A1S1S0S3aScA1M0Vbv1;Vx;A1Vbv0;Vx;A1A3S0G0Vrv1;Vx;A1Vrv0;Vx;A1A3A2F_;").
  Proof using HRl HRr HV.
    intros NK. unfold bv1, bv0, rv1, rv0, byteview_of.
    destruct (0 <=? x) eqn:E1; destruct (x <? 2 ^ 64) eqn:E2; cbn [andb]; try (split; reflexivity).
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold Contract.rd_of, Contract.wok_of. rewrite (m'_out x) by (auto; lia). split; reflexivity.
  Qed.

  Lemma fp'_out e x : ltac2:(tb__ "0|1|
S48S38S4fScA2Ve;S50S6A1A3S1SdS57VL;S42S4fScVe;A3A2M0Vx;A2SfVx;SeG0S43S4fScVe;A3A2A2A2S2SaVx;A1A1F_;F_;").
  Proof using HL HRk HRl HRr HXr Hinit Hno.
    intros He Hx K. destruct (footprint'_old e He) as [_ D]. unfold ranges_disjoint, crange, inK in *. cbn [fst snd] in D. lia.
  Qed.

  Lemma cell_holds_ext (b0 b1 : byteview) c : ltac2:(tb__ "0|2|
S3cS69R1S5dVc;A1M0A2S0S3aScA1Vb1;SeS57VL;S5cVc;A1A2S10R2A1A2M1A1Vb0;G1A1A3F_;Fk;S69U0G0A2S51VL;Vb0;Vc;A3S51VL;Vb1;Vc;A3F_;F_;F_;").
  Proof using .
    intros B Hw Hc. unfold cell_holds in *. destruct (mc_val c).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
    - destruct Hc as (b & Hb & Hm5). exists b. split; [|exact Hm5]. specialize (B 0%nat Hw). rewrite Z.add_0_r in B. rewrite B. exact Hb.
    - intros j Hj. rewrite (B j Hj). exact (Hc j Hj).
  Qed.

  Lemma cells' : ltac2:(tb__ "0|1|
S1S6dS53S51VL;Vbv1;A2M0S52S6A1A3S6dS53G0S6aS6A1A3A2").
  Proof using HI HL HRk HRl HRr HV HXr Hinit Hno bv0 rv0 rv1.
    pose proof (mig_reprO HMI) as [[_ [HI0 _]] HF0]. cbn [ma_s ma_L] in HI0, HF0.
    pose proof s'_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EI & EF & _).
    assert (ALL : forall c, In c (image km_s' ++ footer_cells km_s') -> cell_holds L bv1 c).
    { intros c Hc.
      destruct (cell_in_footprintI X R U km_s' L HI' HXr' c Hc) as (e & He & [I1 I2]). unfold cell_range in I1, I2. cbn [fst snd] in I1, I2.
      unfold crange in I1, I2. cbn [fst snd] in I1, I2.
      apply (cell_holds_ext bv0 bv1 c).
      - intros k Hkw. assert (ZK : Z.of_nat k < Z.of_nat (mc_w c)) by (apply Nat2Z.inj_lt; exact Hkw).
        eapply (fun XX => proj1 (views_out _ (fp'_out e _ He XX))). lia.
      - exact (cell_w_posI km_s' c Hc).
      - rewrite EI, EF in Hc. apply in_app_iff in Hc as [Hc|Hc]; [exact (proj1 (Forall_forall _ _) HI0 c Hc) | exact (proj1 (Forall_forall _ _) HF0 c Hc)]. }
    split; apply Forall_forall; intros c Hc; apply ALL; apply in_app_iff; [left|right]; exact Hc.
  Qed.

  Lemma owned' : ltac2:(tb__ "0|0|
S6bVL;S6Vbv1;A3").
  Proof using HL HRk HRl HRr HV HXr Hinit Hno bv0 rv0 rv1.
    pose proof (mig_reprO HMI) as [[_ [_ HO0]] _]. cbn [ma_s ma_L] in HO0.
    intros x [(e & He & Hx) Hnu]. rewrite (proj1 (views_out x (fp'_out e x He Hx))). apply HO0. split.
    - exists e. split; [exact (proj1 (footprint'_old e He)) | exact Hx].
    - intros (b & Hb & Hxb). apply Hnu. exists b. pose proof s'_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EU & _). rewrite EU. auto.
  Qed.

  Lemma reprO' : ltac2:(tb__ "0|0|
S6cVL;S6Vbv1;A3").
  Proof using HI HL HRk HRl HRr HV HXr Hinit Hno bv0 rv0 rv1. destruct cells' as [CI CF]. split; [split; [exact HL' | split; [exact CI | exact owned']] | exact CF]. Qed.

  Lemma img_out x : ltac2:(tb__ "0|0|
S1SdS18VC;A1Vx;A2SfVx;S17VC;A1A2A2S2SaVx;A1A1F_;").
  Proof using HLG HRk HRl HRr HV. intros Hx K. pose proof a_off_image. unfold inK in K. lia. Qed.

  Lemma holds_ext (b0 b1 : byteview) a0 w v : ltac2:(tb__ "0|1|
S3cS69R1Vw;A2S0S3aScA1Vb1;SeVa0;S10R2A1A2M0A1Vb0;G0A1A3F_;Fk;S16Vb0;Va0;Vw;Vv;A4S16Vb1;Va0;Vw;Vv;A4F_;F_;").
  Proof using . intros B H k Kk. rewrite (B k Kk). exact (H k Kk). Qed.

  Lemma statics' : ltac2:(tb__ "0|0|
S1aVC;Vrv1;Vbv1;A3").
  Proof using HLG HRk HRl HRr HS HV bv0 rv0.
    pose proof (mig_statics HMI) as ST. cbn [ma_s ma_L] in ST. fold rv0 bv0 in ST.
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (Ilibc & Irep & Isc & Ismall & Imed & Ictz & Igot & Iguard & Ilock & Ictx & Ierr & Hpg & Hceil).
    destruct ST as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & (gd & T9 & T10)).
    assert (RV : forall x, mc_img_lo C <= x < mc_img_hi C -> rv1 x = rv0 x) by (intros x Hx; exact (proj2 (views_out x (img_out x Hx)))).
    assert (BV : forall x, mc_img_lo C <= x < mc_img_hi C -> bv1 x = bv0 x) by (intros x Hx; exact (proj1 (views_out x (img_out x Hx)))).
    unfold statics_ok, mc_need_locks, mc_page_size in *.
    split; [apply (holds_ext rv0); [intros k Kk; apply RV; cbn in Kk |- *; lia | exact T1]|].
    split; [apply (holds_ext rv0); [intros k Kk; apply RV; cbn in Kk |- *; lia | exact T2]|].
    split; [apply (holds_ext rv0); [intros k Kk; apply RV; cbn in Kk |- *; lia | exact T3]|].
    split; [apply (holds_ext bv0); [intros k Kk; apply BV; cbn in Kk |- *; lia | exact T4]|].
    split; [intros k Kk; rewrite RV by lia; exact (T5 k Kk)|].
    split; [intros k Kk; rewrite RV by lia; exact (T6 k Kk)|].
    split; [intros k Kk; rewrite RV by lia; exact (T7 k Kk)|].
    split; [intros k Kk; rewrite RV by lia; exact (T8 k Kk)|].
    exists gd. split; (apply (holds_ext rv0); [intros k Kk; apply RV; cbn in Kk |- *; lia | assumption]).
  Qed.

  Lemma vm'_maps : ltac2:(tb__ "0|1|
S0S39S38S4bQ40A1M0G0A2A1S60S8A1S65S60Vvm;A1S13S5A1A2A3").
  Proof using . reflexivity. Qed.
  Lemma vm'_noaccess : ltac2:(tb__ "0|1|
S0S39S38S4bQ40A1M0G0A2A1S61S8A1S66S61Vvm;A1S5SeS5S7A2A3A3").
  Proof using HRl HRr HV. unfold km_vm', munmap_vm. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity. Qed.
  Lemma vm'_brk : ltac2:(tb__ "0|1|
S1S0S4bQ40A1M0S62S8A1S62Vvm;A1A3S1S0G0S64S8A1S64Vvm;A1A3S0S39S38G0G0A2A1S63S8A1S63Vvm;A1A3A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma range_in_maps_keep x w : ltac2:(tb__ "0|0|
SfZ0Vw;A2S4SdSeVx;Vw;A2S5A2SdSeS5S7A2Vx;A2A2S15S60Vvm;A1Vx;Vw;A3S15S60S8A1Vx;Vw;A3F_;F_;F_;").
  Proof using HMW HRk HRl HRr HV.
    intros Hw D (e & He & E1 & E2). exists e. split; [|split; [exact E1 | exact E2]].
    rewrite vm'_maps. apply (map_remove_keeps (vm_maps vm) (wz km_a, wz km_n) e HMW entry_In He).
    assert (NE : e <> (wz km_a, wz km_n)).
    { intros ->. cbn [fst snd] in E1, E2. rewrite Ua in E1, E2. rewrite Un in E2. lia. }
    apply wdisj_sym. exact (mwf_In_ne_wdisj _ _ _ HMW He entry_In NE).
  Qed.

  Lemma in_noaccess' e : ltac2:(tb__ "0|5|
S48S38S4bQ40M0A1M1G1A2M2Ve;S61S8A1A3S3G2G2S1S48G2R1S61Vvm;A1A3S1SdS4cG0S42G1G1R1A3A2M3S4cG0S42G1G1Ve;A3A2M4A2SdSeG4S4cG0S43G1G1Ve;A3A2A2SeG3S4cG0S43G1G1R1A3A2A2A2A2A2Le0;A2F_;").
  Proof using HRl HRr HV.
    rewrite vm'_noaccess. intros Hin. apply in_maps_subtract in Hin as (a' & sz' & Hin & He).
    exists (a', sz'). split; [exact Hin|]. cbn [fst snd].
    pose proof a64 as A. unfold iv_subtract in He. apply in_app_iff in He as [He|He].
    - destruct (bv_unsigned a' <? km_a) eqn:E; [|destruct He]. destruct He as [<-|[]]. cbn [fst snd]. apply Z.ltb_lt in E.
      pose proof (bv_unsigned_in_range _ sz') as Rs. rewrite two64 in Rs.
      rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia.
    - destruct (km_a + km_n <? bv_unsigned a' + bv_unsigned sz') eqn:E; [|destruct He]. destruct He as [<-|[]]. cbn [fst snd]. apply Z.ltb_lt in E.
      pose proof (bv_unsigned_in_range _ sz') as Rs. pose proof (bv_unsigned_in_range _ a') as Ra. rewrite two64 in Rs, Ra.
      rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite two64; lia). lia.
  Qed.

  Lemma range_in_noaccess_keep x w : ltac2:(tb__ "0|0|
SfZ0Vw;A2S4SdSeVx;Vw;A2S5A2SdSeS5S7A2Vx;A2A2S15S61Vvm;A1Vx;Vw;A3S15S61S8A1Vx;Vw;A3F_;F_;F_;").
  Proof using HRl HRr HV.
    intros Hw D (e & He & E1 & E2). rewrite vm'_noaccess. unfold range_in_maps, maps_subtract.
    pose proof a64 as A. destruct e as [a0 sz0]. cbn [fst snd] in E1, E2.
    pose proof (bv_unsigned_in_range _ a0) as Ra. pose proof (bv_unsigned_in_range _ sz0) as Rs. rewrite two64 in Ra, Rs.
    destruct D as [D|D].
    -
      exists (a0, Z_to_bv 64 (Z.min (bv_unsigned sz0) (km_a - bv_unsigned a0))). split.
      + apply (in_maps_subtract_intro _ _ _ a0 sz0); [exact He|]. unfold iv_subtract. apply in_app_iff. left.
        replace (bv_unsigned a0 <? km_a) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
      + cbn [fst snd]. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia.
    - exists (Z_to_bv 64 (Z.max (bv_unsigned a0) (km_a + km_n)), Z_to_bv 64 (bv_unsigned a0 + bv_unsigned sz0 - Z.max (bv_unsigned a0) (km_a + km_n))). split.
      + apply (in_maps_subtract_intro _ _ _ a0 sz0); [exact He|]. unfold iv_subtract. apply in_app_iff. right.
        replace (km_a + km_n <? bv_unsigned a0 + bv_unsigned sz0) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
      + cbn [fst snd]. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite two64; lia). lia.
  Qed.

  Lemma Ulyreg k rg' : ltac2:(tb__ "0|3|
S0S3aS1cA1S4eVs;Vk;A2S3eS1cVrg';A2A3S0S3dS1fVrg';A1S40A3S1S0ScS4cQ40M0S13S58VL;Vk;A2M1A1A2G1A3S0ScS4cG0S13S23Vrg';A1M2A1A2G2A3A2F_;F_;").
  Proof using HV.
    intros H1 H2. pose proof HV as (_ & _ & _ & _ & _ & _ & V7 & V8 & _).
    pose proof (V8 k rg' H1 H2) as [A B]. pose proof (V7 k rg' H1 H2) as Cn. top_ranges. unfold PGSZ in *.
    unfold wz. rewrite !u64 by lia. lia.
  Qed.

  Lemma live_apart k rg' : ltac2:(tb__ "0|1|
S2S0S3cVk;Vr;A3A1S0S3aS1cA1S4eVs;Vk;A2S3eS1cVrg';A2A3S0S3dS1fVrg';A1S40A3S2S0S36S35Vrg';A1S2cA3A1S4SdSeS58VL;Vk;A2M0S23Vrg';A1A2S5A2SdSeS5S7A2G0A2A2F_;F_;F_;F_;").
  Proof using HL HRk HRl HRr HV HXr Hinit Hno.
    intros Hne H1 H2 HnB. pose proof HV as (_ & _ & _ & _ & _ & _ & V7 & V8 & V9 & _).
    destruct (rg_kind rg') eqn:EK.
    - exfalso. exact (HnB eq_refl).
    -
      destruct (V9 k rg' (SP r 0) km_n H1 EK H2 e_In ltac:(cbn; congruence)) as [D|D]; cbn [loc_addr prid poff] in D; unfold km_a; lia.
    -
      pose proof (footprint_region_In s k rg' H1 EK H2) as Hin.
      assert (Hin' : In (LMem (SP k 0), rg_len rg') (footprint km_s')).
      { destruct footprint_split as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in Hin.
        apply in_app_iff in Hin as [Y|[Y|Y]]; [apply in_app_iff; left; exact Y | exfalso; injection Y as Y1 _; exact (Hne (eq_sym Y1)) | apply in_app_iff; right; exact Y]. }
      destruct (footprint'_old _ Hin') as [_ D]. unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D. lia.
  Qed.

  Lemma Hvm' : ltac2:(tb__ "0|0|
S1bVL;S6S8A3").
  Proof using HI HL HMW HRk HRl HRr HV HXr Hinit Hno.
    pose proof HV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). pose proof a64 as A64.
    destruct vm'_brk as (EB1 & EB2 & _).
    unfold vm_ok. rewrite EB1, EB2.
    split.
    {
      intros k rg' H1 H2 H3. destruct (live'_live k rg' H1 H2) as [Hne H1o].
      rewrite vm'_maps. apply (map_remove_keeps (vm_maps vm) (wz km_a, wz km_n) _ HMW entry_In (V1 k rg' H1o H2 H3)).
      destruct (Ulyreg k rg' H1o H2) as [U1 U2].
      unfold wdisj. cbn [fst snd]. rewrite Ua, Un, U1, U2. pose proof (live_apart k rg' Hne H1o H2 ltac:(rewrite H3; discriminate)). lia. }
    split.
    {
      intros k rg' H1 H2.
      assert (Hne : k <> r) by (intros ->; rewrite region_of'_r in H1; injection H1 as <-; discriminate H2).
      rewrite (region_of'_other k Hne) in H1. destruct (V2 k rg' H1 H2) as (A & B & Cc).
      pose proof (inv_areas HI) as (_ & _ & _ & _ & AR & _). destruct (AR k rg' H1 H2) as (Hlk & _ & Hlen0).
      pose proof (live_apart k rg' Hne H1 Hlk ltac:(rewrite H2; discriminate)) as AP.
      destruct (Ulyreg k rg' H1 Hlk) as [U1 U2].
      split; [|split].
      - rewrite vm'_maps. apply (map_remove_keeps (vm_maps vm) (wz km_a, wz km_n) _ HMW entry_In A).
        unfold wdisj. cbn [fst snd]. rewrite Ua, Un, U1, U2. lia.
      - intros j Hj1 Hj2 Hnot. apply range_in_noaccess_keep; [unfold PGSZ; lia | unfold PGSZ in *; nia | exact (B j Hj1 Hj2 Hnot)].
      - intros off Hoff e He. destruct (in_noaccess' e He) as (e0 & He0 & S1 & S2).
        destruct (Cc off Hoff e0 He0) as [D|D]; [left | right]; lia. }
    split.
    {
      pose proof s'_fields as (_ & _ & EBK & _). rewrite EBK. destruct (st_brk s) as [| |rb pages] eqn:EBK0; try exact V3.
      destruct V3 as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      intros k Hk1. apply range_in_maps_keep; [unfold PGSZ; lia| |exact (X4 k Hk1)].

      destruct (V10 rb pages r rg eq_refl HRr HRk HRl) as [D|D]; unfold km_a, km_n; rewrite <- X1; unfold PGSZ in *; nia. }
    split.
    {
      intros p n0 Hin. pose proof (footprint'_old _ Hin) as [Hold D]. unfold ranges_disjoint, crange in D. cbn [fst snd] in D.
      pose proof HL as (_ & _ & _ & POS). destruct (POS _ Hold) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd] in P1, P2.
      destruct (Z_lt_dec 0 n0) as [Hn0|Hn0].
      - apply range_in_maps_keep; [exact Hn0 | unfold addr_of, loc_addr in *; cbn [fst snd] in *; lia | exact (V4 p n0 Hold)].
      - exfalso. apply Hn0. clear D P1 P2.

        unfold footprint in Hold. destruct Hold as [E|Hold]; [discriminate E|]. apply in_app_iff in Hold as [Hold|Hold].
        + apply in_map_iff in Hold as (a1 & E & _). injection E as _ <-. unfold PGSZ. lia.
        + apply in_flat_map in Hold as (k & _ & Hk0). destruct (region_of s k) as [rgk|] eqn:ERk; [|destruct Hk0].
          destruct (rg_kind rgk) eqn:EKk; try (destruct Hk0; fail). destruct (rg_live rgk) eqn:ELk; [|destruct Hk0].
          destruct Hk0 as [E|[]]. injection E as _ <-. pose proof (V7 k rgk ERk ELk). unfold PGSZ in *. lia. }
    split; [intros k rg' off H1 H2 Hoff; assert (Hne : k <> r) by (intros ->; rewrite region_of'_r in H1; injection H1 as <-; discriminate H2); rewrite (region_of'_other k Hne) in H1; exact (V5 k rg' off H1 H2 Hoff)|].
    split.
    { intros r1 r2 rg1 rg2 Hne H1 H2 K1 K2.
      assert (N1 : r1 <> r) by (intros ->; rewrite region_of'_r in H1; injection H1 as <-; discriminate K1).
      assert (N2 : r2 <> r) by (intros ->; rewrite region_of'_r in H2; injection H2 as <-; discriminate K2).
      rewrite (region_of'_other r1 N1) in H1. rewrite (region_of'_other r2 N2) in H2. exact (V6 r1 r2 rg1 rg2 Hne H1 H2 K1 K2). }
    split; [intros k rg' H1 H2; destruct (live'_live k rg' H1 H2) as [_ H]; exact (V7 k rg' H H2)|].
    split; [intros k rg' H1 H2; destruct (live'_live k rg' H1 H2) as [_ H]; exact (V8 k rg' H H2)|].
    split; [intros k rg' q n0 H1 H2 H3 Hin Hq; destruct (live'_live k rg' H1 H3) as [_ H]; exact (V9 k rg' q n0 H H2 H3 (proj1 (footprint'_old _ Hin)) Hq)|].
    pose proof s'_fields as (_ & _ & EBK' & _). rewrite EBK'.
    split; [intros rb p k rgk Hb H1 H2 H3; destruct (live'_live k rgk H1 H3) as [_ H]; exact (V10 rb p k rgk Hb H H2 H3)|].
      exact V11.
  Qed.

  Theorem kill_map : ltac2:(tb__ "0|0|
S6fVC;VX;VR;VU;S6eS6VL;A2S67Vsegs;S9A2S68Vsegs;S9A2S8A8").
  Proof using HI HL HLG HMW HRk HRl HRr HS HV HXr Hinit Hno.
    unfold MInvI, MInvG. cbn [ma_s ma_L].
    split; [exact HI'|]. split; [exact Hbounded'|]. split; [exact (mig_ctx HMI)|].
    split; [exact reprO'|]. split; [exact Hvm'|]. split; [exact statics'|].
    split.
    { pose proof s'_fields as (_ & _ & _ & EID & _). rewrite EID, Hinit. intros E; discriminate E. }
    split.
    { intros e He. rewrite vm'_maps in He. unfold map_remove in He. apply filter_In in He as [He _]. exact (HLG e He). }
    split.
    { intros x Hx. exact (mig_img HMI x Hx). }
    unfold maps_wf. rewrite vm'_maps. apply mwf_remove. exact HMW.
  Qed.

  Lemma kill_map_has : ltac2:(tb__ "0|1|
S1S48S38S4bQ40A1M0G0A2S3fG0G0S13S5A1S13S7A1A4S60Vvm;A1A3S1SdS1dS5A2S1SdSeS5S7A2S19VL;A1A2S1SdS1dS7A2S0ScS12S5S1dA2Z0A3A2A2A2A2").
  Proof using HL HRk HRl HRr HV.
    pose proof a_range as (A & B & Cn). split; [exact entry_In|]. split; [exact A|]. split; [exact B|]. split; [exact Cn|].
    pose proof HL as (_ & AL & _). exact (AL r rg HRr HRl).
  Qed.
End KM.
