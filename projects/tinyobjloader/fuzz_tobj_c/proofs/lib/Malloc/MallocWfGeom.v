(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "sub"; "to_nat"; "lt"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "frame"; "poff"; "sptr"; "am_last"; "slot_start"; "prid"; "slotst"; "UNIT"; "ss_fr"; "stride_of"; "am_mem"; "padd"; "nth_slot"; "region"; "fr_off"; "IB"; "FGroup"; "find_in_slots"; "fkind"; "fr_kind"; "RkMap"; "am_maplen"; "am_sc"; "ameta"; "find_frame_in"; "fr_n"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_metas"; "st_regions"; "@Corelib.Init.Datatypes"; "Some"; "option"; "nat"; "bool"; "length"; "pair"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "usedX"; "frame_ptr"; "Inv"; "group_extent"; "inside"; "region_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom"; "GR"; "@Stdlib.Lists.List"; "nth_error"; "@Corelib.Init.Peano"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma poff_padd p d : ltac2:(tb__ "0|0|
S0ScSeS18Vp;Vd;A2A1S6SeVp;A1Vd;A2A3").
Proof. destruct p; reflexivity. Qed.

Lemma prid_padd p d : ltac2:(tb__ "0|0|
S0S2fS12S18Vp;Vd;A2A1S12Vp;A1A3").
Proof. destruct p; reflexivity. Qed.

Lemma poff_slot_start am i : ltac2:(tb__ "0|0|
S0ScSeS11Vam;Vi;A2A1S6S6SeS17Vam;A1A1S14A2S7S16Vam;A1Vi;A2A2A3").
Proof. unfold slot_start. rewrite poff_padd. lia. Qed.

Lemma prid_slot_start am i : ltac2:(tb__ "0|0|
S0S2fS12S11Vam;Vi;A2A1S12S17Vam;A1A1A3").
Proof. unfold slot_start. apply prid_padd. Qed.

Lemma sptr_eq_parts p q : ltac2:(tb__ "0|0|
S0S2fS12Vp;A1S12Vq;A1A3S0ScSeVp;A1SeVq;A1A3S0SfVp;Vq;A3F_;F_;").
Proof. destruct p, q; cbn; intros -> ->; reflexivity. Qed.

Section Geom.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S37VX;VR;VU;Vs;A4").

  Lemma same_group_starts am i1 i2 : ltac2:(tb__ "0|3|
S3S0ScVi1;Vi2;A3A1S5Z10S16Vam;A1M0A2S4S5S6SeS11Vam;Vi1;A2A1M1G0A2SeS11Vam;Vi2;A2A1M2A2S5S6G2G0A2G1A2A2F_;F_;").
  Proof using . intros Hne Hs. rewrite !poff_slot_start. assert (i1 < i2 \/ i2 < i1) as [H|H] by lia; [left|right]; nia. Qed.

  Lemma slot_in_span g am i : ltac2:(tb__ "0|2|
S35VX;Vs;Vg;Vam;A4S1S5Z0Vi;A2S5Vi;S10Vam;A1A2A2S1S5S6SeS17Vam;A1A1M0S14A2SeS11Vam;Vi;A2A1M1A2S5S6G1S16Vam;A1A2S6S6G0S38Vam;A1A2S1cA2A2A2F_;F_;").
  Proof using HI.
    intros Hu Hi. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Hs.
    rewrite poff_slot_start. unfold group_extent. split; nia.
  Qed.

  Lemma fgroup_frame g am j fr : ltac2:(tb__ "0|1|
S35VX;Vs;Vg;Vam;A4S1S5Z0M0Vj;A2S5Vj;S10Vam;A1A2A2S0S2eSdA1S15S19Vam;Vj;A2A1S2dSdVfr;A2A3S0S1fS20Vfr;A1S1dA3S1S0ScS26Vfr;A1S8S16Vam;A1S1cA2A3S0ScS1bVfr;A1G0A3A2F_;F_;F_;F_;").
  Proof using HI.
    intros Hu Hj Hfr Hk. pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _).
    pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & _ & _ & _ & FG) & _).
    destruct (FG Hk) as [A B]. auto.
  Qed.

  Lemma inside_slot_start g1 a1 i1 g2 a2 : ltac2:(tb__ "0|3|
S35VX;Vs;Vg1;Va1;A4S35VX;Vs;Vg2;Va2;A4S1S5Z0M0Vi1;A2S5Vi1;S10Va1;A1A2A2S39VX;Vs;Va1;Va2;A4S2ScScS2SdSdS1S1S5G0R2A2S5R2S10Va2;A1A2A2S1S0S2eSdA1S15S19Va2;R2A2A1S2dSdR1A2A3S1S0S1fS20R1A1S1dA3S1S5S6SeS11Va2;R2A2A1M1S14A2SeS11Va1;Vi1;A2A1M2A2S5S6G2S16Va1;A1A2S6G1S16Va2;A1A2A2A2A2A2A2Lfr;A2Lj;A2F_;F_;F_;F_;").
  Proof using HI.
    intros U1 U2 Hi1 (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mc & Memc & Lo & Hi & Fit).
    exists j, fr. split; [exact Hj|]. split; [exact Hfr|]. split; [exact Hk|].
    destruct (fgroup_frame _ _ _ _ U2 Hj Hfr Hk) as [Fn _].
    pose proof (f_equal poff Memc) as Eoc.
    pose proof (slot_in_span _ _ _ U1 Hi1) as [L1 H1].
    unfold UNIT, IB in *. lia.
  Qed.

  Lemma slot_starts_distinct g1 a1 i1 g2 a2 i2 : ltac2:(tb__ "0|1|
S35VX;Vs;Vg1;Va1;A4S35VX;Vs;Vg2;Va2;A4S1S5Z0M0Vi1;A2S5Vi1;S10Va1;A1A2A2S1S5G0Vi2;A2S5Vi2;S10Va2;A1A2A2S0SfS11Va1;Vi1;A2S11Va2;Vi2;A2A3S1S0SfVg1;Vg2;A3S0ScVi1;Vi2;A3A2F_;F_;F_;F_;F_;").
  Proof using HI.
    intros U1 U2 Hi1 Hi2 E.
    pose proof (inv_groups HI g1 a1 U1) as G1. pose proof (inv_groups HI g2 a2 U2) as G2.
    pose proof (stride_pos _ _ _ _ _ G1) as S1. pose proof (stride_pos _ _ _ _ _ G2) as S2.
    pose proof (f_equal poff E) as Eo. pose proof (f_equal prid E) as Er. rewrite !prid_slot_start in Er.
    destruct (sptr_eq_dec g1 g2) as [<-|Hne].
    - pose proof (usedX_fun _ _ _ _ _ U1 U2) as <-. split; [reflexivity|].
      destruct (Z.eq_dec i1 i2) as [|Hne]; [assumption|]. exfalso.
      destruct (same_group_starts a1 i1 i2 Hne S1); lia.
    - exfalso.
      pose proof (slot_in_span _ _ _ U1 Hi1) as [L1 H1]. pose proof (slot_in_span _ _ _ U2 Hi2) as [L2 H2].
      destruct (inv_laminar HI g1 a1 g2 a2 U1 U2 Hne Er) as [D | [I | I]].
      + unfold spans_disjoint in D. unfold UNIT, IB in *. lia.
      + destruct (inside_slot_start _ _ _ _ _ U1 U2 Hi1 I) as (j & fr & Hj & _ & _ & A & B).
        destruct (Z.eq_dec j i2) as [->|Hji]; [unfold UNIT in *; lia|].
        destruct (same_group_starts a2 j i2 Hji S2); unfold UNIT in *; lia.
      + destruct (inside_slot_start _ _ _ _ _ U2 U1 Hi2 I) as (j & fr & Hj & _ & _ & A & B).
        destruct (Z.eq_dec j i1) as [->|Hji]; [unfold UNIT in *; lia|].
        destruct (same_group_starts a1 j i1 Hji S1); unfold UNIT in *; lia.
  Qed.

  Lemma frame_ptrs_distinct g1 a1 i1 f1 g2 a2 i2 f2 : ltac2:(tb__ "0|2|
S35VX;Vs;Vg1;Va1;A4S35VX;Vs;Vg2;Va2;A4S1S5Z0M0Vi1;A2S5Vi1;S10Va1;A1A2A2S1S5G0Vi2;A2S5Vi2;S10Va2;A1A2A2S0S2eSdA1M1S15S19Va1;Vi1;A2A1S2dSdVf1;A2A3S0G1S15S19Va2;Vi2;A2A1S2dSdVf2;A2A3S0SfS36Va1;Vi1;Vf1;A3S36Va2;Vi2;Vf2;A3A3S1S0SfVg1;Vg2;A3S0ScVi1;Vi2;A3A2F_;F_;F_;F_;F_;F_;F_;").
  Proof using HI.
    intros U1 U2 Hi1 Hi2 F1 F2 E.
    pose proof (inv_groups HI g1 a1 U1) as G1. pose proof (inv_groups HI g2 a2 U2) as G2.
    pose proof (stride_pos _ _ _ _ _ G1) as S1. pose proof (stride_pos _ _ _ _ _ G2) as S2.

    destruct G1 as (_ & _ & Gsl1 & _). pose proof (Gsl1 i1 Hi1) as (_ & _ & T1). rewrite F1 in T1. destruct T1 as (_ & _ & (N1 & O1 & B1 & _ & K1) & _).
    destruct G2 as (_ & _ & Gsl2 & _). pose proof (Gsl2 i2 Hi2) as (_ & _ & T2). rewrite F2 in T2. destruct T2 as (_ & _ & (N2 & O2 & B2 & _ & K2) & _).
    unfold frame_ptr in E. pose proof (f_equal poff E) as Eo. rewrite !poff_padd in Eo.
    pose proof (f_equal prid E) as Er. rewrite !prid_padd, !prid_slot_start in Er.
    destruct (sptr_eq_dec g1 g2) as [<-|Hne].
    - pose proof (usedX_fun _ _ _ _ _ U1 U2) as <-. split; [reflexivity|].
      destruct (Z.eq_dec i1 i2) as [|Hne]; [assumption|]. exfalso.
      destruct (same_group_starts a1 i1 i2 Hne S1); unfold UNIT, IB in *; lia.
    - exfalso.
      pose proof (slot_in_span _ _ _ U1 Hi1) as [L1 H1]. pose proof (slot_in_span _ _ _ U2 Hi2) as [L2 H2].
      destruct (inv_laminar HI g1 a1 g2 a2 U1 U2 Hne Er) as [D | [I | I]].
      + unfold spans_disjoint in D. unfold UNIT, IB in *. lia.
      + destruct (inside_slot_start _ _ _ _ _ U1 U2 Hi1 I) as (j & fr & Hj & Hfr & Hk & A & B).
        destruct (Z.eq_dec j i2) as [->|Hji].
        * rewrite F2 in Hfr. injection Hfr as ->. destruct (K2 Hk) as [Ho2 _]. unfold UNIT, IB in *. nia.
        * destruct (same_group_starts a2 j i2 Hji S2); unfold UNIT, IB in *; nia.
      + destruct (inside_slot_start _ _ _ _ _ U2 U1 Hi2 I) as (j & fr & Hj & Hfr & Hk & A & B).
        destruct (Z.eq_dec j i1) as [->|Hji].
        * rewrite F1 in Hfr. injection Hfr as ->. destruct (K1 Hk) as [Ho1 _]. unfold UNIT, IB in *. nia.
        * destruct (same_group_starts a1 j i1 Hji S1); unfold UNIT, IB in *; nia.
  Qed.

  Lemma find_in_slots_sound sl base stride k0 p k : ltac2:(tb__ "0|0|
S0S2eScA1S1eVsl;Vbase;Vstride;Vk0;Vp;A5S2dScVk;A2A3S2S13S13S2SdSdS1S0S2eS13A1S3cS13Vsl;S9S8Vk;Vk0;A2A1A3S2dS13R2A2A3S1S0S2eSdA1S15R2A1S2dSdR1A2A3S1S5Vk0;Vk;A2S0SfS18Vbase;S6S7Vstride;Vk;A2S7S14S1bR1A1A2A2A2Vp;A3A2A2A2Lfr;A2Lx;A2F_;").
  Proof using .
    revert k0. induction sl as [|x t IH]; intros k0 H; cbn [find_in_slots] in H; [discriminate|].
    destruct (ss_fr x) as [fr|] eqn:Efr.
    - destruct (sptr_eqb (padd base (stride * k0 + UNIT * fr_off fr)) p) eqn:E.
      + injection H as <-. exists x, fr. rewrite Z.sub_diag. cbn [Z.to_nat nth_error]. repeat split; auto; [lia|]. apply sptr_eqb_eq. exact E.
      + destruct (IH _ H) as (x' & fr' & Hn & Hf & Hk & Hp). exists x', fr'.
        replace (Z.to_nat (k - k0)) with (S (Z.to_nat (k - (k0 + 1)))) by lia. cbn [nth_error]. repeat split; auto. lia.
    - destruct (IH _ H) as (x' & fr' & Hn & Hf & Hk & Hp). exists x', fr'.
      replace (Z.to_nat (k - k0)) with (S (Z.to_nat (k - (k0 + 1)))) by lia. cbn [nth_error]. repeat split; auto. lia.
  Qed.

  Lemma find_in_slots_complete sl base stride k0 p j x fr : ltac2:(tb__ "0|0|
S0S2eS13A1S3cS13Vsl;Vj;A3S2dS13Vx;A2A3S0S2eSdA1S15Vx;A1S2dSdVfr;A2A3S0SfS18Vbase;S6S7Vstride;S6Vk0;SbVj;A1A2A2S7S14S1bVfr;A1A2A2A2Vp;A3S2ScScS0S2eScA1S1eVsl;Vbase;Vstride;Vk0;Vp;A5S2dScR1A2A3Lk;A2F_;F_;F_;").
  Proof using .
    revert k0 j. induction sl as [|y t IH]; intros k0 [|j] Hn Hf Hp; cbn [nth_error] in Hn; try discriminate; cbn [find_in_slots].
    - injection Hn as ->. rewrite Hf. rewrite Z.add_0_r in Hp. rewrite Hp, sptr_eqb_refl. eexists. reflexivity.
    - destruct (ss_fr y) as [fy|]; [destruct (sptr_eqb _ p); [eexists; reflexivity|]|];
        eapply (IH (k0 + 1) j); eauto; rewrite <- Hp; f_equal; lia.
  Qed.

  Lemma frame_ptr_base am i fr : ltac2:(tb__ "0|0|
S0SfS36Vam;Vi;Vfr;A3S18S18S17Vam;A1S14A2S6S7S16Vam;A1Vi;A2S7S14S1bVfr;A1A2A2A2A3").
  Proof using .
    unfold frame_ptr. apply sptr_eq_parts.
    - rewrite !prid_padd, prid_slot_start. reflexivity.
    - rewrite !poff_padd, poff_slot_start. lia.
  Qed.

  Lemma find_frame_in_spec g am i fr : ltac2:(tb__ "0|1|
S35VX;Vs;Vg;Vam;A4S1S5Z0Vi;A2S5Vi;S10Vam;A1A2A2S0S2eSdA1S15S19Vam;Vi;A2A1S2dSdVfr;A2A3S0S2eS33SfScA2M0A1S25S2bVs;A1S36Vam;Vi;Vfr;A3A2S2dG0S32SfScVg;Vi;A4A2A3F_;F_;F_;").
  Proof using HI.
    intros Hu Hi Hfr.
    pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
    pose proof (inv_groups HI g am Hu) as ((_ & _ & Glen & _) & _).
    assert (KEY : forall l, (forall q x, In (q, x) l -> MT s q = Some x) ->
                 (In (g, MUsed am) l) ->
                 find_frame_in l (frame_ptr am i fr) = Some (g, i)).
    { induction l as [|[q x] t IH]; intros Hall Hin; [destruct Hin|].
      cbn [find_frame_in].
      assert (Mq : MT s q = Some x) by (apply Hall; left; reflexivity).
      destruct x as [pr nx| |amq].
      - apply IH; [intros; apply Hall; right; assumption|]. destruct Hin as [E|E]; [discriminate|exact E].
      - apply IH; [intros; apply Hall; right; assumption|]. destruct Hin as [E|E]; [discriminate|exact E].
      - destruct (find_in_slots (am_slots amq) (padd (am_mem amq) UNIT) (stride_of amq) 0 (frame_ptr am i fr)) as [k|] eqn:Ef.
        +
          destruct (find_in_slots_sound _ _ _ _ _ _ Ef) as (xk & fk & Hn & Hfk & Hk0 & Hp).
          rewrite Z.sub_0_r in Hn.
          destruct (memb q X) eqn:Mx.
          *
            exfalso. apply memb_In in Mx. destruct (inv_X HI q Mx) as [_ Mq']. rewrite Mq in Mq'.
            destruct Mq' as (_ & _ & Hnone). specialize (Hnone k). unfold nth_slot in Hnone.
            rewrite (nth_error_nth _ _ slot_junk Hn) in Hnone. rewrite Hfk in Hnone. discriminate.
          * assert (Uq : usedX X s q amq) by (apply usedX_intro; assumption).
            pose proof (inv_groups HI q amq Uq) as ((_ & _ & Qlen & _) & _).
            assert (Hk : 0 <= k <= am_last amq).
            { split; [lia|]. apply nth_error_Some_lt in Hn. rewrite Qlen in Hn. lia. }
            assert (Hs : ss_fr (nth_slot amq k) = Some fk).
            { unfold nth_slot. rewrite (nth_error_nth _ _ slot_junk Hn). exact Hfk. }
            destruct (frame_ptrs_distinct q amq k fk g am i fr Uq Hu Hk Hi Hs Hfr) as [-> ->].
            -- rewrite frame_ptr_base. rewrite <- Hp. reflexivity.
            -- reflexivity.
        +
          destruct Hin as [E|Hin].
          * exfalso. injection E as -> ->.
            destruct (nth_error (am_slots am) (Z.to_nat i)) as [x|] eqn:En.
            2:{ apply nth_error_None in En. rewrite Glen in En. lia. }
            assert (Hx : ss_fr x = Some fr) by (unfold nth_slot in Hfr; rewrite (nth_error_nth _ _ slot_junk En) in Hfr; exact Hfr).
            destruct (find_in_slots_complete (am_slots am) (padd (am_mem am) UNIT) (stride_of am) 0 (frame_ptr am i fr)
                        (Z.to_nat i) x fr En Hx) as [k Hk]; [|rewrite Hk in Ef; discriminate].
            rewrite frame_ptr_base. f_equal. replace (0 + Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
          * apply IH; [intros; apply Hall; right; assumption | exact Hin]. }
    apply KEY.
    - intros q x Hin. apply mlookup_of_In; [exact (proj1 (inv_keys HI)) | exact Hin].
    - apply In_of_mlookup. exact Mg.
  Qed.
End Geom.

Definition GR (s : astate) (am : ameta) : Prop := ltac2:(tb__ "0|3|
S2S1aS1aS1S0S2eS1aA1S3aVs;S12S17Vam;A1M0A1A2S2dS1aR1A2A3S1S0S2aS27R1A1S21A3S1S0S30S29R1A1S34A3S1S5Z0M1SeG0A1M2A2S1S5S6S6G2S38Vam;A1A2S1cA2S28R1A1A2SaG1S22Vam;A1A2S0ScG2G1A3F_;A2A2A2A2A2Lrg;A2").

Lemma used_group_region_aux X R U s (HI : Inv X R U s) k : ltac2:(tb__ "0|0|
SfS24S35VX;Vs;R2R1A4S3dS9S8Z40S23R2A1A2A1Vk;A2S3bVs;R3A2F_;F_;Fam;Fg;").
Proof.
  induction k as [|k IH]; intros g am Hu Hk.
  - exfalso. pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _).
    destruct Gcl as [(C & _) | (C & _)]; lia.
  - pose proof (inv_groups HI g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
    destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos | Hz].
    + destruct (Gmp Hpos) as (r & rg & Em & Hr & K & L & Len & Fit).
      exists rg. rewrite Em. cbn [prid poff]. unfold group_extent. unfold PGSZ in *.
      repeat split; auto; try lia.
    + assert (M0 : am_maplen am = 0) by lia.
      destruct (Gns M0) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem & Sc & N63' & Fit).
      assert (Hk' : (Z.to_nat (64 - am_sc am') <= k)%nat) by lia.
      destruct (IH g' am' U' Hk') as (rg & Hr & K & L & P0 & Ext & _).
      pose proof (inv_groups HI g' am' U') as G'. pose proof (stride_pos _ _ _ _ _ G') as S'.
      destruct G' as (_ & _ & Gsl' & _). pose proof (Gsl' i' Hi') as (_ & _ & T'). rewrite F' in T'.
      destruct T' as (_ & _ & (N' & O' & B' & _) & _).
      exists rg. rewrite Mem, prid_slot_start, poff_slot_start.
      assert (Es : stride_of am = class_size (am_sc am)).
      { unfold stride_of. rewrite M0. cbn. destruct (am_last am =? 0); reflexivity. }
      unfold group_extent in *. rewrite Es. unfold UNIT, IB in *.
      repeat split; auto; try lia; try nia.
Qed.

Lemma used_group_region X R U s g am : ltac2:(tb__ "0|0|
S37VX;VR;VU;Vs;A4S35VX;Vs;Vg;Vam;A4S3bVs;Vam;A2F_;F_;").
Proof. intros HI Hu. eapply (used_group_region_aux X R U s HI); [exact Hu | apply Nat.le_refl]. Qed.

Lemma used_group_prid_lt X R U s g am : ltac2:(tb__ "0|0|
S37VX;VR;VU;Vs;A4S35VX;Vs;Vg;Vam;A4S3eS12S17Vam;A1A1S31S1aS2cVs;A1A2A2F_;F_;").
Proof.
  intros HI Hu. destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & _).
  exact (region_of_lt _ _ _ Hr).
Qed.
