(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "mslot"; "META_SIZE"; "MUsed"; "PGSZ"; "am_last"; "am_sc"; "AREA_HDR"; "METAS_PER_AREA"; "SP"; "UNIT"; "am_aidx"; "am_avail"; "am_freed"; "am_maplen"; "am_mem"; "am_next"; "am_prev"; "mkAMeta"; "padd"; "slotst"; "st_areas"; "st_metas"; "stride_of"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "option"; "Some"; "nat"; "cons"; "prod"; "pair"; "S"; "bool"; "list"; "None"; "false"; "length"; "nil"; "true"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "pow"; "testbit"; "@Corelib.Lists.ListDef"; "nth"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.Ring"; "inring"; "mnext"; "mrec"; "mprev"; "@Stdlib.Lists.List"; "In"; "last"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "ring_ok"; "usedX"; "MT"; "Inv"; "active_hd"; "alinks"; "chain"; "meta_bits"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts"; "am_dummy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "mc_img_hi"; "mc_img_lo"; "topL"; "vm_ok"; "@Corelib.Init.Nat"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRings MallocWfSlot
  MallocWfGeom MallocWfRepr MallocWfSurgery MallocLayout FpLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition am_dummy : ameta := ltac2:(tb__ "0|2|
S13S27S0A1M0G0SaU0Z0M1A2G1G1G1G1G1G1S2aS15A1Aa").

Lemma last_nth {A} (l : list A) (d : A) : ltac2:(tb__ "0|0|
S1aVA;S3aVA;Vl;Vd;A3S33VA;S4bS29VA;Vl;A2U1A2Vl;Vd;A4A3").
Proof.
  induction l as [|x t IH] using rev_ind; [reflexivity|].
  rewrite last_last, length_app. cbn [length]. rewrite app_nth2 by lia.
  replace (length t + 1 - 1 - length t)%nat with 0%nat by lia. reflexivity.
Qed.

Section Used.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S3fVX;VR;VU;Vs;A4").

  Lemma mask_u32 m : ltac2:(tb__ "0|0|
S2cZ0Vm;A2S34S2eZ1fR1A2S1aS25S32Vm;R2A2S28A3F_;Fi;S2eVm;S31Z2Z20A2A2F_;F_;").
  Proof using .
    intros Hm Hab. destruct (Z_lt_dec m (2 ^ 32)) as [H|H]; [exact H|]. exfalso.
    assert (E : Z.testbit m (Z.log2 m) = true) by (apply Z.bit_log2; lia).
    assert (32 <= Z.log2 m) by (replace 32 with (Z.log2 (2 ^ 32)) by reflexivity; apply Z.log2_le_mono; lia).
    rewrite (Hab (Z.log2 m)) in E by lia. discriminate.
  Qed.

  Lemma used_ranges g am : ltac2:(tb__ "0|6|
S3dVX;Vs;Vg;Vam;A4S19S19S2cZ0M0SdVam;A1M1A2S2eG1S31Z2Z20A2M2A2A2S19S19S2cG0SeVam;A1M3A2S2eG3G2A2A2S19S19S2cG0S6Vam;A1M4A2S2cG4Z1fA2A2S19S19S2cG0ScVam;A1M5A2S2cG5G4A2A2S2cG0SfVam;A1A2A2A2A2A2F_;").
  Proof using HI.
    intros Hu. pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & _) & Gml & _).
    assert (AV : am_avail am < 2 ^ 32) by (apply mask_u32; [lia | intros i Hi; apply (proj1 (Gabove i ltac:(lia)))]).
    assert (FR : am_freed am < 2 ^ 32) by (apply mask_u32; [lia | intros i Hi; apply (proj2 (Gabove i ltac:(lia)))]).
    repeat split; lia.
  Qed.

  Lemma meta_in_areaI p x : ltac2:(tb__ "0|0|
S39S22S0S2A2S23S0S2Vp;Vx;A4S17Vs;A1A3S1bS0S0S1bS34S34S19S39S0R2S16Vs;A1A3S19S19S2cZ0R1A2S2eR1S9A2A2S1aS0Vp;S14R2S2dS8S30S3R1A2A2A2A3A2A2Lk;A2La;A2F_;").
  Proof using HI.
    intros Hin. pose proof (inv_keys HI) as (ND & KP & _ & _ & Hcnt).
    destruct (KP p ltac:(unfold keys; apply in_map_iff; exists (p, x); auto)) as (a & k & Ha & Hk & E).
    exists a, k. split; [exact Ha|]. split; [|exact E]. unfold handed in Hk. destruct (sptr_eqb a _); lia.
  Qed.

  Variables (C : mconsts) (L : layout) (vm : VmMaps).
  Hypothesis HL : layout_ok L s.
  Hypothesis HV : ltac2:(tb__ "0|0|
S4aVL;Vs;Vvm;A3").
  Hypothesis HLG : ledger_ok C vm.

  Lemma used_addrs g am : ltac2:(tb__ "0|8|
S3dVX;Vs;Vg;Vam;A4S19S2cS5S46VL;Vg;A2M0A2S19S2cS2dG0S3A2M1S49VL;A1M2A2S19S1aS34S2fG0Z8A2Z0M3A3S19S1dS2cG1S48VC;A1M4A2S2cS47VC;A1M5G0A2A2S19S2cS5S46VL;S10Vam;A1A2M6A2S19S2cS2dS2dG6SbA2M7S30S18Vam;A1S2dS6Vam;A1Z1A2A2A2G2A2S19S1aS34S2fG6Z10A2G3A3S1dS2cG7G4A2S2cG5G6A2A2A2A2A2A2A2A2A2F_;").
  Proof using HI HL HLG HV.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M _].
    destruct (meta_in_areaI g (MUsed am) ltac:(unfold MT in M; apply In_of_mlookup; exact M)) as (a & k & Ha & Hk & Eg).
    assert (InA : In (LMem a, PGSZ) (footprint s)).
    { unfold footprint. right. apply in_app_iff. left. apply in_map_iff. exists a. auto. }
    pose proof (fp_mem_range C L s vm _ _ HV HLG InA ltac:(unfold PGSZ; lia)) as (A1 & A2 & A3).
    pose proof HL as (_ & Halign & _ & POS).
    destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk' & Hl & Ho & Hext & Hm0).
    pose proof (footprint_region_In s _ _ Hr Hk' Hl) as InR.
    pose proof (extent_pos _ _ _ _ _ (inv_groups HI g am Hu)) as EP.
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as SP16.
    pose proof (used_ranges g am Hu) as (_ & _ & RL & _).
    assert (E16 : 16 <= stride_of am * (am_last am + 1)) by nia.
    assert (LEN : 0 <= rg_len rg) by (unfold IB in Hext; lia).
    pose proof (fp_mem_range C L s vm _ _ HV HLG InR LEN) as (M1 & M2 & M3).
    pose proof (used_group_aligned X R U s HI _ g am Hu (Nat.le_refl _)) as AL.
    pose proof (Halign _ _ Hr Hl) as RAL.

    assert (Ezg : addr_of L g = addr_of L a + AREA_HDR + META_SIZE * k).
    { rewrite Eg. unfold addr_of, loc_addr. destruct a; cbn [padd prid poff]. lia. }
    assert (Ezm : addr_of L (am_mem am) = ly_reg L (prid (am_mem am)) + poff (am_mem am)).
    { unfold addr_of, loc_addr. destruct (am_mem am); reflexivity. }
    unfold addr_of, loc_addr in M1, M2, M3. cbn [prid poff] in M1, M2, M3.
    unfold group_extent in Hext, EP.
    assert (AAL : addr_of L a mod 4096 = 0).
    { pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
      subst a. unfold addr_of, loc_addr. cbn [prid poff]. pose proof (Halign _ _ Hra Hla) as RA. unfold PGSZ in *.
      Z.to_euclidean_division_equations; lia. }
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ, UNIT, IB in *.
    rewrite Ezg, Ezm. rewrite Ezm in Ezg |- * || idtac.
    repeat split; try lia; Z.to_euclidean_division_equations; lia.
  Qed.
End Used.

Section Ring.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (sc : Z) (m0 : sptr).
  Hypothesis HI : ltac2:(tb__ "0|0|
S3fVX;VR;VU;Vs;A4").
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S1aS1eS0A1S40Vs;Vsc;A2S1fS0Vm0;A2A3").

  Definition mrec (q : sptr) : ameta := ltac2:(tb__ "0|1|
S1eS2A1S1Lx;S3eVs;Vq;A2S2S2S1Lm;R1S1eS0A1M0G0S45Lnext;Lprev;S45S1R1Lam;X2x3Lm;S45X1ex2").
  Definition mnext (q : sptr) : sptr := ltac2:(tb__ "0|0|
S1eS0A1S0Lx;S11S37Vq;A1A1S0R1Ln;Vq;X1ex2").
  Definition mprev (q : sptr) : sptr := ltac2:(tb__ "0|0|
S1eS0A1S0Lx;S12S37Vq;A1A1S0R1Lp;Vq;X1ex2").

  Let lk : ltac2:(tb__ "0|1|
S0S1eS22S1eS0A1M0G0A2A1Fg;") := ltac2:(tb__ "0|0|
S41VX;Vs;Vsc;A3").

  Lemma ring_step rest q : ltac2:(tb__ "0|1|
S3cVlk;S1fS0Vm0;A2S21S0Vm0;Vrest;A3M0A3S39S0Vq;G0A3S19S1bS1S1S19S3dVX;Vs;Vq;R1A4S19S1aS34S7R1A1Vsc;A3S19S1aS1eS2A1S3eVs;Vq;A2S1fS2S4R1A1A2A3S1aS1S37Vq;A1R1A3A2A2A2Lam;A2S19S39S0S36Vq;A1G0A3S39S0S38Vq;A1G0A3A2A2F_;F_;").
  Proof using .
    intros Rg Hq.
    destruct (ring_members_used _ _ _ _ _ _ Rg Hq) as (am & Hu & Hs).
    pose proof (usedX_MT _ _ _ _ Hu) as [M _].
    assert (Er : mrec q = am) by (unfold mrec; rewrite M; reflexivity).
    split; [exists am; auto|].
    destruct (ring_links _ _ _ _ Rg Hq) as (pr & nx & Lq).
    pose proof Rg as [[Hnd Hch] _].
    destruct (chain_next _ _ _ _ _ _ _ Hch Hq Lq) as (l1 & l2 & El & Enx & Epr).
    destruct (alinks_used _ _ _ _ _ Lq) as (am' & Hu2 & _ & Elk). pose proof (usedX_fun _ _ _ _ _ Hu2 Hu) as ->.
    injection Elk as Epr' Enx'.
    unfold mnext, mprev. rewrite Er, <- Enx', <- Epr'. injection Enx as ->. injection Epr as ->.
    split.
    - destruct l2 as [|y l2']; cbn [hd]; [left; reflexivity|]. rewrite El. apply in_app_iff. right. right. left. reflexivity.
    - destruct l1 as [|y l1'] using rev_ind.
      + cbn [app] in El |- *.
        assert (LI : forall l (d : sptr), In (last l d) (d :: l)).
        { clear. induction l as [|z t IH]; intros d; [left; reflexivity|].
          cbn [last]. destruct t as [|w t']; [right; left; reflexivity|].
          destruct (IH d) as [E|Hin]; [left; exact E | right; right; exact Hin]. }
        cbn [last]. change (match rest with [] => m0 | _ :: _ => last rest m0 end) with (last (m0 :: rest) m0). cbn [last].
        destruct rest as [|r1 rt]; [left; reflexivity|]. exact (LI (r1 :: rt) m0).
      + rewrite last_last. rewrite El. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma ring_ex : ltac2:(tb__ "0|1|
S1bS26S0A1M0G0S3cVlk;S1fS0Vm0;A2S21S0Vm0;R1A3A3Lrest;A2").
  Proof using HI Hhd Hsc.
    destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & _).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [_ [rest Ems]]. subst ms. exists rest. exact Rg.
  Qed.

  Definition inring (q : sptr) : Prop := ltac2:(tb__ "0|0|
S26S0A1S3cVlk;S1fS0Vm0;A2S21S0Vm0;R1A3A3S39S0Vq;S21S0Vm0;R2A3A3F_;Frest;").

  Lemma inring_m0 : inring m0. Proof using . intros rest _. left. reflexivity. Qed.
  Lemma inring_next q : ltac2:(tb__ "0|0|
S35Vq;A1S35S36Vq;A1A1F_;").
  Proof using . intros H rest Rg. exact (proj1 (proj2 (ring_step rest q Rg (H rest Rg)))). Qed.
  Lemma inring_prev q : ltac2:(tb__ "0|0|
S35Vq;A1S35S38Vq;A1A1F_;").
  Proof using . intros H rest Rg. exact (proj2 (proj2 (ring_step rest q Rg (H rest Rg)))). Qed.
  Lemma inring_used q : ltac2:(tb__ "0|0|
S35Vq;A1S1bS1S1S19S3dVX;Vs;Vq;R1A4S19S1aS34S7R1A1Vsc;A3S19S1aS1eS2A1S3eVs;Vq;A2S1fS2S4R1A1A2A3S1aS1S37Vq;A1R1A3A2A2A2Lam;A2F_;").
  Proof using HI Hhd Hsc. intros H. destruct ring_ex as [rest Rg]. exact (proj1 (ring_step rest q Rg (H rest Rg))). Qed.

  Lemma member_freeable q am : ltac2:(tb__ "0|0|
S35Vq;A1S1aS1S37Vq;A1Vam;A3S1aS25S32S43Vam;A1Z5A2S2bA3F_;F_;").
  Proof using HI Hhd Hsc.
    intros Hq Er. destruct (inring_used q Hq) as (am' & Hu & Hs & M & Er'). rewrite Er in Er'. subst am'.
    pose proof (used_ranges X R U s HI q am Hu) as (_ & _ & Hl & _ & Hml).
    unfold meta_bits. rewrite Z.testbit_true by lia. change (2 ^ 5) with 32.
    replace ((am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) / 32) with (1 + (2 * am_sc am + 128 * am_maplen am))
      by (Z.to_euclidean_division_equations; nia).
    Z.to_euclidean_division_equations; lia.
  Qed.

  Lemma chain_pos (lk' : sptr -> option (option sptr * option sptr)) prev l first : ltac2:(tb__ "0|2|
S42Vlk';Vprev;Vl;Vfirst;A4S20S0S1aS1eS0A1M0S3bS0Vl;R2A3S1fS0R1A2A3S1aS1eS22G0G0A2M1A1Vlk';R2A1S1fG1S23G0G0S1fS0S20S0Li;R3Vprev;S20S33S0R1Vl;R3A4Lj;X20x2A2S1fS0S33S0S24R3A1Vl;Vfirst;A4A2A4A2A3F_;Fx;Fi;F_;").
  Proof using .
    revert prev. induction l as [|y t IH]; intros prev Hc i x Hx; [destruct i; discriminate|].
    cbn [chain] in Hc. destruct Hc as [Hy Ht].
    destruct i as [|j].
    - cbn in Hx. injection Hx as ->. rewrite Hy. destruct t; reflexivity.
    - cbn in Hx. rewrite (IH y Ht j x Hx). destruct j; reflexivity.
  Qed.

  Lemma lk_mnext_mprev q pr nx : ltac2:(tb__ "0|2|
S1aS1eS22S1eS0A1M0G0A2M1A1Vlk;Vq;A1S1fG1S23G0G0Vpr;Vnx;A4A2A3S19S1aS0S36Vq;A1G0S0Lnx;Vnx;S0R1Ln;Vq;X1ex2A3S1aS0S38Vq;A1G0S0Lpr;Vpr;S0R1Lp;Vq;X1ex2A3A2F_;").
  Proof using X sc.
    intros H. destruct (alinks_used _ _ _ _ _ H) as (am & Hu & _ & E).
    pose proof (usedX_MT _ _ _ _ Hu) as [M _].
    unfold mnext, mprev, mrec. rewrite M. injection E as -> ->. split; reflexivity.
  Qed.

  Variable rest : list sptr.
  Hypothesis Rg : ltac2:(tb__ "0|0|
S3cVlk;S1fS0Vm0;A2S21S0Vm0;Vrest;A3A3").
  Let rl := m0 :: rest.
  Let n := length rl.

  Lemma ring_nodup : List.NoDup rl. Proof using Rg. exact (proj1 (proj1 Rg)). Qed.

  Lemma ring_pos i : ltac2:(tb__ "0|1|
S44Vi;Vn;A2S19S1aS0S36S33S0Vi;Vrl;Vm0;A4M0A1S33S0S24Vi;A1Vrl;Vm0;A4A3S1aS0S38G0A1S20S0Li;Vi;S3aS0Vrl;Vm0;A3S20S33S0R1Vrl;Vm0;A4Lj;X20x2A3A2F_;").
  Proof using Hsc Rg.
    intros Hi. pose proof Rg as [[_ Hch] _]. cbn [last] in Hch |- *.
    fold rl in Hch.
    destruct (nth_error rl i) as [x|] eqn:Ex; [| apply nth_error_None in Ex; lia].
    pose proof (chain_pos lk _ rl m0 Hch i x Ex) as Lx.
    assert (Enx : nth i rl m0 = x) by (apply nth_error_nth; exact Ex). rewrite Enx.
    destruct (lk_mnext_mprev x _ _ Lx) as [E1 E2]. rewrite E1, E2. split; [reflexivity|].
    destruct i as [|j]; [reflexivity|]. apply nth_indep. assert (NE : nth_error rl (S j) <> None) by (rewrite Ex; discriminate). apply nth_error_Some in NE. lia.
  Qed.

  Lemma ring_next_last : ltac2:(tb__ "0|0|
S1aS0S36S3aS0Vrl;Vm0;A3A1Vm0;A3").
  Proof using Hsc Rg n.
    rewrite last_nth. fold n. destruct (ring_pos (n - 1) ltac:(unfold n; cbn; lia)) as [-> _].
    apply nth_overflow. unfold n. cbn [length]. lia.
  Qed.

  Lemma ring_distinct i j : ltac2:(tb__ "0|0|
S44Vi;Vn;A2S44Vj;Vn;A2S1cS1aS20Vi;Vj;A3A1S1cS1aS0S33S0Vi;Vrl;Vm0;A4S33S0Vj;Vrl;Vm0;A4A3A1F_;F_;F_;").
  Proof using Rg.
    intros Hi Hj Hne E. pose proof ring_nodup as ND.
    rewrite (List.NoDup_nth rl m0) in ND. exact (Hne (ND i j Hi Hj E)).
  Qed.

End Ring.
