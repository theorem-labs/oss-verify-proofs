(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "am_sc"; "astate"; "ameta"; "bind"; "am_freed"; "am_aidx"; "am_avail"; "am_last"; "MUsed"; "am_next"; "am_set_avail"; "ones"; "UNIT"; "am_prev"; "am_set_aidx"; "class_size"; "ret"; "stride_of"; "am_set_freed"; "frame"; "getm"; "FModel"; "IB"; "PGSZ"; "am_slots"; "ctz32"; "decay_bounces"; "fail"; "fkind"; "lowbit"; "setm"; "slotst"; "span_loop"; "st_active"; "st_metas"; "st_mmap_counter"; "st_regions"; "st_usage"; "upd_slot"; "FGroup"; "FUser"; "HActive"; "M"; "MMAP_THRESHOLD"; "activate_group"; "am_maplen"; "bit"; "enframe"; "massert"; "mkFrame"; "mkSlot"; "mslot"; "nth_slot"; "osptr_eqb"; "padd"; "region"; "set_head"; "slot_start"; "ss_fr"; "try_avail"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "land"; "mul"; "sub"; "testbit"; "eqb"; "lor"; "div"; "ldiff"; "ltb"; "@Corelib.Init.Datatypes"; "Some"; "pair"; "prod"; "option"; "bool"; "None"; "unit"; "true"; "list"; "negb"; "false"; "length"; "nat"; "tt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "active_hd"; "usedX"; "allocated"; "fold_off"; "masks_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "allzero"; "ta_post"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Lemma land_le_l a b : ltac2:(tb__ "0|0|
S44Z0Va;A2S44S47Va;Vb;A2Va;A2F_;").
Proof.
  intros Ha.
  assert (E : Z.land a b + Z.ldiff a b = a).
  { rewrite Z.add_nocarry_lxor.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.ldiff_spec.
      destruct (Z.testbit a i), (Z.testbit b i); reflexivity.
    - apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0.
      destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.

Lemma fold_off_le slack off0 : ltac2:(tb__ "0|1|
S44Z0M0Voff0;A2S44G0Vslack;A2S44S62Vslack;Voff0;A2Voff0;A2F_;F_;").
Proof.
  intros H0 Hs. unfold fold_off.
  destruct (slack <? off0) eqn:E; [|lia].
  match goal with |- (if slack <? ?x then _ else _) <= _ => set (off1 := x) end.
  assert (Hand : off1 <= off0) by (subst off1; apply land_le_l; exact H0).
  destruct (slack <? off1); lia.
Qed.

Lemma land255_range z : 0 <= Z.land z 255 <= 255.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  rewrite Z.land_comm. apply land_le_l. lia.
Qed.

Lemma mod256_range z : 0 <= z mod 256 <= 255.
Proof. pose proof (Z.mod_pos_bound z 256 ltac:(lia)). lia. Qed.

Lemma am_slots_upd_slot_length am i x : ltac2:(tb__ "0|0|
S1S5cS5bS27S20S2eVam;Vi;Vx;A3A1A2S5bS27S20Vam;A1A2A3").
Proof. unfold upd_slot. cbn. apply length_lupd. Qed.

Lemma ring_facts X R U s g am : ltac2:(tb__ "0|9|
S5eVX;VR;VU;Vs;A4S60VX;Vs;Vg;Vam;A4S45S8Vam;A1M0Z30A2S44Z0M1G0A2S2S1S52S53S7A1M2G2A2S51G2G2S15Vam;A1S11Vam;A1A4S51G2G2S55S7A1M3G3A4A3M4S2S1S0SeVam;A1G1A3M5S1S0ScVam;A1G1A3M6A2F_;S2S3G5A1S1G2S5fVs;G0A2S50S7Vg;A2A3M7F_;S3G4A1S3G7A1S0S3S1S53S52S7S0A2M8A1VR;S50G8S51S7S0Vg;R1A4A2A3A1Fi;S3G6A1F_;F_;F_;A2A2F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hsc0. destruct (inv_rings HI) as (_ & A & _).
  destruct (A (am_sc am) ltac:(lia)) as (ms & Rg & Mem & Full & Q1 & Q2).
  split; [|split].
  - intros HL. apply (Full g am Hu eq_refl). intros Hin. apply (Mem g am Hu eq_refl) in Hin. exact (Hin HL).
  - intros Hav. exact (Q1 g am Hu eq_refl Hav).
  - intros HL Hnh HnR. apply (Q2 g am Hu eq_refl); [|exact Hnh|exact HnR]. apply (Mem g am Hu eq_refl). exact HL.
Qed.

Lemma div16_mono a b : ltac2:(tb__ "0|1|
S44Va;Vb;A2S44S4dVa;Z10M0A2S4dVb;G0A2A2F_;").
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma enframe_spec X U s g idx n ctr k am (Q : sptr * astate -> Prop) : ltac2:(tb__ "0|8|
S5eVX;S50S52S7S0A2M0S51S7S0Vg;Vidx;A4A2VU;Vs;A4S60VX;Vs;Vg;Vam;A4S44Z0M1Vn;A2S44Vn;S49S19Vam;A1S1eA2M2A2S44G1Vctr;A2S1S24Vk;S2fA3M3S1S0Vn;G2A3F_;S1S0S8Vam;A1M4Z3fA3S2S1S24Vk;S30A3S2S44S33Vn;A2S45S48S35Vam;A1S1fA2S46S46S46Vn;S14A2S1eA2S1fA2A2A2A2F_;S45G4Z30A2S3S1S52S53S7A1M5G5A2S51G5G5S15Vam;A1S11Vam;A1A4S51G5G5S55S7A1M6G6A4A3A1S1G5S5fVs;G4A2S50S7Vg;A2A3F_;F_;S0S9S52S0S0A2M7S2S44G1R3A2S44R3ZffA2A2S44S46S48S14R4A2Vn;A2G2A2G3S1S0R6G1A3F_;S1S9R5S66Vg;S10S2eVam;Vidx;S3aS50G7R4A2S50S1bS39R6Vn;Vk;A3A2A2A3A1Vs;A3A3S5eVX;S55G0A1VU;R6A4VQ;S51S7S9S3eS41Vam;Vidx;A2S48S14R8A2A2R7A4A1F_;F_;F_;F_;F_;Fhdr;Fs';Foff;S64S52S7S9A2S37Vg;Vidx;Vn;Vctr;Vk;Vs;A6VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hn Hnst Hctr Hgrp H63 Hhdg HQ.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  pose proof (inv_groups HI g am Hu) as G. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  destruct (inv_reserved HI g idx eq_refl) as (am' & Hu' & Hidx & Hfr0 & Hal0).
  pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (stride_pos _ _ _ _ _ G) as Hsp.
  destruct Gm as (Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra).
  set (stride := stride_of am) in *.
  set (slack := (stride - IB - n) / UNIT).
  assert (Hslack : 0 <= slack) by (subst slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
  assert (Hslack16 : UNIT * slack <= stride - IB - n).
  { subst slack. unfold UNIT. pose proof (Z.mul_div_le (stride - IB - n) 16 ltac:(lia)). lia. }
  unfold enframe. mbinds. eapply itok_getm; [exact Mg|]. msimp.
  mbinds. apply itok_mcheck; [apply andb_true_intro; split; apply Z.leb_le; lia|]. msimp. fold stride. fold slack.

  match goal with |- itok (bind ?m0 ?kk s) Q =>
    assert (OFF0 : itok (m0 s) (fun r => snd r = s /\ 0 <= fst r <= 255 /\ (slack = 0 -> fst r = 0))) end.
  { destruct (slack =? 0) eqn:Es.
    - apply itok_ret. cbn. split; [reflexivity|]. split; [lia | auto].
    - apply Z.eqb_neq in Es. destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|].
      + apply itok_ret. cbn [fst snd]. split; [reflexivity|]. split; [apply land255_range | intros; lia].
      + mbinds. apply itok_askz; [exact I|]. intros z Hz. msimp. apply itok_ret. cbn [fst snd].
        split; [reflexivity|]. split; [apply mod256_range | intros; lia]. }
  apply itok_bind. eapply itok_mono; [|exact OFF0]. intros [off0 s0] (Hs0 & Hoff0 & Hz0). cbn [fst snd] in *. subst s0.
  match goal with |- itok ((massert (?o <=? _) _ ;; _) _) _ => change o with (fold_off slack off0) end.
  set (off := fold_off slack off0).
  pose proof (fold_off_ok slack off0 Hslack ltac:(lia)) as Hoff. fold off in Hoff.
  pose proof (fold_off_le slack off0 ltac:(lia) Hslack) as Hoffle. fold off in Hoffle.
  assert (Hoffz : slack = 0 -> off = 0) by (intros E0; rewrite E0 in Hoff; lia).
  mbinds. apply itok_massert; [apply Z.leb_le; lia|]. msimp.
  mbinds. apply itok_setm'. msimp. apply itok_ret.
  assert (Hoff16 : UNIT * off + n <= stride - IB) by (unfold UNIT in *; nia).
  assert (HoffG : k = FGroup -> off = 0).
  { intros Hk. apply Hoffz. subst slack. rewrite (Hgrp Hk). replace (stride - IB - (stride - IB)) with 0 by lia. reflexivity. }
  eapply HQ; [lia | exact Hoff16 | exact HoffG | reflexivity |].

  set (fr := mkFrame off n k).
  match goal with |- Inv X None U (upd_meta g (MUsed (upd_slot am idx ?sl)) s) => set (sl1 := sl) end.
  set (am1 := upd_slot am idx sl1).
  assert (Hlen : (Z.to_nat idx < length (am_slots am))%nat) by (rewrite Glen; lia).
  assert (NS : forall j, 0 <= j -> nth_slot am1 j = if j =? idx then sl1 else nth_slot am j).
  { intros j Hj. subst am1. apply nth_slot_upd_slot; [lia | exact Hj | exact Hlen]. }
  assert (GS : geom_same am am1).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros j frj Hj Hkj. destruct (Z_le_dec 0 j) as [Hj0|Hj0].
    - rewrite NS by exact Hj0. destruct (j =? idx) eqn:E; [|exact Hj]. apply Z.eqb_eq in E. subst j. rewrite Hfr0 in Hj. discriminate.
    - unfold nth_slot, am1, upd_slot in *. cbn [am_slots am_set_slots]. replace (Z.to_nat j) with 0%nat in * by lia.
      rewrite nth_lupd. destruct (Nat.eqb 0 (Z.to_nat idx) && Nat.ltb (Z.to_nat idx) (length (am_slots am)))%bool eqn:E; [|exact Hj].
      apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. replace idx with 0 in Hfr0 by lia.
      unfold nth_slot in Hfr0. cbn in Hfr0. rewrite Hfr0 in Hj. discriminate. }
  assert (Hscr : am_sc am = 63 \/ (0 <= am_sc am < 48)).
  { destruct Gcl as [(C1 & _) | (C1 & _)]; [left; exact C1 | right; exact C1]. }
  eapply (Inv_used_update X (Some (g, idx)) None U s g am am1 HI Hu (geom_same_upto_of X s _ _ GS)).
  - split; reflexivity.
  -   unfold masks_ok. subst am1. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
    repeat (split; [assumption|]). exact Gfra.
  -
    intros i Hi. cbn [am_last am1 upd_slot am_set_slots] in Hi.
    pose proof (Gsl i Hi) as (S1 & S2 & S3). unfold slot_ok. rewrite NS by lia.
    replace (am_maplen am1) with (am_maplen am) by reflexivity.
    replace (allocated am1 i) with (allocated am i) by reflexivity.
    destruct (i =? idx) eqn:Ei.
    + apply Z.eqb_eq in Ei. subst i. subst sl1. cbn [ss_hdr ss_fr].
      split; [intros; discriminate|]. split.
      { intros h3 h16 Eh.
        assert (Hh16 : 0 <= stride * idx / UNIT <= 65535).
        { split; [apply Z.div_pos; unfold UNIT; nia|].
          destruct Hscr as [H63' | Hsc48].
          - destruct Gcl as [(_ & Hl0 & _) | (C1 & _)]; [|lia]. replace idx with 0 by lia. rewrite Z.mul_0_r. cbn. lia.
          - destruct Gcl as [(C1 & _) | (_ & _ & _ & Hspan)]; [lia|]. fold stride in Hspan.
            apply Z.div_le_upper_bound; [unfold UNIT; lia|]. unfold UNIT. nia. }
        set (r5 := if 5 <=? stride - IB - UNIT * off - n then 5 else stride - IB - UNIT * off - n) in Eh.
        assert (Hr5 : 0 <= r5 <= 5) by (subst r5; destruct (5 <=? stride - IB - UNIT * off - n) eqn:E5; [apply Z.leb_le in E5|apply Z.leb_gt in E5]; lia).
        destruct (off =? 0); [destruct k|];
          pose proof (f_equal (fun o : option (Z * Z) => match o with Some p => fst p | None => 0 end) Eh) as E1;
          pose proof (f_equal (fun o : option (Z * Z) => match o with Some p => snd p | None => 0 end) Eh) as E2;
          cbn [fst snd] in E1, E2; subst h3 h16; lia. }
      split; [exact Hal0|]. split; [discriminate|]. split.
      { unfold frame_ok. subst fr. cbn [fr_n fr_off fr_kind]. fold stride.
        split; [lia|]. split; [lia|]. split; [exact Hoff16|]. split.
        - unfold hdr_off16. change (stride_of am1) with stride. cbn [fr_off].
          destruct Hscr as [H63' | Hsc48].
          + destruct Gcl as [(_ & Hl0 & _) | (C1 & _)]; [|lia]. replace idx with 0 by lia. rewrite Z.mul_0_r. cbn. lia.
          + destruct Gcl as [(C1 & _) | (_ & _ & _ & Hspan)]; [lia|]. fold stride in Hspan.
            assert (Hs16 : UNIT * off < stride) by (unfold IB in *; lia).
            unfold UNIT in *.
            assert (H1 : 16 * (stride * idx / 16) <= stride * idx) by (apply Z.mul_div_le; lia).
            assert (H3 : stride * idx + stride <= stride * (am_last am + 1)) by nia.
            lia.
        - intros Hk. split; [apply HoffG; exact Hk | apply Hgrp; exact Hk]. }
      intros Hoff0'. subst fr. cbn [fr_off] in Hoff0'. rewrite Hoff0', Z.eqb_refl. f_equal. f_equal.
      * unfold hdr_byte3, rsv_code. cbn [fr_kind fr_off fr_n]. change (stride_of am1) with stride.
        destruct (5 <=? stride - IB - UNIT * 0 - n); destruct k; lia.
      * unfold hdr_off16. cbn [fr_off]. change (stride_of am1) with stride. lia.
    + apply Z.eqb_neq in Ei. split; [exact S1|]. split; [exact S2|].
      destruct (ss_fr (nth_slot am i)) as [fri|].
      * destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [discriminate|].
        split; [| exact A4]. unfold frame_ok in *. unfold hdr_off16 in *. exact A3.
      * destruct S3 as [S3|S3]; [left; exact S3|]. exfalso. injection S3. lia.
  -
    destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & C2 & C3 & C4)].
    + left. repeat (split; [assumption|]). right.
      replace idx with 0 in * by lia. exists fr. rewrite NS by lia. rewrite Z.eqb_refl. subst sl1 fr. cbn.
      destruct (H63 C1) as (-> & Hbig & Hrsv). cbn [am_maplen upd_slot am_set_slots]. destruct am; cbn in *; auto.
    + right. repeat (split; [assumption|]). exact C4.
  - intros p i Hp. split; intros HH; [discriminate | injection HH; intros; subst; exfalso; exact (Hp eq_refl)].
  - intros i HH. discriminate.
  - intros Hsc HL. apply (proj1 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia))). exact HL.
  - intros Hsc Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia)))). exact Hav.
  - intros Hsc HL Hnh _. exfalso. apply Hnh. apply Hhdg; assumption.
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
Qed.

Lemma Inv_masks X R R' U s g am0 av fr ai : ltac2:(tb__ "0|15|
S5eVX;VR;VU;Vs;A4S60VX;Vs;Vg;Vam0;A4S2S44Z0M0S8Vam0;A1M1A2S45G1Z30A2A2S16Vai;S1aVfr;S12Vav;Vam0;A2A2A2SaS63R1A1S0S2S44G0R1A2S44R1SfVam0;A1M2A2A2S5S1S54S61R4R2A2M3S61Vam0;R2A2M4A3S5S2S1S53S52S7S0A2M5A1M6VR;S55G5A1M7A3S2S1G6VR';S50G5S51S7S0Vg;R2A4A2M8A3M9S2S1S54G4S5aA3S1S54G3S57A3A2A2A2S2S1G6VR;G8A3S2S1G6VR';G7A3S2S1S54G4S57A3S1S54G3S5aA3A2A2A2A2A2F_;Fi;S7S0S3S1G5S51S7S0R2R1A4S51S7S0Vg;G6S0LR';VR';G5G5S0Lp0;R1S7S0R1Lj;Ls0;X52x1Lp0;MaN1MbX53x2A4A3A1S3S1G5S51S7S0R3R2A4S51S7S0Vg;G6S0LR;VR;GaGbX53x2A4A3A1S6S1G6VR;S50G5S51S7S0R4R3A4A2McA3S1G6VR';GcA3A2F_;F_;Fi;Fp;S0S1G6VR';S50G5S51S7S0Vg;R1A4A2MdA3MeS2S2S44G0R2A2S44R2G2A2A2S2S1S53S1bA1S42S3cVam0;R2A2A1S55S1bA1A3S1S54S61R6R2A2S57A3A2A2F_;Fi;S0S1G6VR;GdA3S5G9S1S54S61R7R2A2S5aA3A2F_;Fi;S1S52S53S7A1MfGfA2S51GfGfS15Vam0;A1S11Vam0;A1A4S51GfGfS55S7A1M10G10A4A3M11S2S1S0Vav;G0A3M12S1S0Vfr;G0A3M13A2F_;S3G12A1S1GfS5fVs;G1A2S50S7Vg;A2A3M14F_;S3G11A1S3G14A1S0S3GeA1Fi;S3G13A1F_;F_;F_;S45Vai;G2A2S7SaS60VX;Vs;R2R1A4S3S1S7R3Vg;A3A1S1S0S8R3A1G1A3S3S45SdR4A1SfR4A1A2A1F_;F_;F_;Fa;Fp;F_;S45S19Vam0;A1S17G1A1A2S1S54S61RbG0A2S57A3F_;S5eVX;VR';VU;S66Vg;S10RbA1Vs;A3A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tam1;F_;F_;F_;").
Proof.
  intros HI Hu Hsc am1 Hm Hal HRo HRg HRoff Hfull HR1 HR2 Hpart HN1.
  pose proof (inv_groups HI g am0 Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  assert (GS : geom_same am0 am1) by (repeat split; auto).
  eapply (Inv_used_update X R R' U s g am0 am1 HI Hu (geom_same_upto_of X s _ _ GS)).
  - split; reflexivity.
  - exact Hm.
  - intros i Hi. change (am_last am1) with (am_last am0) in Hi.
    pose proof (Gsl i Hi) as (S1 & S2 & S3). unfold slot_ok. change (nth_slot am1 i) with (nth_slot am0 i).
    change (am_maplen am1) with (am_maplen am0). split; [exact S1|]. split; [exact S2|].
    destruct (ss_fr (nth_slot am0 i)) as [f|] eqn:Ef.
    + destruct S3 as (A1 & A2 & A3 & A4).
      destruct (Hal i Hi) as [E | [(_ & _ & E & _) | (ER & ER' & _ & _)]].
      * rewrite E. split; [exact A1|]. split.
        { intros E'. destruct (HRg i E') as (_ & Hn & _). rewrite Ef in Hn. discriminate. }
        split; [| exact A4]. unfold frame_ok, hdr_off16 in *. exact A3.
      * rewrite A1 in E. discriminate.
      * exfalso. exact (A2 ER).
    + destruct (Hal i Hi) as [E | [(_ & ER' & _ & _) | (ER & ER' & _ & E)]].
      * destruct S3 as [S3|S3]; [left; rewrite E; exact S3|].
        destruct (HRoff i S3) as [H|H]; [right; exact H | left; exact H].
      * right. exact ER'.
      * left. exact E.
  - destruct Gcl as [(C1 & _) | (C1 & C2 & C3 & C4)]; [lia|]. right.
    change (am_sc am1) with (am_sc am0). change (stride_of am1) with (stride_of am0).
    change (am_last am1) with (am_last am0). change (am_maplen am1) with (am_maplen am0).
    split; [exact C1|]. split; [|split; [exact C3 | exact C4]].
    intros Hs. split; [apply (proj1 (C2 Hs)) | apply HN1; exact Hs].
  - intros p i Hp. apply iff_sym. apply HRo; intros E; injection E as Epg _; exact (Hp Epg).
  - intros i E. destruct (HRg i E) as (A & B & C). change (am_last am1) with (am_last am0). auto.
  - intros Hs HL. change (am_avail am1) with av. change (am_freed am1) with fr. apply Hfull. exact HL.
  - intros Hs Hav. apply HR1. exact Hav.
  - intros Hs HL Hnh HnR. change (am_freed am1) with fr. apply HR2; assumption.
  - intros Hai. apply Hpart. exact Hai.
Qed.

Lemma allocated_eq am av fr ai i : ltac2:(tb__ "0|0|
S1S54S61S16Vai;S1aVfr;S12Vav;Vam;A2A2A2Vi;A2S59S4aS4cVav;Vfr;A2Vi;A2A1A3").
Proof. reflexivity. Qed.

Lemma allocated_am am i : ltac2:(tb__ "0|0|
S1S54S61Vam;Vi;A2S59S4aS4cSeVam;A1ScVam;A1A2Vi;A2A1A3").
Proof. reflexivity. Qed.

Lemma take_bit_Inv X U s g am : ltac2:(tb__ "0|4|
S5eVX;S55S52S7S0A2M0A1VU;Vs;A4S60VX;Vs;Vg;Vam;A4S2S44Z0M1S8Vam;A1M2A2S45G2Z30A2A2S1S53S7A1S5fVs;G2A2S50S7Vg;A2A3S3S1S0SeVam;A1M3G1A3A1S25G3A1S0S21R1A1S0S2S2S44G1R1A2S44R1SdVam;A1A2A2S2S1S0R2S36R1A1A3S2S1S54S4aG3R1A2S57A3S5eVX;S50G0S51S7S0Vg;R1A4A2VU;S66Vg;S10S12S49G3R2A2Vam;A2A1Vs;A3A4A2A2A2Tk;Tfirst;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hhd Hav first k.
  pose proof (inv_groups HI g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  destruct Gm as (Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra).
  destruct (lowbit_spec (am_avail am) ltac:(lia)) as (k0 & Hk0 & Hlb & Hbit & Hlow).
  assert (Ek : k = k0) by (subst k first; rewrite Hlb; apply ctz32_bit; exact Hk0). rewrite Ek in *.
  assert (Hkai : k0 <= am_aidx am).
  { destruct (Z_le_dec k0 (am_aidx am)); [assumption|]. rewrite (Gavp k0) in Hbit; [discriminate | lia]. }
  split; [lia|]. split; [exact Hlb|]. split; [exact Hbit|].
  assert (Esub : am_avail am - first = Z.ldiff (am_avail am) (bit k0)).
  { subst first. rewrite Hlb. apply sub_bit_ldiff; [exact Hk0 | exact Hbit]. }
  change (am_set_avail (am_avail am - first) am) with
    (am_set_aidx (am_aidx am) (am_set_freed (am_freed am) (am_set_avail (am_avail am - first) am))).
  rewrite Esub.
  assert (Hfrk : Z.testbit (am_freed am) k0 = false) by (apply Gdisj; [lia | exact Hbit]).
  eapply Inv_masks; try exact HI; try exact Hu; try exact Hsc.
  -
    unfold masks_ok. cbn -[Z.le Z.lt Z.add Z.testbit Z.ldiff Z.to_nat].
    repeat (split; [first [assumption | lia | apply Z.ldiff_nonneg; lia] |]).
    split; [|split; [|split]].
    + intros i Hi Hb. rewrite Z.ldiff_spec in Hb. apply andb_prop in Hb as [Hb _]. apply Gdisj; assumption.
    + intros i Hi. rewrite Z.ldiff_spec. destruct (Gabove i Hi) as [-> ->]. auto.
    + intros i Hi. rewrite Z.ldiff_spec, (Gavp i Hi). reflexivity.
    + exact Gfra.
  - intros i Hi. rewrite allocated_eq, allocated_am, !Z.lor_spec, Z.ldiff_spec, testbit_bit by lia.
    destruct (Z.eq_dec k0 i) as [<-|Hne].
    + right. left. rewrite Hbit, Hfrk, Z.eqb_refl. cbn. auto.
    + left. replace (k0 =? i) with false by (symmetry; apply Z.eqb_neq; exact Hne). cbn.
      destruct (Z.testbit (am_avail am) i); reflexivity.
  - intros p i H1 H2. split; [discriminate | intros E; exfalso; injection E as -> ->; exact (H1 eq_refl)].
  - intros i E. injection E as <-. split; [lia|]. split.
    + pose proof (Gsl k0 ltac:(lia)) as (_ & _ & S3). destruct (ss_fr (nth_slot am k0)) as [f|]; [|reflexivity].
      destruct S3 as (A1 & _). rewrite allocated_am, Z.lor_spec, Hbit in A1. discriminate.
    + rewrite allocated_eq, Z.lor_spec, Z.ldiff_spec, testbit_bit, Hbit, Hfrk, Z.eqb_refl by lia. reflexivity.
  - intros i E. discriminate.
  - intros HL. exfalso. destruct (inv_rings HI) as (_ & A & _). destruct (A _ Hsc) as (ms & Rg & Mem & _).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    apply (Mem g am Hu eq_refl) in Hin. exact (Hin HL).
  - intros _. exact Hhd.
  - intros _ Hnh. exfalso. exact (Hnh Hhd).
  - intros Hai p a Hp Hpg Hsca Ha. apply Hpg. symmetry. eapply (inv_partial HI g am p a); eauto; lia.
  - intros Hs. destruct Gcl as [(C1 & _) | (_ & C2 & _)]; [lia|]. destruct (C2 Hs) as [Hl0 Ha0].
    rewrite allocated_am in Ha0. rewrite allocated_eq, Z.lor_spec, Z.ldiff_spec, testbit_bit by lia.
    rewrite Z.lor_spec in Ha0. destruct (Z.testbit (am_avail am) 0), (Z.testbit (am_freed am) 0), (k0 =? 0); cbn in *; congruence.
Qed.

Lemma activate_Inv X U s g am : ltac2:(tb__ "0|4|
S5eVX;S55S52S7S0A2A1M0VU;Vs;A4S60VX;Vs;Vg;Vam;A4S2S44Z0M1S8Vam;A1M2A2S45G2Z30A2A2S1S53S7A1S5fVs;G2A2S50S7Vg;A2A3S1S0SeVam;A1G1A3S13SdVam;A1A1S0S5eVX;G0VU;S66Vg;S10S12S47ScVam;A1M3R1A2S1aS4eG3R1A2Vam;A2A2A1Vs;A3A4Tact;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hhd Hav act.
  pose proof (inv_groups HI g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  destruct Gm as (Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra).
  change (am_set_avail (Z.land (am_freed am) act) (am_set_freed (Z.ldiff (am_freed am) act) am)) with
    (am_set_aidx (am_aidx am) (am_set_freed (Z.ldiff (am_freed am) act) (am_set_avail (Z.land (am_freed am) act) am))).
  assert (Tact : forall i, Z.testbit act i = (0 <=? i) && (i <=? am_aidx am)) by (intros; subst act; apply testbit_ones; lia).
  eapply Inv_masks; try exact HI; try exact Hu; try exact Hsc.
  - unfold masks_ok. cbn -[Z.le Z.lt Z.add Z.testbit Z.ldiff Z.land Z.to_nat Z.leb andb].
    repeat (split; [first [assumption | lia | apply Z.ldiff_nonneg; lia | apply Z.land_nonneg; lia] |]).
    split; [|split; [|split]].
    + intros i Hi Hb. rewrite Z.land_spec in Hb. rewrite Z.ldiff_spec. apply andb_prop in Hb as [H1 H2]. rewrite H1, H2. reflexivity.
    + intros i Hi. rewrite Z.land_spec, Z.ldiff_spec. destruct (Gabove i Hi) as [_ ->]. auto.
    + intros i Hi. rewrite Z.land_spec, Tact. replace (i <=? am_aidx am) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite andb_false_r. apply andb_false_r.
    + intros i Hi. rewrite Z.ldiff_spec, Tact, (Gfra i Hi). replace (i <=? am_aidx am) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite andb_false_r. reflexivity.
  - intros i Hi. left. rewrite allocated_eq, allocated_am, !Z.lor_spec, Z.land_spec, Z.ldiff_spec, Hav, Z.bits_0. cbn.
    destruct (Z.testbit (am_freed am) i), (Z.testbit act i); reflexivity.
  - intros p i _ _. tauto.
  - intros i E. discriminate.
  - intros i E. discriminate.
  - intros HL. exfalso. destruct (inv_rings HI) as (_ & A & _). destruct (A _ Hsc) as (ms & Rg & Mem & _).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    apply (Mem g am Hu eq_refl) in Hin. exact (Hin HL).
  - intros _. exact Hhd.
  - intros _ Hnh. exfalso. exact (Hnh Hhd).
  - intros Hai p a Hp Hpg Hsca Ha. apply Hpg. symmetry. eapply (inv_partial HI g am p a); eauto; lia.
  - intros Hs. destruct Gcl as [(C1 & _) | (_ & C2 & _)]; [lia|]. destruct (C2 Hs) as [Hl0 Ha0].
    rewrite allocated_am in Ha0. rewrite allocated_eq, !Z.lor_spec, Z.land_spec, Z.ldiff_spec.
    rewrite Z.lor_spec in Ha0. destruct (Z.testbit (am_avail am) 0), (Z.testbit (am_freed am) 0), (Z.testbit act 0); cbn in *; congruence.
Qed.

Lemma extend_aidx_Inv X U s g am ai : ltac2:(tb__ "0|2|
S5eVX;S55S52S7S0A2A1M0VU;Vs;A4S60VX;Vs;Vg;Vam;A4S2S44Z0S8Vam;A1M1A2S45G1Z30A2A2S1S53S7A1S5fVs;G1A2S50S7Vg;A2A3S2S44SdVam;A1Vai;A2S44Vai;SfVam;A1A2A2S5eVX;G0VU;S66Vg;S10S16Vai;Vam;A2A1Vs;A3A4F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hhd Hai.
  pose proof (inv_groups HI g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  destruct Gm as (Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra).
  change (am_set_aidx ai am) with (am_set_aidx ai (am_set_freed (am_freed am) (am_set_avail (am_avail am) am))).
  eapply Inv_masks; try exact HI; try exact Hu; try exact Hsc.
  - unfold masks_ok. cbn -[Z.le Z.lt Z.add Z.testbit Z.to_nat].
    repeat (split; [first [assumption | lia] |]).
    split.
    + intros i Hi. apply Gavp. lia.
    + intros i Hi. apply Gfra. lia.
  - intros i Hi. left. reflexivity.
  - intros p i _ _. tauto.
  - intros i E. discriminate.
  - intros i E. discriminate.
  - intros HL. exfalso. destruct (inv_rings HI) as (_ & A & _). destruct (A _ Hsc) as (ms & Rg & Mem & _).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    apply (Mem g am Hu eq_refl) in Hin. exact (Hin HL).
  - intros _. exact Hhd.
  - intros _ Hnh. exfalso. exact (Hnh Hhd).
  - cbn [am_aidx am_set_aidx am_set_freed am_set_avail]. intros Hai' p a Hp Hpg Hsca Ha.
    apply Hpg. symmetry. eapply (inv_partial HI g am p a); eauto; lia.
  - intros Hs. destruct Gcl as [(C1 & _) | (_ & C2 & _)]; [lia|]. destruct (C2 Hs) as [Hl0 Ha0].
    rewrite allocated_am in Ha0. rewrite allocated_eq. exact Ha0.
Qed.

Lemma nth_In_range (l : list Z) k lo hi : ltac2:(tb__ "0|2|
S0S6aS0R1Vl;A3S2S44Vlo;R2A2S44R2Vhi;A2A2F_;Fu;S2S44Vlo;Z0M0A2S44G0Vhi;A2A2S2S44Vlo;S69S0Vk;Vl;G0A4M1A2S44G1Vhi;A2A2F_;F_;").
Proof.
  intros H H0. destruct (nth_error l k) as [x|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). apply H. eapply nth_error_In. exact E.
  - rewrite nth_overflow; [exact H0|]. apply nth_error_None. exact E.
Qed.

Lemma decay_bounces_spec X R U s sc (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S5eVX;VR;VU;Vs;A4S9S5eVX;VR;VU;R1A4S1S58S52S7S3bA2A1S2aR2A1S2aVs;A1A3S1S58S53S7A1A1S29R3A1S29Vs;A1A3S1S58S3fA1S2cR4A1S2cVs;A1A3S1S58S0A1S2dR5A1S2dVs;A1A3S1S0S2bR6A1S2bVs;A1A3VQ;S51S56S9S5dR7A4A1F_;F_;F_;F_;F_;F_;Fs';S64S52S56S9A2S22Vsc;Vs;A2VQ;A3F_;F_;").
Proof.
  intros HI HQ. unfold decay_bounces. destruct (bounce_idx sc) as [k|].
  - apply itok_modify.
    pose proof (inv_ctx HI) as (_&_&_&C4&_&_&C7&_).
    destruct (znth k (st_bounces s) =? 0) eqn:E; [apply HQ; auto|].
    apply HQ; try reflexivity. apply Inv_set_bounces; [exact HI| |].
    + rewrite length_zset. exact C4.
    + apply Z.eqb_neq in E. pose proof (nth_In_range (st_bounces s) (Z.to_nat k) 0 255 C7 ltac:(lia)) as Hr.
      unfold znth in E |- *.
      assert (Hv : 0 <= nth (Z.to_nat k) (st_bounces s) 0 - 1 <= 255) by lia.
      apply (proj2 (zset_length32_range _ k _ C4 C7 Hv)).
  - apply itok_ret. apply HQ; auto.
Qed.

Definition allzero (X : list sptr) (s : astate) (sc : Z) : Prop := ltac2:(tb__ "0|0|
S7SaS60VX;Vs;R2R1A4S1S0S8R2A1Vsc;A3S1S0SeR3A1Z0A3F_;F_;Fam;Fg;").

Definition ta_post (X : list sptr) (U : Z -> Z) (s : astate) (sc first : Z) (s' : astate) : Prop := ltac2:(tb__ "0|3|
S2S3S1S0Vfirst;Z0M0A3A1S4S7S7S4SaSaS2S5eVX;S50S52S7S0A2S51S7S0R2S21Vfirst;A1M1A4A2VU;Vs';A4S2S1S53S7A1M2S5fVs';Vsc;A2S50S7R2A2A3S2S60VX;Vs';R2R1A4S2S1S0S8R1A1Vsc;A3S2S44S17Vsc;A1S19R1A1A2S2S2S44G0G1A2S44G1SfR1A1A2A2S2S0S44G0R1A2S3S1S0R2Vsc;A3A1S1G2S5fVs';R3A2S5fVs;R3A2A3F_;F_;Fc;S65Vs;Vs';A2A2A2A2A2A2A2A2Lam;A2Lg;A2A2").

Lemma avail_bit_not_undersized X R U s g am i : ltac2:(tb__ "0|2|
S5eVX;VR;VU;Vs;A4S60VX;Vs;Vg;Vam;A4S2S44Z0M0S8Vam;A1M1A2S45G1Z30A2A2S44G0Vi;A2S1S54S4aS4cSeVam;A1ScVam;A1A2Vi;A2S57A3S44S17G1A1S19Vam;A1A2F_;F_;F_;F_;F_;").
Proof.
  intros HI Hu Hsc Hi Hb. pose proof (inv_groups HI g am Hu) as (Gm & _ & _ & Gcl & _).
  destruct Gcl as [(C1 & _) | (_ & C2 & _)]; [lia|].
  destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia].
  destruct (C2 Hlt) as [Hl0 Ha0]. rewrite allocated_am in Ha0.
  destruct Gm as (_ & _ & _ & _ & _ & _ & Gabove & _).
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Hb in Ha0. discriminate.
  - destruct (Gabove i ltac:(lia)) as [A B]. rewrite Z.lor_spec, A, B in Hb. discriminate.
Qed.

Lemma try_avail_finish X U s0 s sc m3 am3 (Q : Z * astate -> Prop) : ltac2:(tb__ "0|3|
S5eVX;S55S52S7S0A2A1VU;Vs;A4S2S44Z0M0Vsc;A2S45Vsc;Z30A2A2S1S53S7A1M1S5fVs;Vsc;A2S50S7Vm3;A2A3S60VX;Vs;Vm3;Vam3;A4S1S0S8Vam3;A1Vsc;A3S3S1S0S47ScVam3;A1S13SdVam3;A1A1A2G0A3A1S67VX;Vs;Vsc;A3S0S44G0R1A2S3S1S0R2Vsc;A3A1S1G1S5fVs;R3A2S5fVs0;R3A2A3F_;F_;Fc;S65Vs0;Vs;A2S0S9S68VX;VU;Vs0;Vsc;R2R1A6VQ;S51S0S9R3R2A4A1F_;Fs';Ffirst;S64S52S0S9A2SbS0S0S34Vm3;A1S0SbS56S0S38S59S4bR1G0A2A1Z3A2S56SbSaS0S1cVm3;A1M2SaSbS56S0S22S8R1A1A1S56S25R4A1S0SbSaS0G2SaSbS56S0S26Vm3;S12S49R6R2A2R1A2A2S56S18S0R3A2L_;A4Lam';A4Tfirst;L_;A4Lam;A4L_;A4Lmask;Vs;A5VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hhd Hu Hsca Hmask Hz Hoth UB0 HQ.
  pose proof (usedX_MT _ _ _ _ Hu) as [M3 NX3].
  pose proof (Hz m3 am3 Hu Hsca) as Hav0.
  unfold activate_group. mbinds. eapply itok_getm; [exact M3|]. msimp.
  mbinds. apply itok_massert; [rewrite Hav0; reflexivity|]. msimp.
  mbinds. apply itok_setm'. msimp. mbinds. apply itok_ret. msimp.
  set (act := ones (am_aidx am3)).
  set (am4 := am_set_avail (Z.land (am_freed am3) act) (am_set_freed (Z.ldiff (am_freed am3) act) am3)).
  set (s4 := upd_meta m3 (MUsed am4) s).
  assert (HI4 : Inv X None U s4).
  { subst s4 am4 act. rewrite <- Hsca in Hhd. apply (activate_Inv X U s m3 am3 HI Hu ltac:(lia) Hhd Hav0). }
  assert (M4 : MT s4 m3 = Some (MUsed am4)) by (subst s4; apply MT_upd_same).
  assert (Hu4 : usedX X s4 m3 am4) by (apply usedX_intro; [exact NX3 | exact M4]).
  mbinds. apply itok_massert.
  { destruct (Z.land (am_freed am3) act =? 0) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. exfalso. exact (Hmask E). }
  msimp. mbinds. eapply itok_getm; [exact M4|]. msimp.
  mbinds. eapply decay_bounces_spec; [exact HI4|].
  intros s5 HI5 Em5 Ea5 Er5 Eu5 Ec5. msimp.
  assert (M5 : MT s5 m3 = Some (MUsed am4)) by (unfold MT; rewrite Em5; exact M4).
  assert (Hu5 : usedX X s5 m3 am4) by (apply usedX_intro; [exact NX3 | exact M5]).
  mbinds. eapply itok_getm; [exact M5|]. msimp.
  mbinds. apply itok_setm'. msimp. apply itok_ret.
  assert (Hhd5 : active_hd s5 (am_sc am4) = Some m3).
  { change (am_sc am4) with (am_sc am3). rewrite Hsca. unfold active_hd. rewrite Ea5. exact Hhd. }
  assert (Hav4 : am_avail am4 <> 0) by (change (am_avail am4) with (Z.land (am_freed am3) act); exact Hmask).
  destruct (take_bit_Inv X U s5 m3 am4 HI5 Hu5 ltac:(change (am_sc am4) with (am_sc am3); lia) Hhd5 Hav4)
    as (Hk & Hfirst & Hbit & HI6).
  change (am_avail am4) with (Z.land (am_freed am3) act) in Hk, Hfirst, Hbit, HI6.
  apply HQ. split.
  { rewrite Hfirst. unfold bit. apply Z.pow_nonzero; lia. }
  exists m3, (am_set_avail (Z.land (am_freed am3) act - lowbit (Z.land (am_freed am3) act)) am4).
  split; [exact HI6|].
  split; [unfold active_hd; cbn; rewrite Ea5; exact Hhd|].
  split; [apply usedX_intro; [exact NX3 | apply MT_upd_same]|].
  split; [exact Hsca|].
  split.
  { change (stride_of _) with (stride_of am4). rewrite <- Hsca. change (am_sc am3) with (am_sc am4).
    apply (avail_bit_not_undersized X None U s4 m3 am4 (ctz32 (lowbit (Z.land (am_freed am3) act))) HI4 Hu4).
    - change (am_sc am4) with (am_sc am3). lia.
    - lia.
    - rewrite Z.lor_spec. change (am_avail am4) with (Z.land (am_freed am3) act). rewrite Hbit. reflexivity. }
  split.
  { pose proof (inv_groups HI Hu m3 am3) as G || pose proof (inv_groups HI m3 am3 Hu) as G.
    destruct G as ((_ & Gaidx & _) & _). change (am_last _) with (am_last am3). change (am_aidx am4) with (am_aidx am3) in Hk. lia. }
  split; [intros c Hc0 Hc; unfold active_hd; cbn; rewrite Ea5; apply Hoth; assumption|].
  eapply ub_same_trans; [exact UB0|].
  apply (ub_same_trans s s5).
  - apply (ub_same_trans s s4); [| apply ub_same_metas; exact Em5].
    subst s4. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M3|]. rewrite M3. cbn. subst am4. apply blocks_of_ext; destruct am3; reflexivity.
  - apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M5|]. rewrite M5. cbn. apply blocks_of_avail.
Qed.

Lemma span_loop_ge f c sp sz : ltac2:(tb__ "0|0|
S44Vc;S28Vf;Vc;Vsp;Vsz;A4A2").
Proof.
  revert c sp. induction f as [|f IH]; intros c sp; cbn; [lia|].
  destruct (Z.lxor sp (sp + sz - 1) <? 4096); [|lia]. specialize (IH (c + 1) (sp + sz)). lia.
Qed.

Lemma head_links X U s sc g am : ltac2:(tb__ "0|2|
S5eVX;S55S52S7S0A2A1VU;Vs;A4S2S44Z0M0Vsc;A2S45Vsc;Z30A2A2S1S53S7A1M1S5fVs;Vsc;A2S50S7Vg;A2A3S60VX;Vs;Vg;Vam;A4S1S0S8Vam;A1Vsc;A3S4S7S7S4S7S7S2S1G1S15Vam;A1S50S7R2A2A3S2S1G1S11Vam;A1S50S7R1A2A3S4SaSaS2S60VX;Vs;R2R1A4S2S1S0S8R1A1Vsc;A3S3S1S7R2Vg;A3A1S2S3S1S0ScR2A1G0A3A1S1S0SeR2A1G0A3A2F_;A2A2Lamn;A2A2A2Lnx;A2Lpr;A2F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hhd Hu Hsca. destruct (inv_rings HI) as (_ & A & _).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). rewrite Hhd in Rg.
  destruct (ring_head_links X s sc g am ms Rg Hu) as (rest & Ems & Hpr & Hnx).
  exists (last rest g), (hd g rest). split; [exact Hpr|]. split; [exact Hnx|].
  assert (Hin : In (hd g rest) (g :: rest)) by (destruct rest; [left; reflexivity | right; left; reflexivity]).
  rewrite <- Ems in Hin.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hin) as (amn & Hun & Hsn). exists amn.
  split; [exact Hun|]. split; [exact Hsn|]. intros Hne. split.
  - apply (Q2 _ _ Hun Hsn Hin); [rewrite Hhd; congruence | intros i; discriminate].
  - destruct (Z.eq_dec (am_avail amn) 0) as [E|E]; [exact E|]. exfalso.
    pose proof (Q1 _ _ Hun Hsn E) as E2. rewrite Hhd in E2. injection E2 as E3. exact (Hne (eq_sym E3)).
Qed.

Lemma try_avail_select X U s0 s sc m1 am1 (K : sptr -> M Z) (Q : Z * astate -> Prop) : ltac2:(tb__ "0|10|
S5eVX;S55S52S7S0A2A1M0VU;Vs;A4S2S44Z0M1Vsc;A2S45Vsc;Z30A2A2S1S53S7A1M2S5fVs;Vsc;A2S50S7Vm1;A2A3S60VX;Vs;Vm1;Vam1;A4S1S0S8Vam1;A1Vsc;A3S3S1S0ScVam1;A1G1A3A1S67VX;Vs;Vsc;A3S0S44G1R1A2M3S3S1S0R2Vsc;A3A1M4S1G2S5fVs;R3A2S5fVs0;R3A2M5A3F_;F_;Fc;S65Vs0;Vs;A2S7SaS9S5eVX;G0VU;R1A4S1G2S5fR2Vsc;A2S50S7R4A2A3S60VX;R3R5R4A4S1S0S8R5A1Vsc;A3S3S1S0S47ScR6A1S13SdR6A1A1A2G1A3A1S67VX;R6Vsc;A3S0G3G4S1G2S5fRaR3A2G5A3F_;F_;Fc;S65Vs0;R8A2S64S52S0S9A2M6VK;RbR9A2VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;Fs3;Fam3;Fm3;S64G6SbSaS0S1cVm1;A1SaSbS7S0S54S32S7A1M7L_;M8S4bScR1A1M9S13SfR1A1A1A2G2G7Lx;MaS11R1A1MbS7SbS56S7S40S31Vsc;A1S50S7R1A2A2S56S18S7R2A2McL_;A4Lnx;MdS23S7S1dZ6A1A2X53x2S18S7Vm1;A2X54x2S7SbSaS0S1cR1A1SaSbS7S0G8S4bS47G9S13SdR1A1A1A2G1A2G8S59S3dGbS50S7R2A2A2A1GaGbGdS23S7S1dZ7A1A2X53x2S17S8R1A1A1S0S46SdR2A1Z2A2S0S28U12cR1S46S14S48R2R1A2A2R2A4S0S54S0L_;S4fS46SfR4A1Z1MeA2MfR1A2GfR1X54x2S0SbS56S7S26R6S16S49R1GeA2R5A2A2S56S18S7R7A2L_;A4Tcnt;Tcnt1;Tcnt0;Tsize;X54x2GcX54x2S7VK;R1A1Lm3;A4Lam2;A4Lm2;A4Lam1';Vs;A5VQ;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hhd Hu Hsca Hfr Hz Hoth UB0 HK.
  pose proof (usedX_MT _ _ _ _ Hu) as [M1 NX1].
  mbinds. eapply itok_getm; [exact M1|]. msimp.

  match goal with |- itok (bind ?mm ?kk s) Q =>
    assert (STEPB : itok (mm s) (fun r => let m2 := fst r in let s2 := snd r in
       Inv X None U s2 /\ active_hd s2 sc = Some m2 /\ (exists am2, usedX X s2 m2 am2 /\ am_sc am2 = sc /\ am_freed am2 <> 0) /\
       allzero X s2 sc /\ (forall c, 0 <= c -> c <> sc -> active_hd s2 c = active_hd s0 c) /\ st_metas s2 = st_metas s)) end.
  { destruct (am_freed am1 =? ones (am_last am1)) eqn:Eall.
    - destruct (head_links X U s sc m1 am1 HI Hsc Hhd Hu Hsca) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
      rewrite Hnx. mbinds. apply itok_set_head. msimp. apply itok_ret. cbn [fst snd].
      pose proof (inv_ctx HI) as (Clen & _).
      assert (HI2 : Inv X None U (set_active (lupd (st_active s) (Z.to_nat sc) (Some nx)) s)).
      { exact (Inv_rotate_head X None U s sc m1 am1 nx HI Hsc Hu Hsca Hhd (Hz _ _ Hu Hsca) Hfr Hnx). }
      split; [exact HI2|]. split; [apply active_hd_set_active_same; rewrite Clen; lia|].
      split.
      { exists amn. split; [exact Hun|]. split; [exact Hsn|].
        destruct (sptr_eq_dec nx m1) as [->|Hne]; [| apply Hnxf; exact Hne].
        pose proof (usedX_fun _ _ _ _ _ Hun Hu) as ->. exact Hfr. }
      split; [intros g am Hg Hs'; apply (Hz g am Hg Hs')|].
      split; [|reflexivity]. intros c Hc0 Hc. rewrite active_hd_set_active_other by lia. apply Hoth; assumption.
    - apply itok_ret. cbn [fst snd]. split; [exact HI|]. split; [exact Hhd|]. split; [exists am1; auto|].
      split; [exact Hz|]. split; [exact Hoth | reflexivity]. }
  apply itok_bind. eapply itok_mono; [|exact STEPB].
  intros [m2 s2] (HI2 & Hhd2 & (am2 & Hu2 & Hs2 & Hfr2) & Hz2 & Hoth2 & Em2). cbn [fst snd] in *.
  pose proof (usedX_MT _ _ _ _ Hu2) as [M2 NX2].
  mbinds. eapply itok_getm; [exact M2|]. msimp.
  pose proof (inv_groups HI2 m2 am2 Hu2) as (Gm2 & _). pose proof Gm2 as (Glast & Gaidx & Glen & Gav & Gfr0 & Gdisj & Gabove & Gavp & Gfra).
  destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0) eqn:Ec.
  - apply Z.eqb_eq in Ec.

    assert (Haidx : am_aidx am2 < am_last am2).
    { destruct (Z_lt_dec (am_aidx am2) (am_last am2)) as [|Hge]; [assumption|]. exfalso. apply Hfr2.
      apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
      destruct (Z_le_dec i (am_last am2)).
      - apply (f_equal (fun z => Z.testbit z i)) in Ec. rewrite Z.land_spec, Z.bits_0, testbit_ones in Ec by lia.
        replace (0 <=? i) with true in Ec by (symmetry; apply Z.leb_le; lia).
        replace (i <=? am_aidx am2) with true in Ec by (symmetry; apply Z.leb_le; lia).
        rewrite andb_true_r in Ec. exact Ec.
      - apply (proj2 (Gabove i ltac:(lia))). }
    destruct (head_links X U s2 sc m2 am2 HI2 Hsc Hhd2 Hu2 Hs2) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
    rewrite Hnx. cbn [osptr_eqb].
    destruct (sptr_eqb nx m2) eqn:Enx; cbn [negb].
    +
      match goal with |- context [am_set_aidx ?a am2] => set (ai := a) end.
      mbinds. apply itok_setm'. msimp. apply itok_ret.
      pose proof (span_loop_ge 300 (am_aidx am2 + 2) (UNIT + class_size (am_sc am2) * (am_aidx am2 + 2)) (class_size (am_sc am2))) as Hsp.
      assert (Hai : am_aidx am2 + 1 <= ai <= am_last am2).
      { subst ai. destruct (am_last am2 + 1 <? span_loop 300 (am_aidx am2 + 2) (UNIT + class_size (am_sc am2) * (am_aidx am2 + 2)) (class_size (am_sc am2))) eqn:E;
          [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
      assert (HI3 : Inv X None U (upd_meta m2 (MUsed (am_set_aidx ai am2)) s2)).
      { eapply extend_aidx_Inv; eauto; [lia | rewrite Hs2; exact Hhd2 | lia]. }
      eapply HK; [exact HI3 | exact Hhd2 | apply usedX_intro; [exact NX2 | apply MT_upd_same] | exact Hs2 | | | |
        eapply ub_same_trans; [exact UB0|]; eapply ub_same_trans; [apply ub_same_metas; exact Em2|];
        apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M2|]; rewrite M2; cbn; apply blocks_of_aidx].
      * cbn [am_freed am_aidx am_set_aidx]. intros E0.
        apply (f_equal (fun z => Z.testbit z (am_aidx am2 + 1))) in E0.
        rewrite Z.land_spec, Z.bits_0, testbit_ones, (Gfra (am_aidx am2 + 1)) in E0 by lia.
        replace (0 <=? am_aidx am2 + 1) with true in E0 by (symmetry; apply Z.leb_le; lia).
        replace (am_aidx am2 + 1 <=? ai) with true in E0 by (symmetry; apply Z.leb_le; lia). discriminate.
      * intros g am Hg Hs'. apply usedX_upd in Hg as [[-> [_ E]] | [Hne Hg]].
        -- injection E as <-. cbn. apply (Hz2 _ _ Hu2 Hs2).
        -- apply (Hz2 _ _ Hg Hs').
      * exact Hoth2.
    +
      apply sptr_eqb_neq in Enx. destruct (Hnxf Enx) as [Hfrn Havn].
      mbinds. apply itok_set_head. msimp. apply itok_ret.
      pose proof (inv_ctx HI2) as (Clen & _).
      assert (HI3 : Inv X None U (set_active (lupd (st_active s2) (Z.to_nat sc) (Some nx)) s2)).
      { exact (Inv_rotate_head X None U s2 sc m2 am2 nx HI2 Hsc Hu2 Hs2 Hhd2 (Hz2 _ _ Hu2 Hs2) Hfr2 Hnx). }
      eapply HK; [exact HI3 | apply active_hd_set_active_same; rewrite Clen; lia | exact Hun | exact Hsn | | | |
        eapply ub_same_trans; [exact UB0|]; eapply ub_same_trans; [apply ub_same_metas; exact Em2|]; apply ub_same_metas; reflexivity].
      *
        intros E0.
        assert (Hnp : ~ am_aidx amn < am_last amn).
        { intros Hp. apply Enx. eapply (inv_partial HI2 nx amn m2 am2); eauto. congruence. }
        pose proof (inv_groups HI2 nx amn Hun) as ((Nlast & Naidx & _ & _ & _ & _ & Nabove & _) & _).
        apply Hfrn. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
        destruct (Z_le_dec i (am_last amn)).
        -- apply (f_equal (fun z => Z.testbit z i)) in E0. rewrite Z.land_spec, Z.bits_0, testbit_ones in E0 by lia.
           replace (0 <=? i) with true in E0 by (symmetry; apply Z.leb_le; lia).
           replace (i <=? am_aidx amn) with true in E0 by (symmetry; apply Z.leb_le; lia).
           rewrite andb_true_r in E0. exact E0.
        -- apply (proj2 (Nabove i ltac:(lia))).
      * intros g am Hg Hs'. apply (Hz2 g am Hg Hs').
      * intros c Hc0 Hc. cbn [snd]. rewrite active_hd_set_active_other by lia. apply Hoth2; assumption.
  - mbinds. apply itok_ret. msimp. apply Z.eqb_neq in Ec. eapply HK; eauto.
    eapply ub_same_trans; [exact UB0|]. apply ub_same_metas. exact Em2.
Qed.

Lemma try_avail_spec X U s sc (Q : Z * astate -> Prop) : ltac2:(tb__ "0|3|
S5eVX;S55S52S7S0A2A1M0VU;Vs;A4S2S44Z0M1Vsc;A2S45Vsc;Z30A2A2S9S5eVX;G0VU;R1A4S1S53S7A1M2S5fR2Vsc;A2S55S7A1A3S0S44G1R1A2S3S1S0R2Vsc;A3A1S1G2S5fR6R3A2S5fVs;R3A2A3F_;F_;Fc;S65Vs;R4A2VQ;S51S0S9G1R5A4A1F_;F_;F_;F_;Fs';S0S9S68VX;VU;Vs;Vsc;R2R1A6VQ;S51S0S9R3R2A4A1F_;Fs';Ffirst;S64S52S0S9A2S43Vsc;Vs;A2VQ;A3F_;F_;F_;F_;").
Proof.
  intros HI Hsc HQ0 HQ1.
  unfold try_avail. mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
  destruct (active_hd s sc) as [m0|] eqn:Ehd.
  2:{ apply itok_ret. apply HQ0; [exact HI | exact Ehd | auto | apply ub_same_refl]. }
  destruct (inv_rings HI) as (F & A & D). destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  rewrite Ehd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin0 _].
  destruct (ring_members_used _ _ _ _ _ m0 Rg Hin0) as (am0 & Hu0 & Hs0).
  pose proof (usedX_MT _ _ _ _ Hu0) as [M0 NX0].
  mbinds. eapply itok_getm; [exact M0|]. msimp.
  destruct (am_avail am0 =? 0) eqn:Eav; cbn [negb].
  -
    apply Z.eqb_eq in Eav.
    assert (Hz : allzero X s sc).
    { intros g am Hg Hsg. destruct (Z.eq_dec (am_avail am) 0) as [E|E]; [exact E|]. exfalso.
      pose proof (Q1 g am Hg Hsg E) as E2. rewrite Ehd in E2. injection E2 as ->.
      pose proof (usedX_fun _ _ _ _ _ Hg Hu0) as ->. exact (E Eav). }

    match goal with |- itok (bind ?mm ?kk s) Q =>
      assert (STEPA : itok (mm s) (fun r => let om1 := fst r in let s1 := snd r in
         Inv X None U s1 /\ active_hd s1 sc = om1 /\ allzero X s1 sc /\
         (forall c, 0 <= c -> c <> sc -> active_hd s1 c = active_hd s c) /\ ub_same s s1 /\
         match om1 with
         | None => True
         | Some m1 => exists am1, usedX X s1 m1 am1 /\ am_sc am1 = sc /\ am_freed am1 <> 0
         end)) end.
    { destruct (am_freed am0 =? 0) eqn:Efr.
      - apply Z.eqb_eq in Efr. mbinds.
        eapply (Inv_dequeue_full_head X None U s sc m0 am0); try assumption; [intros q i; discriminate|].
        intros s1 HI1 Sb Hse Bwd Fwd M0' Hnew UB1. msimp. apply itok_get_head. cbn [fst snd].
        change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
        split; [exact HI1|]. split; [reflexivity|]. split.
        { intros g am' Hg Hsg. destruct (Bwd _ _ Hg) as (am & Hga & E). pose proof (strip_fields _ _ E) as (_&Eav'&_&_&Es&_).
          rewrite Eav'. apply (Hz g am Hga). congruence. }
        split.
        { intros c Hc0 Hc. destruct Hse as (Hoth & _ & _). unfold active_hd. apply Hoth. intros sc' E. injection E as <-. lia. }
        split; [exact UB1|].
        destruct (active_hd s1 sc) as [m1|]; [|exact I].
        destruct Hnew as (Hne & am1 & Hu1 & Hs1 & Hf1 & _). exists am1. auto.
      - apply Z.eqb_neq in Efr.
        destruct (head_links X U s sc m0 am0 HI Hsc Ehd Hu0 Hs0) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
        rewrite Hnx. mbinds. apply itok_set_head. msimp. apply itok_ret. cbn [fst snd].
        pose proof (inv_ctx HI) as (Clen & _).
        split; [exact (Inv_rotate_head X None U s sc m0 am0 nx HI Hsc Hu0 Hs0 Ehd Eav Efr Hnx)|].
        split; [apply active_hd_set_active_same; rewrite Clen; lia|].
        split; [intros g am Hg Hsg; apply (Hz g am Hg Hsg)|].
        split; [intros c Hc0 Hc; rewrite active_hd_set_active_other by lia; reflexivity|].
        split; [apply ub_same_metas; reflexivity|].
        exists amn. split; [exact Hun|]. split; [exact Hsn|].
        destruct (sptr_eq_dec nx m0) as [->|Hne]; [| apply (proj1 (Hnxf Hne))].
        pose proof (usedX_fun _ _ _ _ _ Hun Hu0) as ->. exact Efr. }
    apply itok_bind. eapply itok_mono; [|exact STEPA].
    intros [om1 s1] (HI1 & Hhd1 & Hz1 & Hoth1 & UB1 & Hm1). cbn [fst snd] in *.
    destruct om1 as [m1|].
    2:{ apply itok_ret. apply HQ0; [exact HI1 | exact Hhd1 | exact Hoth1 | exact UB1]. }
    destruct Hm1 as (am1 & Hu1 & Hs1 & Hf1).
    eapply (try_avail_select X U s s1 sc m1 am1); try assumption.
    intros m3 am3 s3 HI3 Hhd3 Hu3 Hs3 Hmask3 Hz3 Hoth3 UB3.
    eapply (try_avail_finish X U s s3 sc m3 am3); try assumption.
  -
    apply Z.eqb_neq in Eav. mbinds. apply itok_setm'. msimp. apply itok_ret.
    rewrite <- Hs0 in Ehd.
    destruct (take_bit_Inv X U s m0 am0 HI Hu0 ltac:(lia) Ehd Eav) as (Hk & Hfirst & Hbit & HI').
    apply HQ1. split.
    { rewrite Hfirst. unfold bit. apply Z.pow_nonzero; lia. }
    exists m0, (am_set_avail (am_avail am0 - lowbit (am_avail am0)) am0).
    split; [exact HI'|]. split; [rewrite Hs0 in Ehd; exact Ehd|].
    split; [apply usedX_intro; [exact NX0 | apply MT_upd_same]|]. split; [exact Hs0|]. split.
    { change (stride_of _) with (stride_of am0). rewrite <- Hs0.
      apply (avail_bit_not_undersized X None U s m0 am0 (ctz32 (lowbit (am_avail am0))) HI Hu0 ltac:(lia) ltac:(lia)).
      rewrite Z.lor_spec, Hbit. reflexivity. }
    split.
    { pose proof (inv_groups HI m0 am0 Hu0) as ((_ & Gaidx & _) & _). change (am_last _) with (am_last am0). lia. }
    split; [intros c Hc0 Hc; reflexivity|].
    apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M0|]. rewrite M0. cbn. apply blocks_of_avail.
Qed.
