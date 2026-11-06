(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "frame"; "astate"; "MUsed"; "am_last"; "mslot"; "nth_slot"; "ss_fr"; "FUser"; "UNIT"; "am_sc"; "am_slots"; "malloc"; "mkFrame"; "padd"; "slot_start"; "slotst"; "upd_slot"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "option"; "pair"; "prod"; "app"; "None"; "Some"; "cons"; "list"; "nil"; "fst"; "length"; "nat"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "usedX"; "MT"; "active_hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ublist"; "ub_same"; "slotst_block"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMalloc"; "malloc_post"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame
  MallocWfRingOps MallocWfSurgery MallocWfRings MallocWfMeta MallocWfSlot MallocWfGeom MallocWfArith MallocWfGroup.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition malloc_post (X : list sptr) (U : Z -> Z) (s : astate) (n : Z) (r : option sptr * astate) : Prop := ltac2:(tb__ "0|5|
S14S29VX;S1bS19S0S16A2M0A1VU;S23S17S0A1M1S3Vr;A3M2A4G1OLx;S20G1S3Vr;A3S0S15S0S0S15S1S1S15S16S16S15S16S16S14S14S2aVX;G2R4R3A4S14S14S24Z0R2A2S24R2S5R3A1A2A2S14S13S17S2A1S8S7R3R2A2A1S1cS2SeR1Vn;S9A3A2A3S13S0R5SfS10R3R2A2S27SaR1A2A2A3A2A2A2S15S1eS19G0G0A2M3A1M4G4S15G4G4S14S13G4S2dG2A1S1aG3R2S1dG3S18G0G0S18S0S16R7Vn;A4S18S0S16R6R4A4A4R1A3A3A3S13G4S2dVs;A1S1aG3R2R1A3A3A2Ll2;A2Ll1;A2A2Loff;A2Lidx;A2Lam;A2Lg;A2Lp;S2eVs;G2A2X17x2A2").

Lemma enframe_inserts X R U s0 s2 g am idx x p n : ltac2:(tb__ "0|5|
S29VX;VR;VU;Vs2;A4S2eVs0;Vs2;A2S13S17S6A1S2bVs2;Vg;A2S1cS6S4Vam;A1A2A3S14S24Z0Vidx;A2S24Vidx;S5Vam;A1M0A2A2S13S22S21S11ScVam;A1A2S28S25G0Z1A2A1A3S13S17S2A1S8S7Vam;Vidx;A2A1S1bS2A1A3S13S1eS19S19S0S16A2M1G1A2M2A1M3S2fVg;Vam;Vidx;Vx;A4S1dG2S18G1G1S18S0S16Vp;Vn;A4S18S0S16Vg;Vidx;A4A4M4S1fG2A1A3A3S15G3G3S15G3G3S14S13G3S2dS30Vg;S4S12Vam;Vidx;Vx;A3A1Vs2;A3A1S1aG2R2S1dG2G4R1A3A3A3S13G3S2dVs0;A1S1aG2R2R1A3A3A2Ll2;A2Ll1;A2F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI UB Mg Hi Hlen Hfr Hx.
  destruct (ublist_upd_slot s2 g am idx x (proj1 (inv_keys HI)) Mg Hi Hlen) as (l1 & l2 & E1 & E2).
  exists l1, l2. rewrite E2, Hx, <- (ub_same_ublist _ _ UB), E1. unfold slot_block. rewrite Hfr. split; reflexivity.
Qed.

Lemma head_used X R U s sc g : ltac2:(tb__ "0|0|
S29VX;VR;VU;Vs;A4S14S24Z0Vsc;A2S26Vsc;Z30A2A2S13S17S0A1S2cVs;Vsc;A2S1cS0Vg;A2A3S15S1S1S14S2aVX;Vs;Vg;R1A4S13S16SbR1A1Vsc;A3A2Lam;A2F_;F_;F_;").
Proof.
  intros HI Hsc Hhd. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & _).
  rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _]. eapply ring_members_used; [exact Rg | exact Hin].
Qed.

Theorem malloc_spec U s n (Q : option sptr * astate -> Prop) : ltac2:(tb__ "0|2|
S29S1fS0A1M0S1bS19S0S16A2A1VU;Vs;A4S24Z0Vn;A2S19S17S0A1S3A2M1S32G0VU;Vs;Vn;R1A5VQ;R2A1F_;Fr;S31G1SdVn;Vs;A2VQ;A3F_;F_;F_;").
Proof.
  intros HI Hn HQ. unfold malloc.
  destruct (size_overflows n) eqn:Eov.
  { apply itok_ret. apply HQ. split; [exact HI | apply ub_same_refl]. }
  destruct (MMAP_THRESHOLD <=? n) eqn:Eth.
  -
    apply Z.leb_le in Eth.
    mbinds. apply itok_ask; [cbn [req_ok]; unfold size_overflows in Eov; apply Z.leb_gt in Eov; unfold IB, UNIT; lia|]. intros z _. msimp.
    destruct (z =? 0); cbn [negb].
    { apply itok_ret. apply HQ. split; [exact HI | apply ub_same_refl]. }
    mbinds. eapply new_region_spec; [exact HI | | reflexivity | pose proof (page_round_ge (n + IB + UNIT)); unfold IB, UNIT in *; lia]. intros s1 HI1 Es1. msimp.
    set (r := length (st_regions s)).
    assert (Hr1 : region_of s1 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)).
    { rewrite Es1. apply region_of_app_new. }
    assert (EU1 : forall q a, usedX [] s1 q a <-> usedX [] s q a) by (intros; rewrite Es1; unfold usedX, MTX, MT; cbn; tauto).
    mbinds. eapply step_seq_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _). msimp.
    assert (Hr2 : region_of s2 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)) by (unfold region_of in *; rewrite Er2; exact Hr1).
    assert (EU2 : forall q a, usedX [] s2 q a <-> usedX [] s q a) by (intros; rewrite <- EU1; unfold usedX, MTX, MT; rewrite Em2; tauto).
    assert (FRESH : forall q a, usedX [] s q a -> (prid (am_mem a) < r)%nat).
    { intros q a Hu. exact (used_group_prid_lt _ _ _ _ q a HI Hu). }
    pose proof (page_round_ge (n + IB + UNIT)) as PR1. pose proof (page_round_mod (n + IB + UNIT)) as PR2.
    mbinds. eapply alloc_meta_spec; [exact HI2 | |].
    +
      intros s3 HI3 (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3. msimp.
      mbinds. apply itok_ask.
      { cbn [req_ok]. exists (mkRegion RkMap (page_round (n + IB + UNIT)) [] true). cbn [rg_kind rg_live rg_len].
        split; [apply Erg3; [exact Hr2 | reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [unfold IB, UNIT; lia|].
        apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
        apply (used_metas_iff s3 q a (proj1 (inv_keys HI3))) in Hin.
        assert (Hu : usedX [] s q a) by (apply EU2, EU3; exact Hin).
        pose proof (FRESH q a Hu). lia. }
      intros z' _. msimp. mbinds. eapply upd_region_kill_spec; [exact HI3 | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | |].
      { intros q a Hu _. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
      intros s4 HI4 Em4 _. msimp. apply itok_ret. apply HQ. split; [exact HI4 |]. cbn [fst snd].
      eapply ub_same_trans; [| apply ub_same_metas; exact Em4]. eapply ub_same_trans; [| exact UB3].
      apply ub_same_metas. rewrite Em2, Es1. reflexivity.
    +
      intros g s3 HI3 NX Kg Mg (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3. msimp.
      set (maplen := page_round (n + IB + UNIT) / 4096).
      assert (Hml : page_round (n + IB + UNIT) = maplen * PGSZ).
      { subst maplen. rewrite Z.mul_comm. unfold PGSZ. pose proof (Z_div_mod_eq_full (page_round (n + IB + UNIT)) 4096). unfold PGSZ in PR2. lia. }
      mbinds. change (mkAMeta None None (SP r 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero]) with (direct_am r maplen).
      eapply install_direct_spec; [exact HI3 | exact NX | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | reflexivity | exact Hml | | |].
      { unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. nia. }
      { intros q a Hu Hp. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
      intros s4 Es4 HI4 U4 UB4. msimp. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
      pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
      set (s5 := set_mmap_counter _ s4).
      assert (HI5 : Inv [] (Some (g, 0)) U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
      assert (U5 : usedX [] s5 g (direct_am r maplen)) by (unfold usedX, MTX, MT in *; subst s5; cbn; exact U4).
      assert (Hstr : stride_of (direct_am r maplen) = maplen * 4096 - UNIT).
      { unfold stride_of, direct_am. cbn [am_last am_maplen am_sc Z.eqb andb].
        destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; unfold PGSZ, MMAP_THRESHOLD, UNIT, IB in *; nia | reflexivity]. }
      mbinds. eapply (enframe_spec [] U s5 g 0 n _ FUser (direct_am r maplen));
        [exact HI5 | exact U5 | exact Hn | rewrite Hstr; unfold PGSZ, UNIT, IB in *; lia | apply land32_range; lia | discriminate
        | intros _; pose proof (page_round_lt (n + IB + UNIT)) as PRlt; cbn [am_maplen direct_am]; repeat split; auto; lia
        | cbn; lia |].
      intros off s6 hdr Hoff Hfit _ Es6 HI6. msimp. apply itok_ret. apply HQ. split; [exact HI6|]. cbn [fst snd].
      exists g, (upd_slot (direct_am r maplen) 0 (mkSlot (Some hdr) (Some (mkFrame off n FUser)))), 0, off. split.
      { split; [rewrite Es6; apply usedX_upd; left; auto|]. cbn. split; [lia|]. split; reflexivity. }
      rewrite Es6. eapply (enframe_inserts [] (Some (g, 0)) U s s5 g (direct_am r maplen) 0); [exact HI5 | | | cbn; lia | reflexivity | reflexivity | reflexivity].
      * eapply ub_same_trans; [| apply ub_same_metas; subst s5; reflexivity]. eapply ub_same_trans; [| exact UB4].
        eapply ub_same_trans; [| exact UB3]. apply ub_same_metas. rewrite Em2, Es1. reflexivity.
      * unfold usedX, MTX in U5. cbn in U5. exact U5.
  -
    apply Z.leb_gt in Eth.
    pose proof (size_to_class_range n ltac:(lia)) as [Hsc0 Hfit0].
    mbinds. apply itok_get. msimp. cbn zeta.
    set (sc0 := size_to_class n) in *.
    match goal with |- itok (bind (match nth (Z.to_nat ?c) _ _ with _ => _ end) _ _) _ => set (sc := c) end.
    assert (Hsc : 0 <= sc < 48 /\ n + IB <= class_size sc).
    { subst sc. destruct (_ && (usage_of s sc0 =? 0)) eqn:E.
      - apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E E32].
        apply andb_prop in E as [_ E4]. apply Z.ltb_lt in E32.
        destruct (_ <=? 12); [|auto]. split; [lia|]. pose proof (class_size_mono sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
      - auto. }
    destruct Hsc as [Hsc Hfit]. clearbody sc.
    change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).

    mbinds.
    match goal with |- itok (?mm s) ?K =>
      assert (FAST : itok (mm s) (fun r => match fst r with
         | None => snd r = s
         | Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U (snd r) /\ usedX [] (snd r) gm am /\
                              n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
                              active_hd (snd r) sc = Some gm /\ ub_same s (snd r) end)) end.
    { destruct (active_hd s sc) as [gm|] eqn:Ehd; [|apply itok_ret; reflexivity].
      destruct (head_used _ _ _ _ sc gm HI Hsc Ehd) as (am & Hu & Hsa).
      pose proof (usedX_MT _ _ _ _ Hu) as [Mgm NXgm].
      mbinds. eapply itok_getm; [exact Mgm|]. msimp.
      destruct (am_avail am =? 0) eqn:Eav; [apply itok_ret; reflexivity|]. apply Z.eqb_neq in Eav.
      mbinds. apply itok_setm'. msimp. apply itok_ret. cbn [fst snd].
      rewrite <- Hsa in Hsc, Ehd.
      destruct (take_bit_Inv [] U s gm am HI Hu Hsc Ehd Eav) as (Hk & Hfirst & Hbit & HI1).
      pose proof (inv_groups HI gm am Hu) as ((_ & Gai & _) & _).
      eexists. split; [exact HI1|]. split; [apply usedX_upd; left; auto|].
      split; [|cbn; split; [lia | split; [exact Hsa | split; [rewrite <- Hsa; exact Ehd |
                apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mgm | rewrite Mgm; cbn; apply blocks_of_avail]]]]].
      pose proof (avail_bit_not_undersized [] None U s gm am (ctz32 (lowbit (am_avail am))) HI Hu Hsc ltac:(lia)
                    ltac:(rewrite Z.lor_spec, Hbit; reflexivity)) as Hus.
      rewrite Hsa in Hus. cbn. change (stride_of (am_set_avail (am_avail am - lowbit (am_avail am)) am)) with (stride_of am) || idtac.
      replace (stride_of (am_set_avail (am_avail am - lowbit (am_avail am)) am)) with (stride_of am) by (destruct am; reflexivity). lia. }
    eapply itok_mono in FAST. 2:{ intros r Hr. exact Hr. }
    revert FAST. apply itok_mono. intros [r s1] Hfast. cbn [fst snd] in Hfast. msimp.

    mbinds.
    match goal with |- itok (?mm s1) ?K =>
      assert (SLOW : itok (mm s1) (fun r => match fst r with
         | None => Inv [] None U (snd r) /\ ub_same s (snd r)
         | Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U (snd r) /\ usedX [] (snd r) gm am /\
                              n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
                              active_hd (snd r) sc = Some gm /\ ub_same s (snd r) end)) end.
    { destruct r as [[gm idx]|].
      - apply itok_ret. cbn [fst snd]. exact Hfast.
      - subst s1. mbinds. destruct (alloc_mutual NEST_FUEL) as [AS _].
        eapply AS; [exact HI | exact Hsc | exact Hn | exact Hfit | apply need_le_fuel; lia |].
        intros [idx s2] [_ [UB2 Hpost]]. cbn [fst snd] in Hpost, UB2. msimp.
        destruct Hpost as [[-> HI2] | (Hidx & g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hlast)].
        + cbn. split; [exact HI2 | exact UB2].
        + destruct (idx <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
          mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat sc) (st_active s2) None) with (active_hd s2 sc). rewrite Hhd2.
          apply itok_ret. cbn [fst snd]. exists am. repeat (split; [assumption|]). split; [lia | split; [exact Sc2 | split; [exact Hhd2 | exact UB2]]]. }
    revert SLOW. apply itok_mono. intros [gi s2] Hslow. cbn [fst snd] in Hslow. msimp.
    destruct gi as [[gm idx]|].
    2:{ apply itok_ret. apply HQ. exact Hslow. }
    destruct Hslow as (am & HI2 & U2 & Str2 & Hidx & Sc2 & Hhd2 & UB2).
    mbinds. apply itok_get. msimp.
    pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
    assert (H63 : am_sc am <> 63) by lia.
    mbinds. eapply (enframe_spec [] U s2 gm idx n (st_mmap_counter s2) FUser am);
      [exact HI2 | exact U2 | exact Hn | unfold IB in *; lia | lia | discriminate | intros H; exfalso; exact (H63 H)
      | intros _ _; rewrite Sc2; exact Hhd2 |].
    intros off s3 hdr Hoff Hofit _ Es3 HI3. msimp. apply itok_ret. apply HQ. split; [exact HI3|]. cbn [fst snd].
    pose proof (inv_groups HI2 gm am U2) as ((_ & _ & Glen & _) & _).
    exists gm, (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))), idx, off. split.
    { split; [rewrite Es3; apply usedX_upd; left; pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]; auto|].
      pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame off n FUser)))) as (_ & Fl & _ & _ & _ & _ & Fss).
      rewrite Fl, Fss. split; [lia|]. split; [|reflexivity].
      rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
    rewrite Es3. destruct (inv_reserved HI2 gm idx eq_refl) as (am_ & U_ & _ & Hfr_ & _). pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_.
    eapply (enframe_inserts [] (Some (gm, idx)) U s s2 gm am idx); [exact HI2 | exact UB2 | exact (proj1 (usedX_MT _ _ _ _ U2)) | lia | exact Glen | exact Hfr_ | reflexivity].
Qed.
