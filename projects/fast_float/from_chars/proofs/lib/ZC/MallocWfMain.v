(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.

Module MallocWfMalloc.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition malloc_post (X : list sptr) (U : Z -> Z) (s : astate) (n : Z) (r : option sptr * astate) : Prop :=
  Inv X None U (snd r) /\
  match fst r with
  | None => ub_same s (snd r)
  | Some p => exists g am idx off, (usedX X (snd r) g am /\ 0 <= idx <= am_last am /\
      ss_fr (nth_slot am idx) = Some (mkFrame off n FUser) /\ p = padd (slot_start am idx) (UNIT * off)) /\
      (exists l1 l2, ublist (snd r) = l1 ++ ((p, n), (g, idx)) :: l2 /\ ublist s = l1 ++ l2)
  end.

(* [comment removed for export] *)
Lemma enframe_inserts X R U s0 s2 g am idx x p n :
  Inv X R U s2 -> ub_same s0 s2 -> MT s2 g = Some (MUsed am) -> 0 <= idx <= am_last am ->
  length (am_slots am) = Z.to_nat (am_last am + 1) -> ss_fr (nth_slot am idx) = None ->
  slotst_block g am idx x = [((p, n), (g, idx))] ->
  exists l1 l2, ublist (upd_meta g (MUsed (upd_slot am idx x)) s2) = l1 ++ ((p, n), (g, idx)) :: l2 /\ ublist s0 = l1 ++ l2.
Proof.
  intros HI UB Mg Hi Hlen Hfr Hx.
  destruct (ublist_upd_slot s2 g am idx x (proj1 (inv_keys HI)) Mg Hi Hlen) as (l1 & l2 & E1 & E2).
  exists l1, l2. rewrite E2, Hx, <- (ub_same_ublist _ _ UB), E1. unfold slot_block. rewrite Hfr. split; reflexivity.
Qed.

Lemma head_used X R U s sc g :
  Inv X R U s -> 0 <= sc < 48 -> active_hd s sc = Some g ->
  exists am, usedX X s g am /\ am_sc am = sc.
Proof.
  intros HI Hsc Hhd. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & _).
  rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _]. eapply ring_members_used; [exact Rg | exact Hin].
Qed.

Theorem malloc_spec U s n (Q : option sptr * astate -> Prop) :
  Inv [] None U s -> 0 <= n ->
  (forall r, malloc_post [] U s n r -> Q r) ->
  itok (malloc n s) Q.
Proof.
  intros HI Hn HQ. unfold malloc.
  destruct (size_overflows n) eqn:Eov.
  { apply itok_ret. apply HQ. split; [exact HI | apply ub_same_refl]. }
  destruct (MMAP_THRESHOLD <=? n) eqn:Eth.
  - (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
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
        | intros _; split; [reflexivity | split; [exact Eth | cbn [am_maplen direct_am]; rewrite <- Hml; pose proof (page_round_lt (n + IB + UNIT)); lia]]
        | cbn; lia |].
      intros off s6 hdr Hoff Hfit _ Es6 HI6. msimp. apply itok_ret. apply HQ. split; [exact HI6|]. cbn [fst snd].
      exists g, (upd_slot (direct_am r maplen) 0 (mkSlot (Some hdr) (Some (mkFrame off n FUser)))), 0, off. split.
      { split; [rewrite Es6; apply usedX_upd; left; auto|]. cbn. split; [lia|]. split; reflexivity. }
      rewrite Es6. eapply (enframe_inserts [] (Some (g, 0)) U s s5 g (direct_am r maplen) 0); [exact HI5 | | | cbn; lia | reflexivity | reflexivity | reflexivity].
      * eapply ub_same_trans; [| apply ub_same_metas; subst s5; reflexivity]. eapply ub_same_trans; [| exact UB4].
        eapply ub_same_trans; [| exact UB3]. apply ub_same_metas. rewrite Em2, Es1. reflexivity.
      * unfold usedX, MTX in U5. cbn in U5. exact U5.
  - (* [comment removed for export] *)
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
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
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
End MallocWfMalloc.


Module MallocWfFree.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Inv_U_ext X R U U' s :
  (forall c, 0 <= c < 48 -> U' c = U c) -> Inv X R U s -> Inv X R U' s.
Proof.
  intros HU HI. split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split; [exact (inv_areas HI)|].
  pose proof (inv_meta HI) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|].
  split; [|exact (conj M7 M8)]. intros c Hc. rewrite (HU c Hc). apply M6. exact Hc.
Qed.

Lemma contrib_nonneg X R U s c q : Inv X R U s -> 0 <= contrib X s c q.
Proof.
  intros HI. unfold contrib. destruct (MTX X s q) as [[| |am]|] eqn:E; try lia.
  destruct (am_sc am =? c); [|lia]. pose proof (inv_groups HI q am E) as ((M1 & _) & _). lia.
Qed.

Lemma fold_sum_nonneg (f : sptr -> Z) l : (forall q, In q l -> 0 <= f q) -> 0 <= fold_right (fun q acc => f q + acc) 0 l.
Proof. induction l as [|x t IH]; intros H; cbn; [lia|]. pose proof (H x (or_introl eq_refl)). assert (0 <= fold_right (fun q acc => f q + acc) 0 t) by (apply IH; intros; apply H; right; assumption). lia. Qed.

Lemma class_sum_ge_contrib X R U s c g :
  Inv X R U s -> In g (keys s) -> contrib X s c g <= class_sum X s c.
Proof.
  intros HI Hg. unfold class_sum.
  rewrite (fold_sum_delta (fun q => if sptr_eqb q g then 0 else contrib X s c q) (contrib X s c) g (keys s) (proj1 (inv_keys HI)) Hg).
  2:{ intros q Hq. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. }
  rewrite sptr_eqb_refl.
  assert (0 <= fold_right (fun q acc => (if sptr_eqb q g then 0 else contrib X s c q) + acc) 0 (keys s)).
  { apply fold_sum_nonneg. intros q _. destruct (sptr_eqb q g); [lia|]. eapply contrib_nonneg. exact HI. }
  lia.
Qed.

Lemma contrib_used X s c g am : usedX X s g am -> contrib X s c g = if am_sc am =? c then am_last am + 1 else 0.
Proof. intros Hu. unfold contrib. unfold usedX in Hu. rewrite Hu. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Inv_exempt X R U s g am :
  Inv X R U s -> usedX X s g am ->
  (forall j, ss_fr (nth_slot am j) = None) ->
  am_prev am = None -> am_next am = None ->
  (forall p i, R = Some (p, i) -> p = g) ->
  Inv (g :: X) None (fun c => U c + contrib X s c g) s.
Proof.
  intros HI Hu Hfr Hp Hn HRg.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  assert (EMTX : forall q, q <> g -> MTX (g :: X) s q = MTX X s q).
  { intros q Hq. unfold MTX. rewrite memb_cons. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity]. }
  assert (EMg : MTX (g :: X) s g = None) by (unfold MTX; rewrite memb_cons, sptr_eqb_refl; reflexivity).
  assert (Bwd : forall p a, usedX (g :: X) s p a -> p <> g /\ usedX X s p a).
  { intros p a Ha. destruct (sptr_eq_dec p g) as [->|Hne]; [unfold usedX in Ha; rewrite EMg in Ha; discriminate|].
    split; [exact Hne|]. unfold usedX in *. rewrite <- (EMTX p Hne). exact Ha. }
  assert (Fwd : forall p a, usedX X s p a -> p <> g -> usedX (g :: X) s p a).
  { intros p a Ha Hne. unfold usedX in *. rewrite (EMTX p Hne). exact Ha. }
  destruct (inv_rings HI) as (F & A & D).
  eapply (Inv_surgery X (g :: X) R None U _ s s HI).
  - intros k rg Hk _. exact Hk.
  - intros p a' Ha'. destruct (Bwd p a' Ha') as [Hne Ha]. exists a'. split; [exact Ha | reflexivity].
  - intros p a Ha. destruct (sptr_eq_dec p g) as [->|Hne].
    + right. pose proof (usedX_fun _ _ _ _ _ Ha Hu) as ->. split; [|exact Hfr]. rewrite memb_cons, sptr_eqb_refl. reflexivity.
    + left. exists a. split; [apply Fwd; assumption | reflexivity].
  - intros p i E. discriminate.
  - intros p i a' Ha'. left. destruct (Bwd p a' Ha') as [Hne _]. split; [intros E; exfalso; exact (Hne (HRg p i E)) | discriminate].
  - exact (inv_ctx HI).
  - exact (inv_keys HI).
  - exact (inv_areas HI).
  - intros x [<-|Hx].
    + split; [exact Kg|]. rewrite Mg. auto.
    + exact (inv_X HI x Hx).
  - split; [|split].
    + destruct F as (ms & Rg & Hall). exists ms. split.
      * eapply ring_ok_ext; [|exact Rg]. intros q _. unfold flinks. destruct (sptr_eq_dec q g) as [->|Hne].
        -- rewrite EMg. unfold MTX. rewrite NXg, Mg. reflexivity.
        -- rewrite (EMTX q Hne). reflexivity.
      * intros q pr nx Hq. destruct (sptr_eq_dec q g) as [->|Hne]; [rewrite EMg in Hq; discriminate|].
        rewrite (EMTX q Hne) in Hq. eapply Hall. exact Hq.
    + intros c Hc. destruct (A c Hc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      assert (Hgn : am_sc am = c -> ~ In g ms).
      { intros Hs Hin. apply (Mem g am Hu Hs) in Hin. apply Hin. rewrite Hp, Hn. reflexivity. }
      split.
      { eapply ring_ok_ext; [|exact Rg]. intros q Hq. unfold alinks. destruct (sptr_eq_dec q g) as [->|Hne].
        - rewrite EMg. unfold MTX. rewrite NXg, Mg. destruct (am_sc am =? c) eqn:E; [|reflexivity].
          exfalso. apply Z.eqb_eq in E. exact (Hgn E Hq).
        - rewrite (EMTX q Hne). reflexivity. }
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Mem; exact Ha|].
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Full; exact Ha|].
      split; [intros q a Hq; destruct (Bwd q a Hq) as [_ Ha]; apply Q1; exact Ha|].
      intros q a Hq Hs Hin Hnh _. destruct (Bwd q a Hq) as [Hne Ha]. apply (Q2 q a Ha Hs Hin Hnh).
      intros i E. exact (Hne (HRg q i E)).
    + intros q a Hq. destruct (Bwd q a Hq) as [_ Ha]. exact (D q a Ha).
  - intros c Hc. rewrite (inv_usage HI c Hc). unfold class_sum.
    rewrite (fold_sum_delta (contrib X s c) (contrib (g :: X) s c) g (keys s) (proj1 (inv_keys HI)) Kg).
    2:{ intros q Hq. unfold contrib. rewrite (EMTX q Hq). reflexivity. }
    replace (contrib (g :: X) s c g) with 0 by (unfold contrib; rewrite EMg; reflexivity). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma usedX_cons_inv X g s q a : usedX (g :: X) s q a -> q <> g /\ usedX X s q a.
Proof.
  intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M N]. rewrite memb_cons in N. apply orb_false_elim in N as [E N].
  apply sptr_eqb_neq in E. split; [exact E|]. apply usedX_intro; assumption.
Qed.

Lemma usedX_cons X g s q a : usedX X s q a -> q <> g -> usedX (g :: X) s q a.
Proof.
  intros Hu Hne. pose proof (usedX_MT _ _ _ _ Hu) as [M N]. apply usedX_intro; [|exact M].
  rewrite memb_cons, N. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma in_split_sptr (g : sptr) ms : In g ms -> NoDup ms -> exists l1 l2, ms = l1 ++ g :: l2 /\ ~ In g l1 /\ ~ In g l2.
Proof.
  intros Hin Hnd. destruct (in_split _ _ Hin) as (l1 & l2 & ->). exists l1, l2. split; [reflexivity|].
  apply NoDup_remove_2 in Hnd. rewrite in_app_iff in Hnd. tauto.
Qed.

Lemma dequeue_exempt_spec X R U s sc g am (Q : unit * astate -> Prop) :
  Inv X R U s -> 0 <= sc < 48 -> usedX X s g am -> am_sc am = sc ->
  (am_prev am, am_next am) <> (None, None) ->
  (forall j, ss_fr (nth_slot am j) = None) ->
  (forall p i, R = Some (p, i) -> p = g) ->
  (forall s',
     Inv (g :: X) None (fun c => U c + contrib X s c g) s' ->
     same_but_metas_heads s s' ->
     MT s' g = Some (MUsed (am_set_links None None am)) ->
     (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
     (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s' q = MT s q) ->
     (forall q a', usedX (g :: X) s' q a' -> q <> g /\ exists a, usedX X s q a /\ strip a' = strip a) ->
     (active_hd s sc <> Some g -> active_hd s' sc = active_hd s sc) ->
     (active_hd s sc = Some g ->
        active_hd s' sc = None \/
        exists h ah, active_hd s' sc = Some h /\ h <> g /\ usedX (g :: X) s' h ah /\ am_sc ah = sc /\ am_avail ah = 0) ->
     ub_same s s' ->
     Q (tt, s')) ->
  itok (dequeue (HActive sc) g s) Q.
Proof.
  intros HI Hsc Hu Hsca Hlinked Hfr HRg HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  assert (Hin : In g ms) by (apply (Mem g am Hu Hsca); exact Hlinked).
  destruct (in_split_sptr g ms Hin (proj1 (proj1 Rg))) as (l1 & l2 & Ems & Hn1 & Hn2).
  assert (Cyc : cycle_ok (alinks X s sc) (g :: l2 ++ l1)).
  { change (g :: l2 ++ l1) with ((g :: l2) ++ l1). apply cycle_rotate_n. rewrite <- Ems. exact (proj1 Rg). }
  set (rest := l2 ++ l1) in Cyc.
  assert (Hms : forall q, In q ms <-> q = g \/ In q rest).
  { intros q. rewrite Ems. subst rest. rewrite !in_app_iff. cbn [In]. split; intros H; decompose [or] H; subst; auto 6. }
  assert (SC : forall q, In q (g :: rest) -> exists a, usedX X s q a /\ am_sc a = sc).
  { intros q Hq. eapply ring_members_used; [exact Rg|]. apply Hms. destruct Hq as [<-|Hq]; auto. }
  assert (SX : forall q, In q (g :: rest) -> memb q X = false).
  { intros q Hq. destruct (SC q Hq) as (a & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
  eapply (dequeue_op (HActive sc) g s (MUsed am) rest (alinks X s sc)).
  - exact Mg.
  - exact Cyc.
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mg' Mother Mrest.
    assert (RL : relinked s s' (g :: rest)).
    { split.
      - exact Mother.
      - intros q Hq. destruct Hq as [<- | Hq].
        + exists (MUsed am), None, None. split; [exact Mg|]. split; [exact Mg'|]. discriminate.
        + destruct (SC q (or_intror Hq)) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
          eexists (MUsed a), _, _. split; [exact Mq|]. split; [apply (Mrest q (MUsed a) Hq Mq) | discriminate]. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.
    pose proof Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg&_&EK).
    destruct Hse as (Hoth & Hfmh & Hlen).
    assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c).
    { intros c Hc Hne. unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }
    (* [comment removed for export] *)
    assert (Bwd' : forall q a', usedX (g :: X) s' q a' -> q <> g /\ exists a, usedX X s q a /\ strip a' = strip a).
    { intros q a' Hq. destruct (usedX_cons_inv _ _ _ _ _ Hq) as [Hne Hq']. split; [exact Hne|]. apply Bwd. exact Hq'. }
    assert (Same : forall q a', usedX (g :: X) s' q a' -> ~ In q (g :: rest) -> usedX X s q a').
    { intros q a' Hq Hnin. destruct (usedX_cons_inv _ _ _ _ _ Hq) as [Hne Hq']. apply (rl_used_same X s s' _ RL q a' Hnin). exact Hq'. }
    assert (NotS : forall q a', usedX (g :: X) s' q a' -> am_sc a' <> sc -> ~ In q (g :: rest)).
    { intros q a' Hq Hs Hi. destruct (SC q Hi) as (a & Hqu & Hqs). destruct (Bwd' q a' Hq) as (_ & a0 & Hq0 & E).
      pose proof (usedX_fun _ _ _ _ _ Hq0 Hqu) as ->. apply strip_fields in E as (_&_&_&_&Es&_). congruence. }
    (* [comment removed for export] *)
    assert (Hhd_old : active_hd s sc = hd_error ms) by exact (proj2 Rg).
    assert (Hhd_new : active_hd s' sc = hd_error (l1 ++ l2)).
    { cbn [head_of] in Hhd'. rewrite Hhd'. rewrite Hhd_old, Ems. subst rest.
      destruct l1 as [|h1 l1']; cbn.
      - destruct l2 as [|y l2']; cbn; [reflexivity|]. rewrite sptr_eqb_refl. reflexivity.
      - destruct (l2 ++ h1 :: l1') as [|y t] eqn:E; [destruct l2; discriminate|].
        destruct (sptr_eqb h1 g) eqn:E2; [|reflexivity]. apply sptr_eqb_eq in E2. subst h1. exfalso. apply Hn1. left. reflexivity. }
    assert (Rg' : ring_ok (alinks (g :: X) s' sc) (active_hd s' sc) (l1 ++ l2)).
    { rewrite Hhd_new. split; [|reflexivity].
      apply cycle_rotate_n. fold rest.
      assert (Cyc' : rest = [] \/ cycle_ok (alinks (g :: X) s' sc) rest).
      { destruct rest as [|y rest'] eqn:Er; [left; reflexivity | right].
        eapply (cycle_remove_first (alinks X s sc) (alinks (g :: X) s' sc) g (y :: rest')).
        - exact Cyc.
        - discriminate.
        - intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (a & Hzu & Hzs & El).
          pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
          pose proof (Mrest z (MUsed a) Hz Mz) as Mz'. cbn [with_links] in Mz'.
          assert (Hzg : z <> g).
          { intros ->. destruct Cyc as [Hnd _]. inversion Hnd; subst. contradiction. }
          unfold alinks, MTX. rewrite memb_cons, NXz. replace (sptr_eqb z g) with false by (symmetry; apply sptr_eqb_neq; exact Hzg).
          cbn [orb]. rewrite Mz'. cbn [am_sc am_prev am_next am_set_links].
          rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity. }
      destruct Cyc' as [-> | Cyc']; [split; [constructor | exact I] | exact Cyc']. }
    apply HQ.
    + eapply (Inv_surgery X (g :: X) R None U _ s s' HI).
      * intros k rg Hk _. unfold region_of in *. rewrite Erg. exact Hk.
      * intros p a' Hp. destruct (Bwd' p a' Hp) as [_ H]. exact H.
      * intros p a Hp. destruct (sptr_eq_dec p g) as [->|Hne].
        -- right. pose proof (usedX_fun _ _ _ _ _ Hp Hu) as ->. split; [rewrite memb_cons, sptr_eqb_refl; reflexivity | exact Hfr].
        -- left. destruct (Fwd _ _ Hp) as (a' & Hp' & E). exists a'. split; [apply usedX_cons; assumption | exact E].
      * intros p i E. discriminate.
      * intros p i a' Hp. left. destruct (Bwd' p a' Hp) as [Hne _]. split; [intros E; exfalso; exact (Hne (HRg p i E)) | discriminate].
      * apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
        intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
        unfold keys in Kg. rewrite Hm in Kg. exact Kg.
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * intros x [<-|Hx].
        -- split; [rewrite EK; exact Kg|]. rewrite Mg'. cbn. split; [reflexivity|]. split; [reflexivity|].
           intros i. unfold nth_slot in *. cbn. apply Hfr.
        -- destruct (inv_X HI x Hx) as [Kx Mx]. split; [rewrite EK; exact Kx|].
           rewrite Mother; [exact Mx|]. intros Hi. pose proof (SX x Hi) as E. apply memb_false_notIn in E. exact (E Hx).
      * (* [comment removed for export] *)
        split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - rewrite (Hfmh ltac:(discriminate)).
            eapply ring_ok_ext; [|exact FR]. intros q _.
            unfold flinks. destruct (sptr_eq_dec q g) as [->|Hne].
            + unfold MTX. rewrite memb_cons, sptr_eqb_refl, NXg, Mg. reflexivity.
            + replace (MTX (g :: X) s' q) with (MTX X s' q) by (unfold MTX; rewrite memb_cons; replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hne); reflexivity).
              fold (flinks X s' q). fold (flinks X s q). eapply rl_flinks_used; eauto.
          - intros q pr nx Hq. apply (Fall q pr nx). unfold MTX in *. rewrite memb_cons in Hq.
            destruct (sptr_eqb q g) eqn:Eqg; [discriminate|]. cbn [orb] in Hq. destruct (memb q X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hq|].
            exfalso. destruct (SC q D1) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
            rewrite Mq in A1. injection A1 as <-. rewrite B1 in Hq. cbn in Hq. discriminate. }
        split.
        { intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
          - exists (l1 ++ l2). split; [exact Rg'|].
            assert (InNew : forall q, In q (l1 ++ l2) <-> In q rest) by (intros q; subst rest; rewrite !in_app_iff; tauto).
            split.
            { intros q a' Hq Hs'. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              destruct (in_dec sptr_eq_dec q rest) as [Hi|Hni].
              + split; [intros _ | intros _; apply InNew; exact Hi].
                destruct (ring_links _ _ _ _ Rg' (proj2 (InNew q) Hi)) as (pr & nx & L).
                unfold alinks in L. pose proof Hq as Hq2. unfold usedX in Hq2. rewrite Hq2, Hs', Z.eqb_refl in L.
                injection L as -> ->. discriminate.
              + assert (Hq0 : usedX X s q a') by (apply Same; [exact Hq | intros [E0|E0]; [exact (Hne (eq_sym E0)) | exact (Hni E0)]]).
                rewrite <- (Mem q a' Hq0 Hs'). rewrite InNew, Hms. split; [intros H; right; exact H | intros [E0|E0]; [exfalso; exact (Hne E0) | exact E0]]. }
            split.
            { intros q a' Hq Hs' Hnin. destruct (Bwd' q a' Hq) as (Hne & _).
              assert (Hni : ~ In q rest) by (intros Hi; apply Hnin; apply InNew; exact Hi).
              assert (Hq0 : usedX X s q a') by (apply Same; [exact Hq | intros [E0|E0]; [exact (Hne (eq_sym E0)) | exact (Hni E0)]]).
              apply (Full q a' Hq0 Hs'). rewrite Hms. intros [E0|E0]; [exact (Hne E0) | exact (Hni E0)]. }
            split.
            { intros q a' Hq Hs' Hav'. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). rewrite Eav in Hav'.
              pose proof (Q1 q a Hqu ltac:(congruence) Hav') as Hh.
              rewrite Hhd_new. rewrite Hhd_old, Ems in Hh. destruct l1 as [|h1 l1']; cbn in Hh |- *.
              - injection Hh as ->. exfalso. exact (Hne eq_refl).
              - exact Hh. }
            { intros q a' Hq Hs' Hiq Hnh _. destruct (Bwd' q a' Hq) as (Hne & a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              apply (Q2 q a Hqu ltac:(congruence)).
              - apply Hms. right. apply InNew. exact Hiq.
              - rewrite Hhd_old, Ems. rewrite Hhd_new in Hnh. destruct l1 as [|h1 l1']; cbn in Hnh |- *.
                + intros E0. injection E0 as ->. exact (Hne eq_refl).
                + exact Hnh.
              - intros i E0. exact (Hne (HRg q i E0)). }
          - destruct (A c Hc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            rewrite (EH c ltac:(lia) Hne). split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q Hq.
              destruct (sptr_eq_dec q g) as [->|Hqg].
              - exfalso. destruct (ring_members_used _ _ _ _ _ g Rg2 Hq) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hu) as ->. lia.
              - unfold alinks. replace (MTX (g :: X) s' q) with (MTX X s' q) by (unfold MTX; rewrite memb_cons; replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hqg); reflexivity).
                fold (alinks X s' c q). fold (alinks X s c q). eapply rl_alinks_other; eauto. }
            split; [|split; [|split]]; intros q a' Hq Hs';
              pose proof (NotS q a' Hq ltac:(lia)) as Hni; pose proof (Same q a' Hq Hni) as Hq0.
            + apply Mem2; [exact Hq0 | exact Hs'].
            + apply Full2; [exact Hq0 | exact Hs'].
            + apply Q12; [exact Hq0 | exact Hs'].
            + intros Hiq Hnh _. apply (Q22 q a' Hq0 Hs' Hiq Hnh). intros i E0. apply (HRg q i) in E0. subst q. apply Hni. left. reflexivity. }
        { intros q a' Hq H63. pose proof (NotS q a' Hq ltac:(lia)) as Hni. pose proof (Same q a' Hq Hni) as Hq0. exact (D q a' Hq0 H63). }
      * (* [comment removed for export] *)
        intros c Hc. rewrite (sbmh_usage_of _ _ c Sb), (inv_usage HI c Hc). unfold class_sum. rewrite EK.
        rewrite (fold_sum_delta (contrib X s c) (contrib (g :: X) s' c) g (keys s) (proj1 (inv_keys HI)) Kg).
        2:{ intros q Hq. rewrite <- (rl_contrib X s s' _ RL c q). unfold contrib, MTX. rewrite memb_cons.
            replace (sptr_eqb q g) with false by (symmetry; apply sptr_eqb_neq; exact Hq). reflexivity. }
        replace (contrib (g :: X) s' c g) with 0 by (unfold contrib, MTX; rewrite memb_cons, sptr_eqb_refl; reflexivity). lia.
    + exact Sb.
    + exact Mg'.
    + exact EH.
    + intros q Hq Hqg. apply Mother. intros Hi. destruct (SC q Hi) as (a & Hqu & Hqs). exact (Hq a Hqu Hqs).
    + exact Bwd'.
    + intros Hnh. rewrite Hhd_new. rewrite Hhd_old, Ems in Hnh |- *. destruct l1 as [|h1 l1']; cbn in Hnh |- *; [exfalso; apply Hnh; reflexivity | reflexivity].
    + intros Hh. rewrite Hhd_old, Ems in Hh. destruct l1 as [|h1 l1']; cbn in Hh.
      2:{ injection Hh as ->. exfalso. apply Hn1. left. reflexivity. }
      rewrite Hhd_new. cbn. destruct l2 as [|y l2']; [left; reflexivity | right].
      cbn. assert (Hy : In y ms) by (rewrite Ems; cbn; right; left; reflexivity).
      destruct (ring_members_used _ _ _ _ _ y Rg Hy) as (ay & Hyu & Hys).
      assert (Hyg : y <> g) by (intros ->; apply Hn2; left; reflexivity).
      destruct (Fwd _ _ Hyu) as (ay' & Hyu' & E). exists y, ay'.
      pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_).
      split; [reflexivity|]. split; [exact Hyg|]. split; [apply usedX_cons; assumption|]. split; [congruence|].
      rewrite Eav. destruct (Z.eq_dec (am_avail ay) 0) as [E0|E0]; [exact E0|]. exfalso.
      pose proof (Q1 y ay Hyu Hys E0) as Hh'. rewrite Hhd_old, Ems in Hh'. cbn in Hh'. injection Hh' as ->. exact (Hyg eq_refl).
    + eapply ub_same_relinked; [exact RL | exact EK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma drop_frame_Inv X U s g am i fr x :
  Inv X None U s -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr ->
  (fr_kind fr = FGroup -> forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am i) ->
  ss_fr x = None ->
  (ss_hdr x = ss_hdr (nth_slot am i) \/ ss_hdr x = Some (255, 0)) ->
  Inv X (Some (g, i)) U (upd_meta g (MUsed (upd_slot am i x)) s).
Proof.
  intros HI Hu Hi Hfr Hchild Hxfr Hxhdr.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  pose proof (inv_groups HI g am Hu) as G. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof Gm as (Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra).
  set (am1 := upd_slot am i x).
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat) by (rewrite Glen; lia).
  assert (NS : forall j, 0 <= j -> nth_slot am1 j = if j =? i then x else nth_slot am j).
  { intros j Hj. subst am1. apply nth_slot_upd_slot; [lia | exact Hj | exact Hlen]. }
  pose proof (Gsl i Hi) as (Si1 & Si2 & Si3). rewrite Hfr in Si3. destruct Si3 as (Hal & _ & Fok & Hhdr0).
  assert (GS : geom_same_upto X s am am1).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros j frj Hj0 Hj Hkj. rewrite NS by exact Hj0. destruct (j =? i) eqn:E; [|left; exact Hj].
    apply Z.eqb_eq in E. subst j. right. rewrite Hfr in Hj. injection Hj as <-. exact (Hchild Hkj). }
  assert (Hscr : am_sc am = 63 \/ (0 <= am_sc am < 48)).
  { destruct Gcl as [(C1 & _) | (C1 & _)]; [left; exact C1 | right; exact C1]. }
  eapply (Inv_used_update X None (Some (g, i)) U s g am am1 HI Hu GS).
  - split; reflexivity.
  - unfold masks_ok. subst am1. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
    repeat (split; [assumption|]). exact Gfra.
  - intros j Hj. cbn [am_last am1 upd_slot am_set_slots] in Hj.
    pose proof (Gsl j Hj) as (S1 & S2 & S3). unfold slot_ok. rewrite NS by lia.
    replace (am_maplen am1) with (am_maplen am) by reflexivity.
    replace (allocated am1 j) with (allocated am j) by reflexivity.
    destruct (j =? i) eqn:Ej.
    + apply Z.eqb_eq in Ej. subst j. rewrite Hxfr. split; [|split; [|right; reflexivity]].
      * intros Hn. destruct Hxhdr as [E|E]; [rewrite E in Hn; apply Si1; exact Hn | rewrite E in Hn; discriminate].
      * intros h3 h16 Eh. destruct Hxhdr as [E|E]; rewrite E in Eh; [apply Si2; exact Eh | injection Eh as <- <-; lia].
    + apply Z.eqb_neq in Ej. split; [exact S1|]. split; [exact S2|].
      destruct (ss_fr (nth_slot am j)) as [frj|].
      * destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [intros E; injection E; lia|].
        split; [| exact A4]. unfold frame_ok, hdr_off16 in *. exact A3.
      * destruct S3 as [S3|S3]; [left; exact S3 | discriminate].
  - destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & C2 & C3 & C4)].
    + (* [comment removed for export] *)
      left. repeat (split; [assumption|]). left. replace i with 0 by lia. reflexivity.
    + right. repeat (split; [assumption|]). exact C4.
  - intros p j Hp. split; intros HH; [injection HH; intros; subst; exfalso; exact (Hp eq_refl) | discriminate].
  - intros j HH. injection HH as <-. cbn [am_last am1 upd_slot am_set_slots]. split; [exact Hi|]. rewrite NS by lia. rewrite Z.eqb_refl.
    split; [exact Hxfr|]. exact Hal.
  - intros Hsc HL. apply (proj1 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia))). exact HL.
  - intros Hsc Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia)))). exact Hav.
  - intros Hsc HL Hnh HnR. exfalso. exact (HnR i eq_refl).
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
  - intros Hai. exact Hai.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma requeue_spec X U s sc g i am (Q : unit * astate -> Prop) :
  Inv X (Some (g, i)) U s -> 0 <= sc < 48 -> usedX X s g am -> am_sc am = sc ->
  am_prev am = None -> am_next am = None -> active_hd s sc <> Some g ->
  (forall s' pr nx,
     Inv X (Some (g, i)) U s' -> same_but_metas_heads s s' ->
     MT s' g = Some (MUsed (am_set_links (Some pr) (Some nx) am)) ->
     (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
     (forall q a', usedX X s' q a' -> exists a, usedX X s q a /\ strip a' = strip a) ->
     ub_same s s' ->
     Q (tt, s')) ->
  itok (queue (HActive sc) g s) Q.
Proof.
  intros HI Hsc Hu Hsca Hp Hn Hnh HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  assert (Hgn : ~ In g ms).
  { intros Hin. apply (Mem g am Hu Hsca) in Hin. apply Hin. rewrite Hp, Hn. reflexivity. }
  destruct (Full g am Hu Hsca Hgn) as [Hav Hfr].
  assert (SC : forall q, In q ms -> exists a, usedX X s q a /\ am_sc a = sc).
  { intros q Hq. eapply ring_members_used; [exact Rg | exact Hq]. }
  assert (SX : forall q, In q (g :: ms) -> memb q X = false).
  { intros q [<-|Hq]; [exact NXg|]. destruct (SC q Hq) as (a & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
  eapply (queue_op (HActive sc) g s (MUsed am) ms (alinks X s sc)).
  - exact Mg.
  - cbn. rewrite Hp, Hn. reflexivity.
  - exact Rg.
  - exact Hgn.
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mg' Mother Mms.
    assert (RL : relinked s s' (g :: ms)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - eexists (MUsed am), _, _. split; [exact Mg|]. split; [exact Mg'|]. discriminate.
      - destruct (SC q Hq) as (a & Hqu & _). pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
        eexists (MUsed a), _, _. split; [exact Mq|]. split; [apply (Mms q _ Hq Mq) | discriminate]. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.
    pose proof Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg&_&EK).
    destruct Hse as (Hoth & Hfmh & Hlen).
    assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c).
    { intros c Hc Hne. unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }
    assert (Hhd_old : active_hd s sc = hd_error ms) by exact (proj2 Rg).
    assert (Hhd_new : active_hd s' sc = hd_error (ms ++ [g])).
    { cbn [head_of] in Hhd'. rewrite Hhd'. destruct ms; reflexivity. }
    assert (Rg' : ring_ok (alinks X s' sc) (active_hd s' sc) (ms ++ [g])).
    { rewrite Hhd_new. split; [|reflexivity].
      destruct ms as [|h0 rest] eqn:Ems.
      - cbn. split; [constructor; [intros [] | constructor]|]. split; [|exact I].
        unfold alinks. pose proof (usedX_intro X s' g _ NXg Mg') as U'. unfold usedX in U'. rewrite U'.
        cbn [am_sc am_prev am_next am_set_links]. rewrite Hsca, Z.eqb_refl. reflexivity.
      - eapply (cycle_snoc (alinks X s sc) (alinks X s' sc) (h0 :: rest) g (proj1 Rg)).
        + discriminate.
        + exact Hgn.
        + intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (a & Hzu & Hzs & El).
          pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
          pose proof (Mms z (MUsed a) Hz Mz) as Mz'. cbn [with_links] in Mz'.
          unfold alinks, MTX. rewrite NXz, Mz'. cbn [am_sc am_prev am_next am_set_links].
          rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity.
        + unfold alinks. pose proof (usedX_intro X s' g _ NXg Mg') as U'. unfold usedX in U'. rewrite U'.
          cbn [am_sc am_prev am_next am_set_links]. rewrite Hsca, Z.eqb_refl. reflexivity. }
    apply (HQ s' (last ms g) (hd g ms)).
    + eapply (Inv_surgery X X (Some (g, i)) (Some (g, i)) U U s s' HI).
      * intros k rg Hk _. unfold region_of in *. rewrite Erg. exact Hk.
      * exact Bwd.
      * intros p a Hpu. left. apply Fwd. exact Hpu.
      * intros q j HR. injection HR as <- <-. destruct (inv_reserved HI g i eq_refl) as (a & Hgu & Hj & Hf & Ha).
        destruct (Fwd _ _ Hgu) as (a' & Hgu' & E). exists a'.
        pose proof (strip_fields _ _ E) as (_&_&_&El&_). rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E), El. auto.
      * intros p j a' _. left. tauto.
      * apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
        intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
        unfold keys in Kg. rewrite Hm in Kg. exact Kg.
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * eapply rl_Xok; eauto. exact (inv_X HI).
      * split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - rewrite (Hfmh ltac:(discriminate)). eapply ring_ok_ext; [|exact FR]. intros q _.
            apply (rl_flinks_used X s s' _ RL sc). intros p [<-|Hpin]; [exists am; split; [exact Hu | exact Hsca] | apply SC; exact Hpin].
          - intros q pr nx Hq. apply (Fall q pr nx). unfold MTX in *. destruct (memb q X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hq|].
            exfalso. assert (exists a, MT s q = Some (MUsed a)) as (a & Ma).
            { destruct D1 as [<-|D1]; [exists am; exact Mg|]. destruct (SC q D1) as (a & Hqu & _). exists a. exact (proj1 (usedX_MT _ _ _ _ Hqu)). }
            rewrite Ma in A1. injection A1 as <-. rewrite B1 in Hq. cbn in Hq. discriminate. }
        split.
        { intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
          - exists (ms ++ [g]). split; [exact Rg'|].
            split.
            { intros q a' Hq Hs'. destruct (Bwd _ _ Hq) as (a & Hqu & E). rewrite in_app_iff. cbn.
              destruct (sptr_eq_dec q g) as [->|Hqg].
              - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg' in M. injection M as <-. cbn. split; [intros _; discriminate | intros _; right; left; reflexivity].
              - destruct (in_dec sptr_eq_dec q ms) as [Hi|Hni].
                + split; [intros _; discriminate || idtac | intros _; left; exact Hi].
                  destruct (ring_links _ _ _ _ Rg' ltac:(apply in_app_iff; left; exact Hi)) as (pr & nx & L).
                  unfold alinks in L. pose proof Hq as Hq2. unfold usedX in Hq2. rewrite Hq2, Hs', Z.eqb_refl in L.
                  intros HL. rewrite HL in L. discriminate.
                + rewrite (rl_used_same X s s' _ RL q a') in Hq by (intros [E0|E0]; [exact (Hqg (eq_sym E0)) | exact (Hni E0)]).
                  rewrite <- (Mem q a' Hq Hs'). split; [intros [H|[H|[]]]; [exact H | exfalso; exact (Hqg (eq_sym H))] | intros H; left; exact H]. }
            split.
            { intros q a' Hq Hs' Hnin. rewrite in_app_iff in Hnin. cbn in Hnin.
              assert (Hqg : q <> g) by (intros ->; apply Hnin; right; left; reflexivity).
              assert (Hni : ~ In q ms) by (intros Hi; apply Hnin; left; exact Hi).
              rewrite (rl_used_same X s s' _ RL q a') in Hq by (intros [E0|E0]; [exact (Hqg (eq_sym E0)) | exact (Hni E0)]).
              exact (Full q a' Hq Hs' Hni). }
            split.
            { intros q a' Hq Hs' Hav'. destruct (Bwd _ _ Hq) as (a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). rewrite Eav in Hav'.
              destruct (sptr_eq_dec q g) as [->|Hqg]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; exfalso; exact (Hav' Hav)|].
              pose proof (Q1 q a Hqu ltac:(congruence) Hav') as Hh. rewrite Hhd_new. rewrite Hhd_old in Hh.
              destruct ms; cbn in Hh |- *; [discriminate | exact Hh]. }
            { intros q a' Hq Hs' Hiq Hnh' HnR. destruct (Bwd _ _ Hq) as (a & Hqu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              destruct (sptr_eq_dec q g) as [->|Hqg]; [exfalso; exact (HnR i eq_refl)|].
              apply (Q2 q a Hqu ltac:(congruence)).
              - rewrite in_app_iff in Hiq. destruct Hiq as [H|[H|[]]]; [exact H | exfalso; exact (Hqg (eq_sym H))].
              - rewrite Hhd_old. rewrite Hhd_new in Hnh'. destruct ms; cbn in Hnh' |- *; [discriminate | exact Hnh'].
              - exact HnR. }
          - destruct (A c Hc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            rewrite (EH c ltac:(lia) Hne). split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q _. apply (rl_alinks_other X s s' _ RL sc c q); [|lia].
              intros p [<-|Hpin]; [exists am; split; [exact Hu | exact Hsca] | apply SC; exact Hpin]. }
            assert (Hsame : forall q a', usedX X s' q a' -> am_sc a' = c -> usedX X s q a').
            { intros q a' Hq Hs'. apply (rl_used_same X s s' _ RL q a'); [|exact Hq].
              intros Hi. destruct (Bwd _ _ Hq) as (a & Hqu & E). pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
              assert (am_sc a = sc); [|congruence].
              destruct Hi as [<-|Hi]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; exact Hsca|].
              destruct (SC q Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hqu) as ->. exact Hs2. }
            split; [|split; [|split]]; intros q a' Hq Hs'; pose proof (Hsame q a' Hq Hs') as Hq0.
            + apply Mem2; [exact Hq0 | exact Hs'].
            + apply Full2; [exact Hq0 | exact Hs'].
            + apply Q12; [exact Hq0 | exact Hs'].
            + apply Q22; [exact Hq0 | exact Hs']. }
        { intros q a' Hq H63.
          assert (Hq0 : usedX X s q a').
          { apply (rl_used_same X s s' _ RL q a'); [|exact Hq]. intros Hi. destruct (Bwd _ _ Hq) as (a & Hqu & E).
            pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
            destruct Hi as [<-|Hi]; [pose proof (usedX_fun _ _ _ _ _ Hqu Hu) as ->; lia|].
            destruct (SC q Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hqu) as ->. lia. }
          exact (D q a' Hq0 H63). }
      * eapply rl_usage; eauto. exact (inv_usage HI).
    + exact Sb.
    + exact Mg'.
    + exact EH.
    + exact Bwd.
    + eapply ub_same_relinked; [exact RL | exact EK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frameless_of_mask X U s g i am :
  Inv X (Some (g, i)) U s -> usedX X s g am ->
  Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am) ->
  forall j, ss_fr (nth_slot am j) = None.
Proof.
  intros HI Hu Hmask.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & _) & _ & Gsl & _).
  assert (Hbit : Z.testbit (Z.lor (am_freed am) (am_avail am)) i = false).
  { unfold allocated in Hal. rewrite Z.lor_comm. destruct (Z.testbit _ i); [discriminate | reflexivity]. }
  pose proof (add_bit_lor _ i ltac:(lia) Hbit) as E. rewrite E in Hmask.
  assert (Hall : forall j, 0 <= j <= am_last am -> j <> i -> Z.testbit (Z.lor (am_freed am) (am_avail am)) j = true).
  { intros j Hj Hne. pose proof (f_equal (fun m => Z.testbit m j) Hmask) as T. cbn beta in T.
    rewrite Z.lor_spec, testbit_bit, testbit_ones in T by lia.
    replace (i =? j) with false in T by (symmetry; apply Z.eqb_neq; lia).
    replace (0 <=? j) with true in T by (symmetry; apply Z.leb_le; lia).
    replace (j <=? am_last am) with true in T by (symmetry; apply Z.leb_le; lia).
    destruct (Z.testbit (Z.lor (am_freed am) (am_avail am)) j); [reflexivity | cbn in T; discriminate]. }
  assert (Hslots : forall j, 0 <= j <= am_last am -> ss_fr (nth_slot am j) = None).
  { intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact Hfr|].
    pose proof (Gsl j Hj) as (_ & _ & S3). destruct (ss_fr (nth_slot am j)) as [fr|]; [|reflexivity].
    destruct S3 as (A1 & _). exfalso. unfold allocated in A1. rewrite Z.lor_comm, (Hall j Hj Hne) in A1. discriminate. }
  intros j. destruct (Z_lt_dec j 0) as [Hj|Hj].
  { unfold nth_slot. replace (Z.to_nat j) with (Z.to_nat 0) by lia. apply (Hslots 0). lia. }
  destruct (Z_lt_dec (am_last am) j) as [Hj2|Hj2].
  { unfold nth_slot. rewrite nth_overflow; [reflexivity|]. rewrite Glen. lia. }
  apply Hslots. lia.
Qed.

(* [comment removed for export] *)
Lemma same_mem_contra X R U s p a q b :
  Inv X R U s -> usedX X s p a -> usedX X s q b -> p <> q -> am_mem a = am_mem b -> False.
Proof.
  intros HI Ha Hb Hne Em.
  pose proof (extent_pos _ _ _ _ _ (inv_groups HI p a Ha)) as Pa. pose proof (extent_pos _ _ _ _ _ (inv_groups HI q b Hb)) as Pb.
  pose proof (stride_pos _ _ _ _ _ (inv_groups HI p a Ha)) as Sa. pose proof (stride_pos _ _ _ _ _ (inv_groups HI q b Hb)) as Sb.
  assert (K : forall a b, am_mem a = am_mem b -> 0 < group_extent a -> 16 <= stride_of b -> inside X s a b -> False).
  { intros a0 b0 E0 P0 S0 (j & fr & c & ac & Hj & _ & _ & _ & _ & Memc & Lo & _ & _).
    rewrite Memc, poff_slot_start, E0 in Lo. unfold UNIT in Lo. nia. }
  destruct (inv_laminar HI p a q b Ha Hb Hne ltac:(rewrite Em; reflexivity)) as [D | [I | I]].
  - unfold spans_disjoint in D. rewrite Em in D. lia.
  - exact (K a b Em Pa Sb I).
  - exact (K b a (eq_sym Em) Pb Sa I).
Qed.

Lemma release_slot_spec X U s g i am fr (Q : unit * astate -> Prop) :
  Inv X None U s -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
  (forall s' x, s' = upd_meta g (MUsed (upd_slot am i x)) s -> ss_fr x = None ->
     Inv X (Some (g, i)) U s' -> Q (tt, s')) ->
  itok (release_slot g i s) Q.
Proof.
  intros HI Hu Hi Hfr Hk HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  unfold release_slot. mbinds. eapply itok_getm; [exact Mg|]. msimp. rewrite Hfr.
  apply itok_setm'.
  set (x := if fr_off fr =? 0 then mkSlot (Some (255, 0)) None else mkSlot (ss_hdr (nth_slot am i)) None).
  assert (Hx : ss_fr x = None /\ (ss_hdr x = ss_hdr (nth_slot am i) \/ ss_hdr x = Some (255, 0))).
  { subst x. destruct (fr_off fr =? 0); cbn; auto. }
  destruct Hx as [Hx1 Hx2].
  apply (HQ _ x eq_refl Hx1). eapply drop_frame_Inv; eauto. intros HG. rewrite Hk in HG. discriminate.
Qed.

Lemma forget_frame_spec X U s g i am fr (Q : unit * astate -> Prop) :
  Inv X None U s -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr ->
  (forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am i) ->
  (forall s', s' = upd_meta g (MUsed (upd_slot am i (mkSlot (ss_hdr (nth_slot am i)) None))) s ->
     Inv X (Some (g, i)) U s' -> Q (tt, s')) ->
  itok (forget_frame g i s) Q.
Proof.
  intros HI Hu Hi Hfr Hno HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  unfold forget_frame. mbinds. eapply itok_getm; [exact Mg|]. msimp. apply itok_setm'.
  apply (HQ _ eq_refl). eapply drop_frame_Inv; eauto; cbn; auto.
Qed.

Lemma activate_group_spec X U s sc h ah (Q : Z * astate -> Prop) :
  Inv X None U s -> 0 <= sc < 48 -> usedX X s h ah -> am_sc ah = sc -> active_hd s sc = Some h -> am_avail ah = 0 ->
  (forall mask s', Inv X None U s' ->
     s' = upd_meta h (MUsed (am_set_avail (Z.land (am_freed ah) (ones (am_aidx ah)))
                              (am_set_freed (Z.ldiff (am_freed ah) (ones (am_aidx ah))) ah))) s ->
     Q (mask, s')) ->
  itok (activate_group h s) Q.
Proof.
  intros HI Hsc Hu Hs Hhd Hav HQ. pose proof (usedX_MT _ _ _ _ Hu) as [Mh _].
  unfold activate_group. mbinds. eapply itok_getm; [exact Mh|]. msimp.
  mbinds. apply itok_massert; [apply Z.eqb_eq; exact Hav|]. msimp. mbinds. apply itok_setm'. msimp. apply itok_ret.
  apply HQ; [|reflexivity]. rewrite <- Hs in Hsc, Hhd. exact (activate_Inv X U s h ah HI Hu Hsc Hhd Hav).
Qed.

(* [comment removed for export] *)
Lemma set_freed_Inv X U s g i am :
  Inv X (Some (g, i)) U s -> usedX X s g am -> 0 <= am_sc am < 48 ->
  (am_prev am, am_next am) <> (None, None) ->
  class_size (am_sc am) <= stride_of am ->
  Inv X None U (upd_meta g (MUsed (am_set_freed (Z.lor (am_freed am) (bit i)) am)) s).
Proof.
  intros HI Hu Hsc Hlinked Hstr.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & _).
  assert (Hbit : Z.testbit (am_freed am) i = false /\ Z.testbit (am_avail am) i = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) i), (Z.testbit (am_freed am) i); cbn in Hal; try discriminate. auto. }
  destruct Hbit as [Hfb Hab].
  assert (Tnew : forall j, Z.testbit (Z.lor (am_freed am) (bit i)) j = Z.testbit (am_freed am) j || (i =? j)).
  { intros j. destruct (Z_lt_dec j 0) as [Hj|Hj]; [rewrite !testbit_neg_idx by lia; cbn; symmetry; apply Z.eqb_neq; lia|].
    rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
  change (am_set_freed (Z.lor (am_freed am) (bit i)) am) with
    (am_set_aidx (am_aidx am) (am_set_freed (Z.lor (am_freed am) (bit i)) (am_set_avail (am_avail am) am))).
  eapply (Inv_masks X (Some (g, i)) None U s g am); try exact HI; try exact Hu; try exact Hsc.
  - unfold masks_ok. cbn -[Z.le Z.lt Z.add Z.testbit Z.lor Z.to_nat Z.leb andb].
    split; [exact Glast|]. split; [exact Gaidx|]. split; [exact Glen|]. split; [exact Gav|].
    split; [apply Z.lor_nonneg; split; [exact Gfrn | unfold bit; apply Z.pow_nonneg; lia]|].
    split; [intros j Hj Ha; rewrite Tnew, (Gdisj j Hj Ha); cbn; apply Z.eqb_neq; intros ->; rewrite Ha in Hab; discriminate|].
    split; [intros j Hj; destruct (Gabove j Hj) as [A B]; rewrite Tnew, A, B; cbn; split; [reflexivity | apply Z.eqb_neq; lia]|].
    split; [exact Gavp|].
    intros j Hj. rewrite Tnew, (Gfra j Hj). reflexivity.
  - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
    + right; right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hal|].
      unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail]. rewrite Z.lor_spec, Tnew, Z.eqb_refl, orb_true_r, orb_true_r. reflexivity.
    + left. unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail]. rewrite !Z.lor_spec, testbit_bit by lia.
      replace (i =? j) with false by (symmetry; apply Z.eqb_neq; lia). rewrite orb_false_r. reflexivity.
  - intros p j Hp1 Hp2. split; intros E; [|discriminate]. exfalso. injection E as -> ->. apply Hp2. reflexivity.
  - intros j E. discriminate.
  - intros j E. injection E as <-. right. unfold allocated. cbn [am_avail am_freed am_set_aidx am_set_freed am_set_avail].
    rewrite Z.lor_spec, Tnew, Z.eqb_refl, !orb_true_r. reflexivity.
  - intros HL. exfalso. exact (Hlinked HL).
  - intros Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu ltac:(lia) ltac:(lia)))). exact Hav.
  - intros _ _ _ E. pose proof (f_equal (fun m => Z.testbit m i) E) as T. cbn beta in T. rewrite Tnew, Z.eqb_refl, orb_true_r, Z.bits_0 in T. discriminate.
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
  - intros Hlt. exfalso. lia.
  - intros Hai. exact Hai.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mask_zero_of_bits m : 0 <= m -> (forall j, 0 <= j -> Z.testbit m j = false) -> m = 0.
Proof. intros Hm Hb. apply bits_inj_nonneg. intros j Hj. rewrite Hb, Z.bits_0 by exact Hj. reflexivity. Qed.

Lemma unlinked_of_next_None X R U s g am :
  Inv X R U s -> usedX X s g am -> 0 <= am_sc am < 48 -> am_next am = None -> am_prev am = None.
Proof.
  intros HI Hu Hsc Hn. destruct (inv_rings HI) as (_ & A & _). destruct (A (am_sc am) Hsc) as (ms & Rg & Mem & _).
  destruct (am_prev am) as [p|] eqn:Ep; [|reflexivity]. exfalso.
  assert (Hin : In g ms) by (apply (Mem g am Hu eq_refl); rewrite Ep, Hn; discriminate).
  destruct (ring_links _ _ _ _ Rg Hin) as (pr & nx & L). unfold alinks in L. unfold usedX in Hu. rewrite Hu, Z.eqb_refl in L.
  rewrite Hn in L. injection L as _ E. discriminate.
Qed.

Definition fneed (sc : Z) : nat := if sc <? 48 then Z.to_nat (48 - sc) else 1%nat.

Lemma fneed_le sc : 0 <= sc -> (fneed sc <= NEST_FUEL)%nat.
Proof. intros H. unfold fneed, NEST_FUEL. destruct (sc <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. Qed.

(* [comment removed for export] *)
Definition ceq (a a0 : ameta) : Prop :=
  am_mem a = am_mem a0 /\ am_maplen a = am_maplen a0 /\ am_last a = am_last a0 /\ am_sc a = am_sc a0 /\ am_aidx a = am_aidx a0.
Lemma ceq_refl a : ceq a a. Proof. unfold ceq; auto. Qed.
Lemma ceq_trans a b c : ceq a b -> ceq b c -> ceq a c.
Proof. unfold ceq; intros (?&?&?&?&?) (?&?&?&?&?); repeat split; congruence. Qed.
Lemma ceq_strip a b : strip a = strip b -> ceq a b.
Proof. intros E. pose proof (strip_fields _ _ E) as (Em&_&_&El&Es&Eml&Ea&_). unfold ceq; auto. Qed.

Definition corr (X : list sptr) (s s' : astate) : Prop :=
  forall q a, usedX X s' q a -> exists a0, usedX X s q a0 /\ ceq a a0.

Lemma corr_refl X s : corr X s s.
Proof. intros q a Hq. exists a. split; [exact Hq | apply ceq_refl]. Qed.

Lemma corr_trans X s1 s2 s3 : corr X s1 s2 -> corr X s2 s3 -> corr X s1 s3.
Proof.
  intros A B q a Hq. destruct (B q a Hq) as (a1 & H1 & C1). destruct (A q a1 H1) as (a0 & H0 & C0).
  exists a0. split; [exact H0 | exact (ceq_trans _ _ _ C1 C0)].
Qed.

Definition nf_post (X : list sptr) (U : Z -> Z) (s : astate) (r : option (nat * Z) * astate) : Prop :=
  Inv X None U (snd r) /\ corr X s (snd r) /\ ub_same s (snd r) /\
  match fst r with
  | None => True
  | Some (k, len) => exists rg, region_of (snd r) k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
      rg_len rg = page_round len /\ 0 <= len /\ (forall q a, usedX X (snd r) q a -> 0 < am_maplen a -> prid (am_mem a) <> k)
  end.

(* [comment removed for export] *)
Lemma else_branch_facts X U s g i am :
  Inv X (Some (g, i)) U s -> usedX X s g am ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  0 <= am_sc am < 48 /\ class_size (am_sc am) <= stride_of am.
Proof.
  intros HI Hu Hcond.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & _).
  assert (Hm0 : am_last am = 0 -> Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)).
  { intros Hl0. assert (i = 0) as -> by lia. rewrite Hl0.
    assert (E : Z.lor (am_freed am) (am_avail am) = 0).
    { apply mask_zero_of_bits; [apply Z.lor_nonneg; lia|]. intros j Hj. rewrite Z.lor_spec.
      destruct (Z.eq_dec j 0) as [->|Hne].
      - unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) 0), (Z.testbit (am_freed am) 0); cbn in Hal |- *; congruence.
      - destruct (Gabove j ltac:(lia)) as [A B]. rewrite A, B. reflexivity. }
    rewrite E. reflexivity. }
  destruct Gcl as [(C63 & Cl & _) | (Csc & CN1 & _ & _)].
  - exfalso. rewrite (Hm0 Cl), Z.eqb_refl in Hcond. unfold okay_to_free in Hcond. rewrite C63 in Hcond. cbn in Hcond. discriminate.
  - split; [exact Csc|]. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia]. exfalso.
    destruct (CN1 Hlt) as [Hl0 _]. rewrite (Hm0 Hl0), Z.eqb_refl in Hcond. unfold okay_to_free in Hcond.
    replace (stride_of am <? class_size (am_sc am)) with true in Hcond by (symmetry; apply Z.ltb_lt; exact Hlt).
    rewrite orb_true_r in Hcond. discriminate.
Qed.

Theorem nontrivial_free_spec fuel : forall X U s g i am (Q : option (nat * Z) * astate -> Prop),
  Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c) ->
  ((am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) <> Some g -> am_freed am <> 0) ->
  (fneed (am_sc am) <= fuel)%nat ->
  (forall r, nf_post X U s r -> Q r) ->
  itok (nontrivial_free fuel g i s) Q.
Proof.
  induction fuel as [|f IH]; intros X U s g i am Q HI Hu HU HR2g Hf HQ.
  { exfalso. unfold fneed in Hf. destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. }
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & Hfr & Hal). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
  pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  cbn fix beta iota delta [nontrivial_free].
  mbinds. eapply itok_getm; [exact Mg|]. msimp. mbinds. apply itok_get. msimp. cbn zeta.
  set (sc := am_sc am) in *. set (mask := Z.lor (am_freed am) (am_avail am)).
  destruct ((mask + bit i =? ones (am_last am)) && okay_to_free s g am) eqn:Hcond.
  - (* [comment removed for export] *)
    apply andb_prop in Hcond as [Hmask Hok]. apply Z.eqb_eq in Hmask.
    pose proof (frameless_of_mask X U s g i am HI Hu Hmask) as Hnofr.
    set (U1 := fun c => U c + contrib X s c g).
    (* [comment removed for export] *)
    mbinds.
    match goal with |- itok (?mm s) _ =>
      assert (STEP1 : itok (mm s) (fun r => let s1 := snd r in
        Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
        st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
        (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
        (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1)) end.
    { destruct (am_next am) as [nx|] eqn:Enx.
      - assert (Hsc : 0 <= sc < 48).
        { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [_ E]. rewrite Enx in E. discriminate. }
        mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
        mbinds. eapply (dequeue_exempt_spec X (Some (g, i)) U s sc g am); [exact HI | exact Hsc | exact Hu | reflexivity | rewrite Enx; intros E; discriminate | exact Hnofr | intros p j E; injection E; auto |].
        intros s1 HI1 Sb1 Mg1 EH1 Mo1 Bwd1 Hk1 Hnew1 UB1. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
        pose proof Sb1 as (_&_&_&_&_&_&_&_&_&Eus1&_&_&_&_&Erg1&_&EK1).
        assert (C1 : forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0).
        { intros q a Hq. destruct (Bwd1 q a Hq) as (_ & a0 & H0 & E). exists a0. split; [exact H0 | exact (ceq_strip _ _ E)]. }
        assert (Cr1 : corr X s s1).
        { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
          - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite Mg1 in M. injection M as <-. exists am.
            split; [exact Hu|]. destruct am; unfold ceq; cbn; auto.
          - apply C1. apply usedX_cons; assumption. }
        assert (POST1 : forall s1', Inv (g :: X) None U1 s1' ->
                  (exists h x, s1' = upd_meta h x s1 /\ h <> g /\
                     (exists ah ah', x = MUsed ah' /\ usedX (g :: X) s1 h ah /\ am_sc ah = sc /\ ceq ah' ah /\
                        blocks_of h ah' = blocks_of h ah)) \/ s1' = s1 ->
                  let s1 := s1' in
                  Inv (g :: X) None U1 s1 /\ MT s1 g = Some (MUsed (am_set_links None None am)) /\
                  st_usage s1 = st_usage s /\ st_regions s1 = st_regions s /\ corr X s s1 /\
                  (forall q a, usedX (g :: X) s1 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
                  (forall q, (forall a, usedX X s q a -> am_sc a <> sc) -> q <> g -> MT s1 q = MT s q) /\ ub_same s s1).
        { intros s1' HI1' Hcase. cbn zeta. destruct Hcase as [(h & x & -> & Hhg & ah & ah' & -> & Uh & Sh & Ceh & Ebl) | ->].
          - split; [exact HI1'|]. split; [rewrite MT_upd_other by (intros E; exact (Hhg (eq_sym E))); exact Mg1|].
            split; [exact Eus1|]. split; [exact Erg1|].
            assert (C2 : forall q a, usedX (g :: X) (upd_meta h (MUsed ah') s1) q a ->
                         exists a0, usedX X s q a0 /\ ceq a a0).
            { intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
              - injection E as <-. destruct (C1 h ah Uh) as (a0 & H0 & C0). exists a0. split; [exact H0 | exact (ceq_trans _ _ _ Ceh C0)].
              - apply C1. exact Hq. }
            split.
            { intros q a Hq. destruct (sptr_eq_dec q g) as [->|Hne].
              - pose proof (usedX_MT _ _ _ _ Hq) as [M _]. rewrite MT_upd_other in M by (intros E; exact (Hhg (eq_sym E))).
                rewrite Mg1 in M. injection M as <-. exists am. split; [exact Hu|]. destruct am; unfold ceq; cbn; auto.
              - apply C2. apply usedX_cons; assumption. }
            split; [exact C2|]. split.
            { intros q Hq Hqg. destruct (sptr_eq_dec q h) as [->|Hqh].
              + exfalso. destruct (Bwd1 h ah Uh) as (_ & a0 & H0 & E0). pose proof (strip_fields _ _ E0) as (_&_&_&_&Es&_).
                apply (Hq a0 H0). congruence.
              + rewrite MT_upd_other by exact Hqh. apply Mo1; assumption. }
            eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ Uh))|].
            rewrite (proj1 (usedX_MT _ _ _ _ Uh)). cbn. exact Ebl.
          - split; [exact HI1'|]. split; [exact Mg1|]. split; [exact Eus1|]. split; [exact Erg1|]. split; [exact Cr1|]. split; [exact C1|]. split; [exact Mo1 | exact UB1]. }
        destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
        + apply osptr_eqb_eq in Ehd. destruct (Hnew1 Ehd) as [Hnone | (h & ah & Hh & Hhg & Uh & Sh & Avh)].
          * rewrite Hnone. apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
          * rewrite Hh. mbinds. eapply activate_group_spec; [exact HI1 | exact Hsc | exact Uh | exact Sh | exact Hh | exact Avh |].
            intros mk s2 HI2 Es2. msimp. apply itok_ret. cbn [snd]. apply (POST1 s2 HI2). left.
            eexists h, _. split; [exact Es2|]. split; [exact Hhg|]. eexists ah, _. split; [reflexivity|]. split; [exact Uh|]. split; [exact Sh|].
            split; [destruct ah; unfold ceq; cbn; auto|]. apply blocks_of_ext; destruct ah; reflexivity.
        + apply itok_ret. cbn [snd]. apply (POST1 s1 HI1). right. reflexivity.
      - apply itok_ret. cbn [snd].
        assert (Hp : am_prev am = None).
        { destruct Hscr as [H63|Hsc]; [destruct (inv_rings HI) as (_ & _ & D); exact (proj1 (D g am Hu H63))|].
          eapply unlinked_of_next_None; eauto. }
        split; [apply (Inv_exempt X (Some (g, i)) U s g am HI Hu Hnofr Hp Enx); intros p j E; injection E; auto|].
        split; [rewrite Mg; destruct am; cbn in Hp, Enx |- *; subst; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [apply corr_refl|]. split.
        + intros q a Hq. apply usedX_cons_inv in Hq as [_ Hq]. exists a. split; [exact Hq | apply ceq_refl].
        + split; [intros; reflexivity | apply ub_same_refl]. }
    revert STEP1. apply itok_mono. intros [u1 s1] (HI1 & Mg1 & Eus1 & Erg1 & Cr1 & C1 & Mo1 & UBs1). cbn [fst snd] in *. msimp.
    mbinds. eapply itok_getm; [exact Mg1|]. msimp.
    replace (am_last (am_set_links None None am)) with (am_last am) by (destruct am; reflexivity).
    replace (am_maplen (am_set_links None None am)) with (am_maplen am) by (destruct am; reflexivity).
    replace (am_mem (am_set_links None None am)) with (am_mem am) by (destruct am; reflexivity).
    assert (HU1 : forall c, 0 <= c < 48 -> U1 c = U c + (if sc =? c then am_last am + 1 else 0)).
    { intros c Hc. unfold U1. rewrite (contrib_used X s c g am Hu). reflexivity. }
    (* [comment removed for export] *)
    mbinds.
    match goal with |- itok (?mm s1) _ =>
      assert (STEP2 : itok (mm s1) (fun r => let s2 := snd r in
        Inv (g :: X) None U s2 /\ st_metas s2 = st_metas s1 /\ st_regions s2 = st_regions s /\ st_active s2 = st_active s1)) end.
    { destruct (sc <? 48) eqn:E48.
      - apply Z.ltb_lt in E48. apply itok_set_usage_of. cbn zeta.
        assert (Hv : am_last am + 1 <= usage_of s sc).
        { rewrite (inv_usage HI sc ltac:(lia)). pose proof (class_sum_ge_contrib X _ U s sc g HI Kg) as Hge.
          rewrite (contrib_used X s sc g am Hu) in Hge. fold sc in Hge. rewrite Z.eqb_refl in Hge. pose proof (HU sc). lia. }
        pose proof (Inv_set_usage (g :: X) None U1 s1 sc (usage_of s sc - (am_last am + 1)) HI1 ltac:(lia) ltac:(lia)) as HI2.
        split; [|split; [reflexivity|split; [exact Erg1|reflexivity]]].
        eapply Inv_U_ext; [|exact HI2]. intros c Hc. unfold Uadd. rewrite (HU1 c Hc).
        replace (usage_of s1 sc) with (usage_of s sc) by (unfold usage_of; rewrite Eus1; reflexivity).
        destruct (c =? sc) eqn:E1; destruct (sc =? c) eqn:E2; try lia;
          try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
      - apply Z.ltb_ge in E48. apply itok_ret. cbn zeta. split; [|split; [reflexivity|split; [exact Erg1|reflexivity]]].
        eapply Inv_U_ext; [|exact HI1]. intros c Hc. rewrite (HU1 c Hc).
        destruct (sc =? c) eqn:E2; [apply Z.eqb_eq in E2; lia | lia]. }
    revert STEP2. apply itok_mono. intros [u2 s2] (HI2 & Em2 & Erg2 & Ea2). cbn [fst snd] in *. msimp.
    assert (MT2 : forall q, MT s2 q = MT s1 q) by (intros; unfold MT; rewrite Em2; reflexivity).
    assert (EU2 : forall Y q a, usedX Y s2 q a <-> usedX Y s1 q a) by (intros; unfold usedX, MTX; rewrite MT2; tauto).
    assert (C2 : forall q a, usedX (g :: X) s2 q a -> exists a0, usedX X s q a0 /\ ceq a a0).
    { intros q a Hq. apply EU2 in Hq. apply C1. exact Hq. }
    (* [comment removed for export] *)
    mbinds.
    match goal with |- itok (?mm s2) _ =>
      assert (STEP3 : itok (mm s2) (fun r => let s4 := snd r in
        Inv (g :: X) None U s4 /\ ub_same s s4 /\
        (forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ ceq a a0) /\
        match fst r with
        | None => True
        | Some (k, len) => exists rg, region_of s4 k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
            rg_len rg = page_round len /\ 0 <= len /\ (forall q a, usedX (g :: X) s4 q a -> 0 < am_maplen a -> prid (am_mem a) <> k)
        end)) end.
    { destruct (negb (am_maplen am =? 0)) eqn:Eml.
      - (* [comment removed for export] *)
        assert (Hml : 0 < am_maplen am) by (destruct (am_maplen am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; lia]).
        mbinds. eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & _ & Er3 & _). msimp.
        mbinds. eapply record_seq_spec; [exact HI3|]. intros s4 HI4 (Em4 & _ & Er4 & _). msimp.
        apply itok_ret. cbn zeta. cbn [fst snd].
        assert (EU4 : forall q a, usedX (g :: X) s4 q a <-> usedX (g :: X) s2 q a) by (intros; unfold usedX, MTX, MT; rewrite Em4, Em3; tauto).
        split; [exact HI4|]. split.
        { eapply ub_same_trans; [exact UBs1|]. apply ub_same_metas. rewrite Em4, Em3, Em2. reflexivity. }
        split; [intros q a Hq; apply C2; apply EU4; exact Hq|].
        destruct (Gmp Hml) as (r & rg & Emem & Hr & Hk & Hl & Hlen & _). exists rg. rewrite Emem. cbn [prid].
        split; [unfold region_of in *; rewrite Er4, Er3, Erg2; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split.
        { rewrite Hlen. unfold PGSZ. rewrite page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult. }
        split; [lia|].
        intros q a Hq Hqm. apply EU4 in Hq. pose proof (usedX_cons_inv _ _ _ _ _ Hq) as [Hqg _].
        destruct (C2 q a Hq) as (a0 & H0 & (E0 & F0 & _)). rewrite E0. rewrite F0 in Hqm. intros Ep. apply Hqg.
        eapply (inv_maps HI q a0 g am H0 Hu Hqm Hml). rewrite Emem. cbn. exact Ep.
      - (* [comment removed for export] *)
        assert (Hml : am_maplen am = 0) by (destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; exact E | discriminate]).
        destruct (Gns Hml) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Emem & Hsc' & N63' & Fit).
        assert (Hsc : 0 <= sc < 48) by (destruct Hscr as [H|H]; [exfalso; exact (N63 H) | exact H]).
        pose proof (inv_groups HI g' am' U') as G'. pose proof G' as (_ & _ & Gsl' & Gcl' & _).
        pose proof (Gsl' i' Hi') as (_ & _ & S3'). rewrite F' in S3'. destruct S3' as (Hal' & _ & (_ & _ & _ & _ & FG') & _).
        destruct (FG' K') as [Hoff' _].
        assert (Hsc'48 : 0 <= am_sc am' < 48) by (destruct Gcl' as [(C & _) | (C & _)]; [exfalso; exact (N63' C) | exact C]).
        assert (Hg'g : g' <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ U' Hu) as E; rewrite E in Hsc'; lia).
        pose proof (usedX_MT _ _ _ _ U') as [Mg' NXg'].
        assert (U'2 : usedX (g :: X) s2 g' am').
        { apply EU2. apply usedX_intro.
          - rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity.
          - rewrite (Mo1 g'); [exact Mg' | | exact Hg'g]. intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha U') as ->. lia. }
        assert (Eptr : am_mem am = frame_ptr am' i' fr').
        { unfold frame_ptr. rewrite Hoff', Z.mul_0_r, padd_0. exact Emem. }
        mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
        rewrite Eptr, (find_frame_in_spec (g :: X) None U s2 HI2 g' am' i' fr' U'2 Hi' F'). msimp. apply itok_ret. cbn [fst snd].
        mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U'2))|]. msimp.
        mbinds. apply itok_mcheck; [unfold slot_is_group; rewrite F', K'; reflexivity|]. msimp.
        mbinds. eapply (forget_frame_spec (g :: X) U s2 g' i' am' fr'); [exact HI2 | exact U'2 | exact Hi' | exact F' | |].
        { intros c ac Hc Hmlc Emc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
          destruct (C2 c ac Hc) as (ac0 & H0 & (E0 & _)).
          eapply (same_mem_contra X _ U s c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Emem. }
        intros s3 Es3 HI3. msimp.
        set (am'' := upd_slot am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) in Es3.
        assert (U'3 : usedX (g :: X) s3 g' am'').
        { rewrite Es3. apply usedX_upd. left. split; [reflexivity|]. split; [|reflexivity].
          rewrite memb_cons, NXg'. replace (sptr_eqb g' g) with false by (symmetry; apply sptr_eqb_neq; exact Hg'g). reflexivity. }
        pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am'' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
        eapply (IH (g :: X) U s3 g' i' am''); [exact HI3 | exact U'3 | exact HU | | |].
        + (* [comment removed for export] *)
          intros Hl Hnh. replace (am_freed am'') with (am_freed am') by (subst am''; destruct am'; reflexivity).
          replace (am_prev am'', am_next am'') with (am_prev am', am_next am') in Hl by (subst am''; destruct am'; reflexivity).
          rewrite Fsc in Hnh. replace (active_hd s3 (am_sc am')) with (active_hd s2 (am_sc am')) in Hnh by (rewrite Es3; reflexivity).
          apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 U'2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate].
        + rewrite Fsc. unfold fneed in Hf |- *. fold sc in Hf.
          replace (sc <? 48) with true in Hf by (symmetry; apply Z.ltb_lt; lia).
          replace (am_sc am' <? 48) with true by (symmetry; apply Z.ltb_lt; lia). lia.
        + intros [mi s4] (HI4 & Cr4 & UB34 & Hmi). cbn [fst snd] in *. cbn zeta.
          assert (C4 : forall q a, usedX (g :: X) s4 q a -> exists a0, usedX X s q a0 /\ ceq a a0).
          { intros q a Hq. destruct (Cr4 q a Hq) as (a3 & H3 & C3).
            rewrite Es3 in H3. apply usedX_upd in H3. destruct H3 as [(-> & _ & E) | (Hne & H2')].
            - injection E as <-. destruct (C2 g' am' U'2) as (a0 & H0 & C0). exists a0. split; [exact H0|].
              refine (ceq_trans _ _ _ C3 (ceq_trans _ _ _ _ C0)). subst am''. destruct am'; unfold ceq; cbn; auto.
            - destruct (C2 q a3 H2') as (a0 & H0 & C0). exists a0. split; [exact H0 | exact (ceq_trans _ _ _ C3 C0)]. }
          split; [exact HI4|]. split; [|split; [exact C4 | exact Hmi]].
          eapply ub_same_trans; [exact UBs1|]. eapply ub_same_trans; [apply ub_same_metas; exact Em2|]. eapply ub_same_trans; [|exact UB34].
          rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U'2))|].
          rewrite (proj1 (usedX_MT _ _ _ _ U'2)). cbn. pose proof (inv_groups HI2 g' am' U'2) as ((_ & _ & Glen' & _) & _).
          apply blocks_of_upd_slot_same; [exact Hi' | exact Glen' |]. unfold slotst_block, slot_block. cbn. rewrite F', K'. reflexivity. }
    revert STEP3. apply itok_mono. intros [mi s4] (HI4 & UB4 & C4 & Hmi). cbn [fst snd] in *. msimp.
    (* [comment removed for export] *)
    mbinds. eapply free_meta_spec; [exact HI4 | left; reflexivity |]. intros s5 HI5 Sb5 Ea5 EU5 UB5. msimp.
    rewrite (remove_head_notin g X NXg) in HI5, EU5.
    apply itok_ret. apply HQ. unfold nf_post. cbn [fst snd].
    split; [exact HI5|]. split.
    { intros q a Hq. apply EU5 in Hq. apply C4. exact Hq. }
    split; [eapply ub_same_trans; [exact UB4 | exact UB5]|].
    destruct mi as [[k len]|]; [|exact I].
    destruct Hmi as (rg & Hr & Hk & Hl & Hlen & Hlen0 & Hno). exists rg.
    pose proof Sb5 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Erg5&_).
    split; [unfold region_of in *; rewrite Erg5; exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
    intros q a Hq. apply EU5 in Hq. exact (Hno q a Hq).
  - (* [comment removed for export] *)
    destruct (else_branch_facts X U s g i am HI Hu Hcond) as [Hsc Hstr]. fold sc in Hsc, Hstr.
    pose proof (ring_facts X (Some (g, i)) U s g am HI Hu ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3). fold sc in RF1, RF2, RF3.
    mbinds.
    match goal with |- itok (?mm s) _ =>
      assert (STEPE : itok (mm s) (fun r => let s1 := snd r in
        Inv X (Some (g, i)) U s1 /\
        exists am2, MT s1 g = Some (MUsed am2) /\ (am_prev am2, am_next am2) <> (None, None) /\ strip am2 = strip am /\
          (forall q a', usedX X s1 q a' -> exists a, usedX X s q a /\ strip a' = strip a) /\ ub_same s s1)) end.
    { destruct (mask =? 0) eqn:Em0.
      - apply Z.eqb_eq in Em0.
        assert (Hfr0 : am_freed am = 0).
        { subst mask. apply Z.lor_eq_0_iff in Em0. exact (proj1 Em0). }
        mbinds. apply itok_massert; [apply Z.ltb_lt; lia|]. msimp. mbinds. apply itok_get_head. msimp.
        change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
        destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
        + apply osptr_eqb_eq in Ehd. apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
          split; [exact Mg|]. split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | apply ub_same_refl]]].
          (* [comment removed for export] *)
          destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & _).
          apply (Mem g am Hu eq_refl). rewrite Ehd in Rg. exact (proj1 (ring_head_In _ _ _ Rg)).
        + assert (Hnh : active_hd s sc <> Some g) by (intros E; rewrite E in Ehd; cbn in Ehd; rewrite sptr_eqb_refl in Ehd; discriminate).
          assert (Hunl : am_prev am = None /\ am_next am = None).
          { destruct (am_prev am) eqn:Ep; destruct (am_next am) eqn:En; try (exfalso; apply (HR2g ltac:(discriminate) Hnh); exact Hfr0). auto. }
          destruct Hunl as [Hp Hn].
          eapply (requeue_spec X U s sc g i am); [exact HI | exact Hsc | exact Hu | reflexivity | exact Hp | exact Hn | exact Hnh |].
          intros s1 pr nx HI1 Sb1 Mg1 EH1 Bwd1 UB1. cbn zeta. cbn [snd]. split; [exact HI1|]. exists (am_set_links (Some pr) (Some nx) am).
          split; [exact Mg1|]. split; [destruct am; cbn; discriminate|]. split; [destruct am; reflexivity | split; [exact Bwd1 | exact UB1]].
      - apply itok_ret. cbn zeta. cbn [snd]. split; [exact HI|]. exists am.
        split; [exact Mg|]. split; [|split; [reflexivity | split; [intros q a' Hq; exists a'; auto | apply ub_same_refl]]].
        intros HL. destruct (RF1 HL) as [Hav0 Hfr0]. apply Z.eqb_neq in Em0. apply Em0. subst mask. rewrite Hav0, Hfr0. reflexivity. }
    revert STEPE. apply itok_mono. intros [u1 s1] (HI1 & am2 & Mg2 & Hl2 & Hst2 & Bwd1 & UB1). cbn [fst snd] in *. msimp.
    pose proof (strip_fields _ _ Hst2) as (Emem2 & _ & _ & _ & Esc2 & Eml2 & _).
    assert (U2 : usedX X s1 g am2) by (apply usedX_intro; [exact NXg | exact Mg2]).
    mbinds. eapply itok_getm; [exact Mg2|]. msimp. mbinds. apply itok_setm'. msimp. apply itok_ret.
    apply HQ. unfold nf_post. cbn [fst snd]. split; [|split; [|split; [|exact I]]].
    + apply (set_freed_Inv X U s1 g i am2 HI1 U2); [rewrite Esc2; exact Hsc | exact Hl2 |].
      rewrite Esc2, (strip_stride _ _ Hst2). exact Hstr.
    + intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
      * injection E as <-. exists am. split; [exact Hu|]. pose proof (ceq_strip _ _ Hst2) as Cq. destruct am2; exact Cq.
      * destruct (Bwd1 q a Hq) as (a0 & H0 & E0). exists a0. split; [exact H0 | exact (ceq_strip _ _ E0)].
    + eapply ub_same_trans; [exact UB1|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg2|]. rewrite Mg2. cbn. apply blocks_of_freed.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem free_spec U s g am idx fr (Q : unit * astate -> Prop) :
  Inv [] None U s -> (forall c, 0 <= U c) -> usedX [] s g am -> 0 <= idx <= am_last am ->
  ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
  (forall s', Inv [] None U s' ->
     (forall q a, usedX [] s' q a -> exists a0, usedX [] s q a0 /\ ceq a a0) ->
     (exists l1 l2, ublist s = l1 ++ ((frame_ptr am idx fr, fr_n fr), (g, idx)) :: l2 /\ ublist s' = l1 ++ l2) ->
     Q (tt, s')) ->
  itok (free (Some (frame_ptr am idx fr)) s) Q.
Proof.
  intros HI HU Hu Hidx Hfr Hk HQ.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
  pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & _ & _).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  unfold free. mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
  rewrite (find_frame_in_spec [] None U s HI g am idx fr Hu Hidx Hfr). apply itok_ret. msimp.
  mbinds. eapply itok_getm; [exact Mg|]. msimp. cbn zeta.
  mbinds. eapply release_slot_spec; [exact HI | exact Hu | exact Hidx | exact Hfr | exact Hk |].
  intros s1 x Es1 Hx HI1. msimp.
  assert (DEL : forall s', ub_same s1 s' -> exists l1 l2, ublist s = l1 ++ ((frame_ptr am idx fr, fr_n fr), (g, idx)) :: l2 /\ ublist s' = l1 ++ l2).
  { intros s' UB'. pose proof (inv_groups HI g am Hu) as ((_ & _ & Glen0 & _) & _).
    destruct (ublist_upd_slot s g am idx x (proj1 (inv_keys HI)) (proj1 (usedX_MT _ _ _ _ Hu)) Hidx Glen0) as (l1 & l2 & E1 & E2).
    exists l1, l2. rewrite (ub_same_ublist _ _ UB'), Es1, E2, E1. unfold slot_block, slotst_block. rewrite Hfr, Hk, Hx. split; reflexivity. }
  set (am1 := upd_slot am idx x) in Es1.
  assert (U1 : usedX [] s1 g am1) by (rewrite Es1; apply usedX_upd; left; auto).
  pose proof (upd_slot_fields am idx x) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am1 in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
  assert (Flk : (am_prev am1, am_next am1) = (am_prev am, am_next am) /\ am_freed am1 = am_freed am /\ am_avail am1 = am_avail am).
  { subst am1. destruct am; repeat split; reflexivity. }
  destruct Flk as (Flk & Ffr & Fav).
  assert (Hbits : Z.testbit (am_freed am) idx = false /\ Z.testbit (am_avail am) idx = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) idx), (Z.testbit (am_freed am) idx); cbn in Hal; try discriminate; auto. }
  destruct Hbits as [Hfb Hab].
  mbinds. apply itok_massert.
  { apply Z.eqb_eq. apply bits_inj_nonneg. intros j Hj. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.bits_0 by lia.
    destruct (Z.eq_dec idx j) as [<-|Hne]; [rewrite Hfb, Hab, Z.eqb_refl; reflexivity|].
    replace (idx =? j) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply andb_false_r. }
  msimp.
  pose proof (ring_facts [] None U s g am HI Hu) as RF.
  destruct (negb (am_freed am =? 0) && negb (Z.lor (am_freed am) (am_avail am) + bit idx =? ones (am_last am))) eqn:Ebr.
  - (* [comment removed for export] *)
    apply andb_prop in Ebr as [Efr0 _]. assert (Hfr0 : am_freed am <> 0) by (destruct (am_freed am =? 0) eqn:E; [discriminate | apply Z.eqb_neq in E; exact E]).
    assert (Hsc : 0 <= am_sc am < 48).
    { destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct Gcl as [(_ & _ & _ & _ & C5 & _) | (C & _)]; [exact (Hfr0 C5) | lia]. }
    destruct (RF ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3).
    assert (Hlinked : (am_prev am, am_next am) <> (None, None)) by (intros HL; destruct (RF1 HL) as [_ E]; exact (Hfr0 E)).
    assert (Hstr : class_size (am_sc am) <= stride_of am).
    { destruct Gcl as [(C & _) | (_ & CN1 & _)]; [lia|]. destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|]; [|lia].
      exfalso. destruct (CN1 Hlt) as [Hl0 _]. apply Hfr0. apply mask_zero_of_bits; [exact Gfrn|]. intros j Hj.
      destruct (Z.eq_dec j idx) as [->|Hne]; [exact Hfb|]. destruct (Gabove j ltac:(lia)) as [_ B]. exact B. }
    mbinds. eapply itok_getm; [rewrite Es1; apply MT_upd_same|]. msimp. apply itok_setm'.
    rewrite (add_bit_lor (am_freed am) idx ltac:(lia) Hfb). rewrite <- Ffr.
    apply HQ.
    + apply (set_freed_Inv [] U s1 g idx am1 HI1 U1); [rewrite Fsc; exact Hsc | rewrite Flk; exact Hlinked | rewrite Fsc, Fst; exact Hstr].
    + intros q a Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
      * injection E as <-. exists am. split; [exact Hu|]. subst am1. destruct am; unfold ceq; cbn; auto.
      * rewrite Es1 in Hq. apply usedX_upd in Hq. destruct Hq as [(E & _) | (_ & Hq)]; [exfalso; exact (Hne E)|]. exists a. split; [exact Hq | apply ceq_refl].
    + apply DEL. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U1))|].
      rewrite (proj1 (usedX_MT _ _ _ _ U1)). cbn. apply blocks_of_freed.
  - (* [comment removed for export] *)
    mbinds. eapply (nontrivial_free_spec NEST_FUEL [] U s1 g idx am1); [exact HI1 | exact U1 | exact HU | | |].
    + rewrite Flk, Ffr, Fsc. replace (active_hd s1 (am_sc am)) with (active_hd s (am_sc am)) by (rewrite Es1; reflexivity).
      intros HL Hnh. destruct Hscr as [H63|Hsc].
      { exfalso. destruct (inv_rings HI) as (_ & _ & D). destruct (D g am Hu H63) as [P N]. apply HL. rewrite P, N. reflexivity. }
      destruct (RF ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
    + rewrite Fsc. apply fneed_le. destruct Hscr as [H|H]; lia.
    + intros [mi s2] (HI2 & Cr2 & UB2 & Hmi). cbn [fst snd] in *. msimp.
      assert (C2 : forall q a, usedX [] s2 q a -> exists a0, usedX [] s q a0 /\ ceq a a0).
      { intros q a Hq. destruct (Cr2 q a Hq) as (a1 & H1 & C1'). rewrite Es1 in H1. apply usedX_upd in H1.
        destruct H1 as [(-> & _ & E) | (Hne & H0)].
        - injection E as <-. exists am. split; [exact Hu|]. refine (ceq_trans _ _ _ C1' _). subst am1. destruct am; unfold ceq; cbn; auto.
        - exists a1. split; [exact H0 | exact C1']. }
      destruct mi as [[r len]|].
      * destruct Hmi as (rg & Hr & Hkd & Hl & Hlen & Hlen0 & Hno).
        mbinds. apply itok_ask.
        { cbn [req_ok]. exists rg. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|]. split; [exact Hlen|]. split; [exact Hlen0|].
          apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
          apply (used_metas_iff s2 q a (proj1 (inv_keys HI2))) in Hin.
          exact (Hno q a (usedX_intro [] s2 q a eq_refl Hin) Hml). }
        intros z _. msimp. eapply upd_region_kill_spec; [exact HI2 | exact Hr | exact Hkd | exact Hno |].
        intros s3 HI3 Em3 _. apply HQ; [exact HI3| |].
        -- intros q a Hq. apply C2. unfold usedX, MTX, MT in *. rewrite Em3 in Hq. exact Hq.
        -- apply DEL. eapply ub_same_trans; [exact UB2 | apply ub_same_metas; exact Em3].
      * apply itok_ret. apply HQ; [exact HI2 | exact C2 | apply DEL; exact UB2].
Qed.
End MallocWfFree.

From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.

Module MallocWfSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import
  MallocModel MallocInv MallocLemmasBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_junk (q : kreq) : bool := match q with KJunk _ => true | _ => false end.

(* [comment removed for export] *)
Lemma tsim_ask_inv {A B} (R : A -> B -> Prop) q sp k q' sp' k' :
  tsim R (IAsk q sp k) (IAsk q' sp' k') ->
  (is_junk q = true /\ is_junk q' = true /\
     forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z'))
  \/ (is_junk q = false /\ q = q' /\ forall z, tsim R (k z) (k' z)).
Proof. intros H. destruct q, q'; cbn in H; first [right; split; [reflexivity|exact H] | left; split; [reflexivity|split; [reflexivity|exact H]] | destruct H as [H _]; discriminate]. Qed.

Lemma tsim_ask_intro {A B} (R : A -> B -> Prop) q sp k q' sp' k' :
  ((is_junk q = true /\ is_junk q' = true /\
     forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z'))
  \/ (is_junk q = false /\ q = q' /\ forall z, tsim R (k z) (k' z))) ->
  tsim R (IAsk q sp k) (IAsk q' sp' k').
Proof.
  intros [(J & J' & H) | (J & <- & H)].
  - destruct q, q'; cbn in J, J'; try discriminate. exact H.
  - destruct q; cbn in J; try discriminate; cbn; (split; [reflexivity|exact H]).
Qed.

Lemma tsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) :
  (forall a b, R a b -> R' a b) -> tsim R x y -> tsim R' x y.
Proof.
  intros HR. revert y. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
    try (cbn in H; first [contradiction | destruct q; contradiction]).
  - exact (HR _ _ H).
  - apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
    + left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
    + right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
  - exact I.
Qed.

Lemma tsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
      (x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) :
  tsim R1 x y -> (forall a b, R1 a b -> tsim R2 (K a) (K' b)) -> tsim R2 (ibind x K) (ibind y K').
Proof.
  intros H HK. revert y H. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
    try (cbn in H; first [contradiction | destruct q; contradiction]).
  - cbn. apply HK, H.
  - cbn [ibind]. apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
    + left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
    + right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
  - exact I.
Qed.

Lemma itok_unbind {A B} (x : itree astate A) (K : A -> itree astate B) Q :
  itok (ibind x K) Q -> itok x (fun a => itok (K a) Q).
Proof.
  induction x as [a | q sp k IH | f]; cbn; intros H; [exact H | | exact H].
  destruct H as [Hq H]. split; [exact Hq|]. intros z Hz. apply IH. apply H, Hz.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rsim {A B} (R : A -> B -> Prop) (x : itree astate A) (y : itree astate B) : Prop :=
  forall P P', itok x P -> itok y P' -> tsim (fun a b => R a b /\ P a /\ P' b) x y.

Lemma rsim_tsim {A B} (R : A -> B -> Prop) x y P P' :
  rsim R x y -> itok x P -> itok y P' -> tsim (fun a b => R a b /\ P a /\ P' b) x y.
Proof. intros H Hx Hy. exact (H P P' Hx Hy). Qed.

Lemma rsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) :
  (forall a b, R a b -> R' a b) -> rsim R x y -> rsim R' x y.
Proof.
  intros HR H P P' Hx Hy. eapply tsim_mono; [|exact (H P P' Hx Hy)]. intros a b (H1 & H2 & H3). auto.
Qed.

Lemma rsim_iret {A B} (R : A -> B -> Prop) a b : R a b -> rsim R (IRet a) (IRet b).
Proof. intros H P P' Hx Hy. cbn in *. auto. Qed.

Lemma rsim_ifail_l {A B} (R : A -> B -> Prop) f (y : itree astate B) : rsim R (IFail f) y.
Proof. intros P P' Hx Hy. destruct Hx. Qed.

Lemma rsim_ifail_r {A B} (R : A -> B -> Prop) (x : itree astate A) f : rsim R x (IFail f).
Proof. intros P P' Hx Hy. destruct Hy. Qed.

Lemma rsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
      (x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) :
  rsim R1 x y -> (forall a b, R1 a b -> rsim R2 (K a) (K' b)) -> rsim R2 (ibind x K) (ibind y K').
Proof.
  intros H HK P P' Hx Hy. apply itok_unbind in Hx. apply itok_unbind in Hy.
  eapply tsim_ibind; [exact (H _ _ Hx Hy)|]. intros a b (H1 & H2 & H3). exact (HK a b H1 P P' H2 H3).
Qed.

(* [comment removed for export] *)
Lemma rsim_iask {A B} (R : A -> B -> Prop) q sp sp' k k' :
  is_junk q = false -> (forall z, rsim R (k z) (k' z)) -> rsim R (IAsk q sp k) (IAsk q sp' k').
Proof.
  intros J H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
  apply tsim_ask_intro. right. split; [exact J|]. split; [reflexivity|]. intros z.
  assert (Az : answer_ok q z) by (destruct q; cbn in J |- *; first [exact I | discriminate]).
  exact (H z P P' (Hx z Az) (Hy z Az)).
Qed.

(* [comment removed for export] *)
Lemma rsim_iask_junk {A B} (R : A -> B -> Prop) c c' sp sp' k k' :
  (forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> rsim R (k z) (k' z')) ->
  rsim R (IAsk (KJunk c) sp k) (IAsk (KJunk c') sp' k').
Proof.
  intros H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
  cbn. intros z z' Hz Hz'. exact (H z z' Hz Hz' P P' (Hx z Hz) (Hy z' Hz')).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s t : astate).

  #[using="Type"] Lemma rsim_ret (R : A * astate -> A * astate -> Prop) (a b : A) s t :
    R (a, s) (b, t) -> rsim R (ret a s) (ret b t).
  Proof. intros H. apply rsim_iret. exact H. Qed.

  #[using="Type"] Lemma rsim_bind (R1 : B * astate -> B * astate -> Prop) (R2 : A * astate -> A * astate -> Prop)
        (m m' : M B) (k k' : B -> M A) s t :
    rsim R1 (m s) (m' t) ->
    (forall b s1 b' t1, R1 (b, s1) (b', t1) -> rsim R2 (k b s1) (k' b' t1)) ->
    rsim R2 (bind m k s) (bind m' k' t).
  Proof.
    intros H HK. unfold bind. eapply rsim_ibind; [exact H|]. intros [b s1] [b' t1] Hb. exact (HK _ _ _ _ Hb).
  Qed.

  #[using="Type"] Lemma rsim_fail_l R f s (y : itree astate (A * astate)) : rsim R (@fail A f s) y.
  Proof. apply rsim_ifail_l. Qed.
  #[using="Type"] Lemma rsim_fail_r R (x : itree astate (A * astate)) f t : rsim R x (@fail A f t).
  Proof. apply rsim_ifail_r. Qed.

  #[using="Type"] Lemma rsim_get (R : astate * astate -> astate * astate -> Prop) s t :
    R (s, s) (t, t) -> rsim R (get s) (get t).
  Proof. intros H. apply rsim_iret. exact H. Qed.

  #[using="Type"] Lemma rsim_put (R : unit * astate -> unit * astate -> Prop) s1 t1 s t :
    R (tt, s1) (tt, t1) -> rsim R (put s1 s) (put t1 t).
  Proof. intros H. apply rsim_iret. exact H. Qed.

  #[using="Type"] Lemma rsim_modify (R : unit * astate -> unit * astate -> Prop) f f' s t :
    R (tt, f s) (tt, f' t) -> rsim R (modify f s) (modify f' t).
  Proof. intros H. apply rsim_iret. exact H. Qed.

  #[using="Type"] Lemma rsim_ask (R : bool * astate -> bool * astate -> Prop) q s t :
    is_junk q = false -> (forall b : bool, R (b, s) (b, t)) -> rsim R (ask q s) (ask q t).
  Proof. intros J H. unfold ask. apply rsim_iask; [exact J|]. intros z. apply rsim_iret. apply H. Qed.

  #[using="Type"] Lemma rsim_askz_junk (R : Z * astate -> Z * astate -> Prop) c c' s t :
    (forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> R (z, s) (z', t)) ->
    rsim R (askz (KJunk c) s) (askz (KJunk c') t).
  Proof. intros H. unfold askz. apply rsim_iask_junk. intros z z' Hz Hz'. apply rsim_iret. apply H; assumption. Qed.
End MonadRules.

  (* [comment removed for export] *)
  Lemma rsim_massert (R : unit * astate -> unit * astate -> Prop) b b' i i' s t :
    (b = true -> b' = true -> R (tt, s) (tt, t)) -> rsim R (massert b i s) (massert b' i' t).
  Proof.
    intros H. unfold massert. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
    apply rsim_ret. apply H; reflexivity.
  Qed.

  Lemma rsim_mcheck (R : unit * astate -> unit * astate -> Prop) b b' i i' s t :
    (b = true -> b' = true -> R (tt, s) (tt, t)) -> rsim R (mcheck b i s) (mcheck b' i' t).
  Proof.
    intros H. unfold mcheck. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
    apply rsim_ret. apply H; reflexivity.
  Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition erase_am (am : ameta) : ameta := am_set_slots (map erase_slot (am_slots am)) am.
Definition ef (e : sptr * mslot) : sptr * mslot := (fst e, erase_meta (snd e)).
Definition mrel (ms mt : list (sptr * mslot)) : Prop := map ef ms = map ef mt.

Lemma erase_unfold s : erase s = set_metas (map ef (st_metas s)) s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition sheq (s t : astate) : Prop := shape_eq s t /\ NoDup (keys s).

Lemma sheq_shape s t : sheq s t -> shape_eq s t.
Proof. intros [H _]; exact H. Qed.

Lemma sq_metas s t : shape_eq s t -> mrel (st_metas s) (st_metas t).
Proof. intros H. exact (f_equal st_metas H). Qed.
Lemma sheq_metas s t : sheq s t -> mrel (st_metas s) (st_metas t).
Proof. intros [H _]. apply sq_metas, H. Qed.

Lemma mrel_keys ms mt : mrel ms mt -> map fst ms = map fst mt.
Proof.
  intros H. transitivity (map fst (map ef ms)); [rewrite map_map; reflexivity|].
  unfold mrel in H. rewrite H, map_map. reflexivity.
Qed.

Lemma sheq_nodup_l s t : sheq s t -> NoDup (keys s).
Proof. intros [_ H]; exact H. Qed.
Lemma sheq_nodup_r s t : sheq s t -> NoDup (keys t).
Proof. intros [H ND]. unfold keys in *. rewrite <- (mrel_keys _ _ (sq_metas _ _ H)). exact ND. Qed.
(* [comment removed for export] *)
Lemma sq_init_done s t : sheq s t -> st_init_done t = st_init_done s.
Proof. intros [H _]. symmetry. exact (f_equal st_init_done H). Qed.
Lemma sq_mmap_counter s t : sheq s t -> st_mmap_counter t = st_mmap_counter s.
Proof. intros [H _]. symmetry. exact (f_equal st_mmap_counter H). Qed.
Lemma sq_free_meta_head s t : sheq s t -> st_free_meta_head t = st_free_meta_head s.
Proof. intros [H _]. symmetry. exact (f_equal st_free_meta_head H). Qed.
Lemma sq_avail_meta s t : sheq s t -> st_avail_meta t = st_avail_meta s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta H). Qed.
Lemma sq_avail_meta_count s t : sheq s t -> st_avail_meta_count t = st_avail_meta_count s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_count H). Qed.
Lemma sq_avail_meta_area_count s t : sheq s t -> st_avail_meta_area_count t = st_avail_meta_area_count s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_area_count H). Qed.
Lemma sq_meta_alloc_shift s t : sheq s t -> st_meta_alloc_shift t = st_meta_alloc_shift s.
Proof. intros [H _]. symmetry. exact (f_equal st_meta_alloc_shift H). Qed.
Lemma sq_area_head s t : sheq s t -> st_area_head t = st_area_head s.
Proof. intros [H _]. symmetry. exact (f_equal st_area_head H). Qed.
Lemma sq_area_tail s t : sheq s t -> st_area_tail t = st_area_tail s.
Proof. intros [H _]. symmetry. exact (f_equal st_area_tail H). Qed.
Lemma sq_avail_meta_areas s t : sheq s t -> st_avail_meta_areas t = st_avail_meta_areas s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_areas H). Qed.
Lemma sq_active s t : sheq s t -> st_active t = st_active s.
Proof. intros [H _]. symmetry. exact (f_equal st_active H). Qed.
Lemma sq_usage s t : sheq s t -> st_usage t = st_usage s.
Proof. intros [H _]. symmetry. exact (f_equal st_usage H). Qed.
Lemma sq_unmap_seq s t : sheq s t -> st_unmap_seq t = st_unmap_seq s.
Proof. intros [H _]. symmetry. exact (f_equal st_unmap_seq H). Qed.
Lemma sq_bounces s t : sheq s t -> st_bounces t = st_bounces s.
Proof. intros [H _]. symmetry. exact (f_equal st_bounces H). Qed.
Lemma sq_seq s t : sheq s t -> st_seq t = st_seq s.
Proof. intros [H _]. symmetry. exact (f_equal st_seq H). Qed.
Lemma sq_brk s t : sheq s t -> st_brk t = st_brk s.
Proof. intros [H _]. symmetry. exact (f_equal st_brk H). Qed.
Lemma sq_regions s t : sheq s t -> st_regions t = st_regions s.
Proof. intros [H _]. symmetry. exact (f_equal st_regions H). Qed.
Lemma sq_areas s t : sheq s t -> st_areas t = st_areas s.
Proof. intros [H _]. symmetry. exact (f_equal st_areas H). Qed.
Lemma sq_is_bouncing s t sc : sheq s t -> is_bouncing t sc = is_bouncing s sc.
Proof. intros H. unfold is_bouncing. rewrite (sq_bounces _ _ H). reflexivity. Qed.
Lemma sq_usage_of s t sc : sheq s t -> usage_of t sc = usage_of s sc.
Proof. intros H. unfold usage_of. rewrite (sq_usage _ _ H). reflexivity. Qed.
Lemma sq_active_hd s t sc : sheq s t -> active_hd t sc = active_hd s sc.
Proof. intros H. unfold active_hd. rewrite (sq_active _ _ H). reflexivity. Qed.
Lemma sq_mmap_plan s t sc req c u : sheq s t -> mmap_plan t sc req c u = mmap_plan s sc req c u.
Proof. intros H. unfold mmap_plan. rewrite !(sq_is_bouncing _ _ _ H), !(sq_usage_of _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Ltac shrw H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H) in *.
Ltac shrwg H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H).

Lemma sq_mk x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 ms mt :
  mrel ms mt -> shape_eq (mkA x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ms x17 x18) (mkA x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mt x17 x18).
Proof. intros H. unfold shape_eq. rewrite !erase_unfold. cbn. unfold mrel in H. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sq_fields s t :
  shape_eq s t <-> (st_init_done s = st_init_done t /\ st_mmap_counter s = st_mmap_counter t /\ st_free_meta_head s = st_free_meta_head t /\ st_avail_meta s = st_avail_meta t /\ st_avail_meta_count s = st_avail_meta_count t /\ st_avail_meta_area_count s = st_avail_meta_area_count t /\ st_meta_alloc_shift s = st_meta_alloc_shift t /\ st_area_head s = st_area_head t /\ st_area_tail s = st_area_tail t /\ st_avail_meta_areas s = st_avail_meta_areas t /\ st_active s = st_active t /\ st_usage s = st_usage t /\ st_unmap_seq s = st_unmap_seq t /\ st_bounces s = st_bounces t /\ st_seq s = st_seq t /\ st_brk s = st_brk t /\ st_regions s = st_regions t /\ st_areas s = st_areas t /\ mrel (st_metas s) (st_metas t)).
Proof.
  split.
  - intros H. repeat match goal with |- _ /\ _ => split end;
      match goal with
      | |- mrel _ _ => exact (f_equal st_metas H)
      | |- ?p s = ?p t => pose proof (f_equal p H) as E; cbn in E; exact E
      end.
  - destruct s as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19], t as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19]. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas].
    intros (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM). subst. unfold shape_eq. rewrite !erase_unfold. unfold set_metas.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. unfold mrel in EM. rewrite EM. reflexivity.
Qed.
Lemma sheq_set_init_done v s t : sheq s t -> sheq (set_init_done v s) (set_init_done v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_init_done. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_mmap_counter v s t : sheq s t -> sheq (set_mmap_counter v s) (set_mmap_counter v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_mmap_counter. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_free_meta_head v s t : sheq s t -> sheq (set_free_meta_head v s) (set_free_meta_head v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_free_meta_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta v s t : sheq s t -> sheq (set_avail_meta v s) (set_avail_meta v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_count v s t : sheq s t -> sheq (set_avail_meta_count v s) (set_avail_meta_count v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_area_count v s t : sheq s t -> sheq (set_avail_meta_area_count v s) (set_avail_meta_area_count v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_area_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_meta_alloc_shift v s t : sheq s t -> sheq (set_meta_alloc_shift v s) (set_meta_alloc_shift v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_meta_alloc_shift. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_head v s t : sheq s t -> sheq (set_area_head v s) (set_area_head v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_area_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_tail v s t : sheq s t -> sheq (set_area_tail v s) (set_area_tail v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_area_tail. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_areas v s t : sheq s t -> sheq (set_avail_meta_areas v s) (set_avail_meta_areas v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_avail_meta_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_active v s t : sheq s t -> sheq (set_active v s) (set_active v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_active. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_usage v s t : sheq s t -> sheq (set_usage v s) (set_usage v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_usage. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_unmap_seq v s t : sheq s t -> sheq (set_unmap_seq v s) (set_unmap_seq v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_unmap_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_bounces v s t : sheq s t -> sheq (set_bounces v s) (set_bounces v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_bounces. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_seq v s t : sheq s t -> sheq (set_seq v s) (set_seq v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_brk v s t : sheq s t -> sheq (set_brk v s) (set_brk v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_brk. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_regions v s t : sheq s t -> sheq (set_regions v s) (set_regions v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_regions. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_areas v s t : sheq s t -> sheq (set_areas v s) (set_areas v t).
Proof.
  intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
  unfold set_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.

(* [comment removed for export] *)
Lemma mrel_mupdate ms mt p x x' :
  mrel ms mt -> erase_meta x = erase_meta x' -> mrel (mupdate ms p x) (mupdate mt p x').
Proof.
  unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H Ex; cbn [mupdate map] in *; try discriminate.
  - unfold ef. cbn [fst snd]. rewrite Ex. reflexivity.
  - unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); cbn [map].
    + unfold ef at 1 3. cbn [fst snd]. rewrite Ex, Et. reflexivity.
    + unfold ef at 1 3. cbn [fst snd]. rewrite Ey. f_equal. apply IH; assumption.
Qed.

Definition orel (o o' : option mslot) : Prop :=
  match o, o' with
  | None, None => True
  | Some x, Some x' => erase_meta x = erase_meta x'
  | _, _ => False
  end.

Lemma mrel_mlookup ms mt p : mrel ms mt -> orel (mlookup ms p) (mlookup mt p).
Proof.
  unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H; cbn [mlookup map] in *; try discriminate; [exact I|].
  unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); [exact Ey|]. apply IH. exact Et.
Qed.

Lemma sheq_MT s t p : sheq s t -> orel (MT s p) (MT t p).
Proof. intros H. unfold MT. apply mrel_mlookup. apply sheq_metas, H. Qed.

(* [comment removed for export] *)
Lemma erase_meta_inv x x' :
  erase_meta x = erase_meta x' ->
  match x with
  | MUsed am =>
      exists sl', x' = MUsed (mkAMeta (am_prev am) (am_next am) (am_mem am) (am_avail am) (am_freed am)
                                     (am_last am) (am_sc am) (am_maplen am) (am_aidx am) sl') /\
                  map erase_slot (am_slots am) = map erase_slot sl'
  | _ => x' = x
  end.
Proof.
  destruct x as [pr nx| |am], x' as [pr' nx'| |am']; cbn; intros E; try discriminate; try congruence.
  destruct am, am'. cbn in E |- *. injection E as -> -> -> -> -> -> -> -> -> Esl. eexists. split; [reflexivity | exact Esl].
Qed.

Lemma erase_am_mk pr nx mem av frd la sc ml ai sl sl' :
  map erase_slot sl = map erase_slot sl' ->
  erase_meta (MUsed (mkAMeta pr nx mem av frd la sc ml ai sl)) = erase_meta (MUsed (mkAMeta pr nx mem av frd la sc ml ai sl')).
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Lemma links_of_erase x x' : erase_meta x = erase_meta x' -> links_of x' = links_of x.
Proof. intros E. apply erase_meta_inv in E. destruct x; subst; try reflexivity. destruct E as (sl' & -> & _). destruct m; reflexivity. Qed.

Lemma with_links_erase x x' pr nx :
  erase_meta x = erase_meta x' -> erase_meta (with_links x pr nx) = erase_meta (with_links x' pr nx).
Proof. intros E. pose proof (erase_meta_inv _ _ E) as E'. destruct x; subst; try reflexivity. destruct E' as (sl' & -> & Es). destruct m. cbn in Es |- *. rewrite Es. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cons_inj {T} (a b : T) (l m : list T) : a :: l = b :: m -> a = b /\ l = m.
Proof. intros H. injection H as -> ->. split; reflexivity. Qed.

Lemma map_erase_nth sl sl' i :
  map erase_slot sl = map erase_slot sl' -> erase_slot (nth i sl slot_junk) = erase_slot (nth i sl' slot_junk).
Proof.
  revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [reflexivity|].
  apply cons_inj in H as [Ex Et]. destruct i; cbn [nth]; [exact Ex | apply IH; exact Et].
Qed.

Lemma map_erase_lupd sl sl' i x x' :
  map erase_slot sl = map erase_slot sl' -> erase_slot x = erase_slot x' ->
  map erase_slot (lupd sl i x) = map erase_slot (lupd sl' i x').
Proof.
  revert sl' i. induction sl as [|y sl IH]; intros [|y' sl'] i H Ex; cbn [map] in H; try discriminate; [reflexivity|].
  apply cons_inj in H as [Ey Et]. destruct i; cbn [lupd map]; [congruence|]. rewrite Ey. f_equal. apply IH; assumption.
Qed.

Lemma map_erase_length sl sl' : map erase_slot sl = map erase_slot sl' -> length sl' = length sl.
Proof. intros H. rewrite <- (length_map erase_slot sl), <- (length_map erase_slot sl'), H. reflexivity. Qed.

Lemma erase_slot_inv x x' :
  erase_slot x = erase_slot x' ->
  (ss_hdr x = None <-> ss_hdr x' = None) /\
  match ss_fr x, ss_fr x' with
  | None, None => True
  | Some fr, Some fr' => fr_n fr' = fr_n fr /\ fr_kind fr' = fr_kind fr /\ (fr_kind fr = FGroup -> fr_off fr' = fr_off fr)
  | _, _ => False
  end.
Proof.
  destruct x as [h f], x' as [h' f']. unfold erase_slot. cbn [ss_hdr ss_fr]. intros E. injection E as Eh Ef. split.
  - destruct h, h'; split; intros; congruence.
  - destruct f as [fr|], f' as [fr'|]; try discriminate; [|exact I]. injection Ef as Eo En Ek.
    split; [congruence|]. split; [congruence|]. intros K. rewrite K in Eo. rewrite <- Ek, K in Eo. congruence.
Qed.

Lemma erase_slot_rehdr x x' f :
  erase_slot x = erase_slot x' -> erase_slot (mkSlot (ss_hdr x) f) = erase_slot (mkSlot (ss_hdr x') f).
Proof. intros E. unfold erase_slot in *. cbn [ss_hdr ss_fr] in *. injection E as Eh Ef. rewrite Eh. reflexivity. Qed.

Lemma map_erase_nth_slot pr nx mem av frd la sc ml ai sl pr' nx' mem' av' frd' la' sc' ml' ai' sl' i :
  map erase_slot sl = map erase_slot sl' ->
  erase_slot (nth_slot (mkAMeta pr nx mem av frd la sc ml ai sl) i) =
  erase_slot (nth_slot (mkAMeta pr' nx' mem' av' frd' la' sc' ml' ai' sl') i).
Proof. intros H. unfold nth_slot. cbn [am_slots]. apply map_erase_nth. exact H. Qed.

(* [comment removed for export] *)
Lemma sheq_set_metas s t p x x' :
  sheq s t -> erase_meta x = erase_meta x' ->
  sheq (set_metas (mupdate (st_metas s) p x) s) (set_metas (mupdate (st_metas t) p x') t).
Proof.
  intros [H ND] Ex. split.
  - pose proof (mrel_mupdate _ _ p x x' (sq_metas _ _ H) Ex) as M.
    apply sq_fields in H. apply (proj2 (sq_fields _ _)). unfold set_metas.
    cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
    repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
  - unfold keys. cbn [st_metas set_metas]. apply NoDup_keys_mupdate. exact ND.
Qed.

Create HintDb sheq.
Hint Resolve sheq_set_init_done sheq_set_mmap_counter sheq_set_free_meta_head sheq_set_avail_meta
  sheq_set_avail_meta_count sheq_set_avail_meta_area_count sheq_set_meta_alloc_shift sheq_set_area_head
  sheq_set_area_tail sheq_set_avail_meta_areas sheq_set_active sheq_set_usage sheq_set_unmap_seq
  sheq_set_bounces sheq_set_seq sheq_set_brk sheq_set_regions sheq_set_areas sheq_set_metas : sheq.
(* [comment removed for export] *)
Definition stride_flds (la ml sc : Z) : Z := if (la =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else class_size sc.
Lemma stride_of_mk pr nx mem av frd la sc ml ai sl :
  stride_of (mkAMeta pr nx mem av frd la sc ml ai sl) = stride_flds la ml sc.
Proof. reflexivity. Qed.

Ltac amsimp := cbn [am_set_slots am_set_avail am_set_freed am_set_aidx am_set_links am_set_prev am_set_next upd_slot
                    am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots]; rewrite ?stride_of_mk.
Ltac eam :=
  amsimp;
  first [ reflexivity | assumption
        | apply erase_am_mk;
          first [ assumption
                | apply map_erase_lupd;
                  first [ assumption | reflexivity
                        | apply erase_slot_rehdr; first [assumption | apply map_erase_nth_slot; assumption | apply map_erase_nth; assumption] ] ]
        | apply with_links_erase; assumption
        | congruence ].
Hint Extern 1 (erase_meta _ = erase_meta _) => eam : sheq.

(* [comment removed for export] *)
Ltac sheq_tac :=
  match goal with H : sheq ?s ?t |- _ => shrwg H; solve [eauto 20 with sheq] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eqr {A} (r r' : A * astate) : Prop := fst r = fst r' /\ sheq (snd r) (snd r').

(* [comment removed for export] *)
Definition amr (p : sptr) (s t : astate) (r r' : ameta * astate) : Prop :=
  exists pr nx mem av frd la sc ml ai sl sl',
    fst r = mkAMeta pr nx mem av frd la sc ml ai sl /\ fst r' = mkAMeta pr nx mem av frd la sc ml ai sl' /\
    map erase_slot sl = map erase_slot sl' /\
    MT s p = Some (MUsed (fst r)) /\ MT t p = Some (MUsed (fst r')) /\ snd r = s /\ snd r' = t.

Section Prims.
  Context {A : Type}.
  Implicit Types (s t : astate).

  #[using="Type"] Lemma rsim_ret_eq (a : A) s t : sheq s t -> rsim eqr (ret a s) (ret a t).
  Proof. intros H. apply rsim_ret. split; [reflexivity | exact H]. Qed.

  #[using="Type"] Lemma rsim_get_eq s t : rsim (fun r r' => r = (s, s) /\ r' = (t, t)) (get s) (get t).
  Proof. apply rsim_get. split; reflexivity. Qed.

  #[using="Type"] Lemma rsim_modify_eq f f' s t : sheq (f s) (f' t) -> rsim eqr (modify f s) (modify f' t).
  Proof. intros H. apply rsim_modify. split; [reflexivity | exact H]. Qed.

  #[using="Type"] Lemma rsim_put_eq s1 t1 s t : sheq s1 t1 -> rsim eqr (put s1 s) (put t1 t).
  Proof. intros H. apply rsim_put. split; [reflexivity | exact H]. Qed.

  #[using="Type"] Lemma rsim_ask_eq q s t : sheq s t -> is_junk q = false -> rsim eqr (ask q s) (ask q t).
  Proof. intros H J. apply rsim_ask; [exact J|]. intros b. split; [reflexivity | exact H]. Qed.

End Prims.

(* [comment removed for export] *)
Definition chk (b b' : bool) (s t : astate) (r r' : unit * astate) : Prop :=
  b = true /\ b' = true /\ snd r = s /\ snd r' = t.

Lemma rsim_massert_chk b b' i i' s t : rsim (chk b b' s t) (massert b i s) (massert b' i' t).
Proof. apply rsim_massert. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.

Lemma rsim_mcheck_chk b b' i i' s t : rsim (chk b b' s t) (mcheck b i s) (mcheck b' i' t).
Proof. apply rsim_mcheck. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.

Lemma rsim_getm p s t : sheq s t -> rsim (amr p s t) (getm p s) (getm p t).
Proof.
  intros H. unfold getm. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|] eqn:Ms, (mlookup (st_metas t) p) as [x'|] eqn:Mt; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  pose proof (erase_meta_inv _ _ OR) as INV. destruct x as [pr0 nx0| |am]; [subst x'; apply rsim_ifail_l .. |].
  destruct INV as (sl' & -> & ES). apply rsim_ret. destruct am as [pr nx mem av frd la sc ml ai sl]. cbn in ES.
  exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl'. unfold MT. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | exact ES | exact Ms | exact Mt].
Qed.

Lemma rsim_setm p am am' s t :
  sheq s t -> erase_meta (MUsed am) = erase_meta (MUsed am') -> rsim eqr (setm p am s) (setm p am' t).
Proof. intros H E. unfold setm. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.

Lemma rsim_setslot p x x' s t :
  sheq s t -> erase_meta x = erase_meta x' -> rsim eqr (setslot p x s) (setslot p x' t).
Proof. intros H E. unfold setslot. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.

Lemma rsim_get_links p s t : sheq s t -> rsim eqr (get_links p s) (get_links p t).
Proof.
  intros H. unfold get_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  apply rsim_ret. split; [cbn [fst]; symmetry; apply links_of_erase; exact OR | exact H].
Qed.

Lemma rsim_set_links p pr nx s t : sheq s t -> rsim eqr (set_links p pr nx s) (set_links p pr nx t).
Proof.
  intros H. unfold set_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
  apply rsim_setslot; [exact H|]. apply with_links_erase. exact OR.
Qed.

Lemma rsim_set_prev p pr s t : sheq s t -> rsim eqr (set_prev p pr s) (set_prev p pr t).
Proof.
  intros H. unfold set_prev. eapply rsim_bind; [apply rsim_get_links; exact H|].
  intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.

Lemma rsim_set_next p nx s t : sheq s t -> rsim eqr (set_next p nx s) (set_next p nx t).
Proof.
  intros H. unfold set_next. eapply rsim_bind; [apply rsim_get_links; exact H|].
  intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.

Lemma rsim_get_head h s t : sheq s t -> rsim eqr (get_head h s) (get_head h t).
Proof.
  intros H. unfold get_head. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
  destruct h; apply rsim_ret; (split; [cbn [fst]; shrwg H; reflexivity | exact H]).
Qed.

Lemma rsim_set_head h v s t : sheq s t -> rsim eqr (set_head h v s) (set_head h v t).
Proof. intros H. unfold set_head. destruct h; apply rsim_modify_eq; shrwg H; auto with sheq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac shall := repeat match goal with H : sheq _ _ |- _ => progress (shrwg H) end.

Create HintDb rsim.

(* [comment removed for export] *)
Ltac rhead :=
  lazymatch goal with
  | |- rsim _ (get _) (get _) => apply rsim_get_eq
  | |- rsim _ (ret _ _) (ret _ _) => apply rsim_ret_eq; assumption
  | |- rsim _ (modify _ _) (modify _ _) => apply rsim_modify_eq; sheq_tac
  | |- rsim _ (put _ _) (put _ _) => apply rsim_put_eq; sheq_tac
  | |- rsim _ (getm _ _) (getm _ _) => apply rsim_getm; assumption
  | |- rsim _ (setm _ _ _) (setm _ _ _) => apply rsim_setm; [assumption | eam]
  | |- rsim _ (setslot _ _ _) (setslot _ _ _) => apply rsim_setslot; [assumption | eam]
  | |- rsim _ (get_links _ _) (get_links _ _) => apply rsim_get_links; assumption
  | |- rsim _ (set_links _ _ _ _) (set_links _ _ _ _) => apply rsim_set_links; assumption
  | |- rsim _ (set_prev _ _ _) (set_prev _ _ _) => apply rsim_set_prev; assumption
  | |- rsim _ (set_next _ _ _) (set_next _ _ _) => apply rsim_set_next; assumption
  | |- rsim _ (get_head _ _) (get_head _ _) => apply rsim_get_head; assumption
  | |- rsim _ (set_head _ _ _) (set_head _ _ _) => apply rsim_set_head; assumption
  | |- rsim _ (massert _ _ _) (massert _ _ _) => apply rsim_massert_chk
  | |- rsim _ (mcheck _ _ _) (mcheck _ _ _) => apply rsim_mcheck_chk
  | |- rsim _ (ask _ _) (ask _ _) => apply rsim_ask_eq; [assumption | reflexivity]
  | |- rsim _ (fail _ _) _ => apply rsim_ifail_l
  | |- rsim _ _ (fail _ _) => apply rsim_ifail_r
  | |- rsim _ _ _ => solve [eauto 3 with rsim nocore]
  end.

(* [comment removed for export] *)
Ltac rintro :=
  let a := fresh "a" in let s1 := fresh "s" in let a' := fresh "a'" in let t1 := fresh "t" in
  let HR := fresh "HR" in
  intros a s1 a' t1 HR; cbn beta in HR;
  lazymatch type of HR with
  | eqr _ _ =>
      let E := fresh "E" in let HS := fresh "HS" in
      destruct HR as [E HS]; cbn [fst snd] in E, HS; subst a'
  | chk _ _ _ _ _ _ =>
      let B1 := fresh "CHK" in let B2 := fresh "CHK'" in let E1 := fresh "E" in let E2 := fresh "E" in
      destruct HR as (B1 & B2 & E1 & E2); cbn [fst snd] in E1, E2; subst s1 t1; destruct a, a'
  | _ = _ /\ _ = _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      destruct HR as [E1 E2]; injection E1 as -> ->; injection E2 as -> ->
  | amr _ _ _ _ _ =>
      let pr := fresh "pr" in let nx := fresh "nx" in let mem := fresh "mem" in let av := fresh "av" in
      let frd := fresh "frd" in let la := fresh "la" in let sc := fresh "sc" in let ml := fresh "ml" in
      let ai := fresh "ai" in let sl := fresh "sl" in let sl' := fresh "sl'" in
      let E1 := fresh "E" in let E2 := fresh "E" in let ES := fresh "ES" in
      let M1 := fresh "Ms" in let M2 := fresh "Mt" in let E3 := fresh "E" in let E4 := fresh "E" in
      destruct HR as (pr & nx & mem & av & frd & la & sc & ml & ai & sl & sl' & E1 & E2 & ES & M1 & M2 & E3 & E4);
      cbn [fst snd] in E1, E2, M1, M2, E3, E4; subst a a' s1 t1
  | _ => idtac
  end; cbn beta iota zeta delta [fst snd].

(* [comment removed for export] *)
Ltac rauto :=
  shall; amsimp;
  first
  [ lazymatch goal with
    | |- rsim _ (bind _ _ _) (bind _ _ _) => eapply rsim_bind; [solve [rauto] | rintro; rauto]
    | |- rsim _ (match ?x with _ => _ end _) (match ?x with _ => _ end _) => destruct x eqn:?; rauto
    | |- rsim _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x eqn:?; rauto
    | |- rsim _ _ _ => rhead
    end
  | idtac ].
(* [comment removed for export] *)
Ltac rstep := shall; amsimp; eapply rsim_bind; [rhead | rintro].
Ltac rbind tac := shall; amsimp; eapply rsim_bind; [tac | rintro].
Ltac rcase :=
  shall; amsimp;
  lazymatch goal with
  | |- rsim _ (match ?x with _ => _ end _) _ => destruct x eqn:?
  | |- rsim _ (match ?x with _ => _ end) _ => destruct x eqn:?
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rsim_queue h m s t : sheq s t -> rsim eqr (queue h m s) (queue h m t).
Proof. intros H. unfold queue. rauto. Qed.
Global Hint Resolve rsim_queue : rsim.

Lemma rsim_dequeue h m s t : sheq s t -> rsim eqr (dequeue h m s) (dequeue h m t).
Proof. intros H. unfold dequeue. rauto. Qed.
Global Hint Resolve rsim_dequeue : rsim.

Lemma rsim_dequeue_head h s t : sheq s t -> rsim eqr (dequeue_head h s) (dequeue_head h t).
Proof. intros H. unfold dequeue_head. rauto. Qed.
Global Hint Resolve rsim_dequeue_head : rsim.

Lemma rsim_free_meta m s t : sheq s t -> rsim eqr (free_meta m s) (free_meta m t).
Proof. intros H. unfold free_meta. rauto. Qed.
Global Hint Resolve rsim_free_meta : rsim.

Lemma rsim_set_usage_of sc v s t : sheq s t -> rsim eqr (set_usage_of sc v s) (set_usage_of sc v t).
Proof. intros H. unfold set_usage_of. rauto. Qed.
Global Hint Resolve rsim_set_usage_of : rsim.

Lemma rsim_step_seq s t : sheq s t -> rsim eqr (step_seq s) (step_seq t).
Proof. intros H. unfold step_seq. apply rsim_modify_eq. shrwg H. destruct (st_seq s =? 255); auto with sheq. Qed.
Global Hint Resolve rsim_step_seq : rsim.

Lemma rsim_record_seq sc s t : sheq s t -> rsim eqr (record_seq sc s) (record_seq sc t).
Proof. intros H. unfold record_seq. destruct (bounce_idx sc); rauto. Qed.
Global Hint Resolve rsim_record_seq : rsim.

Lemma rsim_account_bounce sc s t : sheq s t -> rsim eqr (account_bounce sc s) (account_bounce sc t).
Proof.
  intros H. unfold account_bounce. destruct (bounce_idx sc); [|rauto].
  apply rsim_modify_eq. shrwg H. destruct (negb _ && _); auto with sheq.
Qed.
Global Hint Resolve rsim_account_bounce : rsim.

Lemma rsim_decay_bounces sc s t : sheq s t -> rsim eqr (decay_bounces sc s) (decay_bounces sc t).
Proof.
  intros H. unfold decay_bounces. destruct (bounce_idx sc); [|rauto].
  apply rsim_modify_eq. shrwg H. destruct (_ =? 0); auto with sheq.
Qed.
Global Hint Resolve rsim_decay_bounces : rsim.

Lemma rsim_new_region k len s t : sheq s t -> rsim eqr (new_region k len s) (new_region k len t).
Proof. intros H. unfold new_region. rauto. Qed.
Global Hint Resolve rsim_new_region : rsim.

Lemma rsim_upd_region r f s t : sheq s t -> rsim eqr (upd_region r f s) (upd_region r f t).
Proof. intros H. unfold upd_region. rauto. Qed.
Global Hint Resolve rsim_upd_region : rsim.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rsim_area_from_brk s t : sheq s t -> rsim eqr (area_from_brk s) (area_from_brk t).
Proof. intros H. unfold area_from_brk. rauto. Qed.
Global Hint Resolve rsim_area_from_brk : rsim.

Lemma rsim_area_from_mmap s t : sheq s t -> rsim eqr (area_from_mmap s) (area_from_mmap t).
Proof. intros H. unfold area_from_mmap. rauto. Qed.
Global Hint Resolve rsim_area_from_mmap : rsim.

Lemma rsim_open_area nu s t : sheq s t -> rsim eqr (open_area nu s) (open_area nu t).
Proof. intros H. unfold open_area. rauto. Qed.
Global Hint Resolve rsim_open_area : rsim.

Lemma rsim_alloc_meta s t : sheq s t -> rsim eqr (alloc_meta s) (alloc_meta t).
Proof. intros H. unfold alloc_meta. rauto. Qed.
Global Hint Resolve rsim_alloc_meta : rsim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rsim_activate_group m s t : sheq s t -> rsim eqr (activate_group m s) (activate_group m t).
Proof. intros H. unfold activate_group. rauto. Qed.
Global Hint Resolve rsim_activate_group : rsim.

Lemma rsim_install_group m sc cnt aidx maplen mem sl s t :
  sheq s t -> rsim eqr (install_group m sc cnt aidx maplen mem sl s) (install_group m sc cnt aidx maplen mem sl t).
Proof. intros H. unfold install_group. rauto. Qed.
Global Hint Resolve rsim_install_group : rsim.

Lemma rsim_forget_frame g i s t : sheq s t -> rsim eqr (forget_frame g i s) (forget_frame g i t).
Proof. intros H. unfold forget_frame. rauto. Qed.
Global Hint Resolve rsim_forget_frame : rsim.

Lemma rsim_try_avail sc s t : sheq s t -> rsim eqr (try_avail sc s) (try_avail sc t).
Proof. intros H. unfold try_avail. rauto. Qed.
Global Hint Resolve rsim_try_avail : rsim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enr (g : sptr) (idx n : Z) (k : fkind) (s t : astate) (r r' : sptr * astate) : Prop :=
  exists pr nx mem av frd la sc ml ai sl sl' off off' hdr hdr',
    let am := mkAMeta pr nx mem av frd la sc ml ai sl in
    let am' := mkAMeta pr nx mem av frd la sc ml ai sl' in
    MT s g = Some (MUsed am) /\ MT t g = Some (MUsed am') /\
    map erase_slot sl = map erase_slot sl' /\ 0 <= idx <= la /\
    snd r = set_metas (mupdate (st_metas s) g (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n k)))))) s /\
    snd r' = set_metas (mupdate (st_metas t) g (MUsed (upd_slot am' idx (mkSlot (Some hdr') (Some (mkFrame off' n k)))))) t /\
    fst r = padd (slot_start am idx) (UNIT * off) /\ fst r' = padd (slot_start am idx) (UNIT * off') /\
    (k = FGroup -> off = 0 /\ off' = 0) /\
    sheq (snd r) (snd r').

Lemma rsim_enframe g idx n ctr k s t :
  sheq s t ->
  (k = FGroup -> exists am, MT s g = Some (MUsed am) /\ n = stride_of am - IB) ->
  rsim (enr g idx n k s t) (enframe g idx n ctr k s) (enframe g idx n ctr k t).
Proof.
  intros H HG. unfold enframe. rstep. rstep.
  set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
  set (slack := (stride_flds la ml sc - IB - n) / UNIT).
  assert (EN : erase_slot (nth_slot am idx) = erase_slot (nth_slot am' idx)) by (apply map_erase_nth_slot; exact ES).
  apply erase_slot_inv in EN as [EH _].
  eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t /\ (slack = 0 -> fst r = 0 /\ fst r' = 0))).
  { destruct (slack =? 0) eqn:Es0.
    - apply rsim_ret. cbn [fst snd]. auto.
    - apply Z.eqb_neq in Es0.
      destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh, (ss_hdr (nth_slot am' idx)) as [[h3' h16']|] eqn:Eh';
        [| exfalso; pose proof (proj2 EH eq_refl); congruence | exfalso; pose proof (proj1 EH eq_refl); congruence |].
      + apply rsim_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. intros; lia.
      + eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t)).
        * apply rsim_askz_junk. intros; split; reflexivity.
        * intros z s1 z' t1 [E1 E2]. cbn [fst snd] in E1, E2. subst s1 t1. apply rsim_ret. cbn [fst snd].
          split; [reflexivity|]. split; [reflexivity|]. intros; lia. }
  intros off0 s1 off0' t1 (E1 & E2 & Z0). cbn [fst snd] in E1, E2, Z0. subst s1 t1.
  rstep.
  unfold bind, setm, modify, ret. cbn [ibind]. apply rsim_iret.
  match goal with |- enr _ _ _ _ _ _ (padd _ (UNIT * ?o), _) (padd _ (UNIT * ?o'), _) => set (off := o); set (off' := o') end.
  assert (HG0 : k = FGroup -> off = 0 /\ off' = 0).
  { intros Hk. destruct (HG Hk) as (am0 & M0 & En). rewrite Ms in M0. injection M0 as <-. subst am. rewrite stride_of_mk in En.
    assert (S0 : slack = 0).
    { subst slack. rewrite En. replace (stride_flds la ml sc - IB - (stride_flds la ml sc - IB)) with 0 by lia. reflexivity. }
    destruct (Z0 S0) as [-> ->]. subst off off'. rewrite S0. cbn. split; reflexivity. }
  unfold enr. exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl', off, off'. eexists. eexists. cbn [fst snd]. fold am am'.
  split; [exact Ms|]. split; [exact Mt|]. split; [exact ES|].
  split; [apply andb_prop in CHK as [B1 B2]; apply Z.leb_le in B1; apply Z.leb_le in B2; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HG0|].
  apply sheq_set_metas; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
  destruct k; [reflexivity|]. destruct (HG0 eq_refl) as [-> ->]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac enr_intro HR :=
  destruct HR as (?pr & ?nx & ?mem & ?av & ?frd & ?la & ?sc & ?ml & ?ai & ?sl & ?sl' & ?off & ?off' & ?hdr & ?hdr' &
                  ?Ms & ?Mt & ?ES & ?Hidx & ?E1 & ?E2 & ?P1 & ?P2 & ?HG0 & ?HS); cbn [fst snd] in Ms, Mt, E1, E2, P1, P2, HS.

Lemma rsim_alloc_mutual fuel :
  (forall sc req s t, sheq s t -> rsim eqr (alloc_slot fuel sc req s) (alloc_slot fuel sc req t)) /\
  (forall sc req s t, sheq s t -> rsim eqr (alloc_group fuel sc req s) (alloc_group fuel sc req t)).
Proof.
  induction fuel as [|f [IHs IHg]].
  { split; intros; cbn; apply rsim_ifail_l. }
  split.
  - intros sc req s t H. cbn fix beta iota delta [alloc_slot]. rauto.
  - intros sc req s t H. cbn fix beta iota delta [alloc_group]. rauto.
    (* [comment removed for export] *)
    rbind ltac:(apply rsim_enframe; [assumption | intros _; eexists; split; [eassumption | apply Z.eqb_eq in CHK; rewrite <- CHK; reflexivity]]).
    enr_intro HR. subst. destruct (HG0 eq_refl) as [-> ->]. rauto.
Qed.

Lemma rsim_alloc_slot fuel sc req s t : sheq s t -> rsim eqr (alloc_slot fuel sc req s) (alloc_slot fuel sc req t).
Proof. apply (proj1 (rsim_alloc_mutual fuel)). Qed.
Global Hint Resolve rsim_alloc_slot : rsim.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mres (n : Z) (r r' : option sptr * astate) : Prop :=
  sheq (snd r) (snd r') /\
  match fst r, fst r' with
  | None, None => True
  | Some p, Some p' => exists g idx s0 t0, enr g idx n FUser s0 t0 (p, snd r) (p', snd r')
  | _, _ => False
  end.

(* [comment removed for export] *)
Lemma sq_head_full s t h :
  sheq s t ->
  match mlookup (st_metas t) h with
  | Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
  | _ => true
  end =
  match mlookup (st_metas s) h with
  | Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
  | _ => true
  end.
Proof.
  intros H. pose proof (sheq_MT s t h H) as OR. unfold MT in OR.
  destruct (mlookup (st_metas s) h) as [x|], (mlookup (st_metas t) h) as [x'|]; cbn in OR; try contradiction; [|reflexivity].
  pose proof (erase_meta_inv _ _ OR) as INV. destruct x; [subst x'; reflexivity .. |]. destruct INV as (sl' & -> & _). reflexivity.
Qed.

Lemma enr_sheq g idx n k s t p s1 p' t1 : enr g idx n k s t (p, s1) (p', t1) -> sheq s1 t1.
Proof. intros HR. enr_intro HR. exact HS. Qed.

Ltac mres_leaf :=
  apply rsim_ret; split; [ first [assumption | eapply enr_sheq; eassumption] | cbn [fst snd]; first [exact I | do 4 eexists; eassumption] ].

Lemma rsim_malloc n s t : sheq s t -> rsim (mres n) (malloc n s) (malloc n t).
Proof.
  intros H. unfold malloc. destruct (size_overflows n); [mres_leaf|].
  destruct (MMAP_THRESHOLD <=? n).
  - (* [comment removed for export] *)
    rauto; try mres_leaf.
    rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]). mres_leaf.
  - (* [comment removed for export] *)
    rstep. shall. destruct (nth (Z.to_nat (size_to_class n + 1)) (st_active s) None) as [h|];
      [rewrite (sq_head_full s t h H)|].
    all: match goal with |- rsim _ (bind (match nth (Z.to_nat ?x) _ _ with _ => _ end) _ _) _ => set (sc := x) end.
    all: rauto; try mres_leaf.
    all: rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]); mres_leaf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_in_slots_ge sl base stride i p k : find_in_slots sl base stride i p = Some k -> i <= k.
Proof.
  revert i. induction sl as [|x sl IH]; intros i H; cbn [find_in_slots] in H; [discriminate|].
  destruct (ss_fr x) as [fr|]; [destruct (sptr_eqb _ p); [injection H as <-; lia|]|]; apply IH in H; lia.
Qed.

Lemma find_in_slots_rel sl sl' base stride i p :
  map erase_slot sl = map erase_slot sl' ->
  find_in_slots sl base stride i p = find_in_slots sl' base stride i p
  \/ (exists k, find_in_slots sl base stride i p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) sl slot_junk) = false)
  \/ (exists k, find_in_slots sl' base stride i p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) sl' slot_junk) = false).
Proof.
  revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [left; reflexivity|].
  apply cons_inj in H as [Ex Et]. pose proof (erase_slot_inv _ _ Ex) as [_ FR]. cbn [find_in_slots].
  assert (SH : forall y l k, i + 1 <= k -> nth (Z.to_nat (k - i)) (y :: l) slot_junk = nth (Z.to_nat (k - (i + 1))) l slot_junk).
  { intros y l k Hk. replace (Z.to_nat (k - i)) with (S (Z.to_nat (k - (i + 1)))) by lia. reflexivity. }
  assert (REC : find_in_slots sl base stride (i + 1) p = find_in_slots sl' base stride (i + 1) p
    \/ (exists k, find_in_slots sl base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x :: sl) slot_junk) = false)
    \/ (exists k, find_in_slots sl' base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x' :: sl') slot_junk) = false)).
  { destruct (IH sl' (i + 1) Et) as [E | [(k & Hk & Hik & Hg) | (k & Hk & Hik & Hg)]]; [left; exact E | right; left | right; right];
      exists k; rewrite SH by lia; repeat split; auto; lia. }
  assert (G0 : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl) slot_junk) = false).
  { intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
  assert (G0' : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl') slot_junk) = false).
  { intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
  destruct (ss_fr x) as [fr|] eqn:Fx, (ss_fr x') as [fr'|] eqn:Fx'; try contradiction; [|exact REC].
  destruct FR as (En & Ek & Eo).
  destruct (fr_kind fr) eqn:K.
  - (* [comment removed for export] *)
    destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr)) p).
    + right; left. exists i. split; [reflexivity|]. split; [lia|]. eapply G0; [exact Fx | exact K].
    + destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr')) p).
      * right; right. exists i. split; [reflexivity|]. split; [lia|]. eapply G0'; [exact Fx' | exact Ek].
      * exact REC.
  - (* [comment removed for export] *)
    rewrite (Eo eq_refl). destruct (sptr_eqb _ p); [left; reflexivity | exact REC].
Qed.

Lemma find_frame_in_rel ms mt p :
  mrel ms mt ->
  find_frame_in ms p = find_frame_in mt p
  \/ (exists m k am, find_frame_in ms p = Some (m, k) /\ In (m, MUsed am) ms /\ slot_is_group (nth_slot am k) = false)
  \/ (exists m k am', find_frame_in mt p = Some (m, k) /\ In (m, MUsed am') mt /\ slot_is_group (nth_slot am' k) = false).
Proof.
  unfold mrel. revert mt. induction ms as [|[q x] ms IH]; intros [|[q' x'] mt] H; cbn [map] in H; try discriminate; [left; reflexivity|].
  apply cons_inj in H as [Eqx Et]. unfold ef in Eqx. cbn [fst snd] in Eqx. injection Eqx as Eq Ex. subst q'.
  assert (REC : find_frame_in ms p = find_frame_in mt p
    \/ (exists m k am, find_frame_in ms p = Some (m, k) /\ In (m, MUsed am) ((q, x) :: ms) /\ slot_is_group (nth_slot am k) = false)
    \/ (exists m k am', find_frame_in mt p = Some (m, k) /\ In (m, MUsed am') ((q, x') :: mt) /\ slot_is_group (nth_slot am' k) = false)).
  { destruct (IH mt Et) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]]; [left; exact E | right; left | right; right];
      exists m, k, am; repeat split; auto; right; exact Hin. }
  pose proof (erase_meta_inv _ _ Ex) as INV. cbn [find_frame_in].
  destruct x as [pr0 nx0| |am]; [subst x'; exact REC .. |]. destruct INV as (sl' & -> & ES).
  destruct am as [pr nx mem av frd la sc ml ai sl]. unfold stride_of. cbn [am_slots am_mem am_prev am_next am_avail am_freed am_last am_sc am_maplen am_aidx] in ES |- *.
  match goal with |- context [find_in_slots sl ?b ?st 0 p] =>
    destruct (find_in_slots_rel sl sl' b st 0 p ES) as [E | [(k & Hk & _ & Hg) | (k & Hk & _ & Hg)]] end.
  - rewrite E. destruct (find_in_slots sl' _ _ 0 p); [left; reflexivity | exact REC].
  - right; left. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
  - right; right. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
Qed.

(* [comment removed for export] *)
Definition ffr (s t : astate) (r r' : (sptr * Z) * astate) : Prop :=
  snd r = s /\ snd r' = t /\
  (fst r = fst r'
   \/ (exists am, MT s (fst (fst r)) = Some (MUsed am) /\ slot_is_group (nth_slot am (snd (fst r))) = false)
   \/ (exists am', MT t (fst (fst r')) = Some (MUsed am') /\ slot_is_group (nth_slot am' (snd (fst r'))) = false)).

Lemma rsim_find_frame p s t : sheq s t -> rsim (ffr s t) (find_frame p s) (find_frame p t).
Proof.
  intros H. unfold find_frame. rstep.
  destruct (find_frame_in_rel _ _ p (sheq_metas _ _ H)) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]].
  - rewrite <- E. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity.
  - rewrite Hf. destruct (find_frame_in (st_metas t) p); [|apply rsim_ifail_r]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
    right; left. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_l _ _ H) | exact Hin].
  - rewrite Hf. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
    right; right. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_r _ _ H) | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma rsim_parent_check_fail_l {B C} (R : C * astate -> B -> Prop) m k am s (K : unit -> M C) (y : itree astate B) :
  MT s m = Some (MUsed am) -> slot_is_group (nth_slot am k) = false ->
  rsim R (bind (getm m) (fun amp => bind (mcheck (slot_is_group (nth_slot amp k)) 10) K) s) y.
Proof.
  intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
  unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_l.
Qed.

Lemma rsim_parent_check_fail_r {A C} (R : A -> C * astate -> Prop) m k am t (K : unit -> M C) (x : itree astate A) :
  MT t m = Some (MUsed am) -> slot_is_group (nth_slot am k) = false ->
  rsim R x (bind (getm m) (fun amp => bind (mcheck (slot_is_group (nth_slot amp k)) 10) K) t).
Proof.
  intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
  unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hdr_known_at (s : astate) (g : sptr) (i : Z) : Prop :=
  forall am fr, MT s g = Some (MUsed am) -> ss_fr (nth_slot am i) = Some fr -> fr_off fr = 0 -> ss_hdr (nth_slot am i) <> None.

Lemma rsim_release_slot g i s t :
  sheq s t -> hdr_known_at s g i -> hdr_known_at t g i ->
  rsim eqr (release_slot g i s) (release_slot g i t).
Proof.
  intros H H0s H0t. unfold release_slot. rstep.
  set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
  assert (EN : erase_slot (nth_slot am i) = erase_slot (nth_slot am' i)) by (apply map_erase_nth_slot; exact ES).
  pose proof (erase_slot_inv _ _ EN) as [EH FR].
  apply rsim_setm; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
  match goal with |- erase_slot (match ss_fr ?x with _ => _ end) = erase_slot (match ss_fr ?x' with _ => _ end) =>
    set (sx := x) in *; set (sx' := x') in * end.
  destruct (ss_fr sx) as [fr|] eqn:F, (ss_fr sx') as [fr'|] eqn:F'; try contradiction; [|exact EN].
  destruct FR as (En & Ek & Eo).
  destruct (fr_off fr =? 0) eqn:O, (fr_off fr' =? 0) eqn:O'.
  - reflexivity.
  - apply Z.eqb_eq in O. specialize (H0s _ fr Ms F O). destruct (ss_hdr sx') eqn:Eh'; [reflexivity|]. exfalso. apply H0s. apply (proj2 EH). reflexivity.
  - apply Z.eqb_eq in O'. specialize (H0t _ fr' Mt F' O'). destruct (ss_hdr sx) eqn:Eh; [reflexivity|]. exfalso. apply H0t. apply (proj1 EH). reflexivity.
  - apply erase_slot_rehdr. exact EN.
Qed.

Lemma rsim_nontrivial_free fuel g i s t :
  sheq s t -> rsim eqr (nontrivial_free fuel g i s) (nontrivial_free fuel g i t).
Proof.
  revert g i s t. induction fuel as [|f IH]; intros g i s t H; [cbn; apply rsim_ifail_l|].
  cbn fix beta iota delta [nontrivial_free]. unfold okay_to_free. rauto.
  (* [comment removed for export] *)
  eapply rsim_bind.
  { rcase; [rauto|].
    rbind ltac:(apply rsim_find_frame; assumption).
    destruct HR as (E1 & E2 & CASES); cbn [fst snd] in E1, E2, CASES; subst.
    destruct CASES as [<- | [(am0 & M0 & G0) | (am0 & M0 & G0)]].
    - rauto.
    - eapply rsim_parent_check_fail_l; eassumption.
    - eapply rsim_parent_check_fail_r; eassumption. }
  rintro; rauto.
Qed.
Global Hint Resolve rsim_nontrivial_free : rsim.

Lemma rsim_free p p' g i s t :
  sheq s t ->
  find_frame_in (st_metas s) p = Some (g, i) -> find_frame_in (st_metas t) p' = Some (g, i) ->
  hdr_known_at s g i -> hdr_known_at t g i ->
  rsim eqr (free (Some p) s) (free (Some p') t).
Proof.
  intros H Fs Ft H0s H0t. unfold free.
  eapply (rsim_bind (fun r r' => r = ((g, i), s) /\ r' = ((g, i), t))).
  { unfold find_frame. rstep. rewrite Fs, Ft. apply rsim_ret. split; reflexivity. }
  intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->. cbn beta iota zeta delta [fst snd].
  rstep. rbind ltac:(apply rsim_release_slot; assumption). rauto.
Qed.
End MallocWfSim.

From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfMalloc OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfSim OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.MallocWfTrace.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma user_blocks_frame s p n :
  WF s -> In (p, n) (user_blocks s) ->
  exists g am idx fr, usedX [] s g am /\ 0 <= idx <= am_last am /\ ss_fr (nth_slot am idx) = Some fr /\
    fr_kind fr = FUser /\ fr_n fr = n /\ p = frame_ptr am idx fr.
Proof.
  intros HW Hin. unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]]. cbn [snd] in Hin.
  apply in_flat_map in Hin as [idx [Hidx Hin]]. apply In_zseq in Hidx.
  destruct (ss_fr (nth_slot am idx)) as [fr|] eqn:Efr; [|destruct Hin].
  destruct (fr_kind fr) eqn:Ek; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
  exists g, am, idx, fr. split; [|split; [lia|split; [exact Efr|split; [exact Ek|split; reflexivity]]]].
  apply usedX_intro; [reflexivity|]. apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_safe : forall s n, WF s -> 0 <= n -> safe (malloc n s).
Proof. intros s n HW Hn. eapply itok_safe. apply (malloc_spec U0 s n (fun _ => True) HW Hn). intros; exact I. Qed.

Theorem malloc_reqs_ok : forall s n, WF s -> 0 <= n -> reqs_ok (malloc n s).
Proof. intros s n HW Hn. eapply itok_reqs_ok. apply (malloc_spec U0 s n (fun _ => True) HW Hn). intros; exact I. Qed.

Theorem malloc_wf : forall s n tr p s',
  WF s -> 0 <= n -> yields (malloc n s) tr (p, s') -> WF s'.
Proof.
  intros s n tr p s' HW Hn Hy.
  exact (proj1 (itok_yields _ _ tr (p, s') (malloc_spec U0 s n _ HW Hn (fun r H => H)) Hy)).
Qed.

Lemma U0_nonneg : forall c, 0 <= U0 c.
Proof. intros c. unfold U0. lia. Qed.

Theorem free_safe : forall s p n, WF s -> In (p, n) (user_blocks s) -> safe (free (Some p) s).
Proof.
  intros s p n HW Hin. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  eapply itok_safe. apply (free_spec U0 s g am idx fr (fun _ => True) HW U0_nonneg Hu Hi Hfr Hk). intros; exact I.
Qed.

Theorem free_reqs_ok : forall s p n, WF s -> In (p, n) (user_blocks s) -> reqs_ok (free (Some p) s).
Proof.
  intros s p n HW Hin. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  eapply itok_reqs_ok. apply (free_spec U0 s g am idx fr (fun _ => True) HW U0_nonneg Hu Hi Hfr Hk). intros; exact I.
Qed.

Theorem free_wf : forall s p n tr s',
  WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') -> WF s'.
Proof.
  intros s p n tr s' HW Hin Hy. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  exact (itok_yields _ (fun r => WF (snd r)) tr (tt, s')
           (free_spec U0 s g am idx fr _ HW U0_nonneg Hu Hi Hfr Hk (fun s1 H _ _ => H)) Hy).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_blocks : forall s n tr p s',
  WF s -> 0 <= n -> yields (malloc n s) tr (p, s') ->
  match p with
  | None => user_blocks s' = user_blocks s
  | Some q => exists l1 l2, user_blocks s' = l1 ++ (q, n) :: l2 /\ user_blocks s = l1 ++ l2
              /\ poff q mod UNIT = 0 /\ ~ In q (map fst (user_blocks s))
  end.
Proof.
  intros s n tr p s' HW Hn Hy.
  pose proof (itok_yields _ _ tr (p, s') (malloc_spec U0 s n _ HW Hn (fun r H => H)) Hy) as [HW' Hp]. cbn [fst snd] in HW', Hp.
  destruct p as [q|].
  - destruct Hp as (g & am & idx & off & (Hu & Hi & Hfr & ->) & (l1 & l2 & E1 & E2)).
    rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))).
    exists (map fst l1), (map fst l2). rewrite E1, E2, !map_app. cbn [map fst]. split; [reflexivity|]. split; [reflexivity|]. split.
    + pose proof (used_group_aligned [] None U0 s' HW' _ g am Hu (Nat.le_refl _)) as Hal.
      pose proof (stride_mod16 _ _ _ _ _ _ HW' Hu) as Hst.
      apply Z.div_exact in Hal; [|lia]. apply Z.div_exact in Hst; [|lia].
      rewrite poff_padd, poff_slot_start. unfold UNIT.
      replace (poff (am_mem am) + 16 + stride_of am * idx + 16 * off) with ((poff (am_mem am) / 16 + 1 + stride_of am / 16 * idx + off) * 16) by lia.
      apply Z_mod_mult.
    + pose proof (user_block_ptrs_NoDup s' HW') as ND. rewrite (user_blocks_ublist s' (proj1 (inv_keys HW'))), E1, !map_app in ND. cbn [map fst] in ND.
      apply NoDup_remove_2 in ND. rewrite <- !map_app in ND. rewrite <- !map_app. exact ND.
  - rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))). f_equal. apply ub_same_ublist. exact Hp.
Qed.

Theorem free_blocks : forall s p n tr s',
  WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') ->
  exists l1 l2, user_blocks s = l1 ++ (p, n) :: l2 /\ user_blocks s' = l1 ++ l2.
Proof.
  intros s p n tr s' HW Hin Hy. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & <- & ->).
  pose proof (itok_yields _ (fun r => WF (snd r) /\ exists l1 l2, ublist s = l1 ++ ((frame_ptr am idx fr, fr_n fr), (g, idx)) :: l2 /\ ublist (snd r) = l1 ++ l2)
                tr (tt, s') (free_spec U0 s g am idx fr _ HW U0_nonneg Hu Hi Hfr Hk (fun s1 H _ B => conj H B)) Hy) as [HW' (l1 & l2 & E1 & E2)].
  cbn [snd] in HW', E2.
  rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))). exists (map fst l1), (map fst l2).
  rewrite E1, E2, !map_app. cbn [map fst]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma WF_sheq s t : WF s -> shape_eq s t -> sheq s t.
Proof. intros HW E. split; [exact E | exact (proj1 (inv_keys HW))]. Qed.

Lemma frames_inv s g am i fr :
  WF s -> In (g, am, i, fr) (frames s) ->
  usedX [] s g am /\ 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr.
Proof.
  intros HW Hin. unfold frames in Hin. apply in_flat_map in Hin as [[g0 am0] [Hg Hin]].
  apply in_flat_map in Hin as [j [Hj Hin]]. apply In_zseq in Hj.
  destruct (ss_fr (nth_slot am0 j)) as [fr0|] eqn:Efr; [|destruct Hin]. destruct Hin as [E|[]]. injection E as -> -> -> ->.
  split; [|split; [lia | exact Efr]].
  apply usedX_intro; [reflexivity|]. apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hg.
Qed.

Lemma frames_intro s g am i fr :
  WF s -> MT s g = Some (MUsed am) -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  In (g, am, i, fr) (frames s).
Proof.
  intros HW Mg Hi Hfr. unfold frames. apply in_flat_map. exists (g, am). split.
  - apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Mg.
  - apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hfr. left. reflexivity.
Qed.

Theorem malloc_tsim : forall s t n,
  WF s -> WF t -> shape_eq s t -> 0 <= n ->
  tsim (fun (x : option sptr * astate) (y : option sptr * astate) =>
          shape_eq (snd x) (snd y) /\
          match fst x, fst y with
          | None, None => True
          | Some p, Some p' =>
              exists g am am' i fr fr',
                In (g, am, i, fr) (frames (snd x)) /\ In (g, am', i, fr') (frames (snd y)) /\
                p = frame_ptr am i fr /\ p' = frame_ptr am' i fr'
          | _, _ => False
          end)
       (malloc n s) (malloc n t).
Proof.
  intros s t n HWs HWt E Hn.
  pose proof (malloc_spec U0 s n _ HWs Hn (fun r Hr => Hr)) as Ts.
  pose proof (malloc_spec U0 t n _ HWt Hn (fun r Hr => Hr)) as Tt.
  pose proof (rsim_malloc n s t (WF_sheq s t HWs E) _ _ Ts Tt) as SIM.
  eapply tsim_mono; [|exact SIM]. cbn beta. intros [p s'] [p' t'] ([HS RES] & [HW' _] & [HWt' _]). cbn [fst snd] in *.
  split; [exact (proj1 HS)|].
  destruct p as [p|], p' as [p'|]; try exact RES.
  destruct RES as (g & idx & s0 & t0 & HR). enr_intro HR.
  match type of E1 with s' = set_metas (mupdate _ _ (MUsed ?a)) _ => set (am1 := a) in E1 end.
  match type of E2 with t' = set_metas (mupdate _ _ (MUsed ?a)) _ => set (am1' := a) in E2 end.
  assert (M1 : MT s' g = Some (MUsed am1)) by (rewrite E1; unfold MT; cbn [st_metas set_metas]; apply mlookup_mupdate_same).
  assert (M1' : MT t' g = Some (MUsed am1')) by (rewrite E2; unfold MT; cbn [st_metas set_metas]; apply mlookup_mupdate_same).
  pose proof (inv_groups HW' g am1 (usedX_intro [] s' g am1 eq_refl M1)) as ((_ & _ & Glen & _) & _).
  pose proof (inv_groups HWt' g am1' (usedX_intro [] t' g am1' eq_refl M1')) as ((_ & _ & Glen' & _) & _).
  subst am1 am1'. unfold upd_slot in Glen, Glen'. cbn [am_slots am_last am_set_slots] in Glen, Glen'. rewrite length_lupd in Glen, Glen'.
  exists g. match type of M1 with _ = Some (MUsed ?a) => exists a end. match type of M1' with _ = Some (MUsed ?a) => exists a end.
  exists idx, (mkFrame off n FUser), (mkFrame off' n FUser).
  split; [|split; [|split; [rewrite P1; reflexivity | rewrite P2; reflexivity]]].
  - eapply frames_intro; [exact HW' | exact M1 | cbn [am_last upd_slot am_set_slots]; exact Hidx |].
    rewrite nth_slot_upd_slot; [rewrite Z.eqb_refl; reflexivity | lia | lia | cbn [am_slots]; lia].
  - eapply frames_intro; [exact HWt' | exact M1' | cbn [am_last upd_slot am_set_slots]; exact Hidx |].
    rewrite nth_slot_upd_slot; [rewrite Z.eqb_refl; reflexivity | lia | lia | cbn [am_slots]; lia].
Qed.

Lemma sheq_slot s t g am am' i :
  sheq s t -> MT s g = Some (MUsed am) -> MT t g = Some (MUsed am') ->
  erase_slot (nth_slot am i) = erase_slot (nth_slot am' i).
Proof.
  intros H Ms Mt. pose proof (sheq_MT s t g H) as OR. rewrite Ms, Mt in OR. cbn [orel] in OR.
  pose proof (erase_meta_inv _ _ OR) as (sl' & E & ES). injection E as ->. unfold nth_slot. cbn [am_slots]. apply map_erase_nth. exact ES.
Qed.

Lemma WF_hdr_known s g i : WF s -> hdr_known_at s g i.
Proof.
  intros HW am fr Mg Hfr Hoff.
  assert (Hu : usedX [] s g am) by (apply usedX_intro; [reflexivity | exact Mg]).
  pose proof (inv_groups HW g am Hu) as ((Glast & _ & Glen & _) & _ & Gsl & _).
  destruct (Z_le_dec 0 i) as [Hi0|Hi0]; [destruct (Z_le_dec i (am_last am)) as [Hi1|Hi1]|].
  - pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & _ & S4). rewrite (S4 Hoff). discriminate.
  - unfold nth_slot in Hfr. rewrite nth_overflow in Hfr; [discriminate|]. rewrite Glen. lia.
  - pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). unfold nth_slot in *. replace (Z.to_nat i) with (Z.to_nat 0) in * by lia.
    rewrite Hfr in S3. destruct S3 as (_ & _ & _ & S4). rewrite (S4 Hoff). discriminate.
Qed.

Theorem free_tsim : forall s t g am am' i fr fr',
  WF s -> WF t -> shape_eq s t ->
  In (g, am, i, fr) (frames s) -> In (g, am', i, fr') (frames t) -> fr_kind fr = FUser ->
  tsim (fun (x y : unit * astate) => shape_eq (snd x) (snd y))
       (free (Some (frame_ptr am i fr)) s) (free (Some (frame_ptr am' i fr')) t).
Proof.
  intros s t g am am' i fr fr' HWs HWt E Fs Ft Hk.
  pose proof (WF_sheq s t HWs E) as SH.
  destruct (frames_inv s g am i fr HWs Fs) as (Hu & Hi & Hfr). destruct (frames_inv t g am' i fr' HWt Ft) as (Hu' & Hi' & Hfr').
  assert (Hk' : fr_kind fr' = FUser).
  { pose proof (sheq_slot s t g am am' i SH (proj1 (usedX_MT _ _ _ _ Hu)) (proj1 (usedX_MT _ _ _ _ Hu'))) as EN.
    apply erase_slot_inv in EN as [_ FR]. rewrite Hfr, Hfr' in FR. destruct FR as (_ & Ek & _). rewrite Ek. exact Hk. }
  pose proof (free_spec U0 s g am i fr (fun r => WF (snd r)) HWs U0_nonneg Hu Hi Hfr Hk (fun s1 H _ _ => H)) as Ts.
  pose proof (free_spec U0 t g am' i fr' (fun r => WF (snd r)) HWt U0_nonneg Hu' Hi' Hfr' Hk' (fun s1 H _ _ => H)) as Tt.
  assert (SIM : rsim eqr (free (Some (frame_ptr am i fr)) s) (free (Some (frame_ptr am' i fr')) t)).
  { apply (rsim_free _ _ g i); [exact SH | | | apply WF_hdr_known; exact HWs | apply WF_hdr_known; exact HWt].
    - exact (find_frame_in_spec [] None U0 s HWs g am i fr Hu Hi Hfr).
    - exact (find_frame_in_spec [] None U0 t HWt g am' i fr' Hu' Hi' Hfr'). }
  eapply tsim_mono; [|exact (SIM _ _ Ts Tt)]. cbn beta. intros [[] s'] [[] t'] ([_ HS] & _ & _). exact (proj1 HS).
Qed.

Lemma mrel_user_blocks_sizes ms mt :
  mrel ms mt ->
  map snd (flat_map (fun gm : sptr * ameta =>
    let am := snd gm in
    flat_map (fun i => match ss_fr (nth_slot am i) with
                       | Some fr => match fr_kind fr with
                                    | FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
                                    | FGroup => []
                                    end
                       | None => []
                       end) (zseq 0 (am_last am + 1)))
    (flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) ms)) =
  map snd (flat_map (fun gm : sptr * ameta =>
    let am := snd gm in
    flat_map (fun i => match ss_fr (nth_slot am i) with
                       | Some fr => match fr_kind fr with
                                    | FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
                                    | FGroup => []
                                    end
                       | None => []
                       end) (zseq 0 (am_last am + 1)))
    (flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) mt)).
Proof.
  unfold mrel. revert mt. induction ms as [|[q x] ms IH]; intros [|[q' x'] mt] H; cbn [map flat_map] in H |- *; try discriminate; [reflexivity|].
  apply cons_inj in H as [Eqx Et]. unfold ef in Eqx. cbn [fst snd] in Eqx. injection Eqx as Eq Ex. subst q'.
  pose proof (erase_meta_inv _ _ Ex) as INV.
  destruct x as [pr0 nx0| |am]; [subst x'; cbn [flat_map app]; apply IH; exact Et .. |].
  destruct INV as (sl' & -> & ES). cbn [flat_map app]. rewrite !map_app. f_equal; [|apply IH; exact Et]. cbn [snd].
  destruct am as [pr nx mem av frd la sc ml ai sl]. cbn [am_last am_slots am_prev am_next am_mem am_avail am_freed am_sc am_maplen am_aidx] in ES |- *.
  induction (zseq 0 (la + 1)) as [|i is IHi]; cbn [flat_map]; [reflexivity|]. rewrite !map_app. f_equal; [|exact IHi].
  pose proof (map_erase_nth sl sl' (Z.to_nat i) ES) as EN. apply erase_slot_inv in EN as [_ FR]. unfold nth_slot. cbn [am_slots].
  destruct (ss_fr (nth (Z.to_nat i) sl slot_junk)) as [fr|], (ss_fr (nth (Z.to_nat i) sl' slot_junk)) as [fr'|]; try contradiction; [|reflexivity].
  destruct FR as (En & Ek & _). rewrite Ek. destruct (fr_kind fr); cbn; [rewrite En|]; reflexivity.
Qed.

Theorem shape_eq_erases_only_offsets : forall s t,
  shape_eq s t ->
  st_regions s = st_regions t /\ st_areas s = st_areas t /\ st_active s = st_active t /\
  st_usage s = st_usage t /\ st_brk s = st_brk t /\ map fst (st_metas s) = map fst (st_metas t) /\
  footprint s = footprint t /\ map snd (user_blocks s) = map snd (user_blocks t).
Proof.
  intros s t E. pose proof (proj1 (sq_fields s t) E) as F.
  destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eact & Eus & _ & _ & _ & Ebrk & Ereg & Ear & EM).
  split; [exact Ereg|]. split; [exact Ear|]. split; [exact Eact|]. split; [exact Eus|]. split; [exact Ebrk|].
  split; [apply mrel_keys; exact EM|]. split.
  - unfold footprint, region_of. rewrite Ear, Ereg. reflexivity.
  - unfold user_blocks, used_metas. apply mrel_user_blocks_sizes. exact EM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_regions : forall s n tr p s',
  WF s -> 0 <= n -> yields (malloc n s) tr (p, s') ->
  same_shape_regions (st_regions s') (regions_after (st_regions s) tr).
Proof.
  intros s n tr p s' HW Hn Y. apply same_shape_shp.
  exact (rt_yields _ _ _ tr (p, s') (rt_malloc (st_regions s) n s eq_refl) (malloc_reqs_ok s n HW Hn) Y).
Qed.

Theorem free_regions : forall s p n tr s',
  WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') ->
  same_shape_regions (st_regions s') (regions_after (st_regions s) tr).
Proof.
  intros s p n tr s' HW Hin Y. apply same_shape_shp.
  exact (rt_yields _ _ _ tr (tt, s') (rt_free (st_regions s) (Some p) s eq_refl) (free_reqs_ok s p n HW Hin) Y).
Qed.
