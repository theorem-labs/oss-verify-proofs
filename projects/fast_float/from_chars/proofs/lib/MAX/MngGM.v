(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngImage MngSurgery MngNtfC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma key_once_inv : forall X R U s g, Inv X R U s -> In g (keys s) ->
  filter (fun q => sptr_eqb q g) (all_slots (st_areas s)) = [g].
Proof.
  intros X R U s g HW Hg. apply filter_single; [apply sptr_eqb_eq | |].
  - pose proof (inv_areas HW) as (AND & AOK & _). apply NoDup_all_slots; [exact AND|].
    intros a Ha. destruct (AOK a Ha) as (r & o & rg & E & Ho & _). exists r, o. auto.
  - pose proof (inv_keys HW) as (_ & KP & _). destruct (KP g Hg) as (a & k & Ha & Hk & E).
    unfold all_slots. apply in_flat_map. exists a. split; [exact Ha|]. apply In_aslots.
    assert (Hh : handed s a <= METAS_PER_AREA) by (unfold handed; destruct (sptr_eqb _ _); pose proof (proj2 (proj2 (proj2 (proj2 (inv_keys HW))))); lia).
    exists (Z.to_nat k). split; [unfold METAS_PER_AREA in Hh; lia|]. unfold aslot. rewrite Z2Nat.id by lia. exact E.
Qed.

Lemma KS_of_Inv : forall X R U s, Inv X R U s -> KS s.
Proof. intros X R U s HW. split; [exact (proj1 (inv_keys HW)) | intros q Hq; exact (key_once_inv X R U s q HW Hq)]. Qed.

Theorem get_meta_ok_inv : forall X R U s g am i fr,
  Inv X R U s -> usedX X s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  let p := frame_ptr am i fr in
  In (MCell (LMem (padd p (-4))) 1 (VZ 0)) (image s) /\
  In (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))) (image s) /\
  In (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))) (image s) /\
  In (MCell (LMem (am_mem am)) 8 (VP g)) (image s) /\
  In (MCell (LMem (padd g META_mem)) 8 (VP (am_mem am))) (image s) /\
  In (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am))) (image s) /\
  In (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) (image s) /\
  In (MCell (LMem (padd g META_bits)) 8 (VZ (meta_bits am))) (image s) /\
  padd p (- UNIT * hdr_off16 am i fr - UNIT) = am_mem am /\
  (exists a k, In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * k)
               /\ In (MCell (LMem a) 8 VSec) (image s) /\ In (MCell (LCtx CTX_secret) 8 VSec) (image s)) /\
  Z.land (hdr_byte3 am i fr) 31 = i /\
  get_meta_asserts p (am_mem am) (view_of s g am i fr) = true /\
  find_frame_in (st_metas s) p = Some (g, i).
Proof.
  intros X R U s g am i fr HW Hu Hi Hf p.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  assert (Hg : In (g, am) (used_metas s)) by (apply (used_metas_iff s g am (proj1 (inv_keys HW))); exact Mg).
  assert (HK : KS s) by (split; [exact (proj1 (inv_keys HW)) | intros q Hq; exact (key_once_inv X R U s q HW Hq)]).
  pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hf in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & FG) & Hhdr).
  pose proof (stride_mod16 _ _ _ _ _ _ HW Hu) as Hst16.
  pose proof (used_group_aligned X R U s HW _ g am Hu (Nat.le_refl _)) as Hal16.
  assert (Hrsv : 0 <= rsv_code am fr) by (unfold rsv_code; destruct (5 <=? _); lia).
  assert (Hb3 : exists m, 0 <= m /\ hdr_byte3 am i fr = i + 32 * m).
  { unfold hdr_byte3. destruct (fr_kind fr); [exists (rsv_code am fr) | exists 6]; lia. }
  assert (Hland : Z.land (hdr_byte3 am i fr) 31 = i) by (destruct Hb3 as (m & Hm & ->); apply land31; lia).
  (* [comment removed for export] *)
  assert (HDR : In (MCell (LMem (padd p (-4))) 1 (VZ 0)) (image s) /\
                In (MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr))) (image s) /\
                In (MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))) (image s)).
  { destruct (Z.eq_dec (fr_off fr) 0) as [E0 | E0].
    - assert (Ep : p = slot_start am i) by (subst p; unfold frame_ptr; rewrite E0, Z.mul_0_r; apply padd_0).
      rewrite Ep. specialize (Hhdr E0).
      split; [|split]; eapply In_image_group; try exact Hg; apply (In_group_slot g am i); try exact Hi; unfold slot_cells; rewrite ?Hhdr.
      + left. reflexivity.
      + apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
      + apply in_app_iff. right. apply in_app_iff. left. right. left. reflexivity.
    - split; [|split]; eapply In_image_group; try exact Hg; apply (In_group_slot g am i); try exact Hi; unfold slot_cells; rewrite Hf;
        replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0);
        apply in_app_iff; right; apply in_app_iff; right; cbn; auto. }
  destruct HDR as (C1 & C2 & C3).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [eapply In_image_group; [exact Hg|]; left; reflexivity|].
  split; [apply (msc_key_in_image s g _ _ HK Mg); cbn; auto 10|].
  split; [apply (msc_key_in_image s g _ _ HK Mg); cbn; auto 10|].
  split; [apply (msc_key_in_image s g _ _ HK Mg); cbn; auto 10|].
  split; [apply (msc_key_in_image s g _ _ HK Mg); cbn; auto 10|].
  split.
  { subst p. unfold frame_ptr, hdr_off16. apply sptr_eq_parts.
    - rewrite !prid_padd, prid_slot_start. reflexivity.
    - rewrite !poff_padd, poff_slot_start. unfold UNIT.
      pose proof Hst16 as Hst'. apply Z.div_exact in Hst'; [|lia].
      assert (Hdiv0 : stride_of am * i / 16 = stride_of am / 16 * i).
      { rewrite Hst' at 1. rewrite <- Z.mul_assoc, (Z.mul_comm 16), Z_div_mult by lia. reflexivity. }
      rewrite Hdiv0. lia. }
  split.
  { pose proof (inv_keys HW) as (ND & KP & _ & _ & Hcnt). destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk & Eg).
    exists a, k. split; [exact Ha|]. split; [unfold handed in Hk; destruct (sptr_eqb a _); lia|]. split; [exact Eg|]. split.
    - unfold image. apply in_app_iff. right. apply in_app_iff. left. apply (In_areas_cells_intro s (st_areas s) a _ Ha).
      intros next. unfold area_cells. left. reflexivity.
    - assert (Hid : st_init_done s = true).
      { destruct (st_init_done s) eqn:E; [reflexivity|]. exfalso.
        pose proof (inv_ctx HW) as C. unfold ctx_ok in C.
        destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit). destruct (Hinit E) as (Em & _).
        unfold MT in Mg. rewrite Em in Mg. cbn in Mg. discriminate. }
      unfold image. apply in_app_iff. left. unfold ctx_cells. rewrite Hid. left. reflexivity. }
  split; [exact Hland|].
  split; [|subst p; apply (find_frame_in_spec X R U s HW g am i fr Hu Hi Hf)].
  (* [comment removed for export] *)
  assert (Halloc : Z.testbit (am_avail am) i = false /\ Z.testbit (am_freed am) i = false).
  { unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) i), (Z.testbit (am_freed am) i); cbn in Hal; try discriminate; auto. }
  destruct Halloc as [Ha0 Hf0].
  assert (Hp16 : poff p mod 16 = 0).
  { subst p. unfold frame_ptr. rewrite poff_padd, poff_slot_start. unfold UNIT.
    pose proof Hal16 as Hal'. pose proof Hst16 as Hst'. apply Z.div_exact in Hal'; [|lia]. apply Z.div_exact in Hst'; [|lia].
    replace (poff (am_mem am) + 16 + stride_of am * i + 16 * fr_off fr) with ((poff (am_mem am) / 16 + 1 + stride_of am / 16 * i + fr_off fr) * 16) by lia.
    apply Z_mod_mult. }
  unfold get_meta_asserts, view_of. cbn [gm_p4 gm_p3 gm_off16 gm_meta gm_mem gm_avail gm_freed gm_last gm_sc gm_maplen gm_area_check].
  rewrite Hp16, Hland, sptr_eqb_refl, Ha0, Hf0. cbn [Z.eqb negb andb].
  replace (i <=? am_last am) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  assert (Hdiv : stride_of am * i / 16 * 16 = stride_of am * i).
  { pose proof Hst16 as Hst'. apply Z.div_exact in Hst'; [|lia].
    rewrite Hst' at 1. rewrite <- Z.mul_assoc, (Z.mul_comm 16), Z_div_mult by lia. lia. }
  apply andb_true_intro. split.
  - (* [comment removed for export] *)
    destruct Gcl as [(C63 & _) | (Csc & CN1 & C26 & Cspan)].
    + rewrite C63. reflexivity.
    + replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold hdr_off16. set (sz := znth (am_sc am) size_classes).
      assert (Hcs : class_size (am_sc am) = 16 * sz) by reflexivity.
      pose proof (class_size_bounds (am_sc am) Csc) as [S16 Smax].
      assert (A : sz * i <= stride_of am * i / UNIT + fr_off fr).
      { destruct (Z_lt_dec (stride_of am) (class_size (am_sc am))) as [Hlt|Hge].
        - destruct (CN1 Hlt) as [Hl0 _]. assert (i = 0) as -> by (clear - Hl0 Hi; lia). rewrite !Z.mul_0_r. change (0 / UNIT) with 0. lia.
        - unfold UNIT. assert (sz * i * 16 <= stride_of am * i / 16 * 16) by (rewrite Hdiv; nia). lia. }
      assert (B : stride_of am * i / UNIT + fr_off fr < sz * (i + 1)).
      { destruct (Z.eq_dec (am_last am) 0) as [Hl0 | Hl0].
        - assert (i = 0) as -> by (clear - Hl0 Hi; lia). rewrite !Z.mul_0_r. change (0 / UNIT) with 0. rewrite Z.add_0_l, Z.add_0_l, Z.mul_1_r.
          destruct (Z.eq_dec (am_maplen am) 0) as [Hm0 | Hm0].
          + assert (Es : stride_of am = class_size (am_sc am)) by (unfold stride_of; rewrite Hm0, Hl0; reflexivity).
            rewrite Es, Hcs in Bf. unfold UNIT, IB in Bf. lia.
          + destruct (Gmp ltac:(lia)) as (r & rg & _ & _ & _ & _ & _ & _ & Hpr). specialize (Hpr Hl0 ltac:(lia)).
            assert (Es : stride_of am = am_maplen am * 4096 - UNIT).
            { unfold stride_of. rewrite Hl0. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
            destruct (Z_le_dec 28 (am_sc am)) as [H28 | H28].
            * pose proof (class_size_mono 28 (am_sc am) ltac:(lia) H28 ltac:(lia)) as M28. change (class_size 28) with (16 * 292) in M28. lia.
            * destruct (Z_le_dec (am_sc am) 26) as [H26 | H26]; [destruct (C26 H26); lia|].
              assert (am_sc am = 27) as E27 by lia. rewrite E27 in *. change (class_size 27) with 4080 in Hcs, Hpr. cbn in Hpr.
              change (page_round (4080 + UNIT)) with 4096 in Hpr. unfold PGSZ, UNIT, IB in *. subst sz. change (znth 27 size_classes) with 255. lia.
        - assert (Es : stride_of am = class_size (am_sc am)).
          { unfold stride_of. destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
          rewrite Es, Hcs in Bf |- *. unfold UNIT, IB in *.
          replace (16 * sz * i) with (sz * i * 16) by lia. rewrite Z_div_mult by lia. nia. }
      rewrite (proj2 (Z.leb_le _ _) A), (proj2 (Z.ltb_lt _ _) B). reflexivity.
  - (* [comment removed for export] *)
    unfold implb. destruct (0 <? am_maplen am) eqn:Em; [|reflexivity]. cbn [negb orb]. apply Z.ltb_lt in Em.
    destruct (Gmp Em) as (r & rg & _ & _ & _ & _ & _ & Hfit & _).
    unfold hdr_off16. apply Z.leb_le.
    assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    unfold UNIT, IB, PGSZ in *.
    assert (stride_of am * i / 16 * 16 + 16 * fr_off fr <= am_maplen am * 4096 - 20) by (rewrite Hdiv; lia).
    assert (am_maplen am * 4096 / 16 = am_maplen am * 256) by (replace (am_maplen am * 4096) with (am_maplen am * 256 * 16) by lia; apply Z_div_mult; lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma mask32 : forall x, 0 <= x -> (forall j, 32 <= j -> Z.testbit x j = false) -> 0 <= x <= 2^32 - 1.
Proof.
  intros x Hx Hb. split; [exact Hx|]. assert (x < 2^32); [|lia].
  destruct (Z.eq_dec x 0) as [->|Hnz]; [lia|]. apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
  destruct (Z.lt_ge_cases (Z.log2 x) 32) as [Hl|Hg]; [exact Hl|]. exfalso.
  pose proof (Z.bit_log2 x ltac:(lia)) as Hbit. rewrite Hb in Hbit by lia. discriminate.
Qed.

Lemma masks_range_inv : forall X R U s g am, Inv X R U s -> usedX X s g am ->
  0 <= am_avail am <= 2^32 - 1 /\ 0 <= am_freed am <= 2^32 - 1 /\ 0 <= am_last am <= 31 /\ 0 <= am_sc am <= 63 /\ 0 <= am_maplen am.
Proof.
  intros X R U s g am HI Hu. pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  split; [apply mask32; [exact Gav | intros j Hj; exact (proj1 (Gabove j ltac:(lia)))]|].
  split; [apply mask32; [exact Gfrn | intros j Hj; exact (proj2 (Gabove j ltac:(lia)))]|].
  split; [exact Glast|]. split; [destruct Gcl as [(C & _) | (C & _)]; lia | exact Gml].
Qed.

Lemma meta_bits_range_inv : forall X R U s g am L, Inv X R U s -> usedX X s g am -> layout_ok L s -> 0 <= meta_bits am <= 2^64 - 1.
Proof.
  intros X R U s g am L HI Hu HL. destruct (masks_range_inv X R U s g am HI Hu) as (_ & _ & Rl & Rs & Rm).
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & _ & Gmp & _).
  destruct (Z.eq_dec (am_maplen am) 0) as [E0|E0]; [unfold meta_bits; rewrite E0; lia|].
  destruct (Gmp ltac:(lia)) as (r & rg & _ & Hr & Hk & Hl & Hlen & _).
  pose proof (footprint_region_In s r rg Hr Hk Hl) as F. pose proof HL as (_ & _ & _ & Lrng).
  pose proof (Lrng _ F) as (B1 & B2). cbn [crange fst snd] in B1, B2. rewrite Hlen in B2. unfold PGSZ in B2.
  unfold meta_bits. lia.
Qed.
