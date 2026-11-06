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

Module MallocWfSlot.
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
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_le_l a b : 0 <= a -> Z.land a b <= a.
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

Lemma fold_off_le slack off0 : 0 <= off0 -> 0 <= slack -> fold_off slack off0 <= off0.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma am_slots_upd_slot_length am i x : length (am_slots (upd_slot am i x)) = length (am_slots am).
Proof. unfold upd_slot. cbn. apply length_lupd. Qed.

(* [comment removed for export] *)
Lemma ring_facts X R U s g am :
  Inv X R U s -> usedX X s g am -> am_sc am < 48 -> 0 <= am_sc am ->
  ((am_prev am, am_next am) = (None, None) -> am_avail am = 0 /\ am_freed am = 0) /\
  (am_avail am <> 0 -> active_hd s (am_sc am) = Some g) /\
  ((am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) <> Some g ->
   (forall i, R <> Some (g, i)) -> am_freed am <> 0).
Proof.
  intros HI Hu Hsc Hsc0. destruct (inv_rings HI) as (_ & A & _).
  destruct (A (am_sc am) ltac:(lia)) as (ms & Rg & Mem & Full & Q1 & Q2).
  split; [|split].
  - intros HL. apply (Full g am Hu eq_refl). intros Hin. apply (Mem g am Hu eq_refl) in Hin. exact (Hin HL).
  - intros Hav. exact (Q1 g am Hu eq_refl Hav).
  - intros HL Hnh HnR. apply (Q2 g am Hu eq_refl); [|exact Hnh|exact HnR]. apply (Mem g am Hu eq_refl). exact HL.
Qed.

Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma enframe_spec X U s g idx n ctr k am (Q : sptr * astate -> Prop) :
  Inv X (Some (g, idx)) U s -> usedX X s g am ->
  0 <= n -> n <= stride_of am - IB -> 0 <= ctr ->
  (k = FGroup -> n = stride_of am - IB) ->
  (am_sc am = 63 -> k = FUser /\ MMAP_THRESHOLD <= n /\ am_maplen am * PGSZ < n + UNIT + IB + PGSZ) ->
  (am_sc am < 48 -> (am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) = Some g) ->
  (forall off s' hdr,
     0 <= off <= 255 -> UNIT * off + n <= stride_of am - IB -> (k = FGroup -> off = 0) ->
     s' = upd_meta g (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n k))))) s ->
     Inv X None U s' ->
     Q (padd (slot_start am idx) (UNIT * off), s')) ->
  itok (enframe g idx n ctr k s) Q.
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  - (* [comment removed for export] *) unfold masks_ok. subst am1. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
    repeat (split; [assumption|]). exact Gfra.
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & C2 & C3 & C4)].
    + left. repeat (split; [assumption|]). right.
      replace idx with 0 in * by lia. exists fr. rewrite NS by lia. rewrite Z.eqb_refl. subst sl1 fr. cbn.
      destruct (H63 C1) as (-> & Hbig & Hml'). auto.
    + right. repeat (split; [assumption|]). exact C4.
  - intros p i Hp. split; intros HH; [discriminate | injection HH; intros; subst; exfalso; exact (Hp eq_refl)].
  - intros i HH. discriminate.
  - intros Hsc HL. apply (proj1 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia))). exact HL.
  - intros Hsc Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia)))). exact Hav.
  - intros Hsc HL Hnh _. exfalso. apply Hnh. apply Hhdg; assumption.
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
  - intros Hai. exact Hai.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Inv_masks X R R' U s g am0 av fr ai :
  Inv X R U s -> usedX X s g am0 -> 0 <= am_sc am0 < 48 ->
  let am1 := am_set_aidx ai (am_set_freed fr (am_set_avail av am0)) in
  masks_ok am1 ->
  (* [comment removed for export] *)
  (forall i, 0 <= i <= am_last am0 -> allocated am1 i = allocated am0 i \/
     (R = None /\ R' = Some (g, i) /\ allocated am0 i = false /\ allocated am1 i = true) \/
     (R = Some (g, i) /\ R' = None /\ allocated am0 i = true /\ allocated am1 i = false)) ->
  (forall p i, (p, i) <> (g, match R' with Some (_, j) => j | None => -1 end) ->
               (p, i) <> (g, match R with Some (_, j) => j | None => -1 end) ->
               (R = Some (p, i) <-> R' = Some (p, i))) ->
  (forall i, R' = Some (g, i) -> 0 <= i <= am_last am0 /\ ss_fr (nth_slot am0 i) = None /\ allocated am1 i = true) ->
  (forall i, R = Some (g, i) -> R' = Some (g, i) \/ allocated am1 i = false) ->
  (* [comment removed for export] *)
  ((am_prev am0, am_next am0) = (None, None) -> av = 0 /\ fr = 0) ->
  (av <> 0 -> active_hd s (am_sc am0) = Some g) ->
  ((am_prev am0, am_next am0) <> (None, None) -> active_hd s (am_sc am0) <> Some g -> (forall i, R' <> Some (g, i)) -> fr <> 0) ->
  (ai < am_last am0 -> forall p a, usedX X s p a -> p <> g -> am_sc a = am_sc am0 -> ~ am_aidx a < am_last a) ->
  (* [comment removed for export] *)
  (stride_of am0 < class_size (am_sc am0) -> allocated am1 0 = true) ->
  (* [comment removed for export] *)
  (ai < am_last am0 -> am_aidx am0 < am_last am0) ->
  Inv X R' U (upd_meta g (MUsed am1) s).
Proof.
  intros HI Hu Hsc am1 Hm Hal HRo HRg HRoff Hfull HR1 HR2 Hpart HN1 HPcg.
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
  - exact HPcg.
Qed.

(* [comment removed for export] *)
Lemma allocated_eq am av fr ai i :
  allocated (am_set_aidx ai (am_set_freed fr (am_set_avail av am))) i = negb (Z.testbit (Z.lor av fr) i).
Proof. reflexivity. Qed.

Lemma allocated_am am i : allocated am i = negb (Z.testbit (Z.lor (am_avail am) (am_freed am)) i).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma take_bit_Inv X U s g am :
  Inv X None U s -> usedX X s g am -> 0 <= am_sc am < 48 ->
  active_hd s (am_sc am) = Some g -> am_avail am <> 0 ->
  let first := lowbit (am_avail am) in
  let k := ctz32 first in
  0 <= k <= am_aidx am /\ first = bit k /\ Z.testbit (am_avail am) k = true /\
  Inv X (Some (g, k)) U (upd_meta g (MUsed (am_set_avail (am_avail am - first) am)) s).
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
  - (* [comment removed for export] *)
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
  - intros Hai. exact Hai.
Qed.

(* [comment removed for export] *)
Lemma activate_Inv X U s g am :
  Inv X None U s -> usedX X s g am -> 0 <= am_sc am < 48 ->
  active_hd s (am_sc am) = Some g -> am_avail am = 0 ->
  let act := ones (am_aidx am) in
  Inv X None U (upd_meta g (MUsed (am_set_avail (Z.land (am_freed am) act) (am_set_freed (Z.ldiff (am_freed am) act) am))) s).
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
  - intros Hai. exact Hai.
Qed.

(* [comment removed for export] *)
Lemma extend_aidx_Inv X U s g am ai :
  Inv X None U s -> usedX X s g am -> 0 <= am_sc am < 48 ->
  active_hd s (am_sc am) = Some g -> am_aidx am <= ai <= am_last am ->
  Inv X None U (upd_meta g (MUsed (am_set_aidx ai am)) s).
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
  - intros Hai'. lia.
Qed.

(* [comment removed for export] *)
Lemma nth_In_range (l : list Z) k lo hi :
  (forall u, In u l -> lo <= u <= hi) -> lo <= 0 <= hi -> lo <= nth k l 0 <= hi.
Proof.
  intros H H0. destruct (nth_error l k) as [x|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). apply H. eapply nth_error_In. exact E.
  - rewrite nth_overflow; [exact H0|]. apply nth_error_None. exact E.
Qed.

Lemma decay_bounces_spec X R U s sc (Q : unit * astate -> Prop) :
  Inv X R U s -> (forall s', Inv X R U s' -> st_metas s' = st_metas s -> st_active s' = st_active s ->
                    st_regions s' = st_regions s -> st_usage s' = st_usage s -> st_mmap_counter s' = st_mmap_counter s -> Q (tt, s')) ->
  itok (decay_bounces sc s) Q.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allzero (X : list sptr) (s : astate) (sc : Z) : Prop :=
  forall g am, usedX X s g am -> am_sc am = sc -> am_avail am = 0.

(* [comment removed for export] *)
Definition ta_post (X : list sptr) (U : Z -> Z) (s : astate) (sc first : Z) (s' : astate) : Prop :=
  first <> 0 /\
  exists g am, Inv X (Some (g, ctz32 first)) U s' /\ active_hd s' sc = Some g /\
    usedX X s' g am /\ am_sc am = sc /\ class_size sc <= stride_of am /\
    0 <= ctz32 first <= am_last am /\
    (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) /\ ub_same s s'.

(* [comment removed for export] *)
Lemma avail_bit_not_undersized X R U s g am i :
  Inv X R U s -> usedX X s g am -> 0 <= am_sc am < 48 -> 0 <= i ->
  Z.testbit (Z.lor (am_avail am) (am_freed am)) i = true -> class_size (am_sc am) <= stride_of am.
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

(* [comment removed for export] *)
Lemma try_avail_finish X U s0 s sc m3 am3 (Q : Z * astate -> Prop) :
  Inv X None U s -> 0 <= sc < 48 -> active_hd s sc = Some m3 -> usedX X s m3 am3 -> am_sc am3 = sc ->
  Z.land (am_freed am3) (ones (am_aidx am3)) <> 0 -> allzero X s sc ->
  (forall c, 0 <= c -> c <> sc -> active_hd s c = active_hd s0 c) -> ub_same s0 s ->
  (forall first s', ta_post X U s0 sc first s' -> Q (first, s')) ->
  itok ((mask <- activate_group m3 ;;
         massert (negb (mask =? 0)) 3 ;;
         am <- getm m3 ;; decay_bounces (am_sc am) ;;
         let first := lowbit mask in
         am' <- getm m3 ;; setm m3 (am_set_avail (mask - first) am') ;; ret first) s) Q.
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

Lemma span_loop_ge f c sp sz : c <= span_loop f c sp sz.
Proof.
  revert c sp. induction f as [|f IH]; intros c sp; cbn; [lia|].
  destruct (Z.lxor sp (sp + sz - 1) <? 4096); [|lia]. specialize (IH (c + 1) (sp + sz)). lia.
Qed.

(* [comment removed for export] *)
Lemma head_links X U s sc g am :
  Inv X None U s -> 0 <= sc < 48 -> active_hd s sc = Some g -> usedX X s g am -> am_sc am = sc ->
  exists pr nx, am_prev am = Some pr /\ am_next am = Some nx /\
    exists amn, usedX X s nx amn /\ am_sc amn = sc /\
    (nx <> g -> am_freed amn <> 0 /\ am_avail amn = 0).
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

(* [comment removed for export] *)
Lemma try_avail_select X U s0 s sc m1 am1 (K : sptr -> M Z) (Q : Z * astate -> Prop) :
  Inv X None U s -> 0 <= sc < 48 -> active_hd s sc = Some m1 -> usedX X s m1 am1 -> am_sc am1 = sc ->
  am_freed am1 <> 0 -> allzero X s sc -> (forall c, 0 <= c -> c <> sc -> active_hd s c = active_hd s0 c) -> ub_same s0 s ->
  (forall m3 am3 s3, Inv X None U s3 -> active_hd s3 sc = Some m3 -> usedX X s3 m3 am3 -> am_sc am3 = sc ->
      Z.land (am_freed am3) (ones (am_aidx am3)) <> 0 -> allzero X s3 sc ->
      (forall c, 0 <= c -> c <> sc -> active_hd s3 c = active_hd s0 c) -> ub_same s0 s3 -> itok (K m3 s3) Q) ->
  itok ((am1' <- getm m1 ;;
         m2 <- (if am_freed am1' =? ones (am_last am1')
                then match am_next am1' with
                     | Some nx => set_head (HActive sc) (Some nx) ;; ret nx
                     | None => fail (FModel 6)
                     end
                else ret m1) ;;
         am2 <- getm m2 ;;
         m3 <- (if Z.land (am_freed am2) (ones (am_aidx am2)) =? 0 then
                  if negb (osptr_eqb (am_next am2) (Some m2)) then
                    match am_next am2 with
                    | Some nx => set_head (HActive sc) (Some nx) ;; ret nx
                    | None => fail (FModel 7)
                    end
                  else
                    let size := class_size (am_sc am2) in
                    let cnt0 := am_aidx am2 + 2 in
                    let cnt1 := span_loop 300%nat cnt0 (UNIT + size * cnt0) size in
                    let cnt := if am_last am2 + 1 <? cnt1 then am_last am2 + 1 else cnt1 in
                    setm m2 (am_set_aidx (cnt - 1) am2) ;; ret m2
                else ret m2) ;;
         K m3) s) Q.
Proof.
  intros HI Hsc Hhd Hu Hsca Hfr Hz Hoth UB0 HK.
  pose proof (usedX_MT _ _ _ _ Hu) as [M1 NX1].
  mbinds. eapply itok_getm; [exact M1|]. msimp.
  (* [comment removed for export] *)
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
    (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
      apply sptr_eqb_neq in Enx. destruct (Hnxf Enx) as [Hfrn Havn].
      mbinds. apply itok_set_head. msimp. apply itok_ret.
      pose proof (inv_ctx HI2) as (Clen & _).
      assert (HI3 : Inv X None U (set_active (lupd (st_active s2) (Z.to_nat sc) (Some nx)) s2)).
      { exact (Inv_rotate_head X None U s2 sc m2 am2 nx HI2 Hsc Hu2 Hs2 Hhd2 (Hz2 _ _ Hu2 Hs2) Hfr2 Hnx). }
      eapply HK; [exact HI3 | apply active_hd_set_active_same; rewrite Clen; lia | exact Hun | exact Hsn | | | |
        eapply ub_same_trans; [exact UB0|]; eapply ub_same_trans; [apply ub_same_metas; exact Em2|]; apply ub_same_metas; reflexivity].
      * (* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma try_avail_spec X U s sc (Q : Z * astate -> Prop) :
  Inv X None U s -> 0 <= sc < 48 ->
  (forall s', Inv X None U s' -> active_hd s' sc = None ->
     (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) -> ub_same s s' -> Q (0, s')) ->
  (forall first s', ta_post X U s sc first s' -> Q (first, s')) ->
  itok (try_avail sc s) Q.
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
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Eav.
    assert (Hz : allzero X s sc).
    { intros g am Hg Hsg. destruct (Z.eq_dec (am_avail am) 0) as [E|E]; [exact E|]. exfalso.
      pose proof (Q1 g am Hg Hsg E) as E2. rewrite Ehd in E2. injection E2 as ->.
      pose proof (usedX_fun _ _ _ _ _ Hg Hu0) as ->. exact (E Eav). }
    (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
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
End MallocWfSlot.


Module MallocWfGeom.
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
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma poff_padd p d : poff (padd p d) = poff p + d.
Proof. destruct p; reflexivity. Qed.

Lemma prid_padd p d : prid (padd p d) = prid p.
Proof. destruct p; reflexivity. Qed.

Lemma poff_slot_start am i : poff (slot_start am i) = poff (am_mem am) + UNIT + stride_of am * i.
Proof. unfold slot_start. rewrite poff_padd. lia. Qed.

Lemma prid_slot_start am i : prid (slot_start am i) = prid (am_mem am).
Proof. unfold slot_start. apply prid_padd. Qed.

Lemma sptr_eq_parts p q : prid p = prid q -> poff p = poff q -> p = q.
Proof. destruct p, q; cbn; intros -> ->; reflexivity. Qed.

Section Geom.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : Inv X R U s.

  (* [comment removed for export] *)
  #[using="Type"] Lemma same_group_starts am i1 i2 :
    i1 <> i2 -> 16 <= stride_of am ->
    poff (slot_start am i1) + stride_of am <= poff (slot_start am i2) \/
    poff (slot_start am i2) + stride_of am <= poff (slot_start am i1).
  Proof. intros Hne Hs. rewrite !poff_slot_start. assert (i1 < i2 \/ i2 < i1) as [H|H] by lia; [left|right]; nia. Qed.

  (* [comment removed for export] *)
  #[using="R U HI"] Lemma slot_in_span g am i :
    usedX X s g am -> 0 <= i <= am_last am ->
    poff (am_mem am) + UNIT <= poff (slot_start am i) /\
    poff (slot_start am i) + stride_of am <= poff (am_mem am) + group_extent am + IB.
  Proof.
    intros Hu Hi. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Hs.
    rewrite poff_slot_start. unfold group_extent. split; nia.
  Qed.

  #[using="R U HI"] Lemma fgroup_frame g am j fr :
    usedX X s g am -> 0 <= j <= am_last am -> ss_fr (nth_slot am j) = Some fr -> fr_kind fr = FGroup ->
    fr_n fr = stride_of am - IB /\ fr_off fr = 0.
  Proof.
    intros Hu Hj Hfr Hk. pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _).
    pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & _ & _ & _ & FG) & _).
    destruct (FG Hk) as [A B]. auto.
  Qed.

  (* [comment removed for export] *)
  #[using="R U HI"] Lemma inside_slot_start g1 a1 i1 g2 a2 :
    usedX X s g1 a1 -> usedX X s g2 a2 -> 0 <= i1 <= am_last a1 -> inside X s a1 a2 ->
    exists j fr, 0 <= j <= am_last a2 /\ ss_fr (nth_slot a2 j) = Some fr /\ fr_kind fr = FGroup /\
      poff (slot_start a2 j) + UNIT <= poff (slot_start a1 i1) /\
      poff (slot_start a1 i1) + stride_of a1 <= poff (slot_start a2 j) + stride_of a2.
  Proof.
    intros U1 U2 Hi1 (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mc & Memc & Lo & Hi & Fit).
    exists j, fr. split; [exact Hj|]. split; [exact Hfr|]. split; [exact Hk|].
    destruct (fgroup_frame _ _ _ _ U2 Hj Hfr Hk) as [Fn _].
    pose proof (f_equal poff Memc) as Eoc.
    pose proof (slot_in_span _ _ _ U1 Hi1) as [L1 H1].
    unfold UNIT, IB in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="R U HI"] Lemma slot_starts_distinct g1 a1 i1 g2 a2 i2 :
    usedX X s g1 a1 -> usedX X s g2 a2 ->
    0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
    slot_start a1 i1 = slot_start a2 i2 -> g1 = g2 /\ i1 = i2.
  Proof.
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

  (* [comment removed for export] *)
  #[using="R U HI"] Lemma frame_ptrs_distinct g1 a1 i1 f1 g2 a2 i2 f2 :
    usedX X s g1 a1 -> usedX X s g2 a2 ->
    0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
    ss_fr (nth_slot a1 i1) = Some f1 -> ss_fr (nth_slot a2 i2) = Some f2 ->
    frame_ptr a1 i1 f1 = frame_ptr a2 i2 f2 -> g1 = g2 /\ i1 = i2.
  Proof.
    intros U1 U2 Hi1 Hi2 F1 F2 E.
    pose proof (inv_groups HI g1 a1 U1) as G1. pose proof (inv_groups HI g2 a2 U2) as G2.
    pose proof (stride_pos _ _ _ _ _ G1) as S1. pose proof (stride_pos _ _ _ _ _ G2) as S2.
    (* [comment removed for export] *)
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

  (* [comment removed for export] *)

  #[using="Type"] Lemma find_in_slots_sound sl base stride k0 p k :
    find_in_slots sl base stride k0 p = Some k ->
    exists x fr, nth_error sl (Z.to_nat (k - k0)) = Some x /\ ss_fr x = Some fr /\ k0 <= k /\
      padd base (stride * k + UNIT * fr_off fr) = p.
  Proof.
    revert k0. induction sl as [|x t IH]; intros k0 H; cbn [find_in_slots] in H; [discriminate|].
    destruct (ss_fr x) as [fr|] eqn:Efr.
    - destruct (sptr_eqb (padd base (stride * k0 + UNIT * fr_off fr)) p) eqn:E.
      + injection H as <-. exists x, fr. rewrite Z.sub_diag. cbn [Z.to_nat nth_error]. repeat split; auto; [lia|]. apply sptr_eqb_eq. exact E.
      + destruct (IH _ H) as (x' & fr' & Hn & Hf & Hk & Hp). exists x', fr'.
        replace (Z.to_nat (k - k0)) with (S (Z.to_nat (k - (k0 + 1)))) by lia. cbn [nth_error]. repeat split; auto. lia.
    - destruct (IH _ H) as (x' & fr' & Hn & Hf & Hk & Hp). exists x', fr'.
      replace (Z.to_nat (k - k0)) with (S (Z.to_nat (k - (k0 + 1)))) by lia. cbn [nth_error]. repeat split; auto. lia.
  Qed.

  #[using="Type"] Lemma find_in_slots_complete sl base stride k0 p j x fr :
    nth_error sl j = Some x -> ss_fr x = Some fr -> padd base (stride * (k0 + Z.of_nat j) + UNIT * fr_off fr) = p ->
    exists k, find_in_slots sl base stride k0 p = Some k.
  Proof.
    revert k0 j. induction sl as [|y t IH]; intros k0 [|j] Hn Hf Hp; cbn [nth_error] in Hn; try discriminate; cbn [find_in_slots].
    - injection Hn as ->. rewrite Hf. rewrite Z.add_0_r in Hp. rewrite Hp, sptr_eqb_refl. eexists. reflexivity.
    - destruct (ss_fr y) as [fy|]; [destruct (sptr_eqb _ p); [eexists; reflexivity|]|];
        eapply (IH (k0 + 1) j); eauto; rewrite <- Hp; f_equal; lia.
  Qed.

  #[using="Type"] Lemma frame_ptr_base am i fr :
    frame_ptr am i fr = padd (padd (am_mem am) UNIT) (stride_of am * i + UNIT * fr_off fr).
  Proof.
    unfold frame_ptr. apply sptr_eq_parts.
    - rewrite !prid_padd, prid_slot_start. reflexivity.
    - rewrite !poff_padd, poff_slot_start. lia.
  Qed.

  #[using="R U HI"] Lemma find_frame_in_spec g am i fr :
    usedX X s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
    find_frame_in (st_metas s) (frame_ptr am i fr) = Some (g, i).
  Proof.
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
        + (* [comment removed for export] *)
          destruct (find_in_slots_sound _ _ _ _ _ _ Ef) as (xk & fk & Hn & Hfk & Hk0 & Hp).
          rewrite Z.sub_0_r in Hn.
          destruct (memb q X) eqn:Mx.
          * (* [comment removed for export] *)
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
        + (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GR (s : astate) (am : ameta) : Prop :=
  exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
    0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg /\
    (0 < am_maplen am -> poff (am_mem am) = 0).

Lemma used_group_region_aux X R U s (HI : Inv X R U s) k :
  forall g am, usedX X s g am -> (Z.to_nat (64 - am_sc am) <= k)%nat -> GR s am.
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

Lemma used_group_region X R U s g am :
  Inv X R U s -> usedX X s g am -> GR s am.
Proof. intros HI Hu. eapply (used_group_region_aux X R U s HI); [exact Hu | apply Nat.le_refl]. Qed.

Lemma used_group_prid_lt X R U s g am :
  Inv X R U s -> usedX X s g am -> (prid (am_mem am) < length (st_regions s))%nat.
Proof.
  intros HI Hu. destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & _).
  exact (region_of_lt _ _ _ Hr).
Qed.
End MallocWfGeom.

From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.

Module MallocWfGroup.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_zupd_inv (l : list Z) n v u : In u (zupd l n v) -> u = v \/ In u l.
Proof.
  revert n. induction l as [|h t IH]; intros [|n] H; cbn in H; try contradiction.
  - destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
  - destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH n H) as [E|Hin]; [left; exact E | right; right; exact Hin].
Qed.

Definition Uadd (U : Z -> Z) (sc d : Z) : Z -> Z := fun c => if c =? sc then U c + d else U c.

Lemma Inv_set_usage X R U s sc v :
  Inv X R U s -> 0 <= sc < 48 -> 0 <= v ->
  Inv X R (Uadd U sc (v - usage_of s sc)) (set_usage (zset sc v (st_usage s)) s).
Proof.
  intros HI Hsc Hv.
  set (s' := set_usage (zset sc v (st_usage s)) s).
  assert (EU : forall p am, usedX X s' p am <-> usedX X s p am) by (intros; unfold usedX, MTX, MT; subst s'; cbn; tauto).
  pose proof (inv_ctx HI) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  eapply (Inv_transfer X X R U _ s s' HI EU eq_refl).
  - split; [exact C1|]. split; [subst s'; cbn; rewrite length_zset; exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [|exact (conj C6 (conj C7 C8))].
    intros u Hu. subst s'. cbn in Hu. unfold zset in Hu. apply In_zupd_inv in Hu. destruct Hu as [->|Hu]; [lia | apply C5; exact Hu].
  - exact (inv_keys HI).
  - exact (inv_areas HI).
  - exact (inv_X HI).
  - exact (inv_rings HI).
  - intros c Hc. pose proof (inv_usage HI c Hc) as E. unfold Uadd.
    change (class_sum X s' c) with (class_sum X s c).
    unfold usage_of in *. subst s'. cbn [st_usage set_usage]. rewrite znth_zset by lia. rewrite C2.
    destruct (c =? sc) eqn:Ec; cbn [andb].
    + apply Z.eqb_eq in Ec. subst c. destruct (sc <? Z.of_nat 48) eqn:El; [lia | apply Z.ltb_ge in El; lia].
    + exact E.
Qed.

Lemma itok_set_usage_of sc v s (Q : unit * astate -> Prop) :
  Q (tt, set_usage (zset sc v (st_usage s)) s) -> itok (set_usage_of sc v s) Q.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Install.
  Variables (X : list sptr) (R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate) (m : sptr) (am1 : ameta).
  Hypothesis HI : Inv (m :: X) None U s.
  Hypothesis NX : memb m X = false.
  Hypothesis EM : MT s' m = Some (MUsed am1).
  Hypothesis EO : forall q, q <> m -> MT s' q = MT s q.
  Hypothesis EK : keys s' = keys s.
  Hypothesis ER : st_regions s' = st_regions s.
  Hypothesis G1 : group_ok X R' s' m am1.
  Hypothesis L1 : forall q a, usedX (m :: X) s q a -> prid (am_mem a) = prid (am_mem am1) ->
                    spans_disjoint a am1 \/ inside X s' a am1 \/ inside X s' am1 a.
  Hypothesis M1 : 0 < am_maplen am1 -> forall q a, usedX (m :: X) s q a -> 0 < am_maplen a ->
                    prid (am_mem a) <> prid (am_mem am1).
  Hypothesis P1 : am_aidx am1 < am_last am1 -> forall q a, usedX (m :: X) s q a -> am_sc a = am_sc am1 ->
                    am_last a <= am_aidx a.
  Hypothesis HR' : reserved_ok X R' s'.
  Hypothesis R'm : forall p i, R' = Some (p, i) -> p = m.
  Hypothesis PCG1 : am_aidx am1 < am_last am1 -> 0 < am_maplen am1 /\ am_sc am1 <> 0.

  #[using="R' EM EO G1 L1 M1 P1 PCG1"] Lemma ins_used_bwd q a : usedX X s' q a -> (q = m /\ a = am1) \/ (q <> m /\ usedX (m :: X) s q a).
  Proof.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [Mq Xq].
    destruct (sptr_eq_dec q m) as [->|Hne].
    - left. rewrite EM in Mq. injection Mq as ->. auto.
    - right. split; [exact Hne|]. apply usedX_intro.
      + rewrite memb_cons, Xq. destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
      + rewrite <- (EO q Hne). exact Mq.
  Qed.

  #[using="EO"] Lemma ins_used_fwd q a : usedX (m :: X) s q a -> q <> m /\ usedX X s' q a.
  Proof.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [Mq Xq]. rewrite memb_cons in Xq.
    apply orb_false_elim in Xq as [E Xq]. apply sptr_eqb_neq in E.
    split; [exact E|]. apply usedX_intro; [exact Xq|]. rewrite (EO q E). exact Mq.
  Qed.

  #[using="R' s EM EO G1 L1 M1 P1 PCG1"] Lemma ins_used_m a : usedX X s' m a -> a = am1.
  Proof. intros Hu. destruct (ins_used_bwd _ _ Hu) as [[_ E] | [Hne _]]; [exact E | exfalso; exact (Hne eq_refl)]. Qed.

  #[using="U' EO"] Lemma ins_inside a b : inside (m :: X) s a b -> inside X s' a b.
  Proof.
    intros (j & fr & c & ac & H1 & H2 & H3 & H4 & H5). exists j, fr, c, ac.
    repeat split; try tauto. apply ins_used_fwd. exact H4.
  Qed.

  #[using="EO ER R'm"] Lemma ins_group q a : q <> m -> group_ok (m :: X) None s q a -> group_ok X R' s' q a.
  Proof.
    intros Hne (Gm & Gml & Gsl & Gcl & Gmp & Gns).
    split; [exact Gm|]. split; [exact Gml|]. split.
    { intros i Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
      destruct (ss_fr (nth_slot a i)) as [fr|].
      - destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [|exact (conj A3 A4)].
        intros E. apply R'm in E. exact (Hne E).
      - left. destruct S3 as [S3|S3]; [exact S3 | discriminate]. }
    split.
    { destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C]; [left | right; exact C].
      repeat split; auto. destruct C6 as [C6|C6]; [discriminate | right; exact C6]. }
    split.
    { intros Hm. destruct (Gmp Hm) as (r & rg & H). exists r, rg. unfold region_of in *. rewrite ER. exact H. }
    intros Hm. destruct (Gns Hm) as [N63 (g' & b & i' & fr' & Hu & Hrest)].
    split; [exact N63|]. exists g', b, i', fr'. split; [apply ins_used_fwd; exact Hu | exact Hrest].
  Qed.

  #[using="U s m am1 HI EM EO ER G1 L1 M1 P1 R'm PCG1"] Lemma ins_groups : forall q a, usedX X s' q a -> group_ok X R' s' q a.
  Proof.
    intros q a Hu. destruct (ins_used_bwd _ _ Hu) as [[-> ->] | [Hne Hu0]]; [exact G1|].
    apply ins_group; [exact Hne|]. exact (inv_groups HI q a Hu0).
  Qed.

  #[using="R' U U' s m am1 HI EM EO G1 L1 M1 P1 PCG1"] Lemma ins_laminar : laminar X s'.
  Proof.
    intros p1 a1 p2 a2 H1 H2 Hne Hr.
    destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
    - exfalso. exact (Hne eq_refl).
    - destruct (L1 _ _ U2 (eq_sym Hr)) as [D | [I | I]].
      + left. unfold spans_disjoint in *. tauto.
      + right; right; exact I.
      + right; left; exact I.
    - destruct (L1 _ _ U1 Hr) as [D | [I | I]]; [left; exact D | right; left; exact I | right; right; exact I].
    - destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne Hr) as [D | [I | I]];
        [left; exact D | right; left; apply ins_inside; exact I | right; right; apply ins_inside; exact I].
  Qed.

  #[using="R' U s m am1 HI EM EO G1 L1 M1 P1 PCG1"] Lemma ins_maps : maps_unique X s'.
  Proof.
    intros p1 a1 p2 a2 H1 H2 Hm1 Hm2 Hr.
    destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
    - reflexivity.
    - exfalso. exact (M1 Hm1 _ _ U2 Hm2 (eq_sym Hr)).
    - exfalso. exact (M1 Hm2 _ _ U1 Hm1 Hr).
    - eapply (inv_maps HI); eauto.
  Qed.

  #[using="R' U s m am1 HI EM EO G1 L1 M1 P1 PCG1"] Lemma ins_partial : partial_unique X s'.
  Proof.
    intros p1 a1 p2 a2 H1 H2 Hsc Hp1 Hp2.
    destruct (ins_used_bwd _ _ H1) as [[-> ->] | [N1 U1]]; destruct (ins_used_bwd _ _ H2) as [[-> ->] | [N2 U2]].
    - reflexivity.
    - exfalso. pose proof (P1 Hp1 _ _ U2 (eq_sym Hsc)). lia.
    - exfalso. pose proof (P1 Hp2 _ _ U1 Hsc). lia.
    - eapply (inv_partial HI); eauto.
  Qed.

  #[using="R' U s m am1 HI EM EO G1 L1 M1 P1 PCG1"] Lemma ins_pcg : partial_ok X s'.
  Proof.
    intros p a H Ha. destruct (ins_used_bwd _ _ H) as [[-> ->] | [N U1]]; [exact (PCG1 Ha)|].
    exact (inv_pcg HI p a U1 Ha).
  Qed.

  #[using="U s m HI NX EO EK"] Lemma ins_Xok : Xok X s'.
  Proof.
    intros x Hx.
    assert (Hne : x <> m) by (intros ->; apply memb_In in Hx; rewrite Hx in NX; discriminate).
    destruct (inv_X HI x (or_intror Hx)) as [Kx Mx]. rewrite EK, (EO x Hne). split; [exact Kx | exact Mx].
  Qed.

  #[using="U s m am1 HI NX EM EO EK ER G1 L1 M1 P1 HR' R'm PCG1"] Theorem Inv_install :
    ctx_ok s' -> keys_ok s' -> areas_ok s' -> rings_ok X R' s' -> usage_ok X U' s' -> Inv X R' U' s'.
  Proof.
    intros C K A RG US.
    split; [exact C|]. split; [exact K|]. split; [exact A|].
    split; [apply ins_Xok|]. split; [apply ins_groups|]. split; [apply ins_laminar|]. split; [apply ins_maps|].
    split; [exact RG|]. split; [exact US|]. split; [exact HR'|]. split; [apply ins_partial | apply ins_pcg].
  Qed.
End Install.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sub_subset_ldiff a b : Z.land a b = b -> a - b = Z.ldiff a b.
Proof.
  intros H.
  assert (E : Z.ldiff a b + b = a).
  { rewrite Z.add_nocarry_lxor.
    2:{ apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
        destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
    rewrite Z.lxor_lor.
    2:{ apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
        destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
    rewrite <- H at 2. apply Z.lor_ldiff_and. }
  lia.
Qed.

Ltac bcase t :=
  let E := fresh "E" in
  destruct t eqn:E;
  [first [apply Z.leb_le in E | apply Z.ltb_lt in E | apply Z.eqb_eq in E]
  |first [apply Z.leb_gt in E | apply Z.ltb_ge in E | apply Z.eqb_neq in E]].

Lemma testbit_new_avail ai i : 0 <= ai -> Z.testbit (ones ai - 1) i = (1 <=? i) && (i <=? ai).
Proof.
  intros Hai. change 1 with (bit 0) at 1.
  rewrite sub_bit_ldiff by (try lia; rewrite testbit_ones by lia; cbn; apply Z.leb_le; lia).
  destruct (Z_lt_dec i 0) as [Hi|Hi].
  - rewrite testbit_neg_idx by lia. bcase (1 <=? i); [lia | reflexivity].
  - rewrite Z.ldiff_spec, testbit_ones, testbit_bit by lia.
    bcase (0 <=? i); bcase (i <=? ai); bcase (0 =? i); bcase (1 <=? i); cbn; try reflexivity; lia.
Qed.

Lemma testbit_new_freed la ai i : 0 <= ai <= la -> Z.testbit (ones la - ones ai) i = (ai <? i) && (i <=? la).
Proof.
  intros H. rewrite sub_subset_ldiff.
  2:{ apply bits_inj_nonneg. intros k Hk. rewrite Z.land_spec, !testbit_ones by lia.
      bcase (0 <=? k); bcase (k <=? la); bcase (k <=? ai); cbn; try reflexivity; lia. }
  destruct (Z_lt_dec i 0) as [Hi|Hi].
  - rewrite testbit_neg_idx by lia. bcase (ai <? i); [lia | reflexivity].
  - rewrite Z.ldiff_spec, !testbit_ones by lia.
    bcase (0 <=? i); bcase (i <=? la); bcase (i <=? ai); bcase (ai <? i); cbn; try reflexivity; lia.
Qed.

Definition new_am (mem : sptr) (sc cnt aidx maplen : Z) (sl : slotst) : ameta :=
  mkAMeta None None mem (ones aidx - 1) (ones (cnt - 1) - ones aidx) (cnt - 1) sc maplen aidx (repeat sl (Z.to_nat cnt)).

Lemma new_am_masks mem sc cnt aidx maplen sl :
  1 <= cnt <= 32 -> 0 <= aidx <= cnt - 1 -> masks_ok (new_am mem sc cnt aidx maplen sl).
Proof.
  intros Hc Ha. unfold masks_ok, new_am. cbn [am_last am_aidx am_slots am_avail am_freed].
  rewrite repeat_length.
  pose proof (ones_nonneg aidx ltac:(lia)). pose proof (ones_nonneg (cnt - 1) ltac:(lia)).
  assert (Hsub : ones aidx <= ones (cnt - 1)).
  { unfold ones. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  assert (H1 : 1 <= ones aidx) by (unfold ones; assert (2 ^ 1 <= 2 ^ (aidx + 1)) by (apply Z.pow_le_mono_r; lia); lia).
  repeat split; try lia.
  - intros i Hi Hb. rewrite testbit_new_avail in Hb by lia. rewrite testbit_new_freed by lia.
    apply andb_prop in Hb as [_ Hb]. apply Z.leb_le in Hb. apply andb_false_intro1. apply Z.ltb_ge. lia.
  - rewrite testbit_new_avail by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
  - rewrite testbit_new_freed by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
  - intros i Hi. rewrite testbit_new_avail by lia. apply andb_false_intro2. apply Z.leb_gt. lia.
  - intros i Hi. rewrite testbit_new_freed by lia. apply andb_true_intro. split; [apply Z.ltb_lt | apply Z.leb_le]; lia.
Qed.

Lemma new_am_allocated mem sc cnt aidx maplen sl i :
  1 <= cnt -> 0 <= aidx <= cnt - 1 -> 0 <= i ->
  allocated (new_am mem sc cnt aidx maplen sl) i = (i =? 0) || (cnt - 1 <? i).
Proof.
  intros Hc Ha Hi. unfold allocated, new_am. cbn [am_avail am_freed].
  rewrite Z.lor_spec, testbit_new_avail, testbit_new_freed by lia.
  bcase (1 <=? i); bcase (i <=? aidx); bcase (aidx <? i); bcase (i <=? cnt - 1); bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia.
Qed.

Lemma new_am_nth_slot mem sc cnt aidx maplen sl i :
  0 <= i <= cnt - 1 -> nth_slot (new_am mem sc cnt aidx maplen sl) i = sl.
Proof. intros Hi. unfold nth_slot, new_am. cbn [am_slots]. rewrite nth_repeat'. destruct (Nat.ltb _ _) eqn:E; [reflexivity|]. apply Nat.ltb_ge in E. lia. Qed.

Lemma new_am_stride mem sc cnt aidx maplen sl :
  stride_of (new_am mem sc cnt aidx maplen sl) = if (cnt - 1 =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else class_size sc.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fold_sum_delta (f f' : sptr -> Z) m l :
  NoDup l -> In m l -> (forall q, q <> m -> f' q = f q) ->
  fold_right (fun q acc => f' q + acc) 0 l = fold_right (fun q acc => f q + acc) 0 l + (f' m - f m).
Proof.
  intros ND Hin Hf. induction l as [|x t IH]; [destruct Hin|]. cbn [fold_right].
  inversion ND as [|x' t' Hx Ht]; subst.
  destruct (sptr_eq_dec x m) as [->|Hne].
  - assert (E : fold_right (fun q acc => f' q + acc) 0 t = fold_right (fun q acc => f q + acc) 0 t).
    { clear IH Hin ND. induction t as [|y u IH]; [reflexivity|]. cbn [fold_right].
      rewrite IH by (intros; try (intros Hy; apply Hx; right; exact Hy); inversion Ht; auto).
      rewrite Hf by (intros ->; apply Hx; left; reflexivity). reflexivity. }
    rewrite E. lia.
  - destruct Hin as [E|Hin]; [exfalso; exact (Hne E)|]. rewrite (IH Ht Hin), (Hf x Hne). lia.
Qed.

Section Unexempt.
  Variables (X : list sptr) (s s' : astate) (m : sptr) (am1 : ameta).
  Hypothesis NX : memb m X = false.
  Hypothesis EM : MT s' m = Some (MUsed am1).
  Hypothesis EO : forall q, q <> m -> MT s' q = MT s q.

  #[using="EO"] Lemma ux_MTX q : q <> m -> MTX X s' q = MTX (m :: X) s q.
  Proof.
    intros Hne. unfold MTX. rewrite memb_cons, (EO q Hne).
    destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; contradiction | reflexivity].
  Qed.

  #[using="NX EM"] Lemma ux_MTX_m : MTX X s' m = Some (MUsed am1) /\ MTX (m :: X) s m = None.
  Proof. unfold MTX. rewrite NX, EM, memb_cons, sptr_eqb_refl. split; reflexivity. Qed.

  #[using="am1 NX EM EO"] Lemma ux_flinks q : flinks X s' q = flinks (m :: X) s q.
  Proof.
    unfold flinks. destruct (sptr_eq_dec q m) as [->|Hne].
    - destruct ux_MTX_m as [A B]. rewrite A, B. reflexivity.
    - rewrite (ux_MTX q Hne). reflexivity.
  Qed.

  #[using="NX EM EO"] Lemma ux_alinks c q : am_sc am1 <> c -> alinks X s' c q = alinks (m :: X) s c q.
  Proof.
    intros Hc. unfold alinks. destruct (sptr_eq_dec q m) as [->|Hne].
    - destruct ux_MTX_m as [A B]. rewrite A, B. destruct (am_sc am1 =? c) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
    - rewrite (ux_MTX q Hne). reflexivity.
  Qed.

  #[using="s NX EM"] Lemma ux_alinks_m c : am_sc am1 = c -> alinks X s' c m = Some (am_prev am1, am_next am1).
  Proof. intros Hc. unfold alinks. destruct ux_MTX_m as [A _]. rewrite A. rewrite (proj2 (Z.eqb_eq _ _) Hc). reflexivity. Qed.

  #[using="EO"] Lemma ux_contrib c q : q <> m -> contrib X s' c q = contrib (m :: X) s c q.
  Proof. intros Hne. unfold contrib. rewrite (ux_MTX q Hne). reflexivity. Qed.

  #[using="NX EM"] Lemma ux_contrib_m c : contrib X s' c m = (if am_sc am1 =? c then am_last am1 + 1 else 0) /\ contrib (m :: X) s c m = 0.
  Proof. unfold contrib. destruct ux_MTX_m as [A B]. rewrite A, B. split; reflexivity. Qed.

  #[using="NX EM EO"] Lemma ux_class_sum c :
    keys s' = keys s -> NoDup (keys s) -> In m (keys s) ->
    class_sum X s' c = class_sum (m :: X) s c + (if am_sc am1 =? c then am_last am1 + 1 else 0).
  Proof.
    intros EK ND Hin. unfold class_sum. rewrite EK.
    rewrite (fold_sum_delta (contrib (m :: X) s c) (contrib X s' c) m (keys s) ND Hin (fun q H => ux_contrib c q H)).
    destruct (ux_contrib_m c) as [A B]. rewrite A, B. lia.
  Qed.

  #[using="NX EM EO"] Lemma ux_used_bwd q a : usedX X s' q a -> (q = m /\ a = am1) \/ (q <> m /\ usedX (m :: X) s q a).
  Proof.
    intros Hu. destruct (sptr_eq_dec q m) as [->|Hne].
    - left. unfold usedX in Hu. destruct ux_MTX_m as [A _]. rewrite A in Hu. injection Hu as ->. auto.
    - right. split; [exact Hne|]. unfold usedX in *. rewrite <- (ux_MTX q Hne). exact Hu.
  Qed.

  #[using="am1 NX EM EO"] Lemma ux_used_fwd q a : usedX (m :: X) s q a -> q <> m /\ usedX X s' q a.
  Proof.
    intros Hu. destruct (sptr_eq_dec q m) as [->|Hne].
    - unfold usedX in Hu. destruct ux_MTX_m as [_ B]. rewrite B in Hu. discriminate.
    - split; [exact Hne|]. unfold usedX in *. rewrite (ux_MTX q Hne). exact Hu.
  Qed.

  #[using="s NX EM"] Lemma ux_used_m : usedX X s' m am1.
  Proof. unfold usedX. exact (proj1 ux_MTX_m). Qed.

  (* [comment removed for export] *)
  #[using="am1 NX EM EO"] Lemma ux_free_ring :
    st_free_meta_head s' = st_free_meta_head s -> free_ring_ok (m :: X) s -> free_ring_ok X s'.
  Proof.
    intros EF (ms & Rg & Hall). exists ms. rewrite EF. split.
    - eapply ring_ok_ext; [|exact Rg]. intros q _. apply ux_flinks.
    - intros q pr nx Hq. destruct (sptr_eq_dec q m) as [->|Hne].
      + destruct ux_MTX_m as [A _]. rewrite A in Hq. discriminate.
      + rewrite (ux_MTX q Hne) in Hq. eapply Hall. exact Hq.
  Qed.

  (* [comment removed for export] *)
  #[using="NX EM EO"] Lemma ux_active_other R R' c :
    (forall q i, q <> m -> R = Some (q, i) -> R' = Some (q, i)) ->
    am_sc am1 <> c -> active_hd s' c = active_hd s c -> active_ring_ok (m :: X) R s c -> active_ring_ok X R' s' c.
  Proof.
    intros HRR Hc EH (ms & Rg & Mem & Full & Q1 & Q2). exists ms. rewrite EH. split.
    - eapply ring_ok_ext; [|exact Rg]. intros q _. apply ux_alinks. exact Hc.
    - split; [|split; [|split]]; intros q a Hq Hsc;
        (destruct (ux_used_bwd q a Hq) as [[-> ->] | [Hne Hu]]; [exfalso; exact (Hc Hsc)|]); eauto.
      intros Hin Hnh HnR. eapply Q2; eauto. intros i E. exact (HnR i (HRR q i Hne E)).
  Qed.

  #[using="NX EM EO"] Lemma ux_direct : am_prev am1 = None -> am_next am1 = None -> direct_unlinked (m :: X) s -> direct_unlinked X s'.
  Proof.
    intros P N D q a Hq H63. destruct (ux_used_bwd q a Hq) as [[-> ->] | [Hne Hu]]; [auto|]. exact (D q a Hu H63).
  Qed.
End Unexempt.

Lemma ctx_ok_upd_meta s g x : ctx_ok s -> In g (keys s) -> ctx_ok (upd_meta g x s).
Proof.
  intros C Hg. eapply sbmh_ctx; [apply sbmh_upd_meta; exact Hg | reflexivity | | exact C].
  intros Hi. destruct C as (_&_&_&_&_&_&_&_&_&_&_&C12). destruct (C12 Hi) as (Em & _).
  exfalso. unfold keys in Hg. rewrite Em in Hg. exact Hg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition direct_am (r : nat) (maplen : Z) : ameta := mkAMeta None None (SP r 0) 0 0 0 63 maplen 0 [slot_zero].

Lemma install_direct_spec X U s g r rg maplen (Q : unit * astate -> Prop) :
  Inv (g :: X) None U s -> memb g X = false ->
  region_of s r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> rg_len rg = maplen * PGSZ -> 1 <= maplen ->
  (forall q a, usedX (g :: X) s q a -> prid (am_mem a) <> r) ->
  (forall s', s' = upd_meta g (MUsed (direct_am r maplen)) s -> Inv X (Some (g, 0)) U s' ->
     usedX X s' g (direct_am r maplen) -> ub_same s s' -> Q (tt, s')) ->
  itok (setm g (direct_am r maplen) s) Q.
Proof.
  intros HI NX Hr Hk Hl Hlen Hml Hfresh HQ.
  pose proof (inv_X HI g (or_introl eq_refl)) as [Kg _].
  apply itok_setm'. set (s' := upd_meta g (MUsed (direct_am r maplen)) s).
  assert (EM : MT s' g = Some (MUsed (direct_am r maplen))) by apply MT_upd_same.
  assert (EO : forall q, q <> g -> MT s' q = MT s q) by (intros; apply MT_upd_other; assumption).
  assert (Ug : usedX X s' g (direct_am r maplen)) by (apply ux_used_m; assumption).
  assert (Hal : allocated (direct_am r maplen) 0 = true) by reflexivity.
  apply HQ; [reflexivity| |exact Ug|].
  2:{ subst s'. apply ub_same_upd_In; [exact Kg|]. rewrite (ucontrib_exempt_nil _ _ _ _ g g HI (or_introl eq_refl)). reflexivity. }
  eapply (Inv_install X (Some (g, 0)) U U s s' g (direct_am r maplen) HI NX EM EO).
  - apply keys_upd_In. exact Kg.
  - reflexivity.
  - (* [comment removed for export] *)
    split.
    { unfold masks_ok, direct_am. cbn [am_last am_aidx am_slots am_avail am_freed length].
      repeat split; try lia; intros; rewrite ?Z.bits_0; auto. }
    split; [cbn; lia|]. split.
    { intros i Hi. cbn [am_last direct_am] in Hi. assert (i = 0) as -> by lia.
      unfold slot_ok. change (nth_slot (direct_am r maplen) 0) with slot_zero. cbn [ss_hdr ss_fr slot_zero].
      split; [discriminate|]. split; [intros h3 h16 E; injection E as <- <-; lia|]. right. reflexivity. }
    split.
    { left. cbn. repeat split; try lia; try reflexivity. left. reflexivity. }
    split.
    { intros _. exists r, rg. cbn [am_mem am_maplen am_last direct_am].
      split; [reflexivity|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hlen|].
      unfold stride_of, direct_am. cbn [am_last am_maplen am_sc]. split; [|intros _ H; lia].
      destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [Z.eqb andb negb]. unfold UNIT, PGSZ. lia. }
    intros H0. cbn in H0. lia.
  - intros q a Hu Hp. exfalso. exact (Hfresh q a Hu Hp).
  - intros _ q a Hu _ Hp. exact (Hfresh q a Hu Hp).
  - intros H. cbn in H. lia.
  - intros p i E. injection E as <- <-. exists (direct_am r maplen). split; [exact Ug|]. cbn [am_last direct_am].
    split; [lia|]. split; [reflexivity | exact Hal].
  - intros p i E. injection E as <- <-. reflexivity.
  - intros H. cbn in H. lia.
  - apply ctx_ok_upd_meta; [exact (inv_ctx HI) | exact Kg].
  - eapply sbmh_keys; [apply sbmh_upd_meta; exact Kg | exact (inv_keys HI)].
  - eapply sbmh_areas; [apply sbmh_upd_meta; exact Kg | exact (inv_areas HI)].
  - destruct (inv_rings HI) as (F & A & D). split; [|split].
    + eapply ux_free_ring; eauto.
    + intros c Hc. eapply (ux_active_other X s s' g _ NX EM EO None); eauto; [intros q i _ E; discriminate | cbn; lia].
    + eapply ux_direct; eauto.
  - intros c Hc. change (usage_of s' c) with (usage_of s c). rewrite (inv_usage HI c Hc).
    rewrite (ux_class_sum X s s' g _ NX EM EO c (keys_upd_In _ _ _ Kg) (proj1 (inv_keys HI)) Kg).
    cbn [am_sc direct_am]. destruct (63 =? c) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma usage_of_nonneg s sc : ctx_ok s -> 0 <= usage_of s sc.
Proof.
  intros (_ & _ & _ & _ & C5 & _). unfold usage_of, znth.
  destruct (nth_in_or_default (Z.to_nat sc) (st_usage s) 0) as [H|H]; [apply C5; exact H | rewrite H; lia].
Qed.

Lemma links_fields p n am :
  am_mem (am_set_links p n am) = am_mem am /\ am_last (am_set_links p n am) = am_last am /\
  am_sc (am_set_links p n am) = am_sc am /\ am_maplen (am_set_links p n am) = am_maplen am /\
  am_aidx (am_set_links p n am) = am_aidx am /\ am_avail (am_set_links p n am) = am_avail am /\
  am_freed (am_set_links p n am) = am_freed am /\ am_slots (am_set_links p n am) = am_slots am /\
  am_prev (am_set_links p n am) = p /\ am_next (am_set_links p n am) = n.
Proof. destruct am; repeat split; reflexivity. Qed.

Lemma ring_ok_single lk m : lk m = Some (Some m, Some m) -> ring_ok lk (Some m) [m].
Proof.
  intros H. split; [|reflexivity]. split; [constructor; [intros []|constructor]|]. cbn. split; [exact H | exact I].
Qed.

(* [comment removed for export] *)
Lemma empty_ring_class X R U s sc q a :
  Inv X R U s -> 0 <= sc < 48 -> active_hd s sc = None -> usedX X s q a -> am_sc a = sc ->
  am_avail a = 0 /\ am_freed a = 0 /\ (am_prev a, am_next a) = (None, None) /\ am_aidx a = am_last a.
Proof.
  intros HI Hsc Hhd Hu Hsa.
  destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & Full & _).
  rewrite Hhd in Rg. apply ring_None in Rg. subst ms.
  assert (Hl : (am_prev a, am_next a) = (None, None)).
  { destruct (Mem q a Hu Hsa) as [_ M2]. destruct (am_prev a), (am_next a); try reflexivity; exfalso; apply (M2 ltac:(discriminate)). }
  destruct (Full q a Hu Hsa ltac:(intros [])) as [Av Fr].
  pose proof (inv_groups HI q a Hu) as ((M1 & M2 & _ & _ & _ & _ & _ & _ & M9) & _).
  repeat split; auto; try (injection Hl; auto).
  destruct (Z_lt_dec (am_aidx a) (am_last a)) as [Hlt|]; [|lia]. exfalso.
  pose proof (M9 (am_last a) ltac:(lia)) as Hb. rewrite Fr, Z.bits_0 in Hb. discriminate.
Qed.

Lemma install_group_spec X U s m sc cnt aidx maplen mem sl (Q : unit * astate -> Prop) :
  (aidx < cnt - 1 -> 0 < maplen /\ sc <> 0) ->
  Inv (m :: X) None U s -> memb m X = false ->
  0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= aidx <= cnt - 1 -> 0 <= maplen ->
  active_hd s sc = None ->
  let am1 := new_am mem sc cnt aidx maplen sl in
  ((sl = slot_zero /\ 0 < maplen) \/ (sl = slot_junk /\ maplen = 0)) ->
  class_ok (Some (m, 0)) m am1 ->
  mapped_ok s am1 ->
  (maplen = 0 -> exists g' am' i' fr', usedX (m :: X) s g' am' /\ 0 <= i' <= am_last am' /\
      ss_fr (nth_slot am' i') = Some fr' /\ fr_kind fr' = FGroup /\ mem = slot_start am' i' /\
      sc < am_sc am' /\ am_sc am' <> 63 /\ UNIT + class_size sc * cnt - IB <= fr_n fr') ->
  (forall q a, usedX (m :: X) s q a -> prid (am_mem a) = prid mem ->
      spans_disjoint a am1 \/ inside (m :: X) s am1 a \/
      (maplen = 0 /\ exists j fr, 0 <= j <= am_last a /\ ss_fr (nth_slot a j) = Some fr /\ fr_kind fr = FGroup /\
         mem = slot_start a j /\ group_extent am1 <= fr_n fr)) ->
  (0 < maplen -> forall q a, usedX (m :: X) s q a -> 0 < am_maplen a -> prid (am_mem a) <> prid mem) ->
  (forall s', Inv X (Some (m, 0)) U s' -> active_hd s' sc = Some m ->
     usedX X s' m (am_set_links (Some m) (Some m) am1) ->
     (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) ->
     st_regions s' = st_regions s -> st_mmap_counter s' = st_mmap_counter s ->
     ub_same s s' ->
     Q (tt, s')) ->
  itok (install_group m sc cnt aidx maplen mem sl s) Q.
Proof.
  intros HPCG HI NX Hsc Hcnt Haidx Hml Hhd am1 SL CL MP NS LAM MU HQ.
  pose proof (inv_X HI m (or_introl eq_refl)) as [Km _].
  pose proof (inv_ctx HI) as C0. pose proof C0 as (Clen & _).
  assert (Hfr1 : forall i, ss_fr (nth_slot am1 i) = None).
  { intros i. unfold nth_slot, am1, new_am. cbn [am_slots]. rewrite nth_repeat'.
    destruct (Nat.ltb _ _); [|reflexivity]. destruct SL as [[-> _]|[-> _]]; reflexivity. }
  unfold install_group. mbinds. apply itok_get. msimp. mbinds. apply itok_set_usage_of. msimp.
  set (s1 := set_usage (zset sc (usage_of s sc + cnt) (st_usage s)) s).
  assert (HI1 : Inv (m :: X) None (Uadd U sc cnt) s1).
  { pose proof (Inv_set_usage (m :: X) None U s sc (usage_of s sc + cnt) HI Hsc
                  ltac:(pose proof (usage_of_nonneg s sc C0); lia)) as H.
    replace (usage_of s sc + cnt - usage_of s sc) with cnt in H by lia. exact H. }
  mbinds. apply itok_setm'. msimp. fold am1.
  set (s2 := upd_meta m (MUsed am1) s1).
  assert (HI2 : Inv (m :: X) None (Uadd U sc cnt) s2).
  { apply Inv_upd_exempt; [exact HI1 | left; reflexivity |]. cbn [am_prev am_next am1 new_am]. auto. }
  assert (M2 : MT s2 m = Some (MUsed am1)) by apply MT_upd_same.
  assert (EU2 : forall q a, usedX (m :: X) s2 q a <-> usedX (m :: X) s q a).
  { intros q a. unfold s2. rewrite usedX_upd_exempt by (left; reflexivity). unfold s1, usedX, MTX, MT. cbn. tauto. }
  assert (Hhd2 : active_hd s2 sc = None) by exact Hhd.
  eapply (queue_op (HActive sc) m s2 (MUsed am1) [] (alinks (m :: X) s2 sc)).
  - exact M2.
  - reflexivity.
  - cbn [head_of]. rewrite Hhd2. apply ring_ok_nil.
  - intros [].
  - intros q l [].
  - cbn. rewrite Clen. lia.
  - intros s3 Sb Hse Hhd3 M3 EO3 _. cbn [hd last head_of with_links] in Hhd3, M3.
    set (am1' := am_set_links (Some m) (Some m) am1) in M3.
    pose proof (links_fields (Some m) (Some m) am1) as (Lmem & Llast & Lsc & Lml & Lai & Lav & Lfr & Lsl & Lp & Ln). fold am1' in Lmem, Llast, Lsc, Lml, Lai, Lav, Lfr, Lsl, Lp, Ln.
    assert (EO : forall q, q <> m -> MT s3 q = MT s2 q) by (intros q Hq; apply EO3; intros [E|[]]; exact (Hq (eq_sym E))).
    pose proof Sb as (_&Emc&_&_&_&_&_&_&_&Eus&_&_&_&_&Erg&_&EK).
    destruct Hse as (HA & HF & HL).
    assert (EH : forall c, 0 <= c -> c <> sc -> active_hd s3 c = active_hd s c).
    { intros c Hc Hne. unfold active_hd. rewrite HA; [reflexivity|]. intros sc' E. injection E as <-. intros E. apply Hne. lia. }
    assert (U3 : usedX X s3 m am1') by (apply (ux_used_m X s2 s3 m am1' NX M3)).
    assert (Hal0 : allocated am1' 0 = true).
    { rewrite <- (strip_allocated am1 am1' 0) by (unfold strip; rewrite <- ?Lsl; destruct am1; reflexivity).
      unfold am1. rewrite new_am_allocated by lia. reflexivity. }
    assert (Hst : strip am1' = strip am1) by (unfold am1', strip; destruct am1; reflexivity).
    apply HQ; [ | exact Hhd3 | exact U3 | exact EH | exact Erg | exact Emc |].
    2:{ apply (ub_same_trans s s2).
        - apply (ub_same_trans s s1); [apply ub_same_metas; reflexivity|].
          unfold s2. apply ub_same_upd_In; [exact Km|]. rewrite (ucontrib_exempt_nil _ _ _ _ m m HI1 (or_introl eq_refl)). cbn.
          apply blocks_of_frameless. exact Hfr1.
        - eapply ub_same_relinked; [|exact EK]. split; [exact EO3|].
          intros q [<-|[]]. exists (MUsed am1), (Some m), (Some m). split; [exact M2|]. split; [exact M3 | discriminate]. }
    eapply (Inv_install X (Some (m, 0)) (Uadd U sc cnt) U s2 s3 m am1' HI2 NX M3 EO EK Erg).
    + (* [comment removed for export] *)
      split.
      { unfold masks_ok. rewrite Llast, Lai, Lsl, Lav, Lfr. apply (new_am_masks mem sc cnt aidx maplen sl); lia. }
      split; [rewrite Lml; cbn; exact Hml|]. split.
      { intros i Hi. rewrite Llast in Hi. cbn [am_last am1 new_am] in Hi.
        unfold slot_ok. rewrite (strip_nth_slot _ _ i Hst), (strip_allocated _ _ i Hst), Lml.
        unfold am1. rewrite new_am_nth_slot by lia. rewrite new_am_allocated by lia. cbn [am_maplen new_am].
        destruct SL as [[-> Hpos]|[-> Hz]]; cbn [ss_hdr ss_fr slot_zero slot_junk].
        - split; [discriminate|]. split; [intros h3 h16 E; injection E as <- <-; lia|].
          destruct (Z.eq_dec i 0) as [->|Hne]; [right; reflexivity | left]. bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia.
        - split; [auto|]. split; [discriminate|].
          destruct (Z.eq_dec i 0) as [->|Hne]; [right; reflexivity | left]. bcase (i =? 0); bcase (cnt - 1 <? i); cbn; try reflexivity; lia. }
      split.
      { replace (class_ok (Some (m, 0)) m am1') with (class_ok (Some (m, 0)) m am1); [exact CL|]. unfold am1'; destruct am1; reflexivity. }
      split.
      { intros Hm. rewrite Lml in Hm. destruct (MP Hm) as (r & rg & H1 & H2 & H3). exists r, rg.
        rewrite Lmem, Lml, Llast, (strip_stride _ _ Hst). unfold region_of in *. rewrite Erg. unfold s2, s1 in *. cbn. cbn in H2. auto. }
      intros Hm. rewrite Lml in Hm. cbn [am_maplen am1 new_am] in Hm. rewrite Lsc, Lmem, Llast. cbn [am_sc am_mem am_last am1 new_am].
      destruct (NS Hm) as (g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem' & Sc' & N63 & Fit).
      split; [lia|]. exists g', am', i', fr'.
      split; [apply (ux_used_fwd X s2 s3 m am1' NX M3 EO); apply EU2; exact U'|].
      replace (cnt - 1 + 1) with cnt by lia. repeat split; auto; lia.
    + (* [comment removed for export] *)
      intros q a Hu Hp. apply EU2 in Hu. rewrite Lmem in Hp.
      destruct (LAM q a Hu Hp) as [D | [I | (Hz & j & fr & Hj & Hfr & Hk & Hmem & Hfit)]].
      * left. unfold spans_disjoint in *. rewrite Lmem, (strip_extent _ _ Hst). exact D.
      * right; right. destruct I as (j & fr & c & ac & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
        exists j, fr, c, ac. rewrite Lmem, (strip_extent _ _ Hst).
        repeat split; auto; try lia. apply (ux_used_fwd X s2 s3 m am1' NX M3 EO). apply EU2. exact H4.
      * right; right. exists j, fr, m, am1'. rewrite Lmem, Lml, (strip_extent _ _ Hst).
        repeat split; auto; try lia; unfold am1; cbn [am_mem am_maplen new_am]; lia.
    + intros Hm q a Hu Ha. rewrite Lml in Hm. rewrite Lmem. apply EU2 in Hu. exact (MU Hm q a Hu Ha).
    + intros Hp q a Hu Hsa. rewrite Lai, Llast in Hp. rewrite Lsc in Hsa. cbn [am_sc am_aidx am_last am1 new_am] in Hp, Hsa.
      destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (_ & _ & _ & E). lia.
    + intros p i E. injection E as <- <-. exists am1'. split; [exact U3|]. rewrite Llast, (strip_nth_slot _ _ 0 Hst).
      cbn [am_last am1 new_am]. split; [lia|]. split; [apply Hfr1 | exact Hal0].
    + intros p i E. injection E as <- <-. reflexivity.
    + intros Hp. rewrite Lai, Llast in Hp. rewrite Lml, Lsc. cbn [am_sc am_aidx am_last am_maplen am1 new_am] in Hp |- *.
      apply HPCG. lia.
    + eapply sbmh_ctx; [exact Sb | exact HL | | exact (inv_ctx HI2)].
      intros Hi. exfalso. destruct (inv_ctx HI2) as (_&_&_&_&_&_&_&_&_&_&_&C12). destruct (C12 Hi) as (Em & _).
      unfold MT in M2. rewrite Em in M2. discriminate.
    + eapply sbmh_keys; [exact Sb | exact (inv_keys HI2)].
    + eapply sbmh_areas; [exact Sb | exact (inv_areas HI2)].
    + destruct (inv_rings HI2) as (F & A & D). split; [|split].
      * eapply (ux_free_ring X s2 s3 m am1' NX M3 EO); [apply HF; discriminate | exact F].
      * intros c Hc. destruct (Z.eq_dec c sc) as [->|Hne].
        -- exists [m]. rewrite Hhd3. split.
           { apply ring_ok_single. rewrite (ux_alinks_m X s2 s3 m am1' NX M3 sc Lsc), Lp, Ln. reflexivity. }
           split.
           { intros q a Hq Hsa. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
             - rewrite Lp, Ln. split; [intros _; discriminate | intros _; left; reflexivity].
             - destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (_ & _ & E & _). rewrite E.
               split; [intros [E'|[]]; exfalso; exact (Hne (eq_sym E')) | intros H; exfalso; apply H; reflexivity]. }
           split.
           { intros q a Hq Hsa Hnin. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
             - exfalso. apply Hnin. left. reflexivity.
             - destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (E1 & E2 & _). auto. }
           split.
           { intros q a Hq Hsa Hav. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]]; [reflexivity|].
             destruct (empty_ring_class _ _ _ _ sc q a HI2 Hsc Hhd2 Hu Hsa) as (E1 & _). exfalso. exact (Hav E1). }
           intros q a Hq Hsa Hin Hne _. destruct Hin as [<-|[]]. exfalso. apply Hne. reflexivity.
        -- eapply (ux_active_other X s2 s3 m am1' NX M3 EO None); [intros q i _ E; discriminate | rewrite Lsc; cbn; lia | | apply A; exact Hc].
           rewrite (EH c ltac:(lia) Hne). reflexivity.
      * intros q a Hq H63. destruct (ux_used_bwd X s2 s3 m am1' NX M3 EO q a Hq) as [[-> ->]|[Hne Hu]].
        -- rewrite Lsc in H63. cbn in H63. lia.
        -- exact (D q a Hu H63).
    + intros c Hc. rewrite (sbmh_usage_of _ _ c Sb). rewrite (inv_usage HI2 c Hc).
      rewrite (ux_class_sum X s2 s3 m am1' NX M3 EO c EK (proj1 (inv_keys HI2)) (MT_Some_In_keys _ _ _ M2)).
      rewrite Lsc, Llast. cbn [am_sc am_last am1 new_am]. unfold Uadd.
      destruct (sc =? c) eqn:E1; destruct (c =? sc) eqn:E2; try lia;
        try (apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; lia); try (apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctx_frame (s s' : astate) : Prop :=
  st_metas s' = st_metas s /\ st_active s' = st_active s /\ st_regions s' = st_regions s /\
  st_usage s' = st_usage s /\ st_mmap_counter s' = st_mmap_counter s /\ st_areas s' = st_areas s.

Lemma step_seq_spec X R U s (Q : unit * astate -> Prop) :
  Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (step_seq s) Q.
Proof.
  intros HI HQ. unfold step_seq. apply itok_modify. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&C8&_).
  destruct (st_seq s =? 255) eqn:E.
  - apply HQ; [|repeat split; reflexivity]. apply Inv_set_seq; [|lia].
    destruct repeat0_32_range as [A B]. apply Inv_set_unmap_seq; [exact HI | exact A | exact B].
  - apply Z.eqb_neq in E. apply HQ; [|repeat split; reflexivity]. apply Inv_set_seq; [exact HI | lia].
Qed.

Lemma record_seq_spec X R U s sc (Q : unit * astate -> Prop) :
  Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (record_seq sc s) Q.
Proof.
  intros HI HQ. unfold record_seq. destruct (bounce_idx sc) as [k|]; [apply itok_modify | apply itok_ret]; (apply HQ; [|repeat split; reflexivity]); [|exact HI].
  pose proof (inv_ctx HI) as (_&_&C3&_&_&C6&_&C8&_).
  destruct (zset_length32_range _ k _ C3 C6 C8) as [A B]. apply Inv_set_unmap_seq; [exact HI | exact A | exact B].
Qed.

Lemma account_bounce_spec X R U s sc (Q : unit * astate -> Prop) :
  Inv X R U s -> (forall s', Inv X R U s' -> ctx_frame s s' -> Q (tt, s')) -> itok (account_bounce sc s) Q.
Proof.
  intros HI HQ. unfold account_bounce. destruct (bounce_idx sc) as [k|]; [apply itok_modify | apply itok_ret]; [|apply HQ; [exact HI | repeat split; reflexivity]].
  pose proof (inv_ctx HI) as (_&_&_&C4&_&_&C7&_).
  destruct (negb (znth k (st_unmap_seq s) =? 0) && (st_seq s - znth k (st_unmap_seq s) <? 10)).
  - apply HQ; [|repeat split; reflexivity].
    assert (Hv : 0 <= (if znth k (st_bounces s) + 1 <? 100 then znth k (st_bounces s) + 1 else 150) <= 255).
    { pose proof (nth_In_range (st_bounces s) (Z.to_nat k) 0 255 C7 ltac:(lia)) as Hr. unfold znth.
      destruct (_ <? 100) eqn:E; [apply Z.ltb_lt in E|]; lia. }
    destruct (zset_length32_range _ k _ C4 C7 Hv) as [A B]. apply Inv_set_bounces; [exact HI | exact A | exact B].
  - apply HQ; [exact HI | repeat split; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma areas_ok_map_region s s' :
  areas_ok s ->
  st_areas s' = st_areas s -> st_area_head s' = st_area_head s -> st_area_tail s' = st_area_tail s ->
  st_meta_alloc_shift s' = st_meta_alloc_shift s -> st_brk s' = st_brk s ->
  st_avail_meta_area_count s' = st_avail_meta_area_count s -> st_avail_meta_areas s' = st_avail_meta_areas s ->
  (forall k rg, region_of s k = Some rg -> rg_kind rg <> RkMap -> region_of s' k = Some rg) ->
  (forall k rg, region_of s' k = Some rg -> rg_kind rg <> RkMap -> region_of s k = Some rg) ->
  resv_total s' = resv_total s -> resv_opened s' = resv_opened s -> resv_count s' = resv_count s -> brk_regions s' = brk_regions s ->
  (forall k rg, region_of s' k = Some rg -> (0 <= rg_len rg /\ (rg_live rg = true -> 0 < rg_len rg)) \/ region_of s k = Some rg) ->
  (forall k rg, region_of s k = Some rg -> exists rg', region_of s' k = Some rg') ->
  areas_ok s'.
Proof.
  intros (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10) Ea Eh Et Es Eb Ec Ep Hfwd Hbwd Er Eo Ecn Ebr Hlen9 Hex. unfold areas_ok.
  rewrite Ea, Eh, Et, Es, Eb, Ec, Ep, Er, Eo, Ecn, Ebr.
  refine (conj A1 (conj _ (conj A3 (conj A4 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))));
    [| | | | | intros k rg Hk; destruct (Hlen9 k rg Hk) as [H|H]; [exact H | eapply A9; exact H]
     | intros Hne; destruct (A10 Hne) as (rg & Hrg); exact (Hex _ _ Hrg)].
  - intros a Ha. destruct (A2 a Ha) as (ra & oa & rga & Ea' & Ho & Hlo & Hrg & Hl & Hhi & Hk).
    exists ra, oa, rga. repeat (split; [assumption|]). split; [| split; [exact Hl | split; [exact Hhi | exact Hk]]].
    apply Hfwd; [exact Hrg|]. destruct (rg_kind rga); [discriminate|discriminate|destruct Hk].
  - intros k rg Hk Hkind. eapply A5; [|exact Hkind]. apply Hbwd; [exact Hk|]. rewrite Hkind. discriminate.
  - destruct A6 as (A6a & A6b & A6c & A6d). split; [exact A6a|]. split; [exact A6b|]. split; [exact A6c|].
    intros rq rgq oq Hrq Hkq Hoq1 Hoq2. rewrite Ec, Ep.
    apply (A6d rq rgq oq); [apply Hbwd; [exact Hrq | rewrite Hkq; discriminate] | exact Hkq | exact Hoq1 | exact Hoq2].
  - destruct (st_brk s) as [| |rb pb].
    + exact A7.
    + intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
      split; [|exact Hrest]. apply Hfwd; [exact Hrg|]. destruct (brk_regions_In _ _ Hrr) as (rg' & Hrg' & K'). rewrite Hrg in Hrg'. injection Hrg' as <-. rewrite K'. discriminate.
    + destruct A7 as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
      split; [|exact Hrest]. apply Hfwd; [exact Hrg|].
      assert (Hin : In rb (brk_regions s)) by (rewrite Hbr; left; reflexivity).
      destruct (brk_regions_In _ _ Hin) as (rg' & Hrg' & K'). rewrite Hrg in Hrg'. injection Hrg' as <-. rewrite K'. discriminate.
  - intros Hc. destruct (A8 Hc) as (r & o & rg & E1 & E2 & E3 & Rest). exists r, o, rg.
    split; [exact E1|]. split; [apply Hfwd; [exact E2 | rewrite E3; discriminate] | exact (conj E3 Rest)].
Qed.

Lemma InvMeta_regions' X R U s rs :
  (forall q a rg, usedX X s q a -> 0 < am_maplen a -> region_of s (prid (am_mem a)) = Some rg ->
     region_of (set_regions rs s) (prid (am_mem a)) = Some rg) ->
  InvMeta X R U s -> InvMeta X R U (set_regions rs s).
Proof.
  intros Hreg (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split; [exact M1|]. split.
  { intros g am Hg. pose proof (M2 g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
    intros Hm. destruct (G5 Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
    split; [exact H1|]. split; [|auto]. pose proof (Hreg g am rg Hg Hm) as E. rewrite H1 in E. cbn [prid] in E. apply E. exact H2. }
  split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.

Lemma Inv_new_map X R U s len :
  Inv X R U s -> 0 < len -> Inv X R U (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s).
Proof.
  intros HI Hlen0. set (x := mkRegion RkMap len [] true). set (s' := set_regions _ s).
  split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split.
  - eapply areas_ok_map_region; try exact (inv_areas HI); try reflexivity.
    + intros k rg Hk _. apply region_of_app. exact Hk.
    + intros k rg Hk Hkind. unfold region_of in Hk |- *. subst s'. cbn [st_regions set_regions] in Hk.
      rewrite nth_error_app in Hk. destruct (Nat.ltb k (length (st_regions s))) eqn:El; [exact Hk|].
      exfalso. destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; apply Hkind; reflexivity | destruct k'; discriminate].
    + subst s'. rewrite resv_total_app. cbn. lia.
    + subst s'. rewrite resv_opened_app. unfold x. cbn [rg_kind]. lia.
    + subst s'. rewrite resv_count_app. unfold x. cbn [rg_kind]. lia.
    + subst s'. rewrite brk_regions_app. cbn. apply app_nil_r.
    + intros k rg Hk. unfold region_of in Hk |- *. subst s'. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
      destruct (Nat.ltb k (length (st_regions s))); [right; exact Hk|].
      destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; left; cbn; split; [lia | intros _; exact Hlen0] | destruct k'; discriminate].
    + intros k rg Hk. exists rg. apply region_of_app. exact Hk.
  - apply InvMeta_regions; [|exact (inv_meta HI)]. intros k rg Hk _. apply region_of_app. exact Hk.
Qed.

Lemma new_region_spec X R U s k len (Q : nat * astate -> Prop) :
  Inv X R U s ->
  (forall s', Inv X R U s' -> s' = set_regions (st_regions s ++ [mkRegion k len [] true]) s -> Q (length (st_regions s), s')) ->
  k = RkMap -> 0 < len ->
  itok (new_region k len s) Q.
Proof.
  intros HI HQ -> Hlen. unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. apply itok_ret.
  apply HQ; [apply Inv_new_map; [exact HI | exact Hlen] | reflexivity].
Qed.

Lemma Inv_kill_map X R U s r rg :
  Inv X R U s -> region_of s r = Some rg -> rg_kind rg = RkMap ->
  (forall q a, usedX X s q a -> 0 < am_maplen a -> prid (am_mem a) <> r) ->
  Inv X R U (set_regions (lupd (st_regions s) r (mkRegion RkMap (rg_len rg) [] false)) s).
Proof.
  intros HI Hr Hk Hno. set (x := mkRegion RkMap (rg_len rg) [] false). set (s' := set_regions _ s).
  assert (ER : forall k, k <> r -> region_of s' k = region_of s k).
  { intros k Hne. subst s'. rewrite region_of_upd. replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact Hne). reflexivity. }
  assert (ERr : region_of s' r = Some x).
  { subst s'. rewrite region_of_upd. rewrite Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. eapply region_of_lt. exact Hr. }
  split; [exact (inv_ctx HI)|]. split; [exact (inv_keys HI)|]. split.
  - eapply areas_ok_map_region; try exact (inv_areas HI); try reflexivity.
    + intros k rg' Hk' Hkind. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite Hr in Hk'; injection Hk' as <-; contradiction|].
      rewrite (ER k Hne). exact Hk'.
    + intros k rg' Hk' Hkind. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ERr in Hk'; injection Hk' as <-; exfalso; apply Hkind; reflexivity|].
      rewrite <- (ER k Hne). exact Hk'.
    + subst s'. eapply resv_total_upd; [exact Hr|]. rewrite Hk. discriminate.
    + subst s'. destruct (resv_oc_upd s r x rg Hr ltac:(rewrite Hk; unfold x; cbn [rg_kind]; discriminate)) as (_ & EO). rewrite EO, Hk. lia.
    + subst s'. destruct (resv_oc_upd s r x rg Hr ltac:(rewrite Hk; unfold x; cbn [rg_kind]; discriminate)) as (EC & _). exact EC.
    + subst s'. eapply brk_regions_upd; [exact Hr|]. rewrite Hk. reflexivity.
    + pose proof (inv_areas HI) as (_&_&_&_&_&_&_&_&A9&_).
      intros k rg' Hk'. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ERr in Hk'; injection Hk' as <-; left; unfold x; cbn [rg_len rg_live]; split; [exact (proj1 (A9 _ _ Hr)) | intros E; discriminate E] | right; rewrite <- (ER k Hne); exact Hk'].
    + intros k rg' Hk'. destruct (Nat.eq_dec k r) as [->|Hne]; [exists x; exact ERr | exists rg'; rewrite (ER k Hne); exact Hk'].
  - apply InvMeta_regions'; [|exact (inv_meta HI)]. intros q a rg' Hu Hm Hq.
    fold s'. rewrite (ER _ (Hno q a Hu Hm)). exact Hq.
Qed.

Lemma upd_region_kill_spec X R U s r rg (Q : unit * astate -> Prop) :
  Inv X R U s -> region_of s r = Some rg -> rg_kind rg = RkMap ->
  (forall q a, usedX X s q a -> 0 < am_maplen a -> prid (am_mem a) <> r) ->
  (forall s', Inv X R U s' -> st_metas s' = st_metas s -> st_active s' = st_active s -> Q (tt, s')) ->
  itok (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) s) Q.
Proof.
  intros HI Hr Hk Hno HQ. unfold upd_region. apply itok_modify.
  unfold region_of in Hr. rewrite (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr).
  apply HQ; [|reflexivity|reflexivity]. apply (Inv_kill_map X R U s r rg HI Hr Hk Hno).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd_slot_fields am i x :
  am_mem (upd_slot am i x) = am_mem am /\ am_last (upd_slot am i x) = am_last am /\
  am_sc (upd_slot am i x) = am_sc am /\ am_maplen (upd_slot am i x) = am_maplen am /\
  stride_of (upd_slot am i x) = stride_of am /\ group_extent (upd_slot am i x) = group_extent am /\
  (forall j, slot_start (upd_slot am i x) j = slot_start am j).
Proof. destruct am; repeat split; reflexivity. Qed.

Lemma nested_lam X U s2 g idx am hdr n q a sc cnt0 :
  Inv X (Some (g, idx)) U s2 -> usedX X s2 g am -> n = stride_of am - IB ->
  let am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 n FGroup))) in
  let s3 := upd_meta g (MUsed am') s2 in
  let am1 := new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk in
  0 < group_extent am1 <= n ->
  usedX X s3 q a -> prid (am_mem a) = prid (am_mem am) ->
  spans_disjoint a am1 \/ inside X s3 am1 a \/
  (exists j fr, 0 <= j <= am_last a /\ ss_fr (nth_slot a j) = Some fr /\ fr_kind fr = FGroup /\
     slot_start am idx = slot_start a j /\ group_extent am1 <= fr_n fr).
Proof.
  intros HI Hg Hn am' s3 am1 Hext Hq Hpr.
  pose proof (usedX_MT _ _ _ _ Hg) as [Mg NXg].
  destruct (inv_reserved HI g idx eq_refl) as (amg & Hg' & Hidx & Hfr0 & _).
  pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
  pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((_ & _ & Glen & _) & _ & Gsl & _).
  pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 n FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
  assert (Emem1 : am_mem am1 = slot_start am idx) by reflexivity.
  assert (P1 : poff (am_mem am1) = poff (am_mem am) + UNIT + stride_of am * idx) by (rewrite Emem1; apply poff_slot_start).
  apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
  - (* [comment removed for export] *)
    injection E as <-. right; right. exists idx, (mkFrame 0 n FGroup). rewrite Fl, Fss.
    split; [exact Hidx|]. split; [|split; [reflexivity|split; [reflexivity|cbn [fr_n]; lia]]].
    unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity.
  - destruct (inv_laminar HI q a g am Hq Hg Hne Hpr) as [D | [I | I]].
    + left. unfold spans_disjoint in *. rewrite P1.
      assert (0 <= stride_of am * idx) by nia.
      assert (stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
      assert (Hspan : poff (am_mem am) + UNIT + stride_of am * idx + group_extent am1 <= poff (am_mem am) + group_extent am).
      { unfold group_extent at 2. unfold UNIT, IB in *. lia. }
      unfold UNIT, IB in *. lia.
    + (* [comment removed for export] *)
      destruct I as (j' & fr' & c & ac & Hj' & Hfr' & Hk' & Uc & Mlc & Memc & Lo & Hi & Fit).
      destruct (Z.eq_dec j' idx) as [->|Hjne]; [rewrite Hfr0 in Hfr'; discriminate|].
      left. unfold spans_disjoint. rewrite P1.
      pose proof (Gsl j' Hj') as (_ & _ & S3). rewrite Hfr' in S3. destruct S3 as (_ & _ & (N' & O' & B' & _) & _).
      rewrite Memc, poff_slot_start in Lo, Hi.
      destruct (same_group_starts am j' idx Hjne Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left | right]; lia.
    + (* [comment removed for export] *)
      destruct I as (j' & fr' & c & ac & Hj' & Hfr' & Hk' & Uc & Mlc & Memc & Lo & Hi & Fit).
      right; left.
      assert (Uc3 : exists ac', usedX X s3 c ac' /\ am_mem ac' = am_mem ac /\ group_extent ac' = group_extent ac /\ am_maplen ac' = am_maplen ac).
      { destruct (sptr_eq_dec c g) as [->|Hcg].
        - pose proof (usedX_fun _ _ _ _ _ Uc Hg) as ->. exists am'. split; [|auto].
          apply usedX_upd. left. auto.
        - exists ac. split; [|auto]. apply usedX_upd. right. auto. }
      destruct Uc3 as (ac' & Uc' & Em' & Ex' & Ml').
      assert (0 <= stride_of am * idx) by nia.
      assert (stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
      assert (Hspan : poff (am_mem am) + UNIT + stride_of am * idx + group_extent am1 <= poff (am_mem am) + group_extent am).
      { unfold group_extent at 2. unfold UNIT, IB in *. lia. }
      exists j', fr', c, ac'. rewrite Em', Ex', Ml', P1.
      repeat split; auto; unfold UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma remove_head_notin m X : memb m X = false -> remove sptr_eq_dec m (m :: X) = X.
Proof.
  intros H. cbn. destruct (sptr_eq_dec m m) as [_|N]; [|exfalso; exact (N eq_refl)].
  apply notin_remove. apply memb_false_notIn. exact H.
Qed.

Lemma land32_range a : 0 <= a -> 0 <= Z.land a (2 ^ 32 - 1) < 2 ^ 32.
Proof.
  intros Ha. change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma padd_0 p : padd p 0 = p.
Proof. destruct p. cbn. f_equal. lia. Qed.

Definition heads_below (s s' : astate) (sc : Z) : Prop :=
  forall c, 0 <= c < sc -> active_hd s' c = active_hd s c.

Definition slot_post (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : Z * astate) : Prop :=
  heads_below s (snd r) sc /\ ub_same s (snd r) /\
  ((fst r = -1 /\ Inv X None U (snd r)) \/
   (0 <= fst r /\ exists g am, Inv X (Some (g, fst r)) U (snd r) /\ active_hd (snd r) sc = Some g /\
      usedX X (snd r) g am /\ am_sc am = sc /\ req + IB <= stride_of am /\ fst r <= am_last am)).

Definition group_post (X : list sptr) (U : Z -> Z) (s : astate) (sc req : Z) (r : option sptr * astate) : Prop :=
  heads_below s (snd r) sc /\ ub_same s (snd r) /\
  match fst r with
  | None => Inv X None U (snd r)
  | Some m => exists am, Inv X (Some (m, 0)) U (snd r) /\ active_hd (snd r) sc = Some m /\
      usedX X (snd r) m am /\ am_sc am = sc /\ req + IB <= stride_of am /\ 0 <= am_last am
  end.

Theorem alloc_mutual fuel :
  (forall X U s sc req (Q : Z * astate -> Prop),
     Inv X None U s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
     (forall r, slot_post X U s sc req r -> Q r) -> itok (alloc_slot fuel sc req s) Q) /\
  (forall X U s sc req (Q : option sptr * astate -> Prop),
     Inv X None U s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= S fuel)%nat ->
     active_hd s sc = None ->
     (forall r, group_post X U s sc req r -> Q r) -> itok (alloc_group fuel sc req s) Q).
Proof.
  induction fuel as [|f [IHs IHg]].
  { split; intros X U s sc req Q HI Hsc Hreq Hfit Hf; pose proof (need_ge2 sc); lia. }
  split.
  - (* [comment removed for export] *)
    intros X U s sc req Q HI Hsc Hreq Hfit Hf HQ.
    cbn fix beta iota delta [alloc_slot]. mbinds.
    eapply try_avail_spec; [exact HI | exact Hsc | |].
    + intros s1 HI1 Hhd1 EH1 UB1. msimp. cbn [Z.eqb negb]. mbinds.
      eapply IHg; [exact HI1 | exact Hsc | exact Hreq | exact Hfit | exact Hf | exact Hhd1 |].
      intros [og s2] [HB [UB2 Hpost]]. msimp. cbn [fst snd] in HB, UB2, Hpost.
      assert (HB' : heads_below s s2 sc) by (intros c Hc; rewrite (HB c Hc); apply EH1; lia).
      assert (UB' : ub_same s s2) by (eapply ub_same_trans; [exact UB1 | exact UB2]).
      destruct og as [g|].
      * apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. right. cbn [fst snd]. split; [lia|].
        destruct Hpost as (am & H1 & H2 & H3 & H4 & H5 & H6). exists g, am. repeat (split; [assumption|]). exact H6.
      * apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. left. split; [reflexivity | exact Hpost].
    + intros first s1 (Hnz & g & am & HI1 & Hhd1 & U1 & Sc1 & Str1 & Hidx & EH1 & UB1). msimp.
      destruct (first =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
      apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [intros c Hc; apply EH1; lia|]. split; [exact UB1|]. right. cbn [fst snd].
      split; [lia|]. exists g, am. repeat (split; [assumption|]). split; [lia | lia].
  - (* [comment removed for export] *)
    intros X U s sc req Q HI Hsc Hreq Hfit Hf Hhd HQ.
    pose proof (class_size_bounds sc Hsc) as [S16 Smax].
    cbn fix beta iota delta [alloc_group]. mbinds.
    eapply alloc_meta_spec; [exact HI | |].
    { intros s1 HI1 Fr1 EU1 UB1. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split; [exact UB1 | exact HI1]].
      intros c Hc. destruct Fr1 as (EA & _). unfold active_hd. rewrite EA. reflexivity. }
    intros m s1 HI1 NX Km Mm Fr1 EU1 UB1. msimp. mbinds. apply itok_get. msimp. cbn zeta.
    pose proof Fr1 as (EA1 & EUs1 & _ & Len1 & Emc1).
    assert (Hhd1 : active_hd s1 sc = None) by (unfold active_hd; rewrite EA1; exact Hhd).
    pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (Hc0 & Hc0s & Hc026).
    set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
    assert (FRESH : forall q a, usedX (m :: X) s1 q a -> (prid (am_mem a) < length (st_regions s1))%nat).
    { intros q a Hu. apply EU1 in Hu. pose proof (used_group_prid_lt _ _ _ _ q a HI Hu). lia. }
    destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Ebr.
    + (* [comment removed for export] *)
      set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)).
      destruct plan as [cnt needed] eqn:Ep. subst plan. cbn [fst snd].
      pose proof (mmap_plan_facts s1 sc req cnt0 (usage_of s1 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep)
        as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
      mbinds. eapply account_bounce_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _). msimp.
      mbinds. eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & Ea3 & Er3 & Eu3 & Ec3 & _). msimp.
      mbinds. apply itok_ask; [cbn; unfold PGSZ in N4096; clear - N4096 Nmax; lia|]. intros z _. msimp.
      assert (EU3 : forall q a, usedX (m :: X) s3 q a <-> usedX (m :: X) s1 q a).
      { intros q a. unfold usedX, MTX, MT. rewrite Em3, Em2. tauto. }
      destruct (z =? 0); cbn [negb].
      * (* [comment removed for export] *)
        mbinds. eapply free_meta_spec; [exact HI3 | left; reflexivity |]. intros s4 HI4 Sb4 Ea4 EU4 UB4. msimp.
        apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
        -- intros c Hc. unfold active_hd. rewrite Ea4, Ea3, Ea2, EA1. reflexivity.
        -- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB4].
           apply ub_same_metas. rewrite Em3, Em2. reflexivity.
        -- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI4. exact HI4.
      * (* [comment removed for export] *)
        rewrite (page_round_fixed needed Nmod).
        mbinds. eapply new_region_spec; [exact HI3 | | reflexivity | unfold PGSZ in N4096; lia]. intros s4 HI4 Es4. msimp.
        mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
        set (r := length (st_regions s3)).
        set (s5 := set_mmap_counter (Z.land (st_mmap_counter s4 + 1) (2 ^ 32 - 1)) s4).
        pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
        assert (HI5 : Inv (m :: X) None U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
        assert (EU5 : forall q a, usedX (m :: X) s5 q a <-> usedX (m :: X) s1 q a).
        { intros q a. rewrite <- EU3. unfold usedX, MTX, MT. subst s5 s4. cbn. tauto. }
        assert (Hr5 : region_of s5 r = Some (mkRegion RkMap needed [] true)).
        { subst s5 s4 r. unfold region_of. cbn [st_regions set_mmap_counter set_regions]. apply region_of_app_new. }
        set (aidx := if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
                     else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1).
        assert (Haidx : 0 <= aidx <= cnt - 1).
        { subst aidx. destruct (cnt - 1 <? (4096 - UNIT) / class_size sc - 1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
            (destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia. }
        assert (Hml : 1 <= needed / 4096).
        { apply Z.div_le_lower_bound; unfold PGSZ in *; lia. }
        assert (Hml' : needed / 4096 * 4096 = needed).
        { pose proof (Z_div_mod_eq_full needed 4096). unfold PGSZ in Nmod. lia. }
        mbinds. eapply (install_group_spec X U s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
        -- intros _. split; [lia|]. intros E0. rewrite E0 in Ebr. apply Z.ltb_lt in Ebr. change (class_size 0) with 16 in Ebr.
           unfold PGSZ, UNIT in Ebr. pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (B1 & _ & _). fold cnt0 in B1. change (4096 / 2) with 2048 in Ebr. clear - B1 Ebr. lia.
        -- exact HI5.
        -- exact NX.
        -- exact Hsc.
        -- exact Hcnt.
        -- exact Haidx.
        -- lia.
        -- unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions]. rewrite Ea3, Ea2. exact Hhd1.
        -- left. split; [reflexivity | lia].
        -- (* [comment removed for export] *)
           right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride.
           split; [exact Hsc|]. split; [|split].
           ++ intros Hlt. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
              ** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. split; [exact E|]. rewrite new_am_allocated by lia. reflexivity.
              ** lia.
           ++ intros H26. right. specialize (Hc26 H26). lia.
           ++ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
              ** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
              ** replace (cnt - 1 + 1) with cnt by lia. exact Hcs.
        -- (* [comment removed for export] *)
           intros _. exists r, (mkRegion RkMap needed [] true). cbn [am_mem am_maplen am_last new_am rg_kind rg_live rg_len].
           split; [reflexivity|]. split; [exact Hr5|]. split; [reflexivity|]. split; [reflexivity|].
           rewrite new_am_stride. unfold PGSZ. split; [lia|]. split.
           { destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
             ++ apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
             ++ destruct (Z.eq_dec cnt 1) as [->|Hne1].
                { exfalso. cbn [Z.sub Z.eqb] in E. destruct (needed / 4096 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia | discriminate]. }
                replace (cnt - 1 + 1) with cnt by lia. specialize (Nfit ltac:(lia)). lia. }
           cbn [am_sc new_am]. intros Hl0 _. specialize (Npr ltac:(lia)). unfold PGSZ in Npr |- *. lia.
        -- intros H0. lia.
        -- intros q a Hu Hp. exfalso. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
        -- intros _ q a Hu _ Hp. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. lia.
        -- intros s6 HI6 Hhd6 U6 EH6 Er6 Ec6 UB6. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
           ++ intros c Hc. rewrite (EH6 c ltac:(lia) ltac:(lia)). unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions].
              rewrite Ea3, Ea2, EA1. reflexivity.
           ++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB6].
              apply ub_same_metas. subst s5 s4. cbn. rewrite Em3, Em2. reflexivity.
           ++ cbn [fst snd]. eexists. split; [exact HI6|]. split; [exact Hhd6|]. split; [exact U6|].
              pose proof (links_fields (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) as (_ & Ll & Ls & _).
              rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
              rewrite (strip_stride _ (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) by (unfold strip; reflexivity).
              rewrite new_am_stride. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)); unfold UNIT, IB in *; lia.
    + (* [comment removed for export] *)
      apply Z.ltb_ge in Ebr.
      pose proof (nested_facts sc cnt0 Hsc ltac:(lia) Hc026 Ebr) as NF. cbv zeta in NF.
      destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
      set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
      mbinds.
      eapply (IHs (m :: X) U s1 j total); [exact HI1 | exact Hj48 | lia | exact Hjfit | |].
      { pose proof (need_nested sc j H23 ltac:(lia)). lia. }
      intros [idx s2] [HB2 [UB2 Hpost]]. msimp. cbn [fst snd] in HB2, UB2, Hpost.
      destruct (idx <? 0) eqn:Eneg.
      * (* [comment removed for export] *)
        apply Z.ltb_lt in Eneg. destruct Hpost as [[_ HI2] | [Hge _]]; [|cbn [fst] in Hge; lia]. cbn [snd] in HI2.
        mbinds. eapply free_meta_spec; [exact HI2 | left; reflexivity |]. intros s3 HI3 Sb3 Ea3 EU3 UB3. msimp.
        apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
        -- intros c Hc. pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E |- *. rewrite Ea3, E, EA1. reflexivity.
        -- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2 | exact UB3].
        -- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI3. exact HI3.
      * apply Z.ltb_ge in Eneg. destruct Hpost as [[Hm1 _] | [_ (g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hidx2)]]; [cbn [fst] in Hm1; lia|].
        cbn [fst snd] in HI2, Hhd2, U2, Hidx2, HB2.
        mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat j) (st_active s2) None) with (active_hd s2 j). rewrite Hhd2. msimp.
        pose proof (inv_groups HI2 g am U2) as G2. pose proof G2 as ((_ & _ & Glen & _) & Gml & _ & Gcl & _).
        assert (Hstr : stride_of am = class_size j).
        { destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
          unfold stride_of. rewrite Sc2. destruct C26 as [C|C]; [rewrite C|].
          - destruct (am_last am =? 0); reflexivity.
          - destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
        mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U2))|]. msimp.
        mbinds. apply itok_mcheck; [rewrite Hstr; apply Z.eqb_refl|]. msimp.
        mbinds. apply itok_get. msimp.
        pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
        mbinds. eapply (enframe_spec (m :: X) U s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup am);
          [exact HI2 | exact U2 | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity | intros H63; exfalso; lia
          | intros _ _; rewrite Sc2; exact Hhd2 |].
        intros off s3 hdr Hoff Hofit Hoff0 Es3 HI3. msimp. specialize (Hoff0 eq_refl). subst off. rewrite Z.mul_0_r, padd_0.
        set (am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) in Es3.
        pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
        assert (U3 : usedX (m :: X) s3 g am').
        { rewrite Es3. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. auto. }
        assert (Hext1 : group_extent (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk) = total).
        { unfold group_extent. rewrite new_am_stride. cbn [am_last new_am Z.eqb andb negb].
          destruct (cnt0 - 1 =? 0); cbn [andb]; subst total; (replace (cnt0 - 1 + 1) with cnt0 by lia); lia. }
        mbinds. eapply (install_group_spec X U s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
        -- intros H. lia.
        -- exact HI3.
        -- exact NX.
        -- exact Hsc.
        -- lia.
        -- lia.
        -- lia.
        -- rewrite Es3. unfold active_hd. cbn. pose proof (HB2 sc ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. exact Hhd.
        -- right. split; reflexivity.
        -- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
           replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity).
           split; [exact Hsc|]. split; [lia|]. split; [auto|]. replace (cnt0 - 1 + 1) with cnt0 by lia. exact Hc0s.
        -- intros H0. cbn in H0. lia.
        -- intros _. exists g, am', idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc, Fss. cbn [fr_kind fr_n].
           split; [exact U3|]. split; [lia|]. split.
           { unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
           split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. subst total. unfold UNIT, IB in *. nia.
        -- intros q a Hu Hp. rewrite prid_slot_start in Hp. rewrite Es3 in Hu.
           assert (Htot2 : 0 < total <= class_size j - IB).
           { pose proof Hjfit as HJ. subst total. unfold UNIT, IB in *. split; [nia | lia]. }
           destruct (nested_lam (m :: X) U s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
                       ltac:(rewrite Hext1; exact Htot2) Hu Hp) as [D | [I | P]].
           ++ left. exact D.
           ++ right; left. rewrite Es3. exact I.
           ++ right; right. split; [reflexivity|]. exact P.
        -- intros H0. lia.
        -- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4. msimp. apply itok_ret. apply HQ; unfold group_post, slot_post; cbn [fst snd]; split; [|split].
           ++ intros c Hc. rewrite (EH4 c ltac:(lia) ltac:(lia)). rewrite Es3. unfold active_hd. cbn [st_active upd_meta set_metas].
              pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. reflexivity.
           ++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2|]. eapply ub_same_trans; [|exact UB4].
              rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))|].
              rewrite (proj1 (usedX_MT _ _ _ _ U2)). cbn. apply blocks_of_upd_slot_same; [lia | exact Glen |].
              unfold slotst_block, slot_block. cbn. destruct (inv_reserved HI2 g idx eq_refl) as (am_ & U_ & _ & Hfr_ & _).
              pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_. rewrite Hfr_. reflexivity.
           ++ cbn [fst snd]. eexists. split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|].
              pose proof (links_fields (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) as (_ & Ll & Ls & _).
              rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
              rewrite (strip_stride _ (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) by (unfold strip; reflexivity).
              rewrite new_am_stride. cbn [Z.eqb andb negb]. replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity). lia.
Qed.
End MallocWfGroup.

Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pairwise_app {A} (R : A -> A -> Prop) (u v : list A) :
  pairwise R u -> pairwise R v -> (forall x y, In x u -> In y v -> R x y) -> pairwise R (u ++ v).
Proof.
  revert v. induction u as [|x t IH]; intros v Hu Hv Hx; cbn; [exact Hv|].
  destruct Hu as [H1 H2]. split.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy]; [apply H1; exact Hy | apply Hx; [left; reflexivity | exact Hy]].
  - apply IH; [exact H2 | exact Hv |]. intros a b Ha Hb. apply Hx; [right; exact Ha | exact Hb].
Qed.

Lemma pairwise_flat_map {A B} (R : B -> B -> Prop) (f : A -> list B) (l : list A) :
  (forall a, In a l -> pairwise R (f a)) ->
  (forall l1 a l2 b, l = l1 ++ a :: l2 -> In b l2 -> forall x y, In x (f a) -> In y (f b) -> R x y) ->
  pairwise R (flat_map f l).
Proof.
  induction l as [|a t IH]; intros Hin Hord; cbn; [exact I|].
  apply pairwise_app.
  - apply Hin. left. reflexivity.
  - apply IH; [intros; apply Hin; right; assumption|].
    intros l1 a' l2 b E Hb. apply (Hord (a :: l1) a' l2 b); [rewrite E; reflexivity | exact Hb].
  - intros x y Hx Hy. apply in_flat_map in Hy as [b [Hb Hy]]. eapply (Hord [] a t b eq_refl Hb); assumption.
Qed.

Lemma pairwise_map_In {A B} (R : B -> B -> Prop) (f : A -> B) l a b :
  pairwise R (map f l) -> In a l -> In b l -> a <> b -> R (f a) (f b) \/ R (f b) (f a).
Proof.
  induction l as [|x t IH]; intros HP Ha Hb Hne; [destruct Ha|]. cbn in HP. destruct HP as [H1 H2].
  destruct Ha as [->|Ha]; destruct Hb as [->|Hb].
  - exfalso. exact (Hne eq_refl).
  - left. apply H1. apply in_map. exact Hb.
  - right. apply H1. apply in_map. exact Ha.
  - apply IH; assumption.
Qed.

Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) l :
  map f (flat_map g l) = flat_map (fun a => map f (g a)) l.
Proof. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite map_app, IH. reflexivity. Qed.

Lemma ranges_disjoint_sym a b : ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. tauto. Qed.

Lemma ranges_disjoint_incl a a' b b' :
  ranges_disjoint a b -> range_incl a' a -> range_incl b' b -> ranges_disjoint a' b'.
Proof. unfold ranges_disjoint, range_incl. lia. Qed.

Lemma In_split_first {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a : A) l :
  In a l -> exists l1 l2, l = l1 ++ a :: l2.
Proof. intros H. apply in_split. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma used_metas_usedX s g am : WF s -> (In (g, am) (used_metas s) <-> usedX [] s g am).
Proof.
  intros HW. rewrite (used_metas_iff s g am (proj1 (inv_keys HW))). unfold usedX, MTX. cbn. tauto.
Qed.

Lemma NoDup_used_metas_keys s : NoDup (keys s) -> NoDup (map fst (used_metas s)).
Proof.
  unfold keys, used_metas. induction (st_metas s) as [|[p x] t IH]; intros ND; cbn; [constructor|].
  inversion ND as [|p' t' Hp Ht]; subst. destruct x as [| |am]; cbn; try (apply IH; exact Ht).
  constructor; [|apply IH; exact Ht]. intros Hin. apply Hp. apply in_map_iff in Hin as [[q a] [E Hin]]. cbn in E. subst q.
  apply in_flat_map in Hin as [[q y] [Hq Hin]]. destruct y as [| |b]; cbn in Hin; [destruct Hin | destruct Hin |]. destruct Hin as [E|[]].
  injection E as -> ->. apply in_map_iff. exists (p, MUsed a). auto.
Qed.

Lemma used_metas_split s l1 g am l2 g' am' :
  NoDup (keys s) -> used_metas s = l1 ++ (g, am) :: l2 -> In (g', am') l2 -> g <> g'.
Proof.
  intros ND E Hin Heq. subst g'. pose proof (NoDup_used_metas_keys s ND) as N. rewrite E, map_app in N. cbn in N.
  apply NoDup_remove_2 in N. apply N. apply in_app_iff. right. apply in_map_iff. exists (g, am'). auto.
Qed.

Lemma footprint_region_In s k rg :
  region_of s k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
  In (LMem (SP k 0), rg_len rg) (footprint s).
Proof.
  intros Hr Hk Hl. unfold footprint. right. apply in_app_iff. right. apply in_flat_map. exists k. split.
  - apply in_seq. pose proof (region_of_lt _ _ _ Hr). lia.
  - rewrite Hr, Hk, Hl. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem group_in_mapping : forall s g am,
  WF s -> In (g, am) (used_metas s) ->
  exists k o rg, am_mem am = SP k o /\ region_of s k = Some rg /\ rg_kind rg = RkMap /\
    rg_live rg = true /\ 0 <= o /\ o + group_extent am <= rg_len rg /\
    (0 < am_maplen am -> o = 0).
Proof.
  intros s g am HW Hin. apply (used_metas_usedX s g am HW) in Hin.
  destruct (used_group_region [] None U0 s g am HW Hin) as (rg & Hr & Hk & Hl & Ho & Hext & Hz).
  destruct (am_mem am) as [k o] eqn:Em. exists k, o, rg. cbn [prid poff] in *. unfold IB in Hext. repeat split; auto. lia.
Qed.

Theorem meta_in_area : forall s p x,
  WF s -> In (p, x) (st_metas s) ->
  exists a k, In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\ p = padd a (AREA_HDR + META_SIZE * k).
Proof.
  intros s p x HW Hin. pose proof (inv_keys HW) as (ND & KP & _ & _ & Hcnt).
  destruct (KP p ltac:(unfold keys; apply in_map_iff; exists (p, x); auto)) as (a & k & Ha & Hk & E).
  exists a, k. split; [exact Ha|]. split; [|exact E]. unfold handed in Hk. destruct (sptr_eqb a _); lia.
Qed.

Theorem avail_meta_in_area : forall s,
  WF s -> 0 < st_avail_meta_count s ->
  exists a k, In a (st_areas s) /\ 0 <= k < METAS_PER_AREA /\
    st_avail_meta s = padd a (AREA_HDR + META_SIZE * k).
Proof.
  intros s HW Hc. pose proof (inv_keys HW) as (ND & KP & Hnil & Hav & Hcnt).
  destruct (st_areas s) as [|a0 t] eqn:Ea; [rewrite (Hnil eq_refl) in Hc; lia|].
  exists (last (a0 :: t) (SP 0%nat 0)), (METAS_PER_AREA - st_avail_meta_count s).
  split; [|split; [lia | apply Hav; discriminate]].
  rewrite <- Ea. rewrite <- Ea in *. clear Ea. destruct (st_areas s) as [|b u] eqn:E; [exfalso|].
  { rewrite (Hnil eq_refl) in Hc. lia. }
  apply In_last. discriminate.
Qed.

Theorem indices_in_range : forall s g am,
  WF s -> In (g, am) (used_metas s) ->
  (am_sc am < 48 -> 0 <= am_sc am < 48) /\ 0 <= am_aidx am <= 31 /\ 0 <= am_last am <= 31 /\
  (forall sc, 0 <= sc < 48 -> match bounce_idx sc with Some k => 0 <= k < 32 | None => True end).
Proof.
  intros s g am HW Hin. apply (used_metas_usedX s g am HW) in Hin.
  pose proof (inv_groups HW g am Hin) as ((M1 & M2 & _) & _ & _ & Gcl & _).
  split; [|split; [lia|split; [lia|]]].
  - intros H. destruct Gcl as [(C & _) | (C & _)]; lia.
  - intros sc Hsc. unfold bounce_idx. destruct ((7 <=? sc) && (sc <? 39)) eqn:E; [|exact I].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma block_in_slot s g am i fr :
  WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  poff (slot_start am i) <= poff (frame_ptr am i fr) /\
  poff (frame_ptr am i fr) + fr_n fr <= poff (slot_start am i) + stride_of am - IB /\ 0 <= fr_n fr.
Proof.
  intros HW Hu Hi Hfr. pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
  unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
Qed.

Lemma in_user_blocks_inv s b :
  In b (user_blocks s) ->
  exists g am i fr, In (g, am) (used_metas s) /\ 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr /\
    fr_kind fr = FUser /\ b = (frame_ptr am i fr, fr_n fr).
Proof.
  intros Hin. unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]]. cbn [snd] in Hin.
  apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hin].
  destruct (fr_kind fr) eqn:Ek; [|destruct Hin]. destruct Hin as [E|[]].
  exists g, am, i, fr. repeat split; auto; try lia. all: rewrite <- E; reflexivity.
Qed.

Theorem blocks_in_footprint : forall s L b,
  WF s -> layout_ok L s -> In b (user_blocks s) ->
  exists rg, In rg (footprint s) /\ range_incl (block_range L b) (crange L rg).
Proof.
  intros s L b HW HL Hin.
  destruct (in_user_blocks_inv s b Hin) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
  apply (used_metas_usedX s g am HW) in Hg.
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [apply footprint_region_In; assumption|].
  pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (B1 & B2 & B3).
  pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S2].
  unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
  unfold frame_ptr, slot_start in *. destruct (am_mem am) as [k o]. cbn [padd prid poff] in *.
  unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma blocks_same_group_disjoint s g am i j fi fj :
  WF s -> usedX [] s g am -> 0 <= i <= am_last am -> 0 <= j <= am_last am -> i <> j ->
  ss_fr (nth_slot am i) = Some fi -> ss_fr (nth_slot am j) = Some fj ->
  poff (frame_ptr am i fi) + fr_n fi <= poff (frame_ptr am j fj) \/
  poff (frame_ptr am j fj) + fr_n fj <= poff (frame_ptr am i fi).
Proof.
  intros HW Hu Hi Hj Hne Hfi Hfj.
  pose proof (block_in_slot s g am i fi HW Hu Hi Hfi) as (A1 & A2 & A3).
  pose proof (block_in_slot s g am j fj HW Hu Hj Hfj) as (B1 & B2 & B3).
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hu)) as Sp.
  destruct (same_group_starts am i j Hne Sp) as [LE|LE]; unfold IB in *; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Lemma blocks_other_group_disjoint s g1 a1 i1 f1 g2 a2 i2 f2 :
  WF s -> usedX [] s g1 a1 -> usedX [] s g2 a2 -> g1 <> g2 -> prid (am_mem a1) = prid (am_mem a2) ->
  0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
  ss_fr (nth_slot a1 i1) = Some f1 -> fr_kind f1 = FUser -> ss_fr (nth_slot a2 i2) = Some f2 -> fr_kind f2 = FUser ->
  poff (frame_ptr a1 i1 f1) + fr_n f1 <= poff (frame_ptr a2 i2 f2) \/
  poff (frame_ptr a2 i2 f2) + fr_n f2 <= poff (frame_ptr a1 i1 f1).
Proof.
  intros HW U1 U2 Hne Hr Hi1 Hi2 F1 K1 F2 K2.
  pose proof (block_in_slot s g1 a1 i1 f1 HW U1 Hi1 F1) as (A1 & A2 & A3).
  pose proof (block_in_slot s g2 a2 i2 f2 HW U2 Hi2 F2) as (B1 & B2 & B3).
  pose proof (slot_in_span [] None U0 s HW g1 a1 i1 U1 Hi1) as [S1 S1'].
  pose proof (slot_in_span [] None U0 s HW g2 a2 i2 U2 Hi2) as [S2 S2'].
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW g1 a1 U1)) as Sp1.
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW g2 a2 U2)) as Sp2.
  assert (K : forall ga a ia fa gb b ib fb,
            usedX [] s ga a -> usedX [] s gb b -> 0 <= ia <= am_last a -> 0 <= ib <= am_last b ->
            ss_fr (nth_slot a ia) = Some fa -> ss_fr (nth_slot b ib) = Some fb -> fr_kind fb = FUser ->
            inside [] s a b ->
            poff (frame_ptr a ia fa) + fr_n fa <= poff (frame_ptr b ib fb) \/
            poff (frame_ptr b ib fb) + fr_n fb <= poff (frame_ptr a ia fa)).
  { intros ga a ia fa gb b ib fb Ua Ub Hia Hib Fa Fb Kb I.
    pose proof (block_in_slot s ga a ia fa HW Ua Hia Fa) as (C1 & C2 & C3).
    pose proof (block_in_slot s gb b ib fb HW Ub Hib Fb) as (D1 & D2 & D3).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW gb b Ub)) as Spb.
    destruct (inside_slot_start [] None U0 s HW ga a ia gb b Ua Ub Hia I) as (j & fr & Hj & Hfrj & Hkj & Lo & Hi).
    destruct (Z.eq_dec j ib) as [->|Hjne]; [rewrite Fb in Hfrj; injection Hfrj as ->; rewrite Kb in Hkj; discriminate|].
    destruct (same_group_starts b j ib Hjne Spb) as [LE|LE]; unfold UNIT, IB in *; [left|right]; lia. }
  destruct (inv_laminar HW g1 a1 g2 a2 U1 U2 Hne Hr) as [D | [I | I]].
  - unfold spans_disjoint in D. unfold IB, UNIT in *. destruct D; [left|right]; lia.
  - exact (K g1 a1 i1 f1 g2 a2 i2 f2 U1 U2 Hi1 Hi2 F1 F2 K2 I).
  - destruct (K g2 a2 i2 f2 g1 a1 i1 f1 U2 U1 Hi2 Hi1 F2 F1 K1 I); [right|left]; assumption.
Qed.

Lemma zseq_split lo n l1 i l2 j : zseq lo n = l1 ++ i :: l2 -> In j l2 -> i < j.
Proof.
  unfold zseq. generalize 0%nat as st. generalize (Z.to_nat n) as m. clear n.
  intros m. revert l1. induction m as [|m IH]; intros l1 st E Hj.
  - destruct l1; discriminate.
  - cbn in E. destruct l1 as [|x l1']; cbn in E.
    + injection E as <- E. subst l2. apply in_map_iff in Hj as [k [<- Hk]]. apply in_seq in Hk. lia.
    + injection E as _ E. eapply IH; [exact E | exact Hj].
Qed.

Theorem user_blocks_disjoint : forall s L,
  WF s -> layout_ok L s -> pairwise ranges_disjoint (map (block_range L) (user_blocks s)).
Proof.
  intros s L HW HL. destruct HL as (_ & _ & PW & _).
  assert (REG : forall g1 a1 i1 f1 g2 a2 i2 f2,
            usedX [] s g1 a1 -> usedX [] s g2 a2 -> 0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
            ss_fr (nth_slot a1 i1) = Some f1 -> ss_fr (nth_slot a2 i2) = Some f2 ->
            prid (am_mem a1) <> prid (am_mem a2) ->
            ranges_disjoint (block_range L (frame_ptr a1 i1 f1, fr_n f1)) (block_range L (frame_ptr a2 i2 f2, fr_n f2))).
  { assert (INCL : forall g a i f, usedX [] s g a -> 0 <= i <= am_last a -> ss_fr (nth_slot a i) = Some f ->
       exists rg, region_of s (prid (am_mem a)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
         range_incl (block_range L (frame_ptr a i f, fr_n f)) (crange L (LMem (SP (prid (am_mem a)) 0), rg_len rg))).
    { intros g a i f U Hi F.
      destruct (used_group_region [] None U0 s g a HW U) as (rg & R & K & Lv & O & E & _).
      exists rg. split; [exact R|]. split; [exact K|]. split; [exact Lv|].
      pose proof (block_in_slot s g a i f HW U Hi F) as (A1 & A2 & A3).
      pose proof (slot_in_span [] None U0 s HW g a i U Hi) as [S1 S1'].
      unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
      unfold frame_ptr, slot_start in *. destruct (am_mem a) as [k o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia. }
    intros g1 a1 i1 f1 g2 a2 i2 f2 U1 U2 Hi1 Hi2 F1 F2 Hr.
    destruct (INCL g1 a1 i1 f1 U1 Hi1 F1) as (rg1 & R1 & K1 & L1 & I1).
    destruct (INCL g2 a2 i2 f2 U2 Hi2 F2) as (rg2 & R2 & K2 & L2 & I2).
    pose proof (footprint_region_In s _ _ R1 K1 L1) as In1. pose proof (footprint_region_In s _ _ R2 K2 L2) as In2.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW In1 In2
                ltac:(intros E; injection E; intros _ Ek; exact (Hr Ek))) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact I1 | exact I2].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact I2 | exact I1]. }
  unfold user_blocks. rewrite map_flat_map. apply pairwise_flat_map.
  - intros [g am] Hg. cbn [snd]. apply (used_metas_usedX s g am HW) in Hg. rewrite map_flat_map. apply pairwise_flat_map.
    + intros i _. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; cbn; [split; [intros y [] | exact I] | exact I | exact I].
    + intros l1 i l2 j E Hj x y Hx Hy.
      assert (Hij : i < j /\ 0 <= i <= am_last am /\ 0 <= j <= am_last am).
      { pose proof (zseq_split _ _ _ _ _ _ E Hj) as Hlt.
        assert (Hi : In i (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; left; reflexivity).
        assert (Hj' : In j (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; right; exact Hj).
        apply In_zseq in Hi. apply In_zseq in Hj'. lia. }
      destruct (ss_fr (nth_slot am i)) as [fi|] eqn:Fi; [|destruct Hx]. destruct (fr_kind fi) eqn:Ki; [|destruct Hx]. destruct Hx as [<-|[]].
      destruct (ss_fr (nth_slot am j)) as [fj|] eqn:Fj; [|destruct Hy]. destruct (fr_kind fj) eqn:Kj; [|destruct Hy]. destruct Hy as [<-|[]].
      unfold block_range, ranges_disjoint, loc_addr. cbn [fst snd].
      destruct (blocks_same_group_disjoint s g am i j fi fj HW Hg ltac:(lia) ltac:(lia) ltac:(lia) Fi Fj) as [D|D];
        unfold frame_ptr, slot_start in *; destruct (am_mem am) as [k o]; cbn [padd poff] in *; [left|right]; lia.
  - intros l1 [g1 a1] l2 [g2 a2] E Hin x y Hx Hy. cbn [snd] in Hx, Hy.
    apply in_map_iff in Hx as [bx [<- Hx]]. apply in_map_iff in Hy as [by_ [<- Hy]].
    pose proof (used_metas_split s l1 g1 a1 l2 g2 a2 (proj1 (inv_keys HW)) E Hin) as Hne.
    assert (U1 : usedX [] s g1 a1) by (apply (used_metas_usedX s g1 a1 HW); rewrite E; apply in_app_iff; right; left; reflexivity).
    assert (U2 : usedX [] s g2 a2) by (apply (used_metas_usedX s g2 a2 HW); rewrite E; apply in_app_iff; right; right; exact Hin).
    apply in_flat_map in Hx as [i1 [Hi1 Hx]]. apply In_zseq in Hi1.
    apply in_flat_map in Hy as [i2 [Hi2 Hy]]. apply In_zseq in Hi2.
    destruct (ss_fr (nth_slot a1 i1)) as [f1|] eqn:F1; [|destruct Hx]. destruct (fr_kind f1) eqn:K1; [|destruct Hx]. destruct Hx as [<-|[]].
    destruct (ss_fr (nth_slot a2 i2)) as [f2|] eqn:F2; [|destruct Hy]. destruct (fr_kind f2) eqn:K2; [|destruct Hy]. destruct Hy as [<-|[]].
    destruct (Nat.eq_dec (prid (am_mem a1)) (prid (am_mem a2))) as [Hr|Hr].
    + unfold block_range, ranges_disjoint, loc_addr. cbn [fst snd].
      destruct (blocks_other_group_disjoint s g1 a1 i1 f1 g2 a2 i2 f2 HW U1 U2 Hne Hr ltac:(lia) ltac:(lia) F1 K1 F2 K2) as [D|D];
        unfold frame_ptr, slot_start in *; destruct (am_mem a1) as [k1 o1]; destruct (am_mem a2) as [k2 o2]; cbn [padd poff prid] in *; subst; [left|right]; lia.
    + exact (REG g1 a1 i1 f1 g2 a2 i2 f2 U1 U2 ltac:(lia) ltac:(lia) F1 F2 Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_image_group s g am c :
  In (g, am) (used_metas s) -> In c (group_cells g am) -> In c (image s).
Proof.
  intros Hg Hc. unfold image. apply in_app_iff. right. apply in_app_iff. right.
  apply in_flat_map. exists (g, am). auto.
Qed.

Lemma In_group_slot g am i c :
  0 <= i <= am_last am -> In c (slot_cells am i) -> In c (group_cells g am).
Proof.
  intros Hi Hc. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists i.
  split; [apply In_zseq; lia | exact Hc].
Qed.

Theorem slot_start_cells : forall s g am i,
  WF s -> In (g, am) (used_metas s) -> 0 <= i <= am_last am ->
  In (MCell (LMem (padd (slot_start am i) (-4))) 1 (VZ 0)) (image s) /\
  match ss_hdr (nth_slot am i) with
  | Some (h3, h16) => In (MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ h3)) (image s) /\
                      In (MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ h16)) (image s)
  | None => am_maplen am = 0
  end.
Proof.
  intros s g am i HW Hg Hi.
  pose proof (proj1 (used_metas_usedX s g am HW) Hg) as Hu.
  pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (S1 & _ & _).
  split.
  - eapply In_image_group; [exact Hg|]. apply (In_group_slot g am i); [exact Hi|]. unfold slot_cells. left. reflexivity.
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|] eqn:Eh; [|apply S1; reflexivity].
    split; eapply In_image_group; try exact Hg; apply (In_group_slot g am i); try exact Hi;
      unfold slot_cells; rewrite Eh; apply in_app_iff; right; apply in_app_iff; left; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_cells_ok s :
  forallb (fun c => match mc_loc c with LCtx off => (0 <=? off) && (off + Z.of_nat (mc_w c) <=? CTX_SIZE) | _ => false end)
          (ctx_cells s) = true.
Proof. destruct s. vm_compute. reflexivity. Qed.

Lemma In_ctx_cells s c :
  In c (ctx_cells s) -> exists off, mc_loc c = LCtx off /\ 0 <= off /\ off + Z.of_nat (mc_w c) <= CTX_SIZE.
Proof.
  intros Hin. pose proof (ctx_cells_ok s) as H. rewrite forallb_forall in H. specialize (H c Hin).
  destruct (mc_loc c) as [off|p]; [|discriminate]. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
  exists off. auto.
Qed.

Lemma In_meta_slot_cells q x c :
  In c (meta_slot_cells q x) -> exists d, mc_loc c = LMem (padd q d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= META_SIZE.
Proof.
  intros Hin. unfold meta_slot_cells, META_prev, META_next, META_mem, META_avail, META_freed, META_bits, META_SIZE in *.
  assert (K : forall v1 v2 v3 v4 v5 v6,
    In c [MCell (LMem (padd q 0)) 8 v1; MCell (LMem (padd q 8)) 8 v2; MCell (LMem (padd q 16)) 8 v3;
          MCell (LMem (padd q 24)) 4 v4; MCell (LMem (padd q 28)) 4 v5; MCell (LMem (padd q 32)) 8 v6] ->
    exists d, mc_loc c = LMem (padd q d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= 40).
  { intros v1 v2 v3 v4 v5 v6 H. cbn in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; eexists; (split; [reflexivity | lia]). }
  destruct x as [[pr nx| |am]|]; eapply K; exact Hin.
Qed.

Lemma In_area_cells s a next c :
  In c (area_cells s a next) -> exists d, mc_loc c = LMem (padd a d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= PGSZ.
Proof.
  intros Hin. unfold area_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - cbn in Hin. unfold PGSZ. destruct Hin as [<-|[<-|[<-|[]]]]; cbn.
    + exists 0. rewrite <- (padd_0 a) at 1. split; [reflexivity | lia].
    + exists 8. split; [reflexivity | lia].
    + exists 16. split; [reflexivity | lia].
  - apply in_flat_map in Hin as [k [Hk Hin]]. apply in_seq in Hk.
    destruct (In_meta_slot_cells _ _ _ Hin) as (d & E & Hd & Hw). rewrite E.
    exists (AREA_HDR + META_SIZE * Z.of_nat k + d). split; [destruct a; cbn [padd]; f_equal; f_equal; lia|].
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.

Lemma In_areas_cells s l c :
  In c (areas_cells s l) -> exists a next, In a l /\ In c (area_cells s a next).
Proof.
  induction l as [|a t IH]; intros Hin; cbn [areas_cells] in Hin; [destruct Hin|].
  apply in_app_iff in Hin as [Hin|Hin].
  - exists a, (hd_error t). split; [left; reflexivity | exact Hin].
  - destruct (IH Hin) as (a' & next & Ha' & Hc). exists a', next. split; [right; exact Ha' | exact Hc].
Qed.

Lemma In_slot_cells X R U s g am i c :
  Inv X R U s -> usedX X s g am -> 0 <= i <= am_last am -> In c (slot_cells am i) ->
  exists d, mc_loc c = LMem (padd (am_mem am) d) /\ UNIT + stride_of am * i - IB <= d /\
    d + Z.of_nat (mc_w c) <= UNIT + stride_of am * i + stride_of am - IB /\
    (* [comment removed for export] *)
    (d + Z.of_nat (mc_w c) <= UNIT + stride_of am * i \/
     exists fr, ss_fr (nth_slot am i) = Some fr /\ fr_off fr <> 0 /\
       UNIT + stride_of am * i + UNIT * fr_off fr - IB <= d /\ d + Z.of_nat (mc_w c) <= UNIT + stride_of am * i + UNIT * fr_off fr).
Proof.
  intros HI Hu Hi Hin. pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3).
  assert (Ess : forall d, padd (slot_start am i) d = padd (am_mem am) (UNIT + stride_of am * i + d)).
  { intros d. unfold slot_start. destruct (am_mem am); cbn. f_equal. lia. }
  unfold slot_cells in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - destruct Hin as [<-|[]]. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]. rewrite Ess. eexists. split; [reflexivity|].
    unfold UNIT, IB in *. split; [lia|]. split; [lia|]. left. lia.
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hin].
    destruct Hin as [<-|[<-|[]]]; cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Ess; eexists; (split; [reflexivity|]); unfold UNIT, IB in *;
      (split; [lia|]); (split; [lia|]); left; lia.
  - destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hin].
    destruct (fr_off fr =? 0) eqn:E0; [destruct Hin|]. apply Z.eqb_neq in E0.
    destruct S3 as (_ & _ & (N & O & B & _) & _).
    assert (Ess2 : forall d, padd (padd (slot_start am i) (UNIT * fr_off fr)) d = padd (am_mem am) (UNIT + stride_of am * i + UNIT * fr_off fr + d)).
    { intros d. unfold slot_start. destruct (am_mem am); cbn. f_equal. lia. }
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Ess2; eexists; (split; [reflexivity|]); unfold UNIT, IB in *; (split; [lia|]); (split; [lia|]);
      right; exists fr; (split; [reflexivity|]); (split; [exact E0|]); lia.
Qed.

Lemma In_group_cells X R U s g am c :
  Inv X R U s -> usedX X s g am -> In c (group_cells g am) ->
  exists d, mc_loc c = LMem (padd (am_mem am) d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= group_extent am + IB.
Proof.
  intros HI Hu Hin. pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Glast & _) & _).
  unfold group_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct Hin as [<-|[<-|[]]].
    + exists 0. rewrite <- (padd_0 (am_mem am)) at 1. cbn. split; [reflexivity|]. unfold group_extent, UNIT, IB. nia.
    + destruct (am_maplen am =? 0); cbn; exists 8; (split; [reflexivity|]); unfold group_extent, UNIT, IB; nia.
  - apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
    destruct (In_slot_cells X R U s g am i c HI Hu ltac:(lia) Hin) as (d & E & Lo & Hiw & _).
    exists d. split; [exact E|]. unfold group_extent.
    assert (0 <= stride_of am * i) by nia. assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    unfold UNIT, IB in *. lia.
Qed.

Lemma In_image_inv s c :
  In c (image s) ->
  In c (ctx_cells s) \/ (exists a next, In a (st_areas s) /\ In c (area_cells s a next)) \/
  (exists g am, In (g, am) (used_metas s) /\ In c (group_cells g am)).
Proof.
  intros Hin. unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin]; [left; exact Hin|].
  apply in_app_iff in Hin as [Hin|Hin].
  - right; left. apply In_areas_cells. exact Hin.
  - right; right. apply in_flat_map in Hin as [[g am] [Hg Hc]]. exists g, am. auto.
Qed.

Theorem image_in_footprint : forall s L c,
  WF s -> layout_ok L s -> In c (image s) ->
  exists rg, In rg (footprint s) /\ range_incl (cell_range L c) (crange L rg).
Proof.
  intros s L c HW HL Hin. destruct (In_image_inv s c Hin) as [Hc | [(a & next & Ha & Hc) | (g & am & Hg & Hc)]].
  - destruct (In_ctx_cells s c Hc) as (off & E & Ho & Hw). exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  - destruct (In_area_cells s a next c Hc) as (d & E & Hd & Hw). exists (LMem a, PGSZ). split.
    + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  - apply (used_metas_usedX s g am HW) in Hg.
    destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
    destruct (In_group_cells [] None U0 s g am c HW Hg Hc) as (d & E & Hd & Hw).
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [apply footprint_region_In; assumption|].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma In_group_cells_span X R U s g am c :
  Inv X R U s -> usedX X s g am -> In c (group_cells g am) ->
  exists d, mc_loc c = LMem (padd (am_mem am) d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= group_extent am.
Proof.
  intros HI Hu Hin. pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Glast & _) & _ & Gsl & _).
  unfold group_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct Hin as [<-|[<-|[]]].
    + exists 0. rewrite <- (padd_0 (am_mem am)) at 1. cbn. split; [reflexivity|]. unfold group_extent, UNIT, IB. nia.
    + destruct (am_maplen am =? 0); cbn; exists 8; (split; [reflexivity|]); unfold group_extent, UNIT, IB; nia.
  - apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
    destruct (In_slot_cells X R U s g am i c HI Hu ltac:(lia) Hin) as (d & E & Lo & Hiw & Fine).
    exists d. split; [exact E|]. unfold group_extent.
    assert (0 <= stride_of am * i) by nia. assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
    destruct Fine as [Bl | (fr & Hfr & Ho & Lo2 & Hi2)].
    + unfold UNIT, IB in *. lia.
    + pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
      unfold UNIT, IB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma slot_cells_vs_body X R U s g am k J lo hi c :
  Inv X R U s -> usedX X s g am -> 0 <= k <= am_last am -> 0 <= J <= am_last am ->
  In c (slot_cells am k) ->
  poff (slot_start am J) + UNIT * (match ss_fr (nth_slot am J) with Some f => fr_off f | None => 0 end) <= lo ->
  hi <= poff (slot_start am J) + stride_of am - IB ->
  exists d, mc_loc c = LMem (padd (am_mem am) d) /\
    (poff (am_mem am) + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am) + d).
Proof.
  intros HI Hu Hk HJ Hin Hlo Hhi.
  pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  destruct (In_slot_cells X R U s g am k c HI Hu Hk Hin) as (d & E & Lo & Hiw & Fine). exists d. split; [exact E|].
  rewrite poff_slot_start in Hlo, Hhi.
  assert (Hoff0 : 0 <= match ss_fr (nth_slot am J) with Some f => fr_off f | None => 0 end).
  { pose proof (Gsl J HJ) as (_ & _ & S3). destruct (ss_fr (nth_slot am J)) as [f|]; [|lia]. destruct S3 as (_ & _ & (_ & O & _) & _). lia. }
  destruct (Z_lt_dec k J) as [Hlt | Hge]; [|destruct (Z_lt_dec J k) as [Hgt | Heq]].
  - (* [comment removed for export] *)
    left. assert (stride_of am * k + stride_of am <= stride_of am * J) by nia.
    destruct Fine as [Bl | (fr & Hfr & Ho & Lo2 & Hi2)]; [unfold UNIT, IB in *; lia|].
    pose proof (Gsl k Hk) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _). unfold UNIT, IB in *. lia.
  - (* [comment removed for export] *)
    right. assert (stride_of am * J + stride_of am <= stride_of am * k) by nia.
    destruct Fine as [Bl | (fr & Hfr & Ho & Lo2 & Hi2)]; unfold UNIT, IB in *; lia.
  - assert (k = J) as -> by lia. left.
    destruct Fine as [Bl | (fr & Hfr & Ho & Lo2 & Hi2)]; [unfold UNIT, IB in *; lia|].
    rewrite Hfr in Hlo. unfold UNIT, IB in *. lia.
Qed.

Lemma group_cells_vs_body X R U s g am J lo hi c :
  Inv X R U s -> usedX X s g am -> 0 <= J <= am_last am ->
  In c (group_cells g am) ->
  poff (slot_start am J) + UNIT * (match ss_fr (nth_slot am J) with Some f => fr_off f | None => 0 end) <= lo ->
  hi <= poff (slot_start am J) + stride_of am - IB ->
  exists d, mc_loc c = LMem (padd (am_mem am) d) /\
    (poff (am_mem am) + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am) + d).
Proof.
  intros HI Hu HJ Hin Hlo Hhi.
  pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  assert (Hoff0 : 0 <= match ss_fr (nth_slot am J) with Some f => fr_off f | None => 0 end).
  { pose proof (Gsl J HJ) as (_ & _ & S3). destruct (ss_fr (nth_slot am J)) as [f|]; [|lia]. destruct S3 as (_ & _ & (_ & O & _) & _). lia. }
  unfold group_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - rewrite poff_slot_start in Hlo. assert (0 <= stride_of am * J) by nia.
    destruct Hin as [<-|[<-|[]]].
    + exists 0. rewrite <- (padd_0 (am_mem am)) at 1. cbn. split; [reflexivity|]. left. unfold UNIT in *. lia.
    + destruct (am_maplen am =? 0); cbn; exists 8; (split; [reflexivity|]); left; unfold UNIT in *; lia.
  - apply in_flat_map in Hin as [k [Hk Hin]]. apply In_zseq in Hk.
    exact (slot_cells_vs_body X R U s g am k J lo hi c HI Hu ltac:(lia) HJ Hin Hlo Hhi).
Qed.

Theorem image_outside_user_blocks : forall s L c b,
  WF s -> layout_ok L s -> In c (image s) -> In b (user_blocks s) ->
  ranges_disjoint (cell_range L c) (block_range L b).
Proof.
  intros s L c b HW HL Hc Hb. pose proof HL as (_ & _ & PW & _).
  destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
  apply (used_metas_usedX s g am HW) in Hg.
  pose proof (inv_groups HW g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
  pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
  destruct (used_group_region [] None U0 s g am HW Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
  assert (BI : range_incl (block_range L (frame_ptr am i fr, fr_n fr)) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
  { pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (A1 & A2 & A3).
    pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
    unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
    unfold frame_ptr, slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia. }
  (* [comment removed for export] *)
  assert (VIA : forall e, In e (footprint s) -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg) ->
            range_incl (cell_range L c) (crange L e) -> ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
  { intros e He Hne Hincl.
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR Hne) as [D|D].
    - eapply ranges_disjoint_incl; [exact D | exact Hincl | exact BI].
    - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact BI | exact Hincl]. }
  destruct (In_image_inv s c Hc) as [Hcc | [(a & next & Ha & Hcc) | (g' & am' & Hg' & Hcc)]].
  - destruct (In_ctx_cells s c Hcc) as (off & E & Ho' & Hw). apply (VIA (LCtx 0, CTX_SIZE)); [left; reflexivity | discriminate |].
    unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
  - destruct (In_area_cells s a next c Hcc) as (d & E & Hd & Hw).
    pose proof (inv_areas HW) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
    apply (VIA (LMem a, PGSZ)).
    + right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
    + rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
    + unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
  - apply (used_metas_usedX s g' am' HW) in Hg'.
    destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
    2:{ destruct (used_group_region [] None U0 s g' am' HW Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
        destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw).
        apply (VIA (LMem (SP (prid (am_mem am')) 0), rg_len rg')); [apply footprint_region_In; assumption | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep) |].
        unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia. }
    (* [comment removed for export] *)
    assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
              (poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (frame_ptr am i fr) \/
               poff (frame_ptr am i fr) + fr_n fr <= poff (am_mem am') + d) ->
              ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
    { intros d E D. unfold cell_range, block_range, ranges_disjoint, loc_addr. rewrite E. cbn [fst snd].
      unfold frame_ptr, slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
    pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (A1 & A2 & A3).
    destruct (sptr_eq_dec g' g) as [->|Hne].
    + pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
      destruct (group_cells_vs_body [] None U0 s g am i (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HW Hg Hi Hcc
                  ltac:(rewrite Hfr; unfold frame_ptr; rewrite poff_padd; lia) A2) as (d & E & D).
      exact (GOAL d E D).
    + pose proof (extent_pos _ _ _ _ _ (inv_groups HW g' am' Hg')) as Pa'.
      destruct (inv_laminar HW g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
      * destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
        unfold spans_disjoint in Dj. unfold frame_ptr in *. rewrite poff_padd in *. unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
      * (* [comment removed for export] *)
        destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
        destruct (inside_slot_start [] None U0 s HW g' am' 0 g am Hg' Hg ltac:(pose proof (inv_groups HW g' am' Hg') as ((M1 & _) & _); lia) I) as (j & frj & Hj & Hfrj & Hkj & Lo & Hi2).
        destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
        pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
        rewrite Mem0, poff_slot_start in Lo0, Hi0.
        unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
        destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
      * (* [comment removed for export] *)
        destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
        pose proof (inv_groups HW g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
        destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
        pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
        destruct (group_cells_vs_body [] None U0 s g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HW Hg' Hj' Hcc) as (d & E & D).
        -- rewrite Hfr', Off'. rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
        -- rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
        -- exact (GOAL d E D).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_frames_inv s g am i fr :
  In (g, am, i, fr) (frames s) -> In (g, am) (used_metas s) /\ 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr.
Proof.
  intros Hin. unfold frames in Hin. apply in_flat_map in Hin as [[g' am'] [Hg Hin]].
  apply in_flat_map in Hin as [j [Hj Hin]]. apply In_zseq in Hj.
  destruct (ss_fr (nth_slot am' j)) as [f|] eqn:Ef; [|destruct Hin]. destruct Hin as [E|[]].
  injection E as -> -> -> ->. split; [exact Hg|]. split; [lia | exact Ef].
Qed.

Lemma stride_mod16 X R U s g am : Inv X R U s -> usedX X s g am -> stride_of am mod 16 = 0.
Proof.
  intros HI Hu. unfold stride_of. destruct ((am_last am =? 0) && negb (am_maplen am =? 0)).
  - unfold UNIT. replace (am_maplen am * 4096 - 16) with ((am_maplen am * 256 - 1) * 16) by lia. apply Z_mod_mult.
  - unfold class_size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma used_group_aligned X R U s (HI : Inv X R U s) k :
  forall g am, usedX X s g am -> (Z.to_nat (64 - am_sc am) <= k)%nat -> poff (am_mem am) mod 16 = 0.
Proof.
  induction k as [|k IH]; intros g am Hu Hk.
  - exfalso. pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _). destruct Gcl as [(C & _) | (C & _)]; lia.
  - pose proof (inv_groups HI g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
    destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos | Hz].
    + destruct (Gmp Hpos) as (r & rg & Em & _). rewrite Em. reflexivity.
    + destruct (Gns ltac:(lia)) as (N63 & g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem & Sc & N63' & Fit).
      pose proof (IH g' am' U' ltac:(lia)) as Hal. pose proof (stride_mod16 _ _ _ _ _ _ HI U') as Hst.
      apply Z.div_exact in Hal; [|lia]. apply Z.div_exact in Hst; [|lia].
      rewrite Mem, poff_slot_start. unfold UNIT.
      replace (poff (am_mem am') + 16 + stride_of am' * i') with ((poff (am_mem am') / 16 + 1 + stride_of am' / 16 * i') * 16) by lia.
      apply Z_mod_mult.
Qed.

Lemma In_areas_cells_intro s l a c :
  In a l -> (forall next, In c (area_cells s a next)) -> In c (areas_cells s l).
Proof.
  induction l as [|b t IH]; intros Ha Hc; [destruct Ha|]. cbn [areas_cells]. apply in_app_iff.
  destruct Ha as [->|Ha]; [left; apply Hc | right; apply IH; assumption].
Qed.

Lemma meta_cells_in_image s g am c :
  WF s -> usedX [] s g am -> In c (meta_slot_cells g (Some (MUsed am))) -> In c (image s).
Proof.
  intros HW Hu Hc. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  pose proof (inv_keys HW) as (ND & KP & _ & _ & Hcnt).
  destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk & Eg).
  assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
  unfold image. apply in_app_iff. right. apply in_app_iff. left.
  apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next. unfold area_cells. apply in_app_iff. right.
  apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|].
  rewrite Z2Nat.id by lia. rewrite <- Eg. unfold MT in Mg. rewrite Mg. exact Hc.
Qed.

Lemma land31 i m : 0 <= i <= 31 -> 0 <= m -> Z.land (i + 32 * m) 31 = i.
Proof.
  intros Hi Hm. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * m) with (i + m * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Theorem get_meta_ok : forall s g am i fr,
  WF s -> In (g, am, i, fr) (frames s) ->
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
  intros s g am i fr HW Hfr p.
  destruct (in_frames_inv s g am i fr Hfr) as (Hg & Hi & Hf).
  pose proof (proj1 (used_metas_usedX s g am HW) Hg) as Hu. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hf in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & FG) & Hhdr).
  pose proof (stride_mod16 _ _ _ _ _ _ HW Hu) as Hst16.
  pose proof (used_group_aligned [] None U0 s HW _ g am Hu (Nat.le_refl _)) as Hal16.
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
  split; [apply (meta_cells_in_image s g am _ HW Hu); cbn; auto 10|].
  split; [apply (meta_cells_in_image s g am _ HW Hu); cbn; auto 10|].
  split; [apply (meta_cells_in_image s g am _ HW Hu); cbn; auto 10|].
  split; [apply (meta_cells_in_image s g am _ HW Hu); cbn; auto 10|].
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
  split; [|subst p; apply (find_frame_in_spec [] None U0 s HW g am i fr Hu Hi Hf)].
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
        - destruct (CN1 Hlt) as [Hl0 _]. assert (i = 0) as -> by lia. rewrite !Z.mul_0_r. change (0 / UNIT) with 0. lia.
        - unfold UNIT. assert (sz * i * 16 <= stride_of am * i / 16 * 16) by (rewrite Hdiv; nia). lia. }
      assert (B : stride_of am * i / UNIT + fr_off fr < sz * (i + 1)).
      { destruct (Z.eq_dec (am_last am) 0) as [Hl0 | Hl0].
        - assert (i = 0) as -> by lia. rewrite !Z.mul_0_r. change (0 / UNIT) with 0. rewrite Z.add_0_l, Z.add_0_l, Z.mul_1_r.
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
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pairwise_neq_NoDup {A} (l : list A) : pairwise (fun x y => x <> y) l -> NoDup l.
Proof.
  induction l as [|x t IH]; intros H; [constructor|]. cbn in H. destruct H as [H1 H2].
  constructor; [|apply IH; exact H2]. intros Hin. exact (H1 x Hin eq_refl).
Qed.

Lemma pairwise_map {A B} (R : B -> B -> Prop) (f : A -> B) l :
  pairwise (fun x y => R (f x) (f y)) l -> pairwise R (map f l).
Proof.
  induction l as [|x t IH]; intros H; cbn; [exact I|]. cbn in H. destruct H as [H1 H2]. split; [|apply IH; exact H2].
  intros y Hy. apply in_map_iff in Hy as [a [<- Ha]]. apply H1. exact Ha.
Qed.

Theorem user_block_ptrs_NoDup s : WF s -> NoDup (map fst (user_blocks s)).
Proof.
  intros HW. apply pairwise_neq_NoDup. apply pairwise_map. unfold user_blocks. apply pairwise_flat_map.
  - intros [g am] Hg. cbn [snd]. apply (used_metas_usedX s g am HW) in Hg. apply pairwise_flat_map.
    + intros i _. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; cbn; [split; [intros y [] | exact I] | exact I | exact I].
    + intros l1 i l2 j E Hj x y Hx Hy.
      pose proof (zseq_split _ _ _ _ _ _ E Hj) as Hlt.
      assert (Hi : In i (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; left; reflexivity).
      assert (Hj' : In j (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; right; exact Hj).
      apply In_zseq in Hi. apply In_zseq in Hj'.
      destruct (ss_fr (nth_slot am i)) as [fi|] eqn:Fi; [|destruct Hx]. destruct (fr_kind fi) eqn:Ki; [|destruct Hx]. destruct Hx as [<-|[]].
      destruct (ss_fr (nth_slot am j)) as [fj|] eqn:Fj; [|destruct Hy]. destruct (fr_kind fj) eqn:Kj; [|destruct Hy]. destruct Hy as [<-|[]].
      cbn [fst]. intros Ep.
      destruct (frame_ptrs_distinct [] None U0 s HW g am i fi g am j fj Hg Hg ltac:(lia) ltac:(lia) Fi Fj Ep) as [_ Eij]. lia.
  - intros l1 [g1 a1] l2 [g2 a2] E Hin x y Hx Hy. cbn [snd] in Hx, Hy.
    pose proof (used_metas_split s l1 g1 a1 l2 g2 a2 (proj1 (inv_keys HW)) E Hin) as Hne.
    assert (U1 : usedX [] s g1 a1) by (apply (used_metas_usedX s g1 a1 HW); rewrite E; apply in_app_iff; right; left; reflexivity).
    assert (U2 : usedX [] s g2 a2) by (apply (used_metas_usedX s g2 a2 HW); rewrite E; apply in_app_iff; right; right; exact Hin).
    apply in_flat_map in Hx as [i1 [Hi1 Hx]]. apply In_zseq in Hi1.
    apply in_flat_map in Hy as [i2 [Hi2 Hy]]. apply In_zseq in Hi2.
    destruct (ss_fr (nth_slot a1 i1)) as [f1|] eqn:F1; [|destruct Hx]. destruct (fr_kind f1) eqn:K1; [|destruct Hx]. destruct Hx as [<-|[]].
    destruct (ss_fr (nth_slot a2 i2)) as [f2|] eqn:F2; [|destruct Hy]. destruct (fr_kind f2) eqn:K2; [|destruct Hy]. destruct Hy as [<-|[]].
    cbn [fst]. intros Ep.
    destruct (frame_ptrs_distinct [] None U0 s HW g1 a1 i1 f1 g2 a2 i2 f2 U1 U2 ltac:(lia) ltac:(lia) F1 F2 Ep) as [Eg _]. exact (Hne Eg).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition locw (c : mcell) : option (Z * Z) :=
  match mc_loc c with LCtx off => Some (off, Z.of_nat (mc_w c)) | _ => None end.
Definition disjb (a b : option (Z * Z)) : bool :=
  match a, b with Some (x, w), Some (y, v) => (x + w <=? y) || (y + v <=? x) | _, _ => false end.
Fixpoint pairwiseb {A} (f : A -> A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: t => forallb (f x) t && pairwiseb f t end.

Lemma ctx_cells_pairwiseb s : pairwiseb disjb (map locw (ctx_cells s)) = true.
Proof. destruct s. vm_compute. reflexivity. Qed.

Lemma pairwiseb_pairwise {A} (f : A -> A -> bool) (R : A -> A -> Prop) l :
  (forall x y, f x y = true -> R x y) -> pairwiseb f l = true -> pairwise R l.
Proof.
  intros Hf. induction l as [|x t IH]; intros H; cbn in *; [exact I|].
  apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H1. split; [|apply IH; exact H2].
  intros y Hy. apply Hf. apply H1. exact Hy.
Qed.

Lemma pairwise_map_iff {A B} (R : B -> B -> Prop) (f : A -> B) l :
  pairwise (fun x y => R (f x) (f y)) l <-> pairwise R (map f l).
Proof.
  induction l as [|x t IH]; cbn; [tauto|]. split.
  - intros [H1 H2]. split; [|apply IH; exact H2]. intros y Hy. apply in_map_iff in Hy as [a [<- Ha]]. apply H1. exact Ha.
  - intros [H1 H2]. split; [|apply IH; exact H2]. intros y Hy. apply H1. apply in_map. exact Hy.
Qed.

Lemma pairwise_mono {A} (R1 R2 : A -> A -> Prop) l : (forall x y, R1 x y -> R2 x y) -> pairwise R1 l -> pairwise R2 l.
Proof.
  intros H. induction l as [|x t IH]; cbn; [tauto|]. intros [P1 P2]. split; [|apply IH; exact P2]. intros y Hy. apply H, P1, Hy.
Qed.

Lemma ctx_cells_disjoint L s : pairwise ranges_disjoint (map (cell_range L) (ctx_cells s)).
Proof.
  apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) (ctx_cells s))).
  assert (P : pairwise (fun x y => disjb (locw x) (locw y) = true) (ctx_cells s)).
  { apply (pairwise_map_iff (fun a b => disjb a b = true) locw). eapply pairwiseb_pairwise; [|exact (ctx_cells_pairwiseb s)]. intros x y E. exact E. }
  eapply pairwise_mono; [|exact P]. intros x y P1. unfold disjb, locw in P1. unfold cell_range, ranges_disjoint, loc_addr.
  destruct (mc_loc x) as [ox|px]; [|discriminate]. destruct (mc_loc y) as [oy|py]; [|discriminate]. cbn [fst snd].
  apply orb_prop in P1. destruct P1 as [P1|P1]; apply Z.leb_le in P1; lia.
Qed.

(* [comment removed for export] *)
Lemma cells_disjoint_via_footprint L s c c' e e' :
  layout_ok L s -> In e (footprint s) -> In e' (footprint s) -> e <> e' ->
  range_incl (cell_range L c) (crange L e) -> range_incl (cell_range L c') (crange L e') ->
  ranges_disjoint (cell_range L c) (cell_range L c').
Proof.
  intros (_ & _ & PW & _) He He' Hne I1 I2.
  destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He He' Hne) as [D|D].
  - eapply ranges_disjoint_incl; [exact D | exact I1 | exact I2].
  - apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact I2 | exact I1].
Qed.

(* [comment removed for export] *)
Lemma ctx_cell_home L s c :
  In c (ctx_cells s) -> In (LCtx 0, CTX_SIZE) (footprint s) /\ range_incl (cell_range L c) (crange L (LCtx 0, CTX_SIZE)).
Proof.
  intros Hc. split; [left; reflexivity|]. destruct (In_ctx_cells s c Hc) as (off & E & Ho & Hw).
  unfold cell_range, crange, range_incl, loc_addr. rewrite E. cbn [fst snd]. lia.
Qed.

Lemma area_cell_home L s a next c :
  In a (st_areas s) -> In c (area_cells s a next) ->
  In (LMem a, PGSZ) (footprint s) /\ range_incl (cell_range L c) (crange L (LMem a, PGSZ)).
Proof.
  intros Ha Hc. split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
  destruct (In_area_cells s a next c Hc) as (d & E & Hd & Hw).
  unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
Qed.

Lemma group_cell_home L s g am c :
  WF s -> usedX [] s g am -> In c (group_cells g am) ->
  exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
    In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
    range_incl (cell_range L c) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
Proof.
  intros HW Hu Hc. destruct (used_group_region [] None U0 s g am HW Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
  exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
  destruct (In_group_cells_span [] None U0 s g am c HW Hu Hc) as (d & E & Hd & Hw).
  unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in Hext. lia.
Qed.

(* [comment removed for export] *)
Lemma area_cells_disjoint L s a next :
  pairwise ranges_disjoint (map (cell_range L) (area_cells s a next)).
Proof.
  apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)).
  assert (K : forall c c' d d', mc_loc c = LMem (padd a d) -> mc_loc c' = LMem (padd a d') ->
            (d + Z.of_nat (mc_w c) <= d' \/ d' + Z.of_nat (mc_w c') <= d) -> ranges_disjoint (cell_range L c) (cell_range L c')).
  { intros c c' d d' E E' D. unfold cell_range, ranges_disjoint, loc_addr. rewrite E, E'. destruct a as [r o]. cbn [fst snd padd]. lia. }
  assert (SLOT : forall q x c, In c (meta_slot_cells q x) ->
            exists d, mc_loc c = LMem (padd q d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= META_SIZE /\
              (d = 0 /\ mc_w c = 8%nat \/ d = 8 /\ mc_w c = 8%nat \/ d = 16 /\ mc_w c = 8%nat \/ d = 24 /\ mc_w c = 4%nat \/ d = 28 /\ mc_w c = 4%nat \/ d = 32 /\ mc_w c = 8%nat)).
  { intros q x c Hin. unfold meta_slot_cells, META_prev, META_next, META_mem, META_avail, META_freed, META_bits, META_SIZE in *.
    assert (KK : forall v1 v2 v3 v4 v5 v6,
      In c [MCell (LMem (padd q 0)) 8 v1; MCell (LMem (padd q 8)) 8 v2; MCell (LMem (padd q 16)) 8 v3;
            MCell (LMem (padd q 24)) 4 v4; MCell (LMem (padd q 28)) 4 v5; MCell (LMem (padd q 32)) 8 v6] ->
      exists d, mc_loc c = LMem (padd q d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= 40 /\
        (d = 0 /\ mc_w c = 8%nat \/ d = 8 /\ mc_w c = 8%nat \/ d = 16 /\ mc_w c = 8%nat \/ d = 24 /\ mc_w c = 4%nat \/ d = 28 /\ mc_w c = 4%nat \/ d = 32 /\ mc_w c = 8%nat)).
    { intros v1 v2 v3 v4 v5 v6 H. cbn in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; eexists; (split; [reflexivity|]); (split; [lia|]); (split; [lia|]); tauto. }
    destruct x as [[pr nx| |am]|]; eapply KK; exact Hin. }
  unfold area_cells. apply pairwise_app.
  - (* [comment removed for export] *)
    cbn. unfold cell_range, ranges_disjoint, loc_addr. destruct a as [r o]. cbn [mc_loc mc_w padd fst snd].
    repeat split; intros y Hy; repeat (destruct Hy as [<-|Hy]; [cbn [mc_loc mc_w padd fst snd]; lia|]); destruct Hy.
  - apply pairwise_flat_map.
    + intros k Hk. set (q := padd a (AREA_HDR + META_SIZE * Z.of_nat k)).
      generalize (mlookup (st_metas s) q) as x. intros x.
      assert (KK : forall v1 v2 v3 v4 v5 v6,
        pairwise (fun c c' => ranges_disjoint (cell_range L c) (cell_range L c'))
          [MCell (LMem (padd q 0)) 8 v1; MCell (LMem (padd q 8)) 8 v2; MCell (LMem (padd q 16)) 8 v3;
           MCell (LMem (padd q 24)) 4 v4; MCell (LMem (padd q 28)) 4 v5; MCell (LMem (padd q 32)) 8 v6]).
      { intros. cbn. unfold cell_range, ranges_disjoint, loc_addr. subst q. destruct a as [r o]. cbn [mc_loc mc_w padd fst snd].
        repeat split; intros y Hy; repeat (destruct Hy as [<-|Hy]; [cbn [mc_loc mc_w padd fst snd]; lia|]); destruct Hy. }
      unfold meta_slot_cells, META_prev, META_next, META_mem, META_avail, META_freed, META_bits. destruct x as [[pr nx| |am]|]; apply KK.
    + intros l1 k1 l2 k2 E Hk2 x y Hx Hy.
      assert (Hlt : (k1 < k2)%nat).
      { assert (Hs : forall st n l1 k1 l2 k2, seq st n = l1 ++ k1 :: l2 -> In k2 l2 -> (k1 < k2)%nat).
        { clear. intros st n. revert st. induction n as [|n IH]; intros st l1 k1 l2 k2 E Hk.
          - destruct l1; discriminate.
          - cbn in E. destruct l1 as [|z l1']; cbn in E.
            + injection E as <- E. subst l2. apply in_seq in Hk. lia.
            + injection E as _ E. eapply IH; eauto. }
        eapply Hs; eauto. }
      destruct (SLOT _ _ _ Hx) as (d & Ed & Hd & Hdw & _). destruct (SLOT _ _ _ Hy) as (d' & Ed' & Hd' & Hdw' & _).
      eapply (K x y (AREA_HDR + META_SIZE * Z.of_nat k1 + d) (AREA_HDR + META_SIZE * Z.of_nat k2 + d')).
      * rewrite Ed. destruct a; cbn [padd]. f_equal. f_equal. lia.
      * rewrite Ed'. destruct a; cbn [padd]. f_equal. f_equal. lia.
      * left. unfold META_SIZE, AREA_HDR in *. nia.
  - intros x y Hx Hy. apply in_flat_map in Hy as [k [Hk Hy]]. apply in_seq in Hk.
    destruct (SLOT _ _ _ Hy) as (d' & Ed' & Hd' & Hdw' & _).
    cbn in Hx. destruct Hx as [<-|[<-|[<-|[]]]].
    + eapply (K _ y 0 (AREA_HDR + META_SIZE * Z.of_nat k + d')); [destruct a; cbn; f_equal; f_equal; lia | rewrite Ed'; destruct a; cbn [padd]; f_equal; f_equal; lia | cbn -[Z.mul Z.add]; unfold AREA_HDR, META_SIZE; left; nia].
    + eapply (K _ y 8 (AREA_HDR + META_SIZE * Z.of_nat k + d')); [reflexivity | rewrite Ed'; destruct a; cbn [padd]; f_equal; f_equal; lia | cbn -[Z.mul Z.add]; unfold AREA_HDR, META_SIZE; left; nia].
    + eapply (K _ y 16 (AREA_HDR + META_SIZE * Z.of_nat k + d')); [reflexivity | rewrite Ed'; destruct a; cbn [padd]; f_equal; f_equal; lia | cbn -[Z.mul Z.add]; unfold AREA_HDR, META_SIZE; left; nia].
Qed.

Lemma loc_addr_LMem L p : loc_addr L (LMem p) = ly_reg L (prid p) + poff p.
Proof. destruct p; reflexivity. Qed.

Ltac cellsimp :=
  unfold cell_range, ranges_disjoint; cbn [mc_loc mc_w fst snd];
  rewrite ?loc_addr_LMem, ?prid_padd, ?poff_padd, ?prid_padd, ?poff_padd, ?prid_slot_start, ?poff_slot_start.

(* [comment removed for export] *)
Lemma slot_cells_disjoint L X R U s g am i :
  Inv X R U s -> usedX X s g am -> 0 <= i <= am_last am ->
  pairwise ranges_disjoint (map (cell_range L) (slot_cells am i)).
Proof.
  intros HI Hu Hi. pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3).
  apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)).
  unfold slot_cells.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr.
  - destruct S3 as (_ & _ & (N & O & B & _) & _).
    destruct (fr_off fr =? 0) eqn:E0; [apply Z.eqb_eq in E0 | apply Z.eqb_neq in E0];
      destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; cbn [app pairwise]; unfold UNIT in *;
      repeat split; intros y Hy; repeat (destruct Hy as [<-|Hy]; [cellsimp; lia|]); destruct Hy.
  - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; cbn [app pairwise]; unfold UNIT in *;
      repeat split; intros y Hy; repeat (destruct Hy as [<-|Hy]; [cellsimp; lia|]); destruct Hy.
Qed.

(* [comment removed for export] *)
Lemma group_cells_disjoint L X R U s g am :
  Inv X R U s -> usedX X s g am -> pairwise ranges_disjoint (map (cell_range L) (group_cells g am)).
Proof.
  intros HI Hu. pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _ & Gsl & _).
  apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)).
  assert (HS : forall i c, 0 <= i <= am_last am -> In c (slot_cells am i) ->
            exists d, mc_loc c = LMem (padd (am_mem am) d) /\ UNIT + stride_of am * i - IB <= d /\ d + Z.of_nat (mc_w c) <= UNIT + stride_of am * i + stride_of am - IB).
  { intros i c Hi Hc. destruct (In_slot_cells X R U s g am i c HI Hu Hi Hc) as (d & E & Lo & Hiw & _). exists d. auto. }
  unfold group_cells. apply (pairwise_app (fun x y => ranges_disjoint (cell_range L x) (cell_range L y))).
  - cbn [pairwise]. split; [|split; [intros y [] | exact I]]. intros y [<-|[]].
    destruct (am_maplen am =? 0); cellsimp; lia.
  - apply pairwise_flat_map.
    + intros i Hi. apply In_zseq in Hi. apply (pairwise_map_iff ranges_disjoint (cell_range L)). eapply slot_cells_disjoint; eauto. lia.
    + intros l1 i l2 j E Hj x y Hx Hy.
      pose proof (zseq_split _ _ _ _ _ _ E Hj) as Hlt.
      assert (Hi : In i (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; left; reflexivity).
      assert (Hj' : In j (zseq 0 (am_last am + 1))) by (rewrite E; apply in_app_iff; right; right; exact Hj).
      apply In_zseq in Hi. apply In_zseq in Hj'.
      destruct (HS i x ltac:(lia) Hx) as (d & Ed & Lo & Hiw). destruct (HS j y ltac:(lia) Hy) as (d' & Ed' & Lo' & Hiw').
      assert (stride_of am * i + stride_of am <= stride_of am * j) by nia.
      cellsimp. rewrite Ed, Ed'. cellsimp. unfold UNIT, IB in *. lia.
  - intros x y Hx Hy. apply in_flat_map in Hy as [i [Hi Hy]]. apply In_zseq in Hi.
    destruct (HS i y ltac:(lia) Hy) as (d & Ed & Lo & Hiw). assert (0 <= stride_of am * i) by nia.
    destruct Hx as [<-|[<-|[]]].
    + cellsimp. rewrite Ed. cellsimp. destruct (am_mem am); cbn [prid poff]. unfold UNIT, IB in *. lia.
    + destruct (am_maplen am =? 0); cellsimp; rewrite Ed; cellsimp; unfold UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma groups_cells_disjoint L s g1 a1 g2 a2 x y :
  WF s -> layout_ok L s -> usedX [] s g1 a1 -> usedX [] s g2 a2 -> g1 <> g2 ->
  In x (group_cells g1 a1) -> In y (group_cells g2 a2) -> ranges_disjoint (cell_range L x) (cell_range L y).
Proof.
  intros HW HL U1 U2 Hne Hx Hy.
  destruct (group_cell_home L s g1 a1 x HW U1 Hx) as (rg1 & R1 & K1 & L1 & In1 & I1).
  destruct (group_cell_home L s g2 a2 y HW U2 Hy) as (rg2 & R2 & K2 & L2 & In2 & I2).
  destruct (Nat.eq_dec (prid (am_mem a1)) (prid (am_mem a2))) as [Hsame | Hdiff].
  2:{ eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
      intros E. injection E. intros _ Ep. exact (Hdiff Ep). }
  destruct (In_group_cells_span [] None U0 s g1 a1 x HW U1 Hx) as (d1 & E1 & Hd1 & Hw1).
  destruct (In_group_cells_span [] None U0 s g2 a2 y HW U2 Hy) as (d2 & E2 & Hd2 & Hw2).
  assert (GOAL : forall u v du dv au av, mc_loc u = LMem (padd (am_mem au) du) -> mc_loc v = LMem (padd (am_mem av) dv) ->
            prid (am_mem au) = prid (am_mem av) ->
            (poff (am_mem au) + du + Z.of_nat (mc_w u) <= poff (am_mem av) + dv \/ poff (am_mem av) + dv + Z.of_nat (mc_w v) <= poff (am_mem au) + du) ->
            ranges_disjoint (cell_range L u) (cell_range L v)).
  { intros u v du dv au av Eu Ev Hp D. cellsimp. rewrite Eu, Ev. cellsimp. rewrite Hp. lia. }
  (* [comment removed for export] *)
  assert (INS : forall ga a gb b u v du, usedX [] s ga a -> usedX [] s gb b -> inside [] s a b ->
            In v (group_cells gb b) -> mc_loc u = LMem (padd (am_mem a) du) -> 0 <= du -> du + Z.of_nat (mc_w u) <= group_extent a ->
            prid (am_mem a) = prid (am_mem b) ->
            ranges_disjoint (cell_range L u) (cell_range L v)).
  { intros ga a gb b u v du Ua Ub I Hv Eu Hdu Hwu Hp.
    destruct I as (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mlc & Memc & Lo & Hi & Fit).
    pose proof (inv_groups HW gb b Ub) as (_ & _ & Gslb & _). pose proof (Gslb j Hj) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (Nf & Of & Bf & _ & FG) & _). destruct (FG Hk) as [Off _].
    rewrite Memc, poff_slot_start in Lo, Hi.
    destruct (group_cells_vs_body [] None U0 s gb b j (poff (am_mem a) + du) (poff (am_mem a) + du + Z.of_nat (mc_w u)) v HW Ub Hj Hv
                ltac:(rewrite Hfr, Off, poff_slot_start; unfold UNIT in *; lia)
                ltac:(rewrite poff_slot_start; unfold UNIT, IB in *; lia)) as (dv & Ev & D).
    eapply (GOAL u v du dv a b Eu Ev Hp). lia. }
  destruct (inv_laminar HW g1 a1 g2 a2 U1 U2 Hne Hsame) as [Dj | [I | I]].
  - eapply (GOAL x y d1 d2 a1 a2 E1 E2 Hsame). unfold spans_disjoint in Dj. lia.
  - eapply (INS g1 a1 g2 a2 x y d1); eauto.
  - apply ranges_disjoint_sym. eapply (INS g2 a2 g1 a1 y x d2); eauto.
Qed.

(* [comment removed for export] *)
Lemma areas_cells_pairwise L s l :
  WF s -> layout_ok L s -> NoDup l -> (forall a, In a l -> In a (st_areas s)) ->
  pairwise ranges_disjoint (map (cell_range L) (areas_cells s l)).
Proof.
  intros HW HL. induction l as [|a t IH]; intros ND Hsub; cbn [areas_cells]; [exact I|].
  inversion ND as [|a' t' Ha Ht]; subst. rewrite map_app.
  apply pairwise_app.
  - apply area_cells_disjoint.
  - apply IH; [exact Ht | intros b Hb; apply Hsub; right; exact Hb].
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. apply in_map_iff in Hy as [c' [<- Hc']].
    destruct (In_areas_cells s t c' Hc') as (a' & next' & Ha' & Hc'').
    destruct (area_cell_home L s a (hd_error t) c (Hsub a (or_introl eq_refl)) Hc) as [In1 I1].
    destruct (area_cell_home L s a' next' c' (Hsub a' (or_intror Ha')) Hc'') as [In2 I2].
    eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
    intros E. injection E as <-. exact (Ha Ha').
Qed.

Theorem image_cells_disjoint : forall s L,
  WF s -> layout_ok L s -> pairwise ranges_disjoint (map (cell_range L) (image s)).
Proof.
  intros s L HW HL. pose proof (inv_areas HW) as (AND & A2 & _).
  assert (HOMEa : forall c, In c (areas_cells s (st_areas s)) -> exists a, In a (st_areas s) /\ In (LMem a, PGSZ) (footprint s) /\
             range_incl (cell_range L c) (crange L (LMem a, PGSZ)) /\ poff a <> 0).
  { intros c Hc. destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc').
    destruct (area_cell_home L s a next c Ha Hc') as [In1 I1]. exists a. split; [exact Ha|]. split; [exact In1|]. split; [exact I1|].
    destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _). rewrite Ea. cbn. unfold PGSZ in Hoa. lia. }
  assert (HOMEg : forall c, In c (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s)) ->
             exists k len, In (LMem (SP k 0), len) (footprint s) /\ range_incl (cell_range L c) (crange L (LMem (SP k 0), len))).
  { intros c Hc. apply in_flat_map in Hc as [[g am] [Hg Hc]]. cbn [fst snd] in Hc. apply (used_metas_usedX s g am HW) in Hg.
    destruct (group_cell_home L s g am c HW Hg Hc) as (rg & _ & _ & _ & In1 & I1). eexists _, _. split; [exact In1 | exact I1]. }
  unfold image. rewrite !map_app. apply pairwise_app; [apply ctx_cells_disjoint | apply pairwise_app |].
  - apply areas_cells_pairwise; [exact HW | exact HL | exact AND | intros a Ha; exact Ha].
  - apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)). apply pairwise_flat_map.
    + intros [g am] Hg. cbn [fst snd]. apply (used_metas_usedX s g am HW) in Hg.
      apply (pairwise_map_iff ranges_disjoint (cell_range L)). eapply group_cells_disjoint; [exact HW | exact Hg].
    + intros l1 [g1 a1] l2 [g2 a2] E Hin x y Hx Hy. cbn [fst snd] in Hx, Hy.
      pose proof (used_metas_split s l1 g1 a1 l2 g2 a2 (proj1 (inv_keys HW)) E Hin) as Hne.
      assert (U1 : usedX [] s g1 a1) by (apply (used_metas_usedX s g1 a1 HW); rewrite E; apply in_app_iff; right; left; reflexivity).
      assert (U2 : usedX [] s g2 a2) by (apply (used_metas_usedX s g2 a2 HW); rewrite E; apply in_app_iff; right; right; exact Hin).
      exact (groups_cells_disjoint L s g1 a1 g2 a2 x y HW HL U1 U2 Hne Hx Hy).
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. apply in_map_iff in Hy as [c' [<- Hc']].
    destruct (HOMEa c Hc) as (a & Ha & In1 & I1 & Hpa). destruct (HOMEg c' Hc') as (k & len & In2 & I2).
    eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
    intros E. injection E as Ea _. rewrite Ea in Hpa. exact (Hpa eq_refl).
  - intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. destruct (ctx_cell_home L s c Hc) as [In1 I1].
    apply in_app_iff in Hy as [Hy|Hy]; apply in_map_iff in Hy as [c' [<- Hc']].
    + destruct (HOMEa c' Hc') as (a & Ha & In2 & I2 & _).
      eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | discriminate | exact I1 | exact I2].
    + destruct (HOMEg c' Hc') as (k & len & In2 & I2).
      eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | discriminate | exact I1 | exact I2].
Qed.
