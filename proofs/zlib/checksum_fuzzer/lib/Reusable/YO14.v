(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12 YO0z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
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
Lemma am_slots_upd_slot_length am i x : length (am_slots (upd_slot am i x)) = length (am_slots am).
Proof. unfold upd_slot. cbn. apply length_lupd. Qed.
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
(am_sc am = 63 -> k = FUser /\ MMAP_THRESHOLD <= n) ->
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
destruct (H63 C1) as [-> Hbig]. auto.
+ right. repeat (split; [assumption|]). exact C4.
- intros p i Hp. split; intros HH; [discriminate | injection HH; intros; subst; exfalso; exact (Hp eq_refl)].
- intros i HH. discriminate.
- intros Hsc HL. apply (proj1 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia))). exact HL.
- intros Hsc Hav. apply (proj1 (proj2 (ring_facts _ _ _ _ _ _ HI Hu Hsc ltac:(lia)))). exact Hav.
- intros Hsc HL Hnh _. exfalso. apply Hnh. apply Hhdg; assumption.
- intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
eapply (inv_partial HI g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
Qed.
Lemma Inv_masks X R R' U s g am0 av fr ai :
Inv X R U s -> usedX X s g am0 -> 0 <= am_sc am0 < 48 ->
let am1 := am_set_aidx ai (am_set_freed fr (am_set_avail av am0)) in
masks_ok am1 ->
(forall i, 0 <= i <= am_last am0 -> allocated am1 i = allocated am0 i \/
(R = None /\ R' = Some (g, i) /\ allocated am0 i = false /\ allocated am1 i = true) \/
(R = Some (g, i) /\ R' = None /\ allocated am0 i = true /\ allocated am1 i = false)) ->
(forall p i, (p, i) <> (g, match R' with Some (_, j) => j | None => -1 end) ->
(p, i) <> (g, match R with Some (_, j) => j | None => -1 end) ->
(R = Some (p, i) <-> R' = Some (p, i))) ->
(forall i, R' = Some (g, i) -> 0 <= i <= am_last am0 /\ ss_fr (nth_slot am0 i) = None /\ allocated am1 i = true) ->
(forall i, R = Some (g, i) -> R' = Some (g, i) \/ allocated am1 i = false) ->
((am_prev am0, am_next am0) = (None, None) -> av = 0 /\ fr = 0) ->
(av <> 0 -> active_hd s (am_sc am0) = Some g) ->
((am_prev am0, am_next am0) <> (None, None) -> active_hd s (am_sc am0) <> Some g -> (forall i, R' <> Some (g, i)) -> fr <> 0) ->
(ai < am_last am0 -> forall p a, usedX X s p a -> p <> g -> am_sc a = am_sc am0 -> ~ am_aidx a < am_last a) ->
(stride_of am0 < class_size (am_sc am0) -> allocated am1 0 = true) ->
Inv X R' U (upd_meta g (MUsed am1) s).
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
Lemma allocated_eq am av fr ai i :
allocated (am_set_aidx ai (am_set_freed fr (am_set_avail av am))) i = negb (Z.testbit (Z.lor av fr) i).
Proof. reflexivity. Qed.
Lemma allocated_am am i : allocated am i = negb (Z.testbit (Z.lor (am_avail am) (am_freed am)) i).
Proof. reflexivity. Qed.
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
Qed.
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
Qed.
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
Definition allzero (X : list sptr) (s : astate) (sc : Z) : Prop :=
forall g am, usedX X s g am -> am_sc am = sc -> am_avail am = 0.
Definition ta_post (X : list sptr) (U : Z -> Z) (s : astate) (sc first : Z) (s' : astate) : Prop :=
first <> 0 /\
exists g am, Inv X (Some (g, ctz32 first)) U s' /\ active_hd s' sc = Some g /\
usedX X s' g am /\ am_sc am = sc /\ class_size sc <= stride_of am /\
0 <= ctz32 first <= am_last am /\
(forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) /\ ub_same s s'.
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
