(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
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
-
left. assert (stride_of am * k + stride_of am <= stride_of am * J) by nia.
destruct Fine as [Bl | (fr & Hfr & Ho & Lo2 & Hi2)]; [unfold UNIT, IB in *; lia|].
pose proof (Gsl k Hk) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _). unfold UNIT, IB in *. lia.
-
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
*
destruct (In_group_cells_span [] None U0 s g' am' c HW Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
destruct (inside_slot_start [] None U0 s HW g' am' 0 g am Hg' Hg ltac:(pose proof (inv_groups HW g' am' Hg') as ((M1 & _) & _); lia) I) as (j & frj & Hj & Hfrj & Hkj & Lo & Hi2).
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
*
destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
pose proof (inv_groups HW g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
destruct (group_cells_vs_body [] None U0 s g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HW Hg' Hj' Hcc) as (d & E & D).
-- rewrite Hfr', Off'. rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
-- rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
-- exact (GOAL d E D).
Qed.
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
-
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
-
unfold implb. destruct (0 <? am_maplen am) eqn:Em; [|reflexivity]. cbn [negb orb]. apply Z.ltb_lt in Em.
destruct (Gmp Em) as (r & rg & _ & _ & _ & _ & _ & Hfit & _).
unfold hdr_off16. apply Z.leb_le.
assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia.
unfold UNIT, IB, PGSZ in *.
assert (stride_of am * i / 16 * 16 + 16 * fr_off fr <= am_maplen am * 4096 - 20) by (rewrite Hdiv; lia).
assert (am_maplen am * 4096 / 16 = am_maplen am * 256) by (replace (am_maplen am * 4096) with (am_maplen am * 256 * 16) by lia; apply Z_div_mult; lia).
lia.
Qed.
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
-
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
