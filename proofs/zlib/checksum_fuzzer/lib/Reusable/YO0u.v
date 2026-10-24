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
Section a.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.
Lemma same_group_starts am i1 i2 :
i1 <> i2 -> 16 <= stride_of am ->
poff (slot_start am i1) + stride_of am <= poff (slot_start am i2) \/
poff (slot_start am i2) + stride_of am <= poff (slot_start am i1).
Proof. intros Hne Hs. rewrite !poff_slot_start. assert (i1 < i2 \/ i2 < i1) as [H|H] by lia; [left|right]; nia. Qed.
Lemma slot_in_span g am i :
usedX X s g am -> 0 <= i <= am_last am ->
poff (am_mem am) + UNIT <= poff (slot_start am i) /\
poff (slot_start am i) + stride_of am <= poff (am_mem am) + group_extent am + IB.
Proof.
intros Hu Hi. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Hs.
rewrite poff_slot_start. unfold group_extent. split; nia.
Qed.
Lemma fgroup_frame g am j fr :
usedX X s g am -> 0 <= j <= am_last am -> ss_fr (nth_slot am j) = Some fr -> fr_kind fr = FGroup ->
fr_n fr = stride_of am - IB /\ fr_off fr = 0.
Proof.
intros Hu Hj Hfr Hk. pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _).
pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & _ & _ & _ & FG) & _).
destruct (FG Hk) as [A B]. auto.
Qed.
Lemma inside_slot_start g1 a1 i1 g2 a2 :
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
Lemma slot_starts_distinct g1 a1 i1 g2 a2 i2 :
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
Lemma frame_ptrs_distinct g1 a1 i1 f1 g2 a2 i2 f2 :
usedX X s g1 a1 -> usedX X s g2 a2 ->
0 <= i1 <= am_last a1 -> 0 <= i2 <= am_last a2 ->
ss_fr (nth_slot a1 i1) = Some f1 -> ss_fr (nth_slot a2 i2) = Some f2 ->
frame_ptr a1 i1 f1 = frame_ptr a2 i2 f2 -> g1 = g2 /\ i1 = i2.
Proof.
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
Lemma find_in_slots_sound sl base stride k0 p k :
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
Lemma find_in_slots_complete sl base stride k0 p j x fr :
nth_error sl j = Some x -> ss_fr x = Some fr -> padd base (stride * (k0 + Z.of_nat j) + UNIT * fr_off fr) = p ->
exists k, find_in_slots sl base stride k0 p = Some k.
Proof.
revert k0 j. induction sl as [|y t IH]; intros k0 [|j] Hn Hf Hp; cbn [nth_error] in Hn; try discriminate; cbn [find_in_slots].
- injection Hn as ->. rewrite Hf. rewrite Z.add_0_r in Hp. rewrite Hp, sptr_eqb_refl. eexists. reflexivity.
- destruct (ss_fr y) as [fy|]; [destruct (sptr_eqb _ p); [eexists; reflexivity|]|];
eapply (IH (k0 + 1) j); eauto; rewrite <- Hp; f_equal; lia.
Qed.
Lemma frame_ptr_base am i fr :
frame_ptr am i fr = padd (padd (am_mem am) UNIT) (stride_of am * i + UNIT * fr_off fr).
Proof.
unfold frame_ptr. apply sptr_eq_parts.
- rewrite !prid_padd, prid_slot_start. reflexivity.
- rewrite !poff_padd, poff_slot_start. lia.
Qed.
Lemma find_frame_in_spec g am i fr :
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
End a.
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
