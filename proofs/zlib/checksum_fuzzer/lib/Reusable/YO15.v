(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition strip (am : ameta) : ameta := am_set_links None None am.
Lemma strip_fields a b : strip a = strip b ->
am_mem a = am_mem b /\ am_avail a = am_avail b /\ am_freed a = am_freed b /\ am_last a = am_last b /\
am_sc a = am_sc b /\ am_maplen a = am_maplen b /\ am_aidx a = am_aidx b /\ am_slots a = am_slots b.
Proof. unfold strip, am_set_links. intros H. injection H. auto 10. Qed.
Lemma strip_stride a b : strip a = strip b -> stride_of a = stride_of b.
Proof. intros H. apply strip_fields in H. unfold stride_of. destruct H as (_&_&_&->&->&->&_). reflexivity. Qed.
Lemma strip_extent a b : strip a = strip b -> group_extent a = group_extent b.
Proof. intros H. unfold group_extent. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (_&_&_&->&_). reflexivity. Qed.
Lemma strip_slot_start a b i : strip a = strip b -> slot_start a i = slot_start b i.
Proof. intros H. unfold slot_start. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (->&_). reflexivity. Qed.
Lemma strip_nth_slot a b i : strip a = strip b -> nth_slot a i = nth_slot b i.
Proof. intros H. unfold nth_slot. apply strip_fields in H. destruct H as (_&_&_&_&_&_&_&->). reflexivity. Qed.
Lemma strip_allocated a b i : strip a = strip b -> allocated a i = allocated b i.
Proof. intros H. unfold allocated. apply strip_fields in H. destruct H as (_&->&->&_). reflexivity. Qed.
Lemma strip_hdr_byte3 a b i fr : strip a = strip b -> hdr_byte3 a i fr = hdr_byte3 b i fr.
Proof. intros H. unfold hdr_byte3, rsv_code. rewrite (strip_stride _ _ H). reflexivity. Qed.
Lemma strip_hdr_off16 a b i fr : strip a = strip b -> hdr_off16 a i fr = hdr_off16 b i fr.
Proof. intros H. unfold hdr_off16. rewrite (strip_stride _ _ H). reflexivity. Qed.
Lemma strip_set_links pr nx am : strip (am_set_links pr nx am) = strip am.
Proof. reflexivity. Qed.
Lemma strip_refl am : strip am = strip am.
Proof. reflexivity. Qed.
Lemma class_size_ge16 sc : 0 <= sc < 48 -> 16 <= class_size sc.
Proof.
intros H. unfold class_size, znth.
assert (G : forall n, (n < 48)%nat -> 16 <= UNIT * nth n size_classes 0).
{ intros n Hn. do 48 (destruct n as [|n]; [cbn; lia|]). lia. }
apply G. lia.
Qed.
Lemma stride_pos X R s g am : group_ok X R s g am -> 16 <= stride_of am.
Proof.
intros (Gm & Gml & _ & Gc & _). unfold stride_of. destruct Gm as (Hl & _).
destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
- apply andb_prop in E as [_ E2]. destruct (am_maplen am =? 0) eqn:E3; [discriminate|].
apply Z.eqb_neq in E3. unfold UNIT. lia.
- destruct Gc as [(H63 & Hl0 & Hmp & _) | (Hsc & _)].
+ rewrite Hl0 in E. cbn [Z.eqb andb] in E. destruct (am_maplen am =? 0) eqn:E3; [|discriminate].
apply Z.eqb_eq in E3. lia.
+ apply class_size_ge16. exact Hsc.
Qed.
Lemma extent_pos X R s g am : group_ok X R s g am -> 0 < group_extent am.
Proof.
intros G. pose proof (stride_pos _ _ _ _ _ G) as Hs. destruct G as ((Hl & _) & _).
unfold group_extent, UNIT, IB. nia.
Qed.
Section d.
Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
Hypothesis HI : Inv X R U s.
Hypothesis ER : forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg.
Hypothesis Cb : forall p am', usedX X' s' p am' -> exists am, usedX X s p am /\ strip am' = strip am.
Hypothesis Cf : forall p am, usedX X s p am ->
(exists am', usedX X' s' p am' /\ strip am' = strip am) \/
(memb p X' = true /\ forall j, ss_fr (nth_slot am j) = None).
Hypothesis HR' : reserved_ok X' R' s'.
Hypothesis RR : forall p i am', usedX X' s' p am' ->
(R = Some (p, i) <-> R' = Some (p, i)) \/
(R' = Some (p, i) /\ R <> Some (p, i) /\ ss_fr (nth_slot am' i) = None) \/
(R = Some (p, i) /\ R' <> Some (p, i) /\ (ss_fr (nth_slot am' i) = None -> allocated am' i = false)).
Lemma su_nested a a' : strip a' = strip a -> nested_ok X s a -> nested_ok X' s' a'.
Proof.
intros E N Hm. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _ & _).
rewrite Eml in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
split; [congruence|].
destruct (Cf _ _ Hu) as [(b' & Hu' & Eb) | [_ Hgone]].
- exists g', b', i', fr'. pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&Bs&_&_&Bsl).
split; [exact Hu'|]. split; [rewrite Bl; exact Hi|].
split; [unfold nth_slot in *; rewrite Bsl; exact Hf|]. split; [exact Hk|].
split; [rewrite Em, (strip_slot_start _ _ _ Eb); exact Hmem|].
split; [rewrite Es, Bs; exact Hsc|]. split; [rewrite Bs; exact Hsc'|].
rewrite Es, El. exact Hfit.
- exfalso. rewrite (Hgone i') in Hf. discriminate.
Qed.
Lemma su_mapped a a' : strip a' = strip a -> mapped_ok s a -> mapped_ok s' a'.
Proof.
intros E M Hm. pose proof (strip_stride _ _ E) as Est. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _).
rewrite Eml in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
rewrite Em, Eml, El, Est, Es. split; [exact H1|]. split; [apply ER; assumption|]. auto.
Qed.
Lemma su_group p am am' :
group_ok X R s p am -> usedX X' s' p am' -> strip am' = strip am -> group_ok X' R' s' p am'.
Proof.
intros G Hu E. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (strip_fields _ _ E) as (Em & Eav & Efr & El & Es & Eml & Eai & Esl).
pose proof (strip_stride _ _ E) as Est.
split.
{ unfold masks_ok in *. rewrite El, Eai, Esl, Eav, Efr. exact Gm. }
split; [rewrite Eml; exact Gml|].
split.
{ intros i Hi. rewrite El in Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3).
unfold slot_ok. rewrite (strip_nth_slot _ _ i E), Eml.
split; [exact S1|]. split; [exact S2|].
pose proof (RR p i am' Hu) as RRi. rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E) in RRi.
destruct (ss_fr (nth_slot am i)) as [fr|].
- destruct S3 as (A1 & A2 & A3 & A4). rewrite (strip_allocated _ _ i E).
split; [exact A1|]. split.
{ destruct RRi as [RRi | [(_ & _ & RRi) | (RRi & RRi' & _)]]; [ | discriminate | exact RRi'].
intros H. apply A2. apply RRi. exact H. }
split.
{ unfold frame_ok in *. rewrite Est, (strip_hdr_off16 _ _ i fr E). exact A3. }
rewrite (strip_hdr_byte3 _ _ i fr E), (strip_hdr_off16 _ _ i fr E). exact A4.
- rewrite (strip_allocated _ _ i E).
destruct RRi as [RRi | [(RRi & _) | (_ & _ & RRi)]].
+ destruct S3 as [S3|S3]; [left; exact S3 | right; apply RRi; exact S3].
+ right. exact RRi.
+ left. apply RRi. reflexivity. }
split.
{ unfold class_ok in *. rewrite Es, El, Eml, Eav, Efr, Est, (strip_allocated _ _ 0 E), (strip_nth_slot _ _ 0 E).
destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C]; [left | right; exact C].
repeat split; auto.
destruct C6 as [C6 | C6]; [| right; exact C6].
pose proof (RR p 0 am' Hu) as [RRi | [(RRi & _) | (_ & RRn & RRi)]].
- left. apply RRi. exact C6.
- left. exact RRi.
-
rewrite (strip_nth_slot _ _ 0 E), (strip_allocated _ _ 0 E) in RRi.
destruct (ss_fr (nth_slot am 0)) as [fr|] eqn:Ef.
+ right. pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). rewrite Ef in S3.
exists fr. split; [reflexivity|].
destruct S3 as (_ & HR2 & _). exfalso. exact (HR2 C6).
+ exfalso. specialize (RRi eq_refl). unfold allocated in RRi. rewrite C4, C5 in RRi. cbn in RRi.
rewrite Z.lor_0_l, Z.bits_0 in RRi || (cbn in RRi). discriminate. }
split; [eapply su_mapped; eauto | eapply su_nested; eauto].
Qed.
End d.
Section e.
Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
Hypothesis HI : Inv X R U s.
Hypothesis ER : forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg.
Hypothesis Cb : forall p am', usedX X' s' p am' -> exists am, usedX X s p am /\ strip am' = strip am.
Hypothesis Cf : forall p am, usedX X s p am ->
(exists am', usedX X' s' p am' /\ strip am' = strip am) \/
(memb p X' = true /\ forall j, ss_fr (nth_slot am j) = None).
Hypothesis HR' : reserved_ok X' R' s'.
Hypothesis RR : forall p i am', usedX X' s' p am' ->
(R = Some (p, i) <-> R' = Some (p, i)) \/
(R' = Some (p, i) /\ R <> Some (p, i) /\ ss_fr (nth_slot am' i) = None) \/
(R = Some (p, i) /\ R' <> Some (p, i) /\ (ss_fr (nth_slot am' i) = None -> allocated am' i = false)).
Lemma su_groups : forall p am', usedX X' s' p am' -> group_ok X' R' s' p am'.
Proof.
intros p am' Hu. destruct (Cb _ _ Hu) as (am & Hu0 & E).
eapply su_group; eauto. apply (inv_groups HI). exact Hu0.
Qed.
Lemma su_inside a a' b b' :
strip a' = strip a -> strip b' = strip b -> inside X s a b -> inside X' s' a' b' \/
exists c ac, usedX X s c ac /\ memb c X' = true /\ (forall j, ss_fr (nth_slot ac j) = None) /\
poff (am_mem ac) <= poff (am_mem a) /\ poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac /\
am_maplen ac = 0 /\ prid (am_mem ac) = prid (am_mem b).
Proof.
intros Ea Eb (j & fr & c & ac & Hj & Hfr & Hk & Hc & Hml & Hmem & Hlo & Hhi & Hfit).
destruct (Cf _ _ Hc) as [(ac' & Hc' & Ec) | [Hg Hnone]].
- left. pose proof (strip_fields _ _ Ec) as (Cm&_&_&_&_&Cml&_&_).
pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&_&_&_&Bsl).
pose proof (strip_fields _ _ Ea) as (Am&_).
exists j, fr, c, ac'. split; [rewrite Bl; exact Hj|]. split; [unfold nth_slot in *; rewrite Bsl; exact Hfr|].
split; [exact Hk|]. split; [exact Hc'|]. split; [rewrite Cml; exact Hml|].
split; [rewrite Cm, (strip_slot_start _ _ _ Eb); exact Hmem|].
split; [rewrite Cm, Am; exact Hlo|].
split; [rewrite Am, Cm, (strip_extent _ _ Ea), (strip_extent _ _ Ec); exact Hhi|].
rewrite (strip_extent _ _ Ec). exact Hfit.
- right. exists c, ac. repeat split; auto.
rewrite Hmem. unfold slot_start. destruct (am_mem b); reflexivity.
Qed.
Lemma su_laminar : laminar X' s'.
Proof.
intros p1 a1' p2 a2' H1 H2 Hne Hr.
destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
pose proof (strip_fields _ _ E1) as (M1&_). pose proof (strip_fields _ _ E2) as (M2&_).
assert (Hgone : forall a a' pa c ac, usedX X s pa a -> usedX X' s' pa a' -> strip a' = strip a ->
usedX X s c ac -> memb c X' = true -> (forall j, ss_fr (nth_slot ac j) = None) ->
poff (am_mem ac) <= poff (am_mem a) ->
poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac ->
am_maplen ac = 0 -> prid (am_mem a) = prid (am_mem ac) -> False).
{ intros a a' pa c ac Ua Ua' Ea Uc Xc Fc Lo Hi Mc Pr.
assert (Hpc : pa <> c).
{ intros ->. pose proof (usedX_MT _ _ _ _ Ua') as [_ M]. rewrite M in Xc. discriminate. }
pose proof (extent_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Pa.
destruct (inv_laminar HI pa a c ac Ua Uc Hpc Pr) as [D | [I | I]].
- unfold spans_disjoint in D. lia.
- destruct I as (j & fr & _ & _ & _ & Hfr & _). rewrite (Fc j) in Hfr. discriminate.
- destruct I as (j & fr & c2 & ac2 & Hj & Hfr & Hk & Uc2 & Ml2 & Mem2 & Lo2 & Hi2 & _).
pose proof (stride_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Sp.
unfold slot_start in Mem2. rewrite Mem2 in Lo2. destruct (am_mem a) as [ra oa]. cbn [poff padd] in Lo2, Lo, Hi.
assert (0 <= stride_of a * j) by (apply Z.mul_nonneg_nonneg; lia).
unfold UNIT in Lo2. lia. }
destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne ltac:(rewrite <- M1, <- M2; exact Hr)) as [D | [I | I]].
- left. unfold spans_disjoint in *. rewrite M1, M2, (strip_extent _ _ E1), (strip_extent _ _ E2). exact D.
- destruct (su_inside _ _ _ _ E1 E2 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; left; exact I'|].
exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a1 a1' p1 c ac); eauto.
rewrite Pc, <- M1, <- M2. exact Hr.
- destruct (su_inside _ _ _ _ E2 E1 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; right; exact I'|].
exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a2 a2' p2 c ac); eauto.
rewrite Pc, <- M1, <- M2. symmetry. exact Hr.
Qed.
Lemma su_maps : maps_unique X' s'.
Proof.
intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
pose proof (strip_fields _ _ E1) as (M1&_&_&_&_&L1&_). pose proof (strip_fields _ _ E2) as (M2&_&_&_&_&L2&_).
eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
Qed.
Lemma su_partial : partial_unique X' s'.
Proof.
intros p1 a1' p2 a2' H1 H2 Hsc Hp1 Hp2.
destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
pose proof (strip_fields _ _ E1) as (_&_&_&L1&S1&_&A1&_). pose proof (strip_fields _ _ E2) as (_&_&_&L2&S2&_&A2&_).
eapply (inv_partial HI p1 a1 p2 a2); eauto; try lia; congruence.
Qed.
Theorem Inv_surgery :
ctx_ok s' -> keys_ok s' -> areas_ok s' -> Xok X' s' -> rings_ok X' R' s' -> usage_ok X' U' s' ->
Inv X' R' U' s'.
Proof.
intros C K A XO RG US.
split; [exact C|]. split; [exact K|]. split; [exact A|].
split; [exact XO|]. split; [apply su_groups|]. split; [apply su_laminar|]. split; [apply su_maps|].
split; [exact RG|]. split; [exact US|]. split; [exact HR' | apply su_partial].
Qed.
End e.
