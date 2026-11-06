(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0i YP0q YP0m
YP0w YP10 YP0x YP0t YP0z YP0o YP0k
YP0p YP0s YP0n YP0v YP0r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma mupdate_mupdate_same l p x y : mupdate (mupdate l p y) p x = mupdate l p x.
Proof.
induction l as [|[q z] t IH]; cbn.
- rewrite sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma upd_meta_twice g x y s : upd_meta g x (upd_meta g y s) = upd_meta g x s.
Proof. unfold upd_meta. cbn. rewrite mupdate_mupdate_same. reflexivity. Qed.
Lemma usedX_same_metas X s s' q a : st_metas s' = st_metas s -> (usedX X s' q a <-> usedX X s q a).
Proof. intros E. unfold usedX, MTX, MT. rewrite E. tauto. Qed.
Lemma ublist_frame s p n g idx :
NoDup (keys s) -> In ((p, n), (g, idx)) (ublist s) ->
exists am fr, MT s g = Some (MUsed am) /\ 0 <= idx <= am_last am /\ ss_fr (nth_slot am idx) = Some fr /\
fr_kind fr = FUser /\ fr_n fr = n /\ p = frame_ptr am idx fr.
Proof.
intros ND Hin. unfold ublist in Hin. apply in_flat_map in Hin as [g' [Hg Hin]].
destruct (MT s g') as [[pr nx| |am]|] eqn:Em; cbn [ucontrib] in Hin; [destruct Hin | destruct Hin | | destruct Hin].
unfold blocks_of in Hin. apply in_flat_map in Hin as [i [Hi Hin]]. apply In_zseq in Hi.
unfold slot_block in Hin. destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hin].
destruct (fr_kind fr) eqn:Ek; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <- -> ->.
exists am, fr. rewrite Em. repeat split; auto; lia.
Qed.
Section d.
Variables (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (fr : frame) (n needed : Z).
Hypothesis HI : Inv [] None U s.
Hypothesis Hu : usedX [] s g am.
Hypothesis H63 : am_sc am = 63.
Hypothesis Hfr : ss_fr (nth_slot am 0) = Some fr.
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis Hneeded : n + UNIT * fr_off fr + UNIT + IB <= needed.
Hypothesis Hpg : needed mod PGSZ = 0.
Let r' := length (st_regions s).
Let ml' := needed / 4096.
Let s1 := set_regions (st_regions s ++ [mkRegion RkMap needed [] true]) s.
Let amR := remap_am am r' ml' 0 (fr_off fr) n.
Let s2 := upd_meta g (MUsed amR) s1.
Lemma rm_G : group_ok [] None s g am.
Proof. exact (inv_groups HI g am Hu). Qed.
Lemma rm_shape :
am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\ am_aidx am = 0 /\
am_prev am = None /\ am_next am = None /\ length (am_slots am) = 1%nat.
Proof.
pose proof rm_G as ((Glast & Gaidx & Glen & _) & _ & _ & Gcl & _ & _).
destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & _) | (C1 & _)]; [|lia].
destruct (proj2 (proj2 (inv_rings HI)) g am Hu H63) as [P N].
rewrite C2 in Glen, Gaidx. repeat split; auto; lia.
Qed.
Lemma rm_slots : exists sl, am_slots am = [sl] /\ nth_slot am 0 = sl.
Proof.
destruct rm_shape as (_ & _ & _ & _ & _ & _ & _ & L).
destruct (am_slots am) as [|sl [|]] eqn:E; cbn in L; try lia.
exists sl. split; [reflexivity|]. unfold nth_slot. rewrite E. reflexivity.
Qed.
Lemma rm_ml' : needed = ml' * 4096 /\ 1 <= ml'.
Proof.
pose proof rm_G as (_ & _ & Gsl & _). destruct rm_shape as (Hl & _).
unfold ml'. unfold PGSZ in Hpg. pose proof (Z_div_mod_eq_full needed 4096).
pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (F1 & F2 & _) & _).
unfold MMAP_THRESHOLD, UNIT, IB in *. lia.
Qed.
Lemma rm_amR :
amR = mkAMeta None None (SP r' 0) 0 0 0 63 ml' 0
[resize_slot (ml' * 4096 - UNIT) 0 (nth_slot am 0) (fr_off fr) n].
Proof.
destruct rm_shape as (Hl & _ & Hav & Hfd & Hai & Hp & Hnx & _). destruct rm_slots as (sl & Esl & Ens).
subst amR. unfold remap_am. rewrite Hp, Hnx, Hav, Hfd, Hl, H63, Hai, Esl, Ens. reflexivity.
Qed.
Lemma rm_stride : stride_of amR = ml' * 4096 - UNIT.
Proof.
rewrite rm_amR. unfold stride_of. cbn [am_last am_maplen am_sc Z.eqb andb].
destruct rm_ml' as [_ H1]. destruct (ml' =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma rm_nth0 : nth_slot amR 0 = resize_slot (ml' * 4096 - UNIT) 0 (nth_slot am 0) (fr_off fr) n.
Proof. rewrite rm_amR. reflexivity. Qed.

Let am0 := upd_slot am 0 (mkSlot (ss_hdr (nth_slot am 0)) None).
Let s1a := upd_meta g (MUsed am0) s1.
Lemma rm_HI1 : Inv [] None U s1.
Proof. apply Inv_new_map; [exact HI | destruct rm_ml'; lia]. Qed.
Lemma rm_U1 q a : usedX [] s1 q a <-> usedX [] s q a.
Proof. apply usedX_same_metas. reflexivity. Qed.
Lemma rm_fresh q a : usedX [] s q a -> (prid (am_mem a) < r')%nat.
Proof. intros H. exact (used_group_prid_lt _ _ _ _ q a HI H). Qed.
Lemma rm_am0_nth j : 0 <= j -> nth_slot am0 j = if j =? 0 then mkSlot (ss_hdr (nth_slot am 0)) None else nth_slot am j.
Proof.
intros Hj. subst am0. apply nth_slot_upd_slot; [lia | exact Hj |].
destruct rm_shape as (_ & _ & _ & _ & _ & _ & _ & L). rewrite L. lia.
Qed.
Lemma rm_am0_frameless j : ss_fr (nth_slot am0 j) = None.
Proof.
destruct rm_slots as (sl & Esl & Ens). subst am0. unfold upd_slot, nth_slot. cbn [am_slots am_set_slots].
rewrite Esl. cbn. destruct (Z.to_nat j) as [|[|k]]; reflexivity.
Qed.
Lemma rm_HI1a : Inv [] (Some (g, 0)) U s1a.
Proof.
pose proof rm_HI1 as HI1. pose proof (proj2 (rm_U1 g am) Hu) as Hu1.
pose proof (inv_groups HI1 g am Hu1) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
destruct rm_shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & L).
pose proof (Gsl 0 ltac:(lia)) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & Hfok & Hhdr).
assert (GS : geom_same am am0).
{ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros j frj Hj Hkj. exfalso.
destruct rm_slots as (sl & Esl & Ens).
assert (Hsl : ss_fr sl = Some fr) by (rewrite <- Ens; exact Hfr).
unfold nth_slot in Hj. rewrite Esl in Hj.
destruct (Z.to_nat j) as [|[|k]]; cbn in Hj; try discriminate.
rewrite Hsl in Hj. injection Hj as ->. rewrite Hk in Hkj. discriminate. }
eapply (Inv_used_update [] None (Some (g, 0)) U s1 g am am0 HI1 Hu1 (geom_same_upto_of [] s1 _ _ GS)).
- subst am0. destruct am; split; reflexivity.
-   unfold masks_ok. subst am0. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
repeat (split; [assumption|]). exact Gfra.
-   intros i Hi. cbn [am_last am0 upd_slot am_set_slots] in Hi.
replace (am_last am0) with (am_last am) in Hi by reflexivity. assert (i = 0) as -> by lia.
unfold slot_ok. rewrite rm_am0_nth, Z.eqb_refl by lia. cbn [ss_hdr ss_fr].
replace (am_maplen am0) with (am_maplen am) by reflexivity.
split; [exact S1|]. split; [exact S2|]. right. reflexivity.
-   left. cbn. rewrite H63, Hl, Hav, Hfd. repeat split; try lia. left. reflexivity.
- intros p i Hpg'. split; intros HH; [|discriminate]. injection HH; intros; subst. exfalso. exact (Hpg' eq_refl).
- intros i HH. injection HH as <-. cbn [am_last am0 upd_slot am_set_slots]. replace (am_last am0) with (am_last am) by reflexivity.
split; [lia|]. split; [apply rm_am0_frameless|]. replace (allocated am0 0) with (allocated am 0) by reflexivity. exact Hal.
- intros Hsc. lia.
- intros Hsc. lia.
- intros Hsc. lia.
- intros Hpa. cbn [am_aidx am_last am0 upd_slot am_set_slots] in Hpa.
replace (am_aidx am0) with (am_aidx am) in Hpa by reflexivity. replace (am_last am0) with (am_last am) in Hpa by reflexivity. lia.
Qed.
Let Ug := fun c => U c + contrib [] s1a c g.
Lemma rm_HIx : Inv [g] None Ug s1a.
Proof.
destruct rm_shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & L).
apply (Inv_exempt [] (Some (g, 0)) U s1a g am0 rm_HI1a).
- apply usedX_upd. left. split; [reflexivity|]. split; [exact (proj2 (usedX_MT _ _ _ _ Hu)) | reflexivity].
- apply rm_am0_frameless.
- subst am0. cbn. exact Hp.
- subst am0. cbn. exact Hnx.
- intros p i E. injection E as <- _. reflexivity.
Qed.
Lemma rm_Ug c : 0 <= c < 48 -> Ug c = U c.
Proof.
intros Hc. subst Ug. cbn beta. unfold contrib, MTX. unfold s1a. rewrite MT_upd_same.
change (memb g []) with false. cbn iota.
change (am_sc am0) with (am_sc am). rewrite H63.
destruct (63 =? c) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.
Lemma rm_group : group_ok [] None s2 g amR.
Proof.
pose proof rm_G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
destruct rm_shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & L).
pose proof (Gsl 0 ltac:(lia)) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (F1 & F2 & F3 & F4 & F5) & Hhdr).
destruct rm_ml' as [Eml Hml1]. pose proof rm_stride as Hstr.
assert (Hmasks : masks_ok amR).
{ rewrite rm_amR. unfold masks_ok. cbn [am_last am_aidx am_slots am_avail am_freed length].
repeat split; try lia; intros; rewrite ?Z.bits_0; auto. }
split; [exact Hmasks|]. split; [rewrite rm_amR; cbn; lia|]. split.
{ intros i Hi. rewrite rm_amR in Hi. cbn [am_last] in Hi. assert (i = 0) as -> by lia.
unfold slot_ok. rewrite rm_nth0. unfold resize_slot. cbn [ss_hdr ss_fr].
replace (am_maplen amR) with ml' by (rewrite rm_amR; reflexivity).
set (reserved := ml' * 4096 - UNIT - IB - UNIT * fr_off fr - n).
set (rsv := if 5 <=? reserved then 5 else reserved).
assert (Hrsv : 0 <= rsv <= 5) by (subst rsv reserved; destruct (5 <=? _) eqn:E5; [apply Z.leb_le in E5|apply Z.leb_gt in E5]; unfold UNIT, IB in *; lia).
split.
{ destruct (fr_off fr =? 0); [discriminate | intros E; exfalso; pose proof (S1 E); lia]. }
split.
{ intros h3 h16 Eh. destruct (fr_off fr =? 0).
- injection Eh as <- <-. rewrite Z.mul_0_r. cbn. lia.
- exact (S2 h3 h16 Eh). }
split.
{ replace (allocated amR 0) with (allocated am 0); [exact Hal|]. rewrite rm_amR. unfold allocated. cbn. rewrite Hav, Hfd. reflexivity. }
split; [discriminate|]. split.
{ unfold frame_ok. cbn [fr_n fr_off fr_kind]. rewrite Hstr.
split; [unfold MMAP_THRESHOLD in Hn; lia|]. split; [exact F2|]. split; [unfold UNIT, IB in *; lia|]. split.
- unfold hdr_off16. rewrite Hstr. cbn [fr_off]. rewrite Z.mul_0_r. cbn. lia.
- intros; discriminate. }
cbn [fr_off]. intros E0. rewrite E0, Z.eqb_refl. f_equal. f_equal.
- unfold hdr_byte3, rsv_code. cbn [fr_kind fr_off fr_n]. rewrite Hstr. subst rsv reserved. rewrite E0. lia.
- unfold hdr_off16. cbn [fr_off]. rewrite Hstr. lia. }
split.
{ left. rewrite rm_amR at 1 2 3 4 5. cbn [am_sc am_last am_maplen am_avail am_freed].
repeat (split; [first [reflexivity | lia]|]). right.
exists (mkFrame (fr_off fr) n FUser). rewrite rm_nth0. unfold resize_slot. cbn. auto. }
split.
{ intros _. exists r', (mkRegion RkMap needed [] true).
split; [rewrite rm_amR; reflexivity|]. split.
{ unfold region_of, s2, upd_meta, s1. cbn [st_regions set_metas set_regions]. subst r'.
rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
replace (am_maplen amR) with ml' by (rewrite rm_amR; reflexivity).
replace (am_last amR) with 0 by (rewrite rm_amR; reflexivity).
rewrite Hstr. cbn [rg_len]. unfold PGSZ, UNIT. split; [lia|]. split; [lia|].
intros _ Hsc. rewrite rm_amR in Hsc. cbn in Hsc. lia. }
intros H0. exfalso. rewrite rm_amR in H0. cbn in H0. lia.
Qed.
Lemma remap_Inv : Inv [] None U s2.
Proof.
pose proof rm_HIx as HIx.
destruct rm_shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & L).
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
assert (Kg1a : In g (keys s1a)).
{ unfold s1a. rewrite keys_upd_In; [| eapply MT_Some_In_keys; exact Mg]. eapply MT_Some_In_keys. exact Mg. }
assert (Es2 : s2 = upd_meta g (MUsed amR) s1a) by (unfold s2, s1a; rewrite upd_meta_twice; reflexivity).
assert (EM : MT s2 g = Some (MUsed amR)) by (unfold s2; apply MT_upd_same).
assert (EO : forall q, q <> g -> MT s2 q = MT s1a q).
{ intros q Hq. rewrite Es2. apply MT_upd_other. exact Hq. }
assert (EK : keys s2 = keys s1a) by (rewrite Es2; apply keys_upd_In; exact Kg1a).
assert (FRESH : forall q a, usedX [g] s1a q a -> prid (am_mem a) <> r').
{ intros q a Hq. apply usedX_cons_inv in Hq as [Hne Hq]. unfold s1a in Hq. apply usedX_upd in Hq.
destruct Hq as [(E & _) | (_ & Hq)]; [exfalso; exact (Hne E)|].
apply rm_U1 in Hq. pose proof (rm_fresh q a Hq). lia. }
eapply (Inv_install [] None Ug U s1a s2 g amR HIx eq_refl EM EO EK).
- rewrite Es2. reflexivity.
- exact rm_group.
- intros q a Hq Hp'. exfalso. apply (FRESH q a Hq). rewrite Hp'. rewrite rm_amR. reflexivity.
- intros _ q a Hq _ Hp'. apply (FRESH q a Hq). rewrite Hp'. rewrite rm_amR. reflexivity.
- intros H. rewrite rm_amR in H. cbn in H. lia.
- intros p i E. discriminate.
- intros p i E. discriminate.
- rewrite Es2. apply ctx_ok_upd_meta; [exact (inv_ctx HIx) | exact Kg1a].
- rewrite Es2. eapply sbmh_keys; [apply sbmh_upd_meta; exact Kg1a | exact (inv_keys HIx)].
- rewrite Es2. eapply sbmh_areas; [apply sbmh_upd_meta; exact Kg1a | exact (inv_areas HIx)].
- destruct (inv_rings HIx) as (F & A & D). split; [|split].
+ eapply ux_free_ring; eauto.
+ intros c Hc. eapply (ux_active_other [] s1a s2 g amR eq_refl EM EO None); eauto.
rewrite rm_amR; cbn; lia.
+ eapply ux_direct; eauto; rewrite rm_amR; reflexivity.
- intros c Hc. replace (usage_of s2 c) with (usage_of s1a c) by (rewrite Es2; reflexivity).
rewrite (inv_usage HIx c Hc).
rewrite (ux_class_sum [] s1a s2 g amR eq_refl EM EO c EK (proj1 (inv_keys HIx)) Kg1a).
rewrite (rm_Ug c Hc). replace (am_sc amR) with 63 by (rewrite rm_amR; reflexivity).
destruct (63 =? c) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.
Lemma remap_old_unref q a : usedX [] s2 q a -> 0 < am_maplen a -> prid (am_mem a) <> prid (am_mem am).
Proof.
intros Hq Hm. unfold s2 in Hq. apply usedX_upd in Hq. destruct Hq as [(-> & _ & E) | (Hne & Hq)].
- injection E as <-. rewrite rm_amR. cbn [am_mem prid]. pose proof (rm_fresh g am Hu). lia.
- apply rm_U1 in Hq. intros Ep. apply Hne.
destruct rm_shape as (_ & Hml & _).
exact (inv_maps HI q a g am Hq Hu Hm ltac:(lia) Ep).
Qed.

Lemma remap_ublist :
exists l1 l2, ublist s = l1 ++ [((frame_ptr am 0 fr, fr_n fr), (g, 0))] ++ l2 /\
ublist s2 = l1 ++ [((padd (slot_start amR 0) (UNIT * fr_off fr), n), (g, 0))] ++ l2.
Proof.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
destruct (ublist_split s g (proj1 (inv_keys HI)) (MT_Some_In_keys _ _ _ Mg)) as (L1 & L2 & Hupd & Hs).
exists L1, L2. split.
- rewrite Hs, Mg. cbn [ucontrib]. unfold blocks_of. destruct rm_shape as (Hl & _). rewrite Hl.
change (zseq 0 (0 + 1)) with [0]. cbn [flat_map].
unfold slot_block. rewrite Hfr, Hk, app_nil_r. reflexivity.
- assert (E : ublist s2 = ublist (upd_meta g (MUsed amR) s)).
{ unfold s2, s1, ublist, keys, MT, upd_meta. cbn. reflexivity. }
rewrite E, Hupd. cbn [ucontrib]. unfold blocks_of. replace (am_last amR) with 0 by (rewrite rm_amR; reflexivity).
change (zseq 0 (0 + 1)) with [0]. cbn [flat_map]. unfold slot_block. rewrite rm_nth0. unfold resize_slot. cbn [ss_fr fr_kind fr_off fr_n].
rewrite app_nil_r. reflexivity.
Qed.
End d.
Definition realloc_post (U : Z -> Z) (s : astate) (p : sptr) (nold n : Z) (r : option sptr * astate) : Prop :=
Inv [] None U (snd r) /\
match fst r with
| None => ub_same s (snd r)
| Some q => exists l1 l2 m1 m2 key key',
ublist s = l1 ++ ((p, nold), key) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\ ublist (snd r) = m1 ++ ((q, n), key') :: m2
end.
Lemma split_unique {A B : Type} (f : A -> B) (k1 k2 a1 a2 : list A) (x : A) :
NoDup (map f (k1 ++ x :: k2)) -> k1 ++ x :: k2 = a1 ++ x :: a2 -> k1 = a1 /\ k2 = a2.
Proof.
revert a1. induction k1 as [|y k1 IH]; intros [|z a1] ND E; cbn in E.
- injection E as <-. auto.
- injection E as <- ->. exfalso. cbn in ND. inversion ND as [|? ? Hni _]; subst.
apply Hni. rewrite map_app. apply in_app_iff. right. left. reflexivity.
- injection E as -> E'. exfalso. cbn in ND. inversion ND as [|? ? Hni _]; subst.
apply Hni. rewrite map_app. apply in_app_iff. right. left. reflexivity.
- injection E as -> E'. cbn in ND. inversion ND as [|? ? _ ND']; subst.
destruct (IH a1 ND' E') as [-> ->]. auto.
Qed.
Lemma ublist_ptrs_NoDup s : WF s -> NoDup (map (fun b : (sptr * Z) * (sptr * Z) => fst (fst b)) (ublist s)).
Proof.
intros HW. replace (map (fun b : (sptr * Z) * (sptr * Z) => fst (fst b)) (ublist s)) with (map fst (map fst (ublist s))) by (rewrite map_map; reflexivity).
rewrite <- (user_blocks_ublist s (proj1 (inv_keys HW))). apply user_block_ptrs_NoDup. exact HW.
Qed.
Lemma realloc_move_spec s g am idx fr n (Q : option sptr * astate -> Prop) :
WF s -> usedX [] s g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser -> 0 <= n ->
(forall r, realloc_post U0 s (frame_ptr am idx fr) (fr_n fr) n r -> Q r) ->
itok (realloc_move (frame_ptr am idx fr) n s) Q.
Proof.
intros HI Hu Hidx Hfr Hk Hn HQ.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
assert (Hin : In ((frame_ptr am idx fr, fr_n fr), (g, idx)) (ublist s)).
{ pose proof (inv_groups HI g am Hu) as ((_ & _ & Glen & _) & _).
destruct (ublist_upd_slot s g am idx slot_junk (proj1 (inv_keys HI)) Mg Hidx Glen) as (l1 & l2 & E1 & _).
rewrite E1. unfold slot_block. rewrite Hfr, Hk. apply in_app_iff. right. left. reflexivity. }
unfold realloc_move. mbinds. eapply malloc_spec; [exact HI | exact Hn |].
intros [q s1] [HI1 Hpost]. cbn [fst snd] in HI1, Hpost. msimp.
destruct q as [q|].
- destruct Hpost as (g' & am' & idx' & off' & _ & (l1 & l2 & E1 & E2)).
set (new := ((q, n), (g', idx'))) in *. set (old := ((frame_ptr am idx fr, fr_n fr), (g, idx))) in *.
assert (Hin1 : In old (ublist s1)).
{ rewrite E1. rewrite E2 in Hin. apply in_app_iff in Hin. apply in_app_iff. destruct Hin; [left | right; right]; assumption. }
destruct (ublist_frame s1 _ _ g idx (proj1 (inv_keys HI1)) Hin1) as (am1 & fr1 & M1 & Hidx1 & Hfr1 & Hk1 & Hn1 & Ep).
rewrite Ep. mbinds.
eapply (free_spec U0 s1 g am1 idx fr1); [exact HI1 | intros c; unfold U0; lia | apply usedX_intro; [reflexivity | exact M1] | exact Hidx1 | exact Hfr1 | exact Hk1 |].
intros s2 HI2 _ (k1 & k2 & F1 & F2). msimp. apply itok_ret. apply HQ. split; [exact HI2|]. cbn [fst snd].
rewrite <- Ep, Hn1 in F1. fold old in F1.
pose proof (ublist_ptrs_NoDup s1 HI1) as NDu.
rewrite E2 in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
+ destruct (in_split _ _ Hin) as (a1 & a2 & Ea).
assert (Ek : k1 = a1 /\ k2 = a2 ++ new :: l2).
{ rewrite F1 in NDu. eapply (split_unique _ k1 k2 a1 (a2 ++ new :: l2) old NDu).
rewrite <- F1, E1, Ea, <- app_assoc. reflexivity. }
destruct Ek as [-> ->].
exists a1, (a2 ++ l2), (a1 ++ a2), l2, (g, idx), (g', idx').
split; [rewrite E2, Ea, <- app_assoc; reflexivity|]. split; [rewrite <- app_assoc; reflexivity|].
rewrite F2, <- app_assoc. reflexivity.
+ destruct (in_split _ _ Hin) as (b1 & b2 & Eb).
assert (Ek : k1 = l1 ++ new :: b1 /\ k2 = b2).
{ rewrite F1 in NDu. eapply (split_unique _ k1 k2 (l1 ++ new :: b1) b2 old NDu).
rewrite <- F1, E1, Eb, <- app_assoc. reflexivity. }
destruct Ek as [-> ->].
exists (l1 ++ b1), b2, l1, (b1 ++ b2), (g, idx), (g', idx').
split; [rewrite E2, Eb, <- app_assoc; reflexivity|]. split; [rewrite <- app_assoc; reflexivity|].
rewrite F2, <- app_assoc. reflexivity.
- cbn in Hpost. apply itok_ret. apply HQ. split; [exact HI1 | exact Hpost].
Qed.
Section e.
Variables (U : Z -> Z) (s : astate) (g : sptr) (am : ameta) (fr : frame) (n : Z).
Hypothesis HI : Inv [] None U s.
Hypothesis Hu : usedX [] s g am.
Hypothesis H63 : am_sc am = 63.
Hypothesis Hfr : ss_fr (nth_slot am 0) = Some fr.
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis Hfit : n + UNIT * fr_off fr + UNIT + IB <= am_maplen am * 4096.
Let amS := upd_slot am 0 (resize_slot (stride_of am) 0 (nth_slot am 0) (fr_off fr) n).
Let sS := upd_meta g (MUsed amS) s.
Lemma rs_shape :
am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\ am_aidx am = 0 /\
length (am_slots am) = 1%nat /\ stride_of am = am_maplen am * 4096 - UNIT.
Proof.
pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & _) & _ & _ & Gcl & _ & _).
destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & _) | (C1 & _)]; [|lia].
rewrite C2 in Glen, Gaidx. repeat split; auto; try lia.
unfold stride_of. rewrite C2. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma rs_nth j : 0 <= j -> nth_slot amS j = if j =? 0 then resize_slot (stride_of am) 0 (nth_slot am 0) (fr_off fr) n else nth_slot am j.
Proof.
intros Hj. subst amS. apply nth_slot_upd_slot; [lia | exact Hj |].
destruct rs_shape as (_ & _ & _ & _ & _ & L & _). rewrite L. lia.
Qed.
Lemma resize_Inv : Inv [] None U sS.
Proof.
pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
destruct rs_shape as (Hl & Hml & Hav & Hfd & Hai & L & Hstr).
pose proof (Gsl 0 ltac:(lia)) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (F1 & F2 & F3 & F4 & F5) & Hhdr).
assert (GS : geom_same am amS).
{ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros j frj Hj Hkj. exfalso.
destruct (am_slots am) as [|sl [|]] eqn:Esl; cbn in L; try lia.
assert (Hsl : ss_fr sl = Some fr) by (unfold nth_slot in Hfr; rewrite Esl in Hfr; exact Hfr).
unfold nth_slot in Hj. rewrite Esl in Hj.
destruct (Z.to_nat j) as [|[|k]]; cbn in Hj; try discriminate.
rewrite Hsl in Hj. injection Hj as ->. rewrite Hk in Hkj. discriminate. }
assert (Estr : stride_of amS = stride_of am) by (apply geom_same_stride; exact GS).
eapply (Inv_used_update [] None None U s g am amS HI Hu (geom_same_upto_of [] s _ _ GS)).
- subst amS. destruct am; split; reflexivity.
-   unfold masks_ok. subst amS. unfold upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
repeat (split; [assumption|]). exact Gfra.
-   intros i Hi. change (am_last amS) with (am_last am) in Hi. assert (i = 0) as -> by lia.
unfold slot_ok. rewrite rs_nth, Z.eqb_refl by lia. unfold resize_slot. cbn [ss_hdr ss_fr].
change (am_maplen amS) with (am_maplen am). rewrite Hstr.
set (reserved := am_maplen am * 4096 - UNIT - IB - UNIT * fr_off fr - n).
set (rsv := if 5 <=? reserved then 5 else reserved).
assert (Hrsv : 0 <= rsv <= 5) by (subst rsv reserved; destruct (5 <=? _) eqn:E5; [apply Z.leb_le in E5|apply Z.leb_gt in E5]; unfold UNIT, IB in *; lia).
split.
{ destruct (fr_off fr =? 0); [discriminate | exact S1]. }
split.
{ intros h3 h16 Eh. destruct (fr_off fr =? 0).
- injection Eh as <- <-. rewrite Z.mul_0_r. cbn. lia.
- exact (S2 h3 h16 Eh). }
split; [change (allocated amS 0) with (allocated am 0); exact Hal|].
split; [discriminate|]. split.
{ unfold frame_ok. cbn [fr_n fr_off fr_kind]. rewrite Estr, Hstr.
split; [unfold MMAP_THRESHOLD in Hn; lia|]. split; [exact F2|]. split; [unfold UNIT, IB in *; lia|]. split.
- unfold hdr_off16. rewrite Estr, Hstr. cbn [fr_off]. rewrite Z.mul_0_r. cbn. lia.
- intros; discriminate. }
cbn [fr_off]. intros E0. rewrite E0, Z.eqb_refl. f_equal. f_equal.
+ unfold hdr_byte3, rsv_code. cbn [fr_kind fr_off fr_n]. rewrite Estr, Hstr. subst rsv reserved. rewrite E0. lia.
+ unfold hdr_off16. cbn [fr_off]. rewrite Estr, Hstr. lia.
-   left. change (am_sc amS) with (am_sc am). change (am_last amS) with (am_last am).
change (am_maplen amS) with (am_maplen am). change (am_avail amS) with (am_avail am). change (am_freed amS) with (am_freed am).
repeat (split; [first [assumption | lia]|]). right.
exists (mkFrame (fr_off fr) n FUser). rewrite rs_nth by lia. rewrite Z.eqb_refl. unfold resize_slot. cbn. auto.
- intros p i _. tauto.
- intros i HH. discriminate.
- intros Hsc. lia.
- intros Hsc. lia.
- intros Hsc. lia.
- intros Hpa. change (am_aidx amS) with (am_aidx am) in Hpa. change (am_last amS) with (am_last am) in Hpa. lia.
Qed.
Lemma resize_ublist :
exists l1 l2, ublist s = l1 ++ [((frame_ptr am 0 fr, fr_n fr), (g, 0))] ++ l2 /\
ublist sS = l1 ++ [((frame_ptr am 0 fr, n), (g, 0))] ++ l2.
Proof.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. destruct rs_shape as (Hl & _ & _ & _ & _ & L & _).
destruct (ublist_upd_slot s g am 0 (resize_slot (stride_of am) 0 (nth_slot am 0) (fr_off fr) n) (proj1 (inv_keys HI)) Mg ltac:(lia) ltac:(rewrite L; lia))
as (l1 & l2 & E1 & E2).
exists l1, l2. split.
- rewrite E1. unfold slot_block. rewrite Hfr, Hk. reflexivity.
- unfold sS, amS. rewrite E2. unfold slotst_block, resize_slot. cbn [ss_fr fr_kind fr_off fr_n]. reflexivity.
Qed.
End e.
Theorem realloc_spec s g am idx fr n (Q : option sptr * astate -> Prop) :
WF s -> usedX [] s g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
MMAP_THRESHOLD <= n -> n < 2 ^ 62 ->
(forall r, realloc_post U0 s (frame_ptr am idx fr) (fr_n fr) n r -> Q r) ->
itok (realloc (Some (frame_ptr am idx fr)) n s) Q.
Proof.
intros HI Hu Hidx Hfr Hk Hn Hn62 HQ.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (F1 & F2 & F3 & F4 & F5) & Hhdr).
unfold realloc.
destruct (size_overflows n) eqn:Eov.
{ exfalso. unfold size_overflows in Eov. apply Z.leb_le in Eov. lia. }
mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
rewrite (find_frame_in_spec [] None U0 s HI g am idx fr Hu Hidx Hfr). apply itok_ret. msimp.
mbinds. eapply itok_getm; [exact Mg|]. msimp. rewrite Hfr. cbn zeta.
replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. cbn [andb].
destruct (48 <=? am_sc am) eqn:E48.
2:{
cbn [andb]. eapply realloc_move_spec; eauto. unfold MMAP_THRESHOLD in Hn. lia. }
apply Z.leb_le in E48. rewrite (proj2 (Z.leb_le _ _) Hn). cbn [andb].
assert (H63 : am_sc am = 63) by (destruct Gcl as [(C & _) | (C & _)]; lia).
assert (Hidx0 : idx = 0) by (destruct Gcl as [(_ & C2 & _) | (C & _)]; lia). subst idx.
destruct (rs_shape U0 s g am HI Hu H63) as (Hl & Hml & Hav & Hfd & Hai & L & Hstr).
mbinds. apply itok_massert; [apply Z.eqb_eq; exact H63|]. msimp.
set (needed := page_round (n + UNIT * fr_off fr + UNIT + IB)).
pose proof (page_round_ge (n + UNIT * fr_off fr + UNIT + IB)) as PR1. pose proof (page_round_mod (n + UNIT * fr_off fr + UNIT + IB)) as PR2.
fold needed in PR1, PR2.
assert (Hnd0 : 0 < needed) by (unfold MMAP_THRESHOLD, UNIT, IB in Hn, PR1, F2; lia).
assert (Hneeded63 : needed < 2 ^ 63).
{ subst needed. unfold page_round, PGSZ, UNIT, IB in *.
pose proof (Z.mul_div_le (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096 ltac:(lia)). lia. }
destruct (am_maplen am * 4096 =? needed) eqn:Eeq.
{
apply Z.eqb_eq in Eeq.
mbinds. apply itok_setm'. msimp. apply itok_ret. apply HQ. split.
- cbn [snd]. apply resize_Inv; auto. lia.
- cbn [fst snd]. destruct (resize_ublist U0 s g am fr n HI Hu H63 Hfr Hk) as (l1 & l2 & E1 & E2).
exists l1, l2, l1, l2, (g, 0), (g, 0). split; [exact E1|]. split; [reflexivity | exact E2]. }
apply Z.eqb_neq in Eeq.
destruct (Gmp ltac:(lia)) as (r & rg & Hmem & Hr & Hkd & Hlv & Hlen & _).
assert (Er : prid (am_mem am) = r) by (rewrite Hmem; reflexivity).
mbinds. apply itok_ask.
{ cbn [req_ok]. rewrite Er. split.
- exists rg. rewrite Hlen. unfold PGSZ. repeat split; auto.
- unfold PGSZ, MMAP_THRESHOLD, UNIT, IB in *. repeat split; try lia; try exact PR2. apply Z_mod_mult. }
intros z _. msimp. destruct (z =? 0); cbn [negb].
{   eapply realloc_move_spec; eauto. unfold MMAP_THRESHOLD in Hn. lia. }
mbinds. eapply new_region_spec; [exact HI | | reflexivity | lia]. intros s1 HI1 Es1. msimp. subst s1.
mbinds. apply itok_setm'. msimp.
pose proof (remap_Inv U0 s g am fr n needed HI Hu H63 Hfr Hk Hn PR1 PR2) as HI2.
mbinds. rewrite Er.
eapply upd_region_kill_spec; [exact HI2 | | exact Hkd | |].
{ unfold region_of, upd_meta. cbn [st_regions set_metas set_regions]. unfold region_of in Hr.
rewrite nth_error_app1; [exact Hr | eapply nth_error_Some_length; exact Hr] || (apply region_of_app; exact Hr). }
{ intros q a Hq Hm. rewrite <- Er. exact (remap_old_unref U0 s g am fr n needed HI Hu H63 q a Hq Hm). }
intros s3 HI3 Em3 _. msimp. apply itok_ret. apply HQ. split; [exact HI3|]. cbn [fst snd].
destruct (remap_ublist U0 s g am fr n needed HI Hu H63 Hfr Hk) as (l1 & l2 & E1 & E2).
exists l1, l2, l1, l2, (g, 0), (g, 0). split; [exact E1|]. split; [reflexivity|].
rewrite (ub_same_ublist _ _ (ub_same_metas _ _ Em3)). exact E2.
Qed.
Theorem realloc_safe : forall s p nold n,
WF s -> In (p, nold) (user_blocks s) -> MMAP_THRESHOLD <= n -> n < 2 ^ 62 -> safe (realloc (Some p) n s).
Proof.
intros s p nold n HW Hin Hn Hn62. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
eapply itok_safe. apply (realloc_spec s g am idx fr n (fun _ => True) HW Hu Hi Hfr Hk Hn Hn62). intros; exact I.
Qed.

Theorem realloc_wf : forall s p nold n tr q s',
WF s -> In (p, nold) (user_blocks s) -> MMAP_THRESHOLD <= n -> n < 2 ^ 62 ->
yields (realloc (Some p) n s) tr (q, s') -> WF s'.
Proof.
intros s p nold n tr q s' HW Hin Hn Hn62 Hy. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
exact (proj1 (itok_yields _ _ tr (q, s') (realloc_spec s g am idx fr n _ HW Hu Hi Hfr Hk Hn Hn62 (fun r H => H)) Hy)).
Qed.
Theorem realloc_blocks : forall s p nold n tr q s',
WF s -> In (p, nold) (user_blocks s) -> MMAP_THRESHOLD <= n -> n < 2 ^ 62 ->
yields (realloc (Some p) n s) tr (q, s') ->
match q with
| None => user_blocks s' = user_blocks s
| Some q => exists l1 l2 m1 m2, user_blocks s = l1 ++ (p, nold) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks s' = m1 ++ (q, n) :: m2 /\
poff q mod UNIT = 0 /\ ~ In q (map fst (m1 ++ m2))
end.
Proof.
intros s p nold n tr q s' HW Hin Hn Hn62 Hy. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & ->).
pose proof (itok_yields _ _ tr (q, s') (realloc_spec s g am idx fr n _ HW Hu Hi Hfr Hk Hn Hn62 (fun r H => H)) Hy) as [HW' Hp]. cbn [fst snd] in HW', Hp.
destruct q as [q|].
- destruct Hp as (l1 & l2 & m1 & m2 & key & key' & E1 & E12 & E2). rewrite En in E1.
rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))).
exists (map fst l1), (map fst l2), (map fst m1), (map fst m2). rewrite E1, E2, !map_app. cbn [map fst].
split; [reflexivity|]. split; [rewrite <- !map_app, E12; reflexivity|]. split; [reflexivity|]. split.
+
assert (Hin' : In (q, n) (user_blocks s')).
{ rewrite (user_blocks_ublist s' (proj1 (inv_keys HW'))), E2, map_app. cbn [map fst]. apply in_app_iff. right. left. reflexivity. }
destruct (user_blocks_frame s' q n HW' Hin') as (g' & am' & idx' & fr' & Hu' & Hi' & _ & _ & _ & ->).
pose proof (used_group_aligned [] None U0 s' HW' _ g' am' Hu' (Nat.le_refl _)) as Hal.
pose proof (stride_mod16 _ _ _ _ _ _ HW' Hu') as Hst.
apply Z.div_exact in Hal; [|lia]. apply Z.div_exact in Hst; [|lia].
unfold frame_ptr. rewrite poff_padd, poff_slot_start. unfold UNIT.
replace (poff (am_mem am') + 16 + stride_of am' * idx' + 16 * fr_off fr') with ((poff (am_mem am') / 16 + 1 + stride_of am' / 16 * idx' + fr_off fr') * 16) by lia.
apply Z_mod_mult.
+ pose proof (user_block_ptrs_NoDup s' HW') as ND. rewrite (user_blocks_ublist s' (proj1 (inv_keys HW'))), E2, !map_app in ND. cbn [map fst] in ND.
apply NoDup_remove_2 in ND. rewrite <- !map_app in ND. rewrite <- !map_app. exact ND.
- rewrite (user_blocks_ublist s (proj1 (inv_keys HW))), (user_blocks_ublist s' (proj1 (inv_keys HW'))). f_equal. apply ub_same_ublist. exact Hp.
Qed.
