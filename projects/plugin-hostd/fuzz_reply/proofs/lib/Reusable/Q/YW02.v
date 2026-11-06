(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO0t YO10 YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocRealloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
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
Lemma rm_amR :
amR = mkAMeta None None (SP r' 0) 0 0 0 63 ml' 0
[resize_slot (ml' * 4096 - UNIT) 0 (nth_slot am 0) (fr_off fr) n].
Proof.
destruct rm_shape as (Hl & _ & Hav & Hfd & Hai & Hp & Hnx & _). destruct rm_slots as (sl & Esl & Ens).
subst amR. unfold remap_am. rewrite Hp, Hnx, Hav, Hfd, Hl, H63, Hai, Esl, Ens. reflexivity.
Qed.
End d.
Lemma remap_ublist s g am fr n : RMH s g am fr n ->
exists l1 l2, ublist s = l1 ++ [((frame_ptr am 0 fr, fr_n fr), (g, 0))] ++ l2 /\
ublist (rm_state s g am 0 (fr_off fr) n) =
l1 ++ [((padd (slot_start (rm_am s am 0 (fr_off fr) n) 0) (UNIT * fr_off fr), n), (g, 0))] ++ l2.
Proof.
intros H. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
destruct (rm_basic s g am fr n H) as (Hl & _ & _ & _ & _ & _ & _ & Hsl & _).
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
destruct (ublist_split s g (proj1 (inv_keys HW)) (MT_Some_In_keys _ _ _ Mg)) as (L1 & L2 & Hup & Hs).
assert (EU : ublist (rm_state s g am 0 (fr_off fr) n) = ublist (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s))
by reflexivity.
exists L1, L2. rewrite EU, Hup, Hs, Mg. cbn [ucontrib].
rewrite (blocks_last0 g am Hl), (blocks_last0 g (rm_am s am 0 (fr_off fr) n) Hl).
unfold slot_block. rewrite Hfr, Hk, (rm_slot0 s am (fr_off fr) n Hsl). cbn [resize_slot ss_fr fr_kind fr_off fr_n].
split; reflexivity.
Qed.
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
Lemma resize_ublist s g am idx fr n :
WF s -> usedX [] s g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
exists l1 l2, ublist s = l1 ++ [((frame_ptr am idx fr, fr_n fr), (g, idx))] ++ l2 /\
ublist (upd_meta g (MUsed (rs_am am idx (fr_off fr) n)) s) = l1 ++ [((frame_ptr am idx fr, n), (g, idx))] ++ l2.
Proof.
intros HW Hu Hidx Hfr Hk.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (inv_groups HW g am Hu) as ((_ & _ & Glen & _) & _).
destruct (ublist_upd_slot s g am idx (resize_slot (stride_of am) idx (nth_slot am idx) (fr_off fr) n) (proj1 (inv_keys HW)) Mg Hidx Glen)
as (l1 & l2 & E1 & E2).
exists l1, l2. split.
- rewrite E1. unfold slot_block. rewrite Hfr, Hk. reflexivity.
- unfold rs_am. rewrite E2. unfold slotst_block, resize_slot. cbn [ss_fr fr_kind fr_off fr_n]. reflexivity.
Qed.
Theorem realloc_spec s g am idx fr n (Q : option sptr * astate -> Prop) :
WF s -> usedX [] s g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
0 <= n < 2 ^ 62 ->
(forall r, realloc_post U0 s (frame_ptr am idx fr) (fr_n fr) n r -> Q r) ->
itok (realloc (Some (frame_ptr am idx fr)) n s) Q.
Proof.
intros HI Hu Hidx Hfr Hk [Hn0 Hn62] HQ.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
pose proof (inv_groups HI g am Hu) as G. pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (F1 & F2 & F3 & F4 & F5) & Hhdr).
assert (INPL : IPH s g am idx fr n ->
realloc_post U0 s (frame_ptr am idx fr) (fr_n fr) n (Some (frame_ptr am idx fr), upd_meta g (MUsed (rs_am am idx (fr_off fr) n)) s)).
{ intros Hip. split; [exact (ip_wf s g am idx fr n Hip)|]. cbn [fst snd].
destruct (resize_ublist s g am idx fr n HI Hu Hidx Hfr Hk) as (l1 & l2 & E1 & E2).
exists l1, l2, l1, l2, (g, idx), (g, idx). split; [exact E1|]. split; [reflexivity | exact E2]. }
unfold realloc.
destruct (size_overflows n) eqn:Eov.
{ exfalso. unfold size_overflows in Eov. apply Z.leb_le in Eov. lia. }
mbinds. unfold find_frame. mbinds. apply itok_get. msimp.
rewrite (find_frame_in_spec [] None U0 s HI g am idx fr Hu Hidx Hfr). apply itok_ret. msimp.
mbinds. eapply itok_getm; [exact Mg|]. msimp. rewrite Hfr. cbn zeta.
destruct ((n <=? stride_of am - IB - UNIT * fr_off fr) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1)) eqn:Ein.
{ msimp. mbinds. apply itok_setm'. msimp. apply itok_ret. apply HQ. apply INPL.
exact (ip_of_c1 s g am idx fr n HI Hu Hidx Hfr Hk Hn0 Ein). }
destruct ((48 <=? am_sc am) && (MMAP_THRESHOLD <=? n)) eqn:Ebig.
2:{ msimp. eapply realloc_move_spec; eauto. }
msimp. apply andb_prop in Ebig as [E48 Hn]. apply Z.leb_le in E48. apply Z.leb_le in Hn.
assert (H63 : am_sc am = 63) by (destruct Gcl as [(C & _) | (C & _)]; lia).
assert (Hidx0 : idx = 0) by (destruct Gcl as [(_ & C2 & _) | (C & _)]; lia). subst idx.
assert (Hml : 1 <= am_maplen am) by (destruct Gcl as [(_ & _ & C3 & _) | (C & _)]; lia).
mbinds. apply itok_massert; [apply Z.eqb_eq; exact H63|]. msimp.
set (needed := page_round (n + UNIT * fr_off fr + UNIT + IB)).
pose proof (page_round_ge (n + UNIT * fr_off fr + UNIT + IB)) as PR1. pose proof (page_round_mod (n + UNIT * fr_off fr + UNIT + IB)) as PR2.
fold needed in PR1, PR2.
assert (Hnd0 : 0 < needed) by (unfold MMAP_THRESHOLD, UNIT, IB in Hn, PR1, F2; lia).
assert (Hneeded63 : needed < 2 ^ 63).
{ subst needed. unfold page_round, PGSZ, UNIT, IB in *.
pose proof (Z.mul_div_le (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096 ltac:(lia)). lia. }
destruct (am_maplen am * 4096 =? needed) eqn:Eeq.
{ apply Z.eqb_eq in Eeq. mbinds. apply itok_setm'. msimp. apply itok_ret. apply HQ. apply INPL.
exact (ip_of_same s g am 0 fr n HI Hu Hidx Hfr Hk H63 Hn Eeq). }
apply Z.eqb_neq in Eeq.
destruct (Gmp ltac:(lia)) as (r & rg & Hmem & Hr & Hkd & Hlv & Hlen & _).
assert (Er : prid (am_mem am) = r) by (rewrite Hmem; reflexivity).
mbinds. apply itok_ask.
{ cbn [req_ok]. rewrite Er. split.
- exists rg. rewrite Hlen. unfold PGSZ. repeat split; auto.
- unfold PGSZ, MMAP_THRESHOLD, UNIT, IB in *. repeat split; try lia; try exact PR2; apply Z_mod_mult. }
intros z _. msimp. destruct (z =? 0); cbn [negb].
{ eapply realloc_move_spec; eauto. }
destruct (rm_of s g am 0 fr n HI Hu Hidx Hfr Hk H63 Hn) as [_ R].
assert (POST : realloc_post U0 s (frame_ptr am 0 fr) (fr_n fr) n
(Some (padd (slot_start (rm_am s am 0 (fr_off fr) n) 0) (UNIT * fr_off fr)), rm_state s g am 0 (fr_off fr) n)).
{ split; [exact (rm_wf s g am fr n R)|]. cbn [fst snd].
destruct (remap_ublist s g am fr n R) as (l1 & l2 & E1 & E2).
exists l1, l2, l1, l2, (g, 0), (g, 0). split; [exact E1|]. split; [reflexivity | exact E2]. }
cbn [bind ibind fst snd new_region setm upd_region modify get put ret itok]. exact (HQ _ POST).
Qed.
Theorem realloc_safe : forall s p nold n,
WF s -> In (p, nold) (user_blocks s) -> 0 <= n < 2 ^ 62 -> safe (realloc (Some p) n s).
Proof.
intros s p nold n HW Hin Hn. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
eapply itok_safe. apply (realloc_spec s g am idx fr n (fun _ => True) HW Hu Hi Hfr Hk Hn). intros; exact I.
Qed.
Theorem realloc_wf : forall s p nold n tr q s',
WF s -> In (p, nold) (user_blocks s) -> 0 <= n < 2 ^ 62 ->
yields (realloc (Some p) n s) tr (q, s') -> WF s'.
Proof.
intros s p nold n tr q s' HW Hin Hn Hy. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
exact (proj1 (itok_yields _ _ tr (q, s') (realloc_spec s g am idx fr n _ HW Hu Hi Hfr Hk Hn (fun r H => H)) Hy)).
Qed.
Theorem realloc_safe_p_ok : forall A p k n, WF A -> In (p, k) (user_blocks A) -> 0 <= n < 2 ^ 62 -> safe (realloc (Some p) n A).
Proof. exact realloc_safe. Qed.
Theorem realloc_blocks : forall s p nold n tr q s',
WF s -> In (p, nold) (user_blocks s) -> 0 <= n < 2 ^ 62 ->
yields (realloc (Some p) n s) tr (q, s') ->
match q with
| None => user_blocks s' = user_blocks s
| Some q => exists l1 l2 m1 m2, user_blocks s = l1 ++ (p, nold) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks s' = m1 ++ (q, n) :: m2 /\
poff q mod UNIT = 0 /\ ~ In q (map fst (m1 ++ m2))
end.
Proof.
intros s p nold n tr q s' HW Hin Hn Hy. destruct (user_blocks_frame s p nold HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & ->).
pose proof (itok_yields _ _ tr (q, s') (realloc_spec s g am idx fr n _ HW Hu Hi Hfr Hk Hn (fun r H => H)) Hy) as [HW' Hp]. cbn [fst snd] in HW', Hp.
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
Theorem realloc_null_spec U s n (Q : option sptr * astate -> Prop) :
Inv [] None U s -> 0 <= n -> (forall r, malloc_post [] U s n r -> Q r) -> itok (realloc None n s) Q.
Proof. exact (malloc_spec U s n Q). Qed.
Theorem realloc_null_safe : forall s n, WF s -> 0 <= n -> safe (realloc None n s).
Proof. exact malloc_safe. Qed.
Theorem realloc_null_wf : forall s n tr p s', WF s -> 0 <= n -> yields (realloc None n s) tr (p, s') -> WF s'.
Proof. exact malloc_wf. Qed.
Theorem realloc_null_blocks : forall s n tr p s',
WF s -> 0 <= n -> yields (realloc None n s) tr (p, s') ->
match p with
| None => user_blocks s' = user_blocks s
| Some q => exists l1 l2, user_blocks s' = l1 ++ (q, n) :: l2 /\ user_blocks s = l1 ++ l2
/\ poff q mod UNIT = 0 /\ ~ In q (map fst (user_blocks s))
end.
Proof. exact malloc_blocks. Qed.
