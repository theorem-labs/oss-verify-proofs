(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s
YO11 YO15 YO12 YO0z YO14 YO0u YO0q
YO0v YO0y YO0t YO10 YO13 YO16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
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
