(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0i YP0q YP0m
YP0w YP10 YP0x YP0t YP0z YP0o YP0k
YP0p YP0s YP0n YP0v YP0y YP11.
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







