(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1c.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN30.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN17.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN18.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section n.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis XC : Xclean X s.
Hypothesis HL : layout_ok L s.
Lemma group_cell_homeX g am c :
usedX X s g am -> In c (group_cells g am) ->
exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
range_incl (cell_range L c) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
Proof.
intros Hu Hc. destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
destruct (In_group_cells_span X R U s g am c HI Hu Hc) as (d & E & Hd & Hw).
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in Hext. lia.
Qed.
Lemma groups_cells_disjointX g1 a1 g2 a2 x y :
usedX X s g1 a1 -> usedX X s g2 a2 -> g1 <> g2 ->
In x (group_cells g1 a1) -> In y (group_cells g2 a2) -> ranges_disjoint (cell_range L x) (cell_range L y).
Proof.
intros U1 U2 Hne Hx Hy.
destruct (group_cell_homeX g1 a1 x U1 Hx) as (rg1 & R1 & K1 & L1 & In1 & I1).
destruct (group_cell_homeX g2 a2 y U2 Hy) as (rg2 & R2 & K2 & L2 & In2 & I2).
destruct (Nat.eq_dec (prid (am_mem a1)) (prid (am_mem a2))) as [Hsame | Hdiff].
2:{ eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
intros E. injection E. intros _ Ep. exact (Hdiff Ep). }
destruct (In_group_cells_span X R U s g1 a1 x HI U1 Hx) as (d1 & E1 & Hd1 & Hw1).
destruct (In_group_cells_span X R U s g2 a2 y HI U2 Hy) as (d2 & E2 & Hd2 & Hw2).
assert (GOAL : forall u v du dv au av, mc_loc u = LMem (padd (am_mem au) du) -> mc_loc v = LMem (padd (am_mem av) dv) ->
prid (am_mem au) = prid (am_mem av) ->
(poff (am_mem au) + du + Z.of_nat (mc_w u) <= poff (am_mem av) + dv \/ poff (am_mem av) + dv + Z.of_nat (mc_w v) <= poff (am_mem au) + du) ->
ranges_disjoint (cell_range L u) (cell_range L v)).
{ intros u v du dv au av Eu Ev Hp D. unfold cell_range, ranges_disjoint; cbn [mc_loc mc_w fst snd]. rewrite Eu, Ev.
rewrite ?loc_addr_LMem, ?prid_padd, ?poff_padd, ?prid_padd, ?poff_padd. rewrite Hp. lia. }
assert (INS : forall ga a gb b u v du, usedX X s ga a -> usedX X s gb b -> inside X s a b ->
In v (group_cells gb b) -> mc_loc u = LMem (padd (am_mem a) du) -> 0 <= du -> du + Z.of_nat (mc_w u) <= group_extent a ->
prid (am_mem a) = prid (am_mem b) ->
ranges_disjoint (cell_range L u) (cell_range L v)).
{ intros ga a gb b u v du Ua Ub I Hv Eu Hdu Hwu Hp.
destruct I as (j & fr & c & ac & Hj & Hfr & Hk & Uc & Mlc & Memc & Lo & Hi & Fit).
pose proof (inv_groups HI gb b Ub) as (_ & _ & Gslb & _). pose proof (Gslb j Hj) as (_ & _ & S3). rewrite Hfr in S3.
destruct S3 as (_ & _ & (Nf & Of & Bf & _ & FG) & _). destruct (FG Hk) as [Off _].
rewrite Memc, poff_slot_start in Lo, Hi.
destruct (group_cells_vs_body X R U s gb b j (poff (am_mem a) + du) (poff (am_mem a) + du + Z.of_nat (mc_w u)) v HI Ub Hj Hv
ltac:(rewrite Hfr, Off, poff_slot_start; unfold UNIT in *; lia)
ltac:(rewrite poff_slot_start; unfold UNIT, IB in *; lia)) as (dv & Ev & D).
eapply (GOAL u v du dv a b Eu Ev Hp). lia. }
destruct (inv_laminar HI g1 a1 g2 a2 U1 U2 Hne Hsame) as [Dj | [I | I]].
- eapply (GOAL x y d1 d2 a1 a2 E1 E2 Hsame). unfold spans_disjoint in Dj. lia.
- eapply (INS g1 a1 g2 a2 x y d1); eauto.
- apply ranges_disjoint_sym. eapply (INS g2 a2 g1 a1 y x d2); eauto.
Qed.
Lemma areas_cells_pairwiseX l :
NoDup l -> (forall a, In a l -> In a (st_areas s)) ->
pairwise ranges_disjoint (map (cell_range L) (areas_cells s l)).
Proof.
induction l as [|a t IH]; intros ND Hsub; cbn [areas_cells]; [exact I|].
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
Theorem image_cells_disjointX : pairwise ranges_disjoint (map (cell_range L) (image s)).
Proof.
pose proof (inv_areas HI) as (AND & A2 & _).
assert (HOMEa : forall c, In c (areas_cells s (st_areas s)) -> exists a, In a (st_areas s) /\ In (LMem a, PGSZ) (footprint s) /\
range_incl (cell_range L c) (crange L (LMem a, PGSZ)) /\ poff a <> 0).
{ intros c Hc. destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc').
destruct (area_cell_home L s a next c Ha Hc') as [In1 I1]. exists a. split; [exact Ha|]. split; [exact In1|]. split; [exact I1|].
destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _). rewrite Ea. cbn. unfold PGSZ in Hoa. lia. }
assert (HOMEg : forall c, In c (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s)) ->
exists k len, In (LMem (SP k 0), len) (footprint s) /\ range_incl (cell_range L c) (crange L (LMem (SP k 0), len))).
{ intros c Hc. apply in_flat_map in Hc as [[g am] [Hg Hc]]. cbn [fst snd] in Hc. apply (used_metas_usedX' X R U s HI XC g am) in Hg.
destruct (group_cell_homeX g am c Hg Hc) as (rg & _ & _ & _ & In1 & I1). eexists _, _. split; [exact In1 | exact I1]. }
unfold image. rewrite !map_app. apply pairwise_app; [apply ctx_cells_disjoint | apply pairwise_app |].
- apply areas_cells_pairwiseX; [exact AND | intros a Ha; exact Ha].
- apply (proj1 (pairwise_map_iff ranges_disjoint (cell_range L) _)). apply pairwise_flat_map.
+ intros [g am] Hg. cbn [fst snd]. apply (used_metas_usedX' X R U s HI XC g am) in Hg.
apply (pairwise_map_iff ranges_disjoint (cell_range L)). eapply group_cells_disjoint; [exact HI | exact Hg].
+ intros l1 [g1 a1] l2 [g2 a2] E Hin x y Hx Hy. cbn [fst snd] in Hx, Hy.
pose proof (used_metas_split s l1 g1 a1 l2 g2 a2 (proj1 (inv_keys HI)) E Hin) as Hne.
assert (U1 : usedX X s g1 a1) by (apply (used_metas_usedX' X R U s HI XC g1 a1); rewrite E; apply in_app_iff; right; left; reflexivity).
assert (U2 : usedX X s g2 a2) by (apply (used_metas_usedX' X R U s HI XC g2 a2); rewrite E; apply in_app_iff; right; right; exact Hin).
exact (groups_cells_disjointX g1 a1 g2 a2 x y U1 U2 Hne Hx Hy).
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
Lemma block_in_slotX g am i fr :
usedX X s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
poff (slot_start am i) <= poff (frame_ptr am i fr) /\
poff (frame_ptr am i fr) + fr_n fr <= poff (slot_start am i) + stride_of am - IB /\ 0 <= fr_n fr.
Proof.
intros Hu Hi Hfr. pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _).
pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & B & _) & _).
unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
Qed.
Theorem tail_cells_outside_user_blocksX : forall c b,
In c (tail_cells s) -> In b (user_blocks s) -> ranges_disjoint (cell_range L c) (block_range L b).
Proof.
intros c b Hc Hb. pose proof HL as (_ & _ & PW & _).
destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
apply (used_metas_usedX' X R U s HI XC g am) in Hg.
pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
destruct (used_group_region X R U s g am HI Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
assert (BI : range_incl (block_range L (frame_ptr am i fr, fr_n fr)) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
{ pose proof (block_in_slotX g am i fr Hg Hi Hfr) as (A1 & A2 & A3).
pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
unfold frame_ptr, slot_start in *. destruct (am_mem am) as [r o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia. }
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g' am'] & Hg' & Hcc). cbn [snd] in Hcc.
apply (used_metas_usedX' X R U s HI XC g' am') in Hg'.
destruct (tail_cell_home X R U s HI g' am' c Hg' Hcc) as (rg' & d & Hr' & Hkd' & Hl' & E & Hd & Ho' & Hfit & Hw).
destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (footprint_region_In s _ _ Hr' Hkd' Hl') InR
ltac:(intros E2; injection E2; intros _ Ep; exact (Hdiff Ep))) as [D|D].
- eapply ranges_disjoint_incl; [exact D | | exact BI].
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o] eqn:Em. rewrite ?Em in *. cbn [fst snd padd prid poff] in *. unfold UNIT in *. lia.
- apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact BI |].
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o] eqn:Em. rewrite ?Em in *. cbn [fst snd padd prid poff] in *. unfold UNIT in *. lia. }
assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
(poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (frame_ptr am i fr) \/
poff (frame_ptr am i fr) + fr_n fr <= poff (am_mem am') + d) ->
ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
{ intros d0 E0 D. unfold cell_range, block_range, ranges_disjoint, loc_addr. rewrite E0. cbn [fst snd].
unfold frame_ptr, slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
pose proof (block_in_slotX g am i fr Hg Hi Hfr) as (A1 & A2 & A3).
destruct (sptr_eq_dec g' g) as [->|Hne].
- pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
destruct (tail_cells_vs_body X R U s HI g am i (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c Hg Hi Hcc)
as (d1 & E1 & D1); [lia | lia | | exact (GOAL d1 E1 D1)].
intros f Hf _. rewrite Hfr in Hf. injection Hf as <-. lia.
- pose proof (extent_pos _ _ _ _ _ (inv_groups HI g' am' Hg')) as Pa'.
destruct (inv_laminar HI g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
+ apply (GOAL d E). pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
unfold spans_disjoint in Dj. unfold frame_ptr in *. rewrite poff_padd in *. unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
+ apply (GOAL d E).
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
+ destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
pose proof (inv_groups HI g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
destruct (tail_cells_vs_body X R U s HI g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c Hg' Hj' Hcc) as (d1 & E1 & D1).
* rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
* rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
* intros f Hf Hkf. rewrite Hfr' in Hf. injection Hf as <-. rewrite Hk' in Hkf. discriminate.
* exact (GOAL d1 E1 D1).
Qed.
Theorem image_outside_user_blocksX : forall c b,
In c (image s) -> In b (user_blocks s) -> ranges_disjoint (cell_range L c) (block_range L b).
Proof.
intros c b Hc Hb. pose proof HL as (_ & _ & PW & _).
destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
apply (used_metas_usedX' X R U s HI XC g am) in Hg.
pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
destruct (used_group_region X R U s g am HI Hg) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
pose proof (footprint_region_In s _ _ Hr Hkd Hl) as InR.
assert (BI : range_incl (block_range L (frame_ptr am i fr, fr_n fr)) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
{ pose proof (block_in_slotX g am i fr Hg Hi Hfr) as (A1 & A2 & A3).
pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
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
pose proof (inv_areas HI) as (_ & A2 & _). destruct (A2 a Ha) as (ra & oa & rga & Ea & _ & Hoa & _).
apply (VIA (LMem a, PGSZ)).
+ right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
+ rewrite Ea. intros E2. injection E2 as _ Eo _. unfold PGSZ in Hoa. lia.
+ unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct a as [r o]. cbn [fst snd padd]. lia.
- apply (used_metas_usedX' X R U s HI XC g' am') in Hg'.
destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (used_group_region X R U s g' am' HI Hg') as (rg' & Hr' & Hkd' & Hl' & Ho2 & Hext' & _).
destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw).
apply (VIA (LMem (SP (prid (am_mem am')) 0), rg_len rg')); [apply footprint_region_In; assumption | intros E2; injection E2; intros _ Ep; exact (Hdiff Ep) |].
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am') as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in *. lia. }
assert (GOAL : forall d, mc_loc c = LMem (padd (am_mem am') d) ->
(poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (frame_ptr am i fr) \/
poff (frame_ptr am i fr) + fr_n fr <= poff (am_mem am') + d) ->
ranges_disjoint (cell_range L c) (block_range L (frame_ptr am i fr, fr_n fr))).
{ intros d E D. unfold cell_range, block_range, ranges_disjoint, loc_addr. rewrite E. cbn [fst snd].
unfold frame_ptr, slot_start in *. destruct (am_mem am') as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
pose proof (block_in_slotX g am i fr Hg Hi Hfr) as (A1 & A2 & A3).
destruct (sptr_eq_dec g' g) as [->|Hne].
+ pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
destruct (group_cells_vs_body X R U s g am i (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HI Hg Hi Hcc
ltac:(rewrite Hfr; unfold frame_ptr; rewrite poff_padd; lia) A2) as (d & E & D).
exact (GOAL d E D).
+ pose proof (extent_pos _ _ _ _ _ (inv_groups HI g' am' Hg')) as Pa'.
destruct (inv_laminar HI g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
* destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
unfold spans_disjoint in Dj. unfold frame_ptr in *. rewrite poff_padd in *. unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
* destruct (In_group_cells_span X R U s g' am' c HI Hg' Hcc) as (d & E & Hd & Hw). apply (GOAL d E).
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
* destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
pose proof (inv_groups HI g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
pose proof (slot_in_span X R U s HI g am i Hg Hi) as [S1 S1'].
destruct (group_cells_vs_body X R U s g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c HI Hg' Hj' Hcc) as (d & E & D).
-- rewrite Hfr', Off'. rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
-- rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
-- exact (GOAL d E D).
Qed.
Theorem tail_geom_of_Inv : tail_geom L s.
Proof.
unfold tail_geom. apply Forall_forall. intros c Hc k Hk. split.
- destruct (tail_cell_region X R U s HI XC c Hc) as (p & rg & Hloc & Hr & Hkd & Hl & Hpo & Hpw).
exists (LMem (SP (prid p) 0), rg_len rg). split; [apply footprint_region_In; assumption|]. cbn [fst snd loc_addr]. rewrite Hloc. destruct p as [r o]. cbn [loc_addr prid poff] in *. lia.
- intros (b & Hb & Hx). pose proof (tail_cells_outside_user_blocksX c b Hc Hb) as D.
unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. lia.
Qed.
End n.
Section NS.
Variables (X : list sptr) (U : Z -> Z) (sq : astate) (m hg : sptr) (am : ameta) (idx sc K j : Z).
Hypothesis HIq : Inv (m :: X) (Some (hg, idx)) U sq.
Hypothesis NXm : memb m X = false.
Hypothesis Uhg : usedX (m :: X) sq hg am.
Hypothesis Hscj : am_sc am = j.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HK : 1 <= K <= 32.
Hypothesis H26 : sc <= 26 -> 2 <= K.
Hypothesis ARM : class_size sc * K + UNIT <= PGSZ / 2.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis Hhd : active_hd sq j = Some hg.
Hypothesis HhdN : active_hd sq sc = None.
Definition totalN : Z := UNIT + K * class_size sc - IB.
Hypothesis Ej : size_to_class totalN = j.
Definition pN : sptr := slot_start am idx.
Definition amE : ameta := am_enf am idx j.
Definition sE : astate := upd_meta hg (MUsed amE) sq.
Definition amN0 : ameta := am_nest0 pN sc K.
Definition amN : ameta := am_nest m pN sc K.
Definition sN : astate := nest_st sc m K hg am idx j sq.
Let Mhg : MT sq hg = Some (MUsed am) := proj1 (usedX_MT _ _ _ _ Uhg).
Lemma factsN : sc <= 23 /\ 2 <= K /\ 0 <= totalN <= 2044 /\ sc < j <= 24 /\ 0 <= j < 48 /\ totalN + IB <= class_size j /\ class_size sc < class_size j.
Proof.
pose proof (nested_facts sc K Hsc ltac:(lia) H26 ARM) as NF. cbv zeta in NF.
replace (UNIT + K * class_size sc - IB) with totalN in NF by reflexivity. rewrite Ej in NF. exact NF.
Qed.
Lemma G_facts :
0 <= am_last am <= 31 /\ length (am_slots am) = Z.to_nat (am_last am + 1) /\ stride_of am = class_size j /\
ss_fr (nth_slot am idx) = None /\ allocated am idx = true /\ 0 <= am_maplen am /\
stride_of am * (am_last am + 1) < 2 ^ 20 /\ 0 <= st_mmap_counter sq < 2 ^ 32 /\
(forall h3 h16, ss_hdr (nth_slot am idx) = Some (h3, h16) -> 0 <= h3 <= 255 /\ 0 <= h16 <= 65535) /\
16 <= stride_of am /\ In hg (keys sq) /\ memb hg (m :: X) = false.
Proof.
pose proof factsN as (H23 & HK2 & Htot & Hjr & Hj48 & Hfit & Hlt).
pose proof (inv_groups HIq hg am Uhg) as GG. pose proof (stride_pos _ _ _ _ _ GG) as Sp.
pose proof GG as ((Glast & _ & Glen & _) & Gml & Gsl & Gcl & _).
destruct (inv_reserved HIq hg idx eq_refl) as (am_ & Hu_ & _ & Hfr_ & Hal_). pose proof (usedX_fun _ _ _ _ _ Hu_ Uhg) as ->.
pose proof (Gsl idx Hidx) as (_ & S2 & _).
pose proof (inv_ctx HIq) as (_&_&_&_&_&_&_&_&Rctr&_).
assert (Hstr : stride_of am = class_size j).
{ destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
unfold stride_of. rewrite Hscj. destruct C26 as [C|C]; [rewrite C|].
- destruct (am_last am =? 0); reflexivity.
- destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
split; [exact Glast|]. split; [exact Glen|]. split; [exact Hstr|]. split; [exact Hfr_|]. split; [exact Hal_|]. split; [exact Gml|].
split; [destruct Gcl as [(C & _)|(_ & _ & _ & C)]; [lia | exact C]|]. split; [exact Rctr|]. split; [exact S2|]. split; [exact Sp|].
split; [exact (MT_Some_In_keys sq hg _ Mhg) | exact (proj2 (usedX_MT _ _ _ _ Uhg))].
Qed.
Lemma amE_eq : amE = upd_slot am idx (mkSlot (Some (idx + 192, stride_of am * idx / UNIT)) (Some (mkFrame 0 (stride_of am - IB) FGroup))).
Proof. unfold amE, am_enf. rewrite (proj1 (proj2 (proj2 G_facts))). reflexivity. Qed.
Lemma amE_fields : am_mem amE = am_mem am /\ am_last amE = am_last am /\ am_sc amE = am_sc am /\ am_maplen amE = am_maplen am /\
stride_of amE = stride_of am /\ group_extent amE = group_extent am /\ am_slots amE = lupd (am_slots am) (Z.to_nat idx) (mkSlot (Some (idx + 192, class_size j * idx / UNIT)) (Some (mkFrame 0 (class_size j - IB) FGroup))) /\
am_aidx amE = am_aidx am /\ am_avail amE = am_avail am /\ am_freed amE = am_freed am /\ am_prev amE = am_prev am /\ am_next amE = am_next am.
Proof.
pose proof (upd_slot_fields am idx (mkSlot (Some (idx + 192, class_size j * idx / UNIT)) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
unfold amE, am_enf. repeat (split; [first [assumption | destruct am; reflexivity]|]). destruct am; reflexivity.
Qed.
Lemma slotE : nth_slot amE idx = mkSlot (Some (idx + 192, class_size j * idx / UNIT)) (Some (mkFrame 0 (class_size j - IB) FGroup)).
Proof.
pose proof G_facts as (Glast & Glen & _). unfold amE, am_enf. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma slotE_other : forall i, 0 <= i -> i <> idx -> nth_slot amE i = nth_slot am i.
Proof.
intros i Hi Hne. pose proof G_facts as (Glast & Glen & _). unfold amE, am_enf. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia).
replace (i =? idx) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
Qed.
Lemma SE_shape : shape_eq am amE idx.
Proof. pose proof G_facts as (Glast & Glen & _). rewrite amE_eq. apply shape_eq_upd_slot; [lia | rewrite Glen; lia]. Qed.
Lemma enframe_run : enframe hg idx (class_size j - IB) (st_mmap_counter sq) FGroup sq = IRet (pN, sE).
Proof.
pose proof G_facts as (Glast & Glen & Hstr & _).
pose proof (enframe_eval0 sq hg am idx (st_mmap_counter sq) Mhg Hidx) as EV. rewrite Hstr in EV. rewrite EV.
unfold pN, sE. rewrite amE_eq, Hstr. reflexivity.
Qed.
Lemma sE_inv : Inv (m :: X) None U sE /\ usedX (m :: X) sE hg amE /\ MT sE hg = Some (MUsed amE) /\ (forall q, q <> hg -> MT sE q = MT sq q) /\
keys sE = keys sq /\ st_regions sE = st_regions sq /\ st_areas sE = st_areas sq /\ st_active sE = st_active sq /\ st_usage sE = st_usage sq /\
st_mmap_counter sE = st_mmap_counter sq /\ ctx_cells sE = ctx_cells sq /\ footprint sE = footprint sq /\ st_brk sE = st_brk sq.
Proof.
pose proof factsN as (H23 & HK2 & Htot & Hjr & Hj48 & Hfit & Hlt).
pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & Khg & NXhg).
assert (SPEC : itok (enframe hg idx (class_size j - IB) (st_mmap_counter sq) FGroup sq) (fun r => Inv (m :: X) None U (snd r))).
{ eapply (enframe_spec (m :: X) U sq hg idx (class_size j - IB) (st_mmap_counter sq) FGroup am);
[exact HIq | exact Uhg | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity
| intros H63; exfalso; lia | intros _ _; rewrite Hscj; exact Hhd |].
intros off s' hdr Hoff Hofit Hoff0 Es' HI'. exact HI'. }
rewrite enframe_run in SPEC. cbn [itok snd] in SPEC.
split; [exact SPEC|]. split; [unfold sE; apply usedX_upd; left; split; [reflexivity | split; [exact NXhg | reflexivity]]|].
split; [unfold sE; apply MT_upd_same|]. split; [intros q Hq; unfold sE; rewrite MT_upd_other by exact Hq; reflexivity|].
split; [unfold sE, keys, upd_meta; cbn [st_metas set_metas]; exact (keys_upd_In hg (MUsed amE) sq Khg)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold sE; apply ctx_cells_upd_meta|]. split; [unfold sE; apply footprint_upd_meta | reflexivity].
Qed.
Lemma sN_eq : sN = instn_st sc m K pN sE.
Proof. reflexivity. Qed.
Lemma amN_new : amN0 = new_am pN sc K (K - 1) 0 slot_junk /\ amN = am_set_links (Some m) (Some m) (new_am pN sc K (K - 1) 0 slot_junk).
Proof. split; reflexivity. Qed.
Lemma amN_fields : am_mem amN = pN /\ am_last amN = K - 1 /\ am_prev amN = Some m /\ am_next amN = Some m /\ am_sc amN = sc /\ am_maplen amN = 0 /\ am_aidx amN = K - 1 /\
am_avail amN = ones (K - 1) - 1 /\ am_freed amN = 0 /\ stride_of amN = class_size sc /\ group_extent amN = totalN /\
(forall i, 0 <= i < K -> nth_slot amN i = slot_junk).
Proof.
assert (ST : stride_of amN = class_size sc).
{ unfold stride_of, amN, am_nest, am_nest0, am_set_links. cbn [am_last am_maplen am_sc Z.eqb negb]. destruct (K - 1 =? 0); reflexivity. }
unfold group_extent. rewrite ST.
unfold amN, am_nest, am_nest0, am_set_links in *. cbn [am_mem am_last am_prev am_next am_sc am_maplen am_aidx am_avail am_freed am_slots nth_slot].
repeat (split; [first [reflexivity | exact ST | unfold totalN; lia | lia] |]).
intros i Hi. apply nth_repeat_lt. lia.
Qed.
Lemma sN_fields :
st_metas sN = mupdate (st_metas sE) m (MUsed amN) /\
st_regions sN = st_regions sq /\ st_areas sN = st_areas sq /\ st_brk sN = st_brk sq /\
st_active sN = lupd (st_active sq) (Z.to_nat sc) (Some m) /\
st_usage sN = zset sc (usage_of sq sc + K) (st_usage sq) /\
st_mmap_counter sN = st_mmap_counter sq /\
st_init_done sN = st_init_done sq /\ st_free_meta_head sN = st_free_meta_head sq /\ st_avail_meta sN = st_avail_meta sq /\
st_avail_meta_count sN = st_avail_meta_count sq /\ st_avail_meta_area_count sN = st_avail_meta_area_count sq /\
st_meta_alloc_shift sN = st_meta_alloc_shift sq /\ st_area_head sN = st_area_head sq /\ st_area_tail sN = st_area_tail sq /\
st_avail_meta_areas sN = st_avail_meta_areas sq /\ st_unmap_seq sN = st_unmap_seq sq /\ st_bounces sN = st_bounces sq /\ st_seq sN = st_seq sq.
Proof.
unfold sN, nest_st, instn_st, upd_meta. fold pN. cbn. rewrite mupdate_mupdate. repeat split; reflexivity.
Qed.
Lemma sN_MT : forall q, MT sN q = if sptr_eqb q m then Some (MUsed amN) else if sptr_eqb q hg then Some (MUsed amE) else MT sq q.
Proof.
intros q. unfold MT at 1. rewrite (proj1 sN_fields). pose proof sE_inv as (_ & _ & Mh & Mo & _).
destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; subst; apply mlookup_mupdate_same | apply sptr_eqb_neq in E; rewrite mlookup_mupdate_other by exact E].
change (mlookup (st_metas sE) q) with (MT sE q).
destruct (sptr_eqb q hg) eqn:E'; [apply sptr_eqb_eq in E'; subst; exact Mh | apply sptr_eqb_neq in E'; exact (Mo q E')].
Qed.
Lemma m_ne_hg : m <> hg.
Proof. intros E. pose proof G_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NX). rewrite <- E in NX. cbn in NX. rewrite sptr_eqb_refl in NX. discriminate. Qed.
Lemma Km : In m (keys sq).
Proof. exact (proj1 (inv_X HIq m (or_introl eq_refl))). Qed.
Hypothesis Mraw : rawm sq m.
Lemma Mm_raw : exists x, MT sq m = Some x /\ nonusedb (Some x) = true.
Proof. destruct Mraw as [E|E]; rewrite E; eexists; (split; [reflexivity | reflexivity]). Qed.
Lemma sN_keys : keys sN = keys sq.
Proof.
pose proof sE_inv as (_ & _ & _ & _ & KE & _).
transitivity (keys (upd_meta m (MUsed amN) sE)); [unfold keys; rewrite (proj1 sN_fields); reflexivity|].
rewrite (keys_upd_In m _ sE) by (rewrite KE; exact Km). exact KE.
Qed.
Hypothesis RXq : rawX (m :: X) sq.
Lemma XCq : Xclean (m :: X) sq.
Proof. intros x a Hx Hu. destruct (RXq x Hx) as [E|E]; rewrite E in Hu; discriminate. Qed.
Lemma hg_notX : ~ In hg X.
Proof. intros Hin. pose proof (RXq hg (or_intror Hin)) as [E|E]; rewrite Mhg in E; discriminate. Qed.
Lemma sN_rawX : rawX X sN /\ (forall x, In x X -> MT sN x = MT sq x).
Proof.
assert (EQ : forall x, In x X -> MT sN x = MT sq x).
{ intros x Hx. rewrite sN_MT. destruct (sptr_eqb x m) eqn:E1.
- apply sptr_eqb_eq in E1. subst x. apply (proj2 (memb_In m X)) in Hx. rewrite NXm in Hx. discriminate.
- destruct (sptr_eqb x hg) eqn:E2; [| reflexivity]. apply sptr_eqb_eq in E2. subst x. exfalso. exact (hg_notX Hx). }
split; [| exact EQ]. intros x Hx. unfold rawm. rewrite (EQ x Hx). exact (RXq x (or_intror Hx)).
Qed.
Lemma sN_inv : Inv X (Some (m, 0)) U sN /\ active_hd sN sc = Some m /\ usedX X sN m amN /\
(forall c, 0 <= c -> c <> sc -> active_hd sN c = active_hd sq c) /\ ub_same sE sN /\ Xclean X sN.
Proof.
pose proof factsN as (H23 & HK2 & Htot & Hjr & Hj48 & Hfit & Hlt).
pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & Khg & NXhg).
pose proof sE_inv as (IE & UE & MhE & MoE & KE & RE & ArE & AcE & UsE & McE & _).
pose proof amE_fields as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss & _).
assert (HhdE : active_hd sE sc = None) by (unfold active_hd; rewrite AcE; exact HhdN).
assert (Hext1 : group_extent (new_am pN sc K (K - 1) 0 slot_junk) = totalN).
{ rewrite <- (proj1 amN_new). exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 amN_fields))))))))))). }
assert (SPEC : itok (install_group m sc K (K - 1) 0 pN slot_junk sE)
(fun r => Inv X (Some (m, 0)) U (snd r) /\ active_hd (snd r) sc = Some m /\ usedX X (snd r) m (am_set_links (Some m) (Some m) (new_am pN sc K (K - 1) 0 slot_junk)) /\
(forall c, 0 <= c -> c <> sc -> active_hd (snd r) c = active_hd sE c) /\ ub_same sE (snd r))).
{ eapply (install_group_spec X U sE m sc K (K - 1) 0 pN slot_junk).
- exact IE.
- exact NXm.
- exact Hsc.
- lia.
- lia.
- lia.
- exact HhdE.
- right. split; reflexivity.
- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
replace ((K - 1 =? 0) && false) with false by (destruct (K - 1 =? 0); reflexivity).
split; [exact Hsc|]. split; [intros H0; exfalso; clear - H0; lia|]. split; [intros _; left; reflexivity|]. replace (K - 1 + 1) with K by lia. unfold PGSZ, UNIT in ARM. clear - ARM. change (4096 / 2) with 2048 in ARM. change (2 ^ 20) with 1048576. lia.
- intros H0. cbn in H0. lia.
- intros _. exists hg, amE, idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc. cbn [fr_kind fr_n].
split; [exact UE|]. split; [lia|]. split; [rewrite slotE; reflexivity|]. split; [reflexivity|].
split; [unfold pN, slot_start; rewrite Fm, Fst; reflexivity|]. split; [lia|]. split; [lia|]. unfold totalN in Hfit. unfold UNIT, IB in *. nia.
- intros q a Hu Hp. unfold pN in Hp. rewrite prid_slot_start in Hp.
assert (Htot2 : 0 < totalN <= class_size j - IB) by (pose proof (class_size_bounds sc Hsc); unfold totalN in *; unfold UNIT, IB in *; split; [nia | lia]).
pose proof (nested_lam (m :: X) U sq hg idx am (idx + 192, stride_of am * idx / UNIT) (class_size j - IB) q a sc K HIq Uhg ltac:(rewrite Hstr; reflexivity)) as NL.
cbv zeta in NL. fold pN in NL. rewrite Hext1 in NL.
assert (EsE : upd_meta hg (MUsed (upd_slot am idx (mkSlot (Some (idx + 192, stride_of am * idx / UNIT)) (Some (mkFrame 0 (class_size j - IB) FGroup))))) sq = sE).
{ unfold sE. rewrite amE_eq, Hstr. reflexivity. }
rewrite EsE in NL.
destruct (NL Htot2 Hu Hp) as [D | [I | P]].
+ left. exact D.
+ right; left. exact I.
+ right; right. split; [reflexivity|]. rewrite Hext1. exact P.
- intros H0. lia.
- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4. cbn [snd]. split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|]. split; [exact EH4 | exact UB4]. }
rewrite (install_nest_eq sc m K pN sE HhdE) in SPEC. cbn [itok snd] in SPEC. rewrite <- sN_eq in SPEC.
destruct SPEC as (HI4 & Hhd4 & U4 & EH4 & UB4). rewrite <- (proj2 amN_new) in U4.
split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|]. split; [| split; [exact UB4 |]].
- intros c Hc Hne. rewrite (EH4 c Hc Hne). unfold active_hd. rewrite AcE. reflexivity.
- intros x a Hx Hu. rewrite (proj2 sN_rawX x Hx) in Hu. destruct (RXq x (or_intror Hx)) as [E|E]; rewrite E in Hu; discriminate.
Qed.
Lemma sN_lists :
(exists v1 v2 u1 u2, used_metas sq = v1 ++ (hg, am) :: v2 /\ used_metas sE = v1 ++ (hg, amE) :: v2 /\
used_metas sE = u1 ++ u2 /\ used_metas sN = u1 ++ (m, amN) :: u2) /\
user_blocks sN = user_blocks sq /\ footprint sN = footprint sq /\ (forall k, region_of sN k = region_of sq k) /\
(forall c, In c (tail_cells sN) <-> In c (tail_cells sq) \/ c = MCell (LMem (padd pN totalN)) 1 (VZ 0)) /\
(forall c, In c (group_cells m amN) <-> c = MCell (LMem pN) 8 (VP m) \/ c = MCell (LMem (padd pN 8)) 1 (VLo5 (K - 1)) \/
exists i, 0 <= i < K /\ c = MCell (LMem (padd (slot_start amN i) (-4))) 1 (VZ 0)) /\
(forall gm, In gm (used_metas sN) <-> gm = (m, amN) \/ gm = (hg, amE) \/ (In gm (used_metas sq) /\ fst gm <> hg)) /\
(forall g a i fr, In (g, a, i, fr) (frames sN) -> In (g, a, i, fr) (frames sq) \/ (a = amE /\ (In (g, am, i, fr) (frames sq) \/ fr_kind fr = FGroup))).
Proof.
pose proof factsN as (H23 & HK2 & Htot & Hjr & Hj48 & Hfit & Hlt).
pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & Khg & NXhg).
pose proof sE_inv as (IE & UE & MhE & MoE & KE & RE & ArE & AcE & UsE & McE & CcE & FpE & BrE).
pose proof amE_fields as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss & _).
pose proof amN_fields as (Nmem & Nlast & Npr & Nnx & Nsc & Nml & Nai & Nav & Nfr & Nst & Next & Nsl).
pose proof sN_fields as (Qm & Qr & Qar & _).
destruct (used_metas_upd sq hg am Mhg) as (v1 & v2 & Ev & Ev'). specialize (Ev' amE). fold sE in Ev'.
destruct Mm_raw as (x & Mx & NU).
assert (MxE : MT sE m = Some x) by (rewrite (MoE m m_ne_hg); exact Mx).
destruct (used_metas_ins sE m amN x MxE NU) as (u1 & u2 & Eu & Eu').
assert (UMN : used_metas sN = used_metas (upd_meta m (MUsed amN) sE)) by (unfold used_metas; rewrite Qm; reflexivity). rewrite <- UMN in Eu'.
assert (FRn : forall i, In i (zseq 0 (am_last amN + 1)) -> ss_fr (nth_slot amN i) = None).
{ intros i Hi. apply In_zseq in Hi. rewrite Nlast in Hi. rewrite Nsl by lia. reflexivity. }
assert (NDk : NoDup (keys sq)) by exact (proj1 (inv_keys HIq)).
assert (Hv12 : forall gm, In gm (v1 ++ v2) -> fst gm <> hg).
{ intros [g a] Hin E. cbn in E. subst g. pose proof (used_metas_split sq v1 hg am v2 hg a NDk Ev) as NE.
apply in_app_iff in Hin as [Hin|Hin]; [| exact (NE Hin eq_refl)].
pose proof (NoDup_used_metas_keys sq NDk) as ND. rewrite Ev, map_app in ND. cbn [map fst] in ND.
apply NoDup_remove_2 in ND. apply ND. apply in_app_iff. left. apply in_map_iff. exists (hg, a). split; [reflexivity | exact Hin]. }
split; [exists v1, v2, u1, u2; auto|].
split.
{
transitivity (user_blocks sE).
- unfold user_blocks. rewrite Eu, Eu', !flat_map_app. cbn [flat_map snd]. rewrite (flat_map_nil_In _ (zseq 0 (am_last amN + 1))); [reflexivity|]. intros i Hi. rewrite (FRn i Hi). reflexivity.
- unfold user_blocks. rewrite Ev, Ev', !flat_map_app. cbn [flat_map snd]. f_equal. f_equal. rewrite Fl.
apply flat_map_ext_In. intros i Hi. apply In_zseq in Hi.
destruct (Z.eq_dec i idx) as [->|Hne]; [rewrite slotE, Hfr; reflexivity | rewrite (slotE_other i) by lia].
unfold slot_start. rewrite Fm, Fst. reflexivity. }
split.
{   rewrite <- FpE. unfold footprint. rewrite Qr, Qar, RE, ArE. f_equal. }
split; [intros k; unfold region_of; rewrite Qr; reflexivity|].
split.
{
intros c. assert (GT : group_tail_cells amN = [MCell (LMem (padd pN totalN)) 1 (VZ 0)]).
{ unfold group_tail_cells. rewrite Nmem, Next, (flat_map_nil_In (frame_tail_cells amN) (zseq 0 (am_last amN + 1))) by (intros i Hi; unfold frame_tail_cells; rewrite (FRn i Hi); reflexivity). reflexivity. }
assert (GTE : group_tail_cells amE = group_tail_cells am).
{ unfold group_tail_cells. rewrite Fm, Fex, Fl. f_equal. apply flat_map_ext_In. intros i Hi. apply In_zseq in Hi. unfold frame_tail_cells.
destruct (Z.eq_dec i idx) as [->|Hne]; [rewrite slotE, Hfr; reflexivity | rewrite (slotE_other i) by lia].
unfold reserved_of, frame_ptr, slot_end, slot_start. rewrite Fm, Fst. reflexivity. }
transitivity (In c (tail_cells sE) \/ c = MCell (LMem (padd pN totalN)) 1 (VZ 0)).
- unfold tail_cells. rewrite Eu, Eu', !flat_map_app. cbn [flat_map snd]. rewrite GT, !in_app_iff. cbn [In app].
split; [intros [H|[[H|[]]|H]]; [left; left; exact H | right; symmetry; exact H | left; right; exact H] | intros [[H|H]| ->]; [left; exact H | right; right; exact H | right; left; left; reflexivity]].
- unfold tail_cells. rewrite Ev, Ev', !flat_map_app. cbn [flat_map snd]. rewrite GTE. reflexivity. }
split.
{
intros c. unfold group_cells. rewrite Nmem, Nml, Nai, Nlast. cbn [Z.eqb app]. replace (K - 1 + 1) with K by lia. split.
- intros [<-|[<-|H]]; [left; reflexivity | right; left; reflexivity | right; right].
apply in_flat_map in H as (i & Hi & Hc). apply In_zseq in Hi. exists i. split; [lia|]. unfold slot_cells in Hc. rewrite Nsl in Hc by lia. cbn [ss_hdr ss_fr slot_junk app In] in Hc. destruct Hc as [<-|[]]. reflexivity.
- intros [->|[->|(i & Hi & ->)]]; [left; reflexivity | right; left; reflexivity | right; right].
apply in_flat_map. exists i. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite Nsl by lia. cbn [ss_hdr ss_fr slot_junk app]. left. reflexivity. }
split.
{
intros gm. rewrite Eu'. assert (EQ : In gm (u1 ++ (m, amN) :: u2) <-> gm = (m, amN) \/ In gm (used_metas sE)).
{ rewrite Eu, !in_app_iff. cbn [In]. split; [intros [H|[H|H]]; [right; left; exact H | left; symmetry; exact H | right; right; exact H] | intros [H|[H|H]]; [right; left; symmetry; exact H | left; exact H | right; right; exact H]]. }
rewrite EQ, Ev', Ev, !in_app_iff. cbn [In].
split.
- intros [H|[H|[H|H]]]; [left; exact H | right; right; split; [left; exact H | exact (Hv12 gm ltac:(apply in_app_iff; left; exact H))] | right; left; symmetry; exact H | right; right; split; [right; right; exact H | exact (Hv12 gm ltac:(apply in_app_iff; right; exact H))]].
- intros [H|[H|[[H|[H|H]] Hne]]]; [left; exact H | right; right; left; symmetry; exact H | right; left; exact H | exfalso; apply Hne; rewrite <- H; reflexivity | right; right; right; exact H]. }
intros g a i fr Hin. unfold frames in Hin. rewrite Eu' in Hin. rewrite flat_map_app in Hin. cbn [flat_map] in Hin.
rewrite (flat_map_nil_In _ (zseq 0 (am_last amN + 1))) in Hin by (intros i' Hi'; rewrite (FRn i' Hi'); reflexivity). cbn [app] in Hin.
rewrite <- flat_map_app, <- Eu, Ev', flat_map_app in Hin. cbn [flat_map] in Hin.
unfold frames. rewrite Ev, !flat_map_app. cbn [flat_map]. rewrite !in_app_iff in Hin |- *.
destruct Hin as [Hin|[Hin|Hin]]; [left; left; exact Hin | | left; right; right; exact Hin].
apply in_flat_map in Hin as (i' & Hi' & Hin). rewrite Fl in Hi'.
destruct (Z.eq_dec i' idx) as [->|Hne].
- rewrite slotE in Hin. cbn [ss_fr] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <- <-. right. split; [reflexivity|]. right. reflexivity.
- rewrite (slotE_other i') in Hin by (apply In_zseq in Hi'; lia). destruct (ss_fr (nth_slot am i')) as [fr'|] eqn:Efr; [| destruct Hin].
destruct Hin as [Hin|[]]. injection Hin as <- <- <- <-. right. split; [reflexivity|]. left. apply in_app_iff. right. apply in_app_iff. left.
apply in_flat_map. exists i'. split; [exact Hi'|]. rewrite Efr. left. reflexivity.
Qed.
Definition N3 : mcell := MCell (LMem (padd pN (-3))) 1 (VZ (idx + 192)).
Definition N16 : mcell := MCell (LMem (padd pN (-2))) 2 (VZ (class_size j * idx / UNIT)).
Definition Nuse : mcell := MCell (LCtx (CTX_usage + 8 * sc)) 8 (VZ (usage_of sq sc + K)).
Definition Nact : mcell := MCell (LCtx (CTX_active + 8 * sc)) 8 (VP m).
Definition NEW : list mcell := [Nuse; Nact; N3; N16] ++ meta_slot_cells m (Some (MUsed amN)) ++ group_cells m amN.
Lemma ctr_lengths : length (st_active sq) = 48%nat /\ length (st_usage sq) = 48%nat.
Proof. pose proof (inv_ctx HIq) as (Cl & Cu & _). exact (conj Cl Cu). Qed.
Lemma sN_post : ama_ok sq -> bounded sq -> rsv_ok sq -> span_ok sq -> (forall k, U k = 0) ->
ama_ok sN /\ bounded sN /\ rsv_ok sN /\ span_ok sN /\ as_keep X sq sN /\
(forall c, 0 <= c < 48 -> usage_of sN c = if c =? sc then usage_of sq sc + K else usage_of sq c) /\
active_hd sN sc = Some m.
Proof.
intros AMA BND RSV SPOK HU.
pose proof factsN as (H23 & HK2 & Htot & Hjr & Hj48 & Hfit & Hlt).
pose proof sN_fields as (Qm & Qr & Qar & Qb & Qac & Qu & Qmc & Qid & Qfh & Qam & Qamc & Qaac & Qsh & Qah & Qat & Qama & Quq & Qbn & Qsq).
pose proof amE_fields as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss & Fai & _).
pose proof amN_fields as (Nmem & Nlast & Npr & Nnx & Nsc & Nml & Nai & _).
pose proof sN_lists as (_ & _ & _ & _ & _ & _ & _ & FR). destruct ctr_lengths as [LA LU].
pose proof (usage_small (m :: X) (Some (hg, idx)) U sq sc HIq BND HU Hsc) as US.
assert (USG : forall c, 0 <= c < 48 -> usage_of sN c = if c =? sc then usage_of sq sc + K else usage_of sq c).
{ intros c Hc. unfold usage_of at 1. rewrite Qu. rewrite znth_zset, LU by lia. change (Z.of_nat 48) with 48.
replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.andb_true_r. reflexivity. }
split; [unfold ama_ok; rewrite Qar, Qama, Qr; exact AMA|].
split.
{ destruct BND as (B1 & B2 & B3). split; [| rewrite Qsh, Qar; exact (conj B2 B3)].
intros c. destruct (Z_lt_le_dec c 0) as [Hneg|Hnn]; [| destruct (Z_lt_le_dec c 48) as [Hlt48|Hge]].
- unfold usage_of, znth. replace (Z.to_nat c) with (Z.to_nat 0) by lia. change (nth (Z.to_nat 0) (st_usage sN) 0) with (usage_of sN 0). rewrite (USG 0) by lia. pose proof (B1 0). pose proof (B1 sc). destruct (0 =? sc); lia.
- rewrite (USG c) by lia. pose proof (B1 c). pose proof (B1 sc). destruct (c =? sc); lia.
- unfold usage_of, znth. rewrite nth_overflow by (rewrite Qu; unfold zset; rewrite length_zupd, LU; lia). lia. }
split.
{ intros g a i fr Hin Hk. destruct (FR g a i fr Hin) as [Hold | [-> [Hold | HG]]]; [exact (RSV g a i fr Hold Hk) | | rewrite HG in Hk; discriminate].
unfold reserved_of. rewrite Fst. exact (RSV g am i fr Hold Hk). }
split.
{ intros g a Hg Hlt'. rewrite sN_MT in Hg. destruct (sptr_eqb g m) eqn:E1; [| destruct (sptr_eqb g hg) eqn:E2].
- injection Hg as <-. rewrite Nai, Nlast in Hlt'. lia.
- injection Hg as <-. rewrite Fai, Fl in Hlt'. rewrite Fsc. exact (SPOK hg am Mhg Hlt').
- exact (SPOK g a Hg Hlt'). }
split.
{ split; [intros x Hx Hr; unfold rawm; rewrite (proj2 sN_rawX x Hx); exact Hr|]. split; [intros a Ha; rewrite Qar; exact Ha|].
intros k rg Hk Hl. exists rg. unfold region_of in *. rewrite Qr. split; [exact Hk|]. split; [exact Hl|]. split; [tauto | lia]. }
split; [exact USG|]. exact (proj1 (proj2 sN_inv)).
Qed.
Lemma ctx_cells_sN : forall c, In c (ctx_cells sN) ->
c = Nuse \/ c = Nact \/
(In c (ctx_cells sq) /\ exists off, mc_loc c = LCtx off /\ 0 <= off /\ off + Z.of_nat (mc_w c) <= CTX_SIZE /\
(off + Z.of_nat (mc_w c) <= CTX_active + 8 * sc \/ CTX_active + 8 * sc + 8 <= off) /\
(off + Z.of_nat (mc_w c) <= CTX_usage + 8 * sc \/ CTX_usage + 8 * sc + 8 <= off)).
Proof.
intros c H.
pose proof sN_fields as (Qm & Qr & Qar & Qb & Qac & Qu & Qmc & Qid & Qfh & Qam & Qamc & Qaac & Qsh & Qah & Qat & Qama & Quq & Qbn & Qsq).
destruct ctr_lengths as [LA LU].
unfold ctx_cells in H. rewrite Qid, Qmc, Qfh, Qar, Qam, Qamc, Qaac, Qsh, Qah, Qat, Qama, Qsq, Qb, Qac, Qu, Quq, Qbn in H. rewrite !in_app_iff in H.
unfold CTX_free_meta_head, CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count, CTX_meta_alloc_shift,
CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk, CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces, CTX_SIZE in *.
destruct H as [H|[H|[H|[H|H]]]].
- cbn [In] in H. right. right.
destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
(split; [unfold ctx_cells; apply in_app_iff; left; cbn [In]; auto 20 | eexists; split; [reflexivity|]; cbn [mc_w]; lia]).
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. rewrite nth_lupd, LA.
destruct (Nat.eqb_spec k (Z.to_nat sc)).
+ subst k. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb optr]. right. left. unfold Nact, CTX_active. rewrite Z2Nat.id by lia. reflexivity.
+ cbn [andb]. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. assert (Z.of_nat k <> sc) by lia. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. unfold zset. rewrite nth_zupd, LU.
destruct (Nat.eqb_spec k (Z.to_nat sc)).
+ subst k. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb]. left. unfold Nuse, CTX_usage. rewrite Z2Nat.id by lia. reflexivity.
+ cbn [andb]. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. assert (Z.of_nat k <> sc) by lia. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
Qed.
Lemma image_sN : forall c, In c (image sN) -> In c NEW \/ In c (image sq).
Proof.
intros c Hc. pose proof G_facts as (Glast & Glen & Hstr & _).
pose proof sE_inv as (IE & UE & MhE & MoE & KE & RE & ArE & AcE & UsE & McE & CcE & FpE & BrE).
pose proof sN_fields as (Qm & Qr & Qar & _).
pose proof sN_lists as (_ & _ & _ & _ & _ & _ & UM & _).
unfold image in Hc. rewrite !in_app_iff in Hc. destruct Hc as [Hc|[Hc|Hc]].
- destruct (ctx_cells_sN c Hc) as [-> | [-> | [Hold _]]]; [left; unfold NEW; apply in_app_iff; left; cbn; auto | left; unfold NEW; apply in_app_iff; left; cbn; auto |].
right. unfold image. rewrite !in_app_iff. left. exact Hold.
- rewrite Qar in Hc.
assert (MTN : forall q, MT sN q = MT (upd_meta m (MUsed amN) sE) q).
{ intros q. rewrite sN_MT, MT_upd. destruct (sptr_eqb q m); [reflexivity|]. destruct (sptr_eqb q hg) eqn:E2; [apply sptr_eqb_eq in E2; subst; symmetry; exact MhE | apply sptr_eqb_neq in E2; symmetry; exact (MoE q E2)]. }
rewrite (areas_cells_MT_ext (upd_meta m (MUsed amN) sE) sN (st_areas sq) MTN) in Hc.
destruct (areas_cells_upd_sharp sE m (MUsed amN) (st_areas sq) c Hc) as [Hnew | (Hold & _)].
+ left. unfold NEW. rewrite !in_app_iff. right. left. exact Hnew.
+ right. unfold image. rewrite !in_app_iff. right. left. unfold sE in Hold. rewrite (areas_cells_upd_same sq hg am amE (st_areas sq) Mhg) in Hold; [exact Hold|].
rewrite amE_eq. apply meta_slot_cells_upd_slot.
- apply in_flat_map in Hc as ([g' a'] & Hgm & Hc). cbn [fst snd] in Hc. apply UM in Hgm as [Hgm | [Hgm | [Hgm Hne]]].
+ injection Hgm as -> ->. left. unfold NEW. rewrite !in_app_iff. right. right. exact Hc.
+ injection Hgm as -> ->. rewrite group_cells_eq, (shape_eq_hdr hg am amE idx SE_shape) in Hc. pose proof amE_fields as (_ & Fl & _). rewrite Fl in Hc.
apply in_app_iff in Hc as [Hc|Hc].
* right. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (hg, am). split; [apply (used_metas_iff sq hg am (proj1 (inv_keys HIq))); exact Mhg|]. cbn [fst snd]. rewrite group_cells_eq. apply in_app_iff. left. exact Hc.
* apply in_flat_map in Hc as (i & Hi & Hc). pose proof Hi as Hi'. apply In_zseq in Hi'.
destruct (Z.eq_dec i idx) as [->|Hne'].
-- unfold slot_cells in Hc. rewrite slotE, (shape_eq_slot_start am amE idx idx SE_shape) in Hc. cbn [ss_hdr ss_fr fr_off Z.eqb app] in Hc. fold pN in Hc.
destruct Hc as [<-|[<-|[<-|[]]]].
++ right. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (hg, am). split; [apply (used_metas_iff sq hg am (proj1 (inv_keys HIq))); exact Mhg|]. cbn [fst snd].
rewrite group_cells_eq. apply in_app_iff. right. apply in_flat_map. exists idx. split; [exact Hi|]. rewrite slot_cells_eq. left. reflexivity.
++ left. unfold NEW. apply in_app_iff. left. cbn. auto.
++ left. unfold NEW. apply in_app_iff. left. cbn. auto 10.
-- rewrite (shape_eq_slot_cells am amE idx i SE_shape) in Hc by lia.
right. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (hg, am). split; [apply (used_metas_iff sq hg am (proj1 (inv_keys HIq))); exact Mhg|]. cbn [fst snd].
rewrite group_cells_eq. apply in_app_iff. right. apply in_flat_map. exists i. auto.
+ right. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (g', a'). auto.
Qed.
Lemma NEW_in_image : forall c, In c NEW -> In c (image sN).
Proof.
intros c Hc. pose proof G_facts as (Glast & Glen & Hstr & _).
pose proof sE_inv as (IE & UE & MhE & MoE & KE & RE & ArE & AcE & UsE & McE & CcE & FpE & BrE).
pose proof sN_fields as (Qm & Qr & Qar & Qb & Qac & Qu & _).
pose proof sN_lists as (_ & _ & _ & _ & _ & GC & UM & _). destruct ctr_lengths as [LA LU].
pose proof amE_fields as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss & _).
unfold NEW in Hc. rewrite !in_app_iff in Hc. cbn [In] in Hc. unfold image. rewrite !in_app_iff.
destruct Hc as [[<-|[<-|[<-|[<-|[]]]]]|[Hc|Hc]].
- left. unfold ctx_cells. rewrite !in_app_iff. right. right. left. apply in_map_iff. exists (Z.to_nat sc). split; [| apply in_seq; lia].
unfold Nuse. rewrite Z2Nat.id by lia. f_equal. f_equal. rewrite Qu. unfold zset. rewrite nth_zupd, LU, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- left. unfold ctx_cells. rewrite !in_app_iff. right. left. apply in_map_iff. exists (Z.to_nat sc). split; [| apply in_seq; lia].
unfold Nact. rewrite Z2Nat.id by lia. f_equal. rewrite Qac, nth_lupd, LA, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- right. right. apply in_flat_map. exists (hg, amE). split; [apply UM; right; left; reflexivity|]. cbn [fst snd]. rewrite group_cells_eq. apply in_app_iff. right.
apply in_flat_map. exists idx. split; [apply In_zseq; rewrite Fl; lia|]. unfold slot_cells. rewrite slotE, (shape_eq_slot_start am amE idx idx SE_shape). cbn [ss_hdr ss_fr fr_off Z.eqb app]. right. left. reflexivity.
- right. right. apply in_flat_map. exists (hg, amE). split; [apply UM; right; left; reflexivity|]. cbn [fst snd]. rewrite group_cells_eq. apply in_app_iff. right.
apply in_flat_map. exists idx. split; [apply In_zseq; rewrite Fl; lia|]. unfold slot_cells. rewrite slotE, (shape_eq_slot_start am amE idx idx SE_shape). cbn [ss_hdr ss_fr fr_off Z.eqb app]. right. right. left. reflexivity.
- right. left. rewrite Qar. pose proof (inv_keys HIq) as (_ & KP & _ & _ & Kc). destruct (KP m Km) as (a & k & Ha & Hk & Eq).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
apply (slot_cells_in_areas sN (st_areas sq) a k c Ha Hk'). unfold slot_of. rewrite <- Eq. rewrite sN_MT, sptr_eqb_refl. exact Hc.
- right. right. apply in_flat_map. exists (m, amN). split; [apply UM; left; reflexivity | exact Hc].
Qed.
Lemma pN_region : exists kr ko rg, am_mem am = SP kr ko /\ pN = SP kr (ko + UNIT + stride_of am * idx) /\
region_of sq kr = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ 0 <= ko /\
ko + UNIT + stride_of am * (am_last am + 1) - IB <= rg_len rg /\
0 <= stride_of am * idx /\ stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1) /\
ko mod 16 = 0 /\ stride_of am mod 16 = 0 /\ In (LMem (SP kr 0), rg_len rg) (footprint sq).
Proof.
pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & _).
destruct (used_group_region (m :: X) (Some (hg, idx)) U sq hg am HIq Uhg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (used_group_aligned (m :: X) (Some (hg, idx)) U sq HIq _ hg am Uhg (Nat.le_refl _)) as Hal16.
pose proof (stride_mod16 (m :: X) (Some (hg, idx)) U sq hg am HIq Uhg) as Hst16.
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
exists kr, ko, rg. split; [reflexivity|]. split; [unfold pN, slot_start; rewrite Emem; cbn [padd]; f_equal; lia|].
split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [lia|].
unfold group_extent, UNIT, IB in *. split; [lia|]. split; [nia|]. split; [nia|]. split; [exact Hal16|]. split; [exact Hst16|].
apply footprint_region_In; assumption.
Qed.
Lemma filter_all_In {T} : forall (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof. induction l as [|x l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). f_equal. apply IH. intros y Hy. apply H. right. exact Hy. Qed.
Lemma used_metasX_eqq : used_metasX (m :: X) sq = used_metas sq.
Proof.
unfold used_metasX. apply filter_all_In. intros [g a] Hin. cbn [fst].
destruct (memb g (m :: X)) eqn:E; [| reflexivity]. exfalso. apply (proj1 (memb_In g (m :: X))) in E.
apply (used_metas_iff sq g a (proj1 (inv_keys HIq))) in Hin. destruct (RXq g E) as [H1|H1]; rewrite H1 in Hin; discriminate.
Qed.
Lemma old_image_body : forall L c k, layout_ok L sq -> In c (image sq) \/ In c (tail_cells sq) -> (k < mc_w c)%nat ->
~ (ptr_addr L pN <= loc_addr L (mc_loc c) + Z.of_nat k < ptr_addr L pN + stride_of am - IB).
Proof.
intros L c k HL Hc Hk Hin. pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & _).
destruct pN_region as (kr & ko & rg & Emem & EpN & _).
pose proof (slot_body_free (m :: X) (Some (hg, idx)) U sq L HIq HL hg am idx (poff pN) (poff pN + stride_of am - IB) Uhg Hidx Hfr
ltac:(unfold pN; lia) ltac:(unfold pN; lia) c) as D.
specialize (D ltac:(unfold imageX, tail_cellsX; rewrite used_metasX_eqq; fold (image sq); fold (tail_cells sq); apply in_app_iff; exact Hc)).
unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D. rewrite Emem in D. cbn [prid] in D.
rewrite EpN in D, Hin. unfold ptr_addr in Hin. cbn [loc_addr poff] in D, Hin. clear - D Hin Sp Hk. lia.
Qed.
Lemma old_tail_body : forall L c k, layout_ok L sq -> In c (tail_cells sq) -> (k < mc_w c)%nat ->
~ (ptr_addr L pN - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < ptr_addr L pN + stride_of am - IB).
Proof.
intros L c k HL Hc Hk Hin. pose proof G_facts as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & _).
destruct pN_region as (kr & ko & rg & Emem & EpN & Hr & Hrk & Hrl & Hko & Hfit & P1 & P2 & _ & _ & InR).
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g' am'] & Hg' & Hc'). cbn [snd] in Hc'.
assert (Hu' : usedX (m :: X) sq g' am') by (apply (used_metas_usedX' (m :: X) (Some (hg, idx)) U sq HIq XCq); exact Hg').
destruct (tail_cell_home (m :: X) (Some (hg, idx)) U sq HIq g' am' c Hu' Hc') as (rg' & d & Hr' & Hk' & Hl' & Eloc & Hd & Ho' & Hfit' & _).
rewrite Eloc in Hin. destruct (am_mem am') as [kr' ko'] eqn:Emem'. cbn [prid poff loc_addr padd] in *.
rewrite EpN in Hin. unfold ptr_addr in Hin. cbn [loc_addr] in Hin.
destruct (Nat.eq_dec kr' kr) as [->|Hne].
- pose proof (tail_cells_avoid_slot (m :: X) (Some (hg, idx)) U sq HIq hg am idx g' am' c d k Uhg Hidx Hfr Hu' Hc') as AV.
rewrite Emem' in AV. cbn [prid poff] in AV. specialize (AV Eloc Hk ltac:(rewrite Emem; reflexivity)).
rewrite poff_slot_start, Emem in AV. cbn [poff] in AV. unfold UNIT, IB in *. lia.
- pose proof HL as (_ & _ & PW & _).
pose proof (footprint_region_In sq _ _ Hr' Hk' Hl') as In'.
assert (Hne' : (LMem (SP kr' 0), rg_len rg') <> (LMem (SP kr 0), rg_len rg)) by (intros XX; injection XX; intros; exact (Hne ltac:(assumption))).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint sq) _ _ PW In' InR Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; unfold UNIT, IB in *;
clear - D Hin Hfit' Ho' Hd Hk Hko Hfit P1 P2 Sp; lia.
Qed.
Lemma loop_addr_12 : forall L kr ko t, am_mem am = SP kr ko -> (ptr_addr L pN + 12 + 16 * t - ly_reg L kr) mod 16 = 12.
Proof.
intros L kr ko t Em. destruct pN_region as (kr' & ko' & rg & Emem & EpN & _ & _ & _ & _ & _ & _ & _ & Hko16 & Hst16 & _).
rewrite Em in Emem. injection Emem as <- <-. rewrite EpN. unfold ptr_addr. cbn [loc_addr].
replace (ly_reg L kr + (ko + UNIT + stride_of am * idx) + 12 + 16 * t - ly_reg L kr) with (12 + (ko + (stride_of am * idx + (t + 1) * 16))) by (unfold UNIT; lia).
rewrite Z.add_mod, (Z.add_mod ko), (Z.add_mod (stride_of am * idx)), Z.mul_mod, Hko16, Hst16, Z_mod_mult by lia. reflexivity.
Qed.
End NS.
End h.
