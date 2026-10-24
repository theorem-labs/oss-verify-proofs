(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.
Lemma tail_cells_vs_body g am J lo hi c :
usedX X s g am -> 0 <= J <= am_last am -> In c (group_tail_cells am) ->
poff (slot_start am J) <= lo -> hi <= poff (slot_start am J) + stride_of am - IB ->
(forall f, ss_fr (nth_slot am J) = Some f -> fr_kind f = FUser ->
poff (frame_ptr am J f) <= lo /\ hi <= poff (frame_ptr am J f) + fr_n f) ->
exists d, mc_loc c = LMem (padd (am_mem am) d) /\
(poff (am_mem am) + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff (am_mem am) + d).
Proof.
intros Hu HJ Hc Hlo Hhi Hbody.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _ & Gsl & _).
rewrite poff_slot_start in Hlo, Hhi.
destruct (In_group_tail_cells am c Hc) as [-> | (j & fr & d & Hj & Hfr & Hk & E & Lo & Hiw)].
- exists (group_extent am). cbn [mc_loc mc_w]. split; [reflexivity|]. right.
unfold group_extent. assert (stride_of am * J + stride_of am <= stride_of am * (am_last am + 1)) by nia. unfold UNIT, IB in *. lia.
- exists (UNIT + stride_of am * j + d). rewrite E. unfold slot_start. rewrite padd_padd. split; [f_equal; f_equal; lia|].
pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
destruct (Z_lt_dec j J) as [Hlt | Hge]; [|destruct (Z_lt_dec J j) as [Hgt | Heq]].
+ left. assert (stride_of am * j + stride_of am <= stride_of am * J) by nia. unfold UNIT, IB in *. lia.
+ right. assert (stride_of am * J + stride_of am <= stride_of am * j) by nia. unfold UNIT, IB in *. lia.
+ assert (j = J) as -> by lia. right. destruct (Hbody fr Hfr Hk) as [B1 B2].
unfold frame_ptr in B2. rewrite poff_padd, poff_slot_start in B2. unfold UNIT, IB in *. lia.
Qed.
Lemma tail_cell_home g am c :
usedX X s g am -> In c (group_tail_cells am) ->
exists rg d, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
mc_loc c = LMem (padd (am_mem am) d) /\ UNIT <= d /\ 0 <= poff (am_mem am) /\
poff (am_mem am) + d + Z.of_nat (mc_w c) <= rg_len rg /\ d + Z.of_nat (mc_w c) <= group_extent am + 1.
Proof.
intros Hu Hc. destruct (tail_cell_span X R U s HI g am c Hu Hc) as (d & E & Hd & Hw).
destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
exists rg, d. repeat split; auto. unfold IB in Hext. lia.
Qed.
End e.
Theorem tail_cells_outside_user_blocks : forall s L c b,
WF s -> layout_ok L s -> In c (tail_cells s) -> In b (user_blocks s) ->
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
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g' am'] & Hg' & Hcc). cbn [snd] in Hcc.
apply (used_metas_usedX s g' am' HW) in Hg'.
destruct (tail_cell_home [] None U0 s HW g' am' c Hg' Hcc) as (rg' & d & Hr' & Hkd' & Hl' & E & Hd & Ho' & Hfit & Hw).
destruct (Nat.eq_dec (prid (am_mem am')) (prid (am_mem am))) as [Hsame | Hdiff].
2:{
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (footprint_region_In s _ _ Hr' Hkd' Hl') InR
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
pose proof (block_in_slot s g am i fr HW Hg Hi Hfr) as (A1 & A2 & A3).
destruct (sptr_eq_dec g' g) as [->|Hne].
- pose proof (usedX_fun _ _ _ _ _ Hg' Hg) as ->.
destruct (tail_cells_vs_body [] None U0 s HW g am i (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c Hg Hi Hcc)
as (d1 & E1 & D1); [lia | lia | | exact (GOAL d1 E1 D1)].
intros f Hf _. rewrite Hfr in Hf. injection Hf as <-. lia.
- pose proof (extent_pos _ _ _ _ _ (inv_groups HW g' am' Hg')) as Pa'.
destruct (inv_laminar HW g' am' g am Hg' Hg Hne Hsame) as [Dj | [I | I]].
+
apply (GOAL d E). pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
unfold spans_disjoint in Dj. unfold frame_ptr in *. rewrite poff_padd in *. unfold UNIT, IB in *. destruct Dj; [left|right]; lia.
+
apply (GOAL d E).
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (Z.eq_dec j0 i) as [->|Hji]; [rewrite Hfr in Hfr0; injection Hfr0 as <-; rewrite Hk in Hk0; discriminate|].
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
unfold frame_ptr in *. rewrite poff_padd, poff_slot_start in *.
destruct (same_group_starts am j0 i Hji Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
+
destruct I as (j' & fr' & c0 & ac0 & Hj' & Hfr' & Hk' & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
pose proof (inv_groups HW g' am' Hg') as (_ & _ & Gsl' & _). pose proof (Gsl' j' Hj') as (_ & _ & S3'). rewrite Hfr' in S3'.
destruct S3' as (_ & _ & (N' & O' & B' & _ & FG') & _). destruct (FG' Hk') as [Off' _].
pose proof (slot_in_span [] None U0 s HW g am i Hg Hi) as [S1 S1'].
destruct (tail_cells_vs_body [] None U0 s HW g' am' j' (poff (frame_ptr am i fr)) (poff (frame_ptr am i fr) + fr_n fr) c Hg' Hj' Hcc) as (d1 & E1 & D1).
* rewrite Mem0 in Lo0. unfold frame_ptr. rewrite poff_padd. unfold UNIT in *. lia.
* rewrite Mem0, poff_slot_start in Hi0. rewrite poff_slot_start. unfold frame_ptr. rewrite poff_padd. unfold UNIT, IB in *. lia.
* intros f Hf Hkf. rewrite Hfr' in Hf. injection Hf as <-. rewrite Hk' in Hkf. discriminate.
* exact (GOAL d1 E1 D1).
Qed.
Theorem tail_cell_in_region : forall s L c k,
WF s -> In c (tail_cells s) -> (k < mc_w c)%nat ->
exists r rg, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
ly_reg L r <= loc_addr L (mc_loc c) + Z.of_nat k < ly_reg L r + rg_len rg.
Proof.
intros s L c k HW Hc Hk.
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g am] & Hg & Hcc). cbn [snd] in Hcc.
apply (used_metas_usedX s g am HW) in Hg.
destruct (tail_cell_home [] None U0 s HW g am c Hg Hcc) as (rg & d & Hr & Hkd & Hl & E & Hd & Ho & Hfit & _).
exists (prid (am_mem am)), rg. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|].
rewrite E. destruct (am_mem am) as [r o]. cbn [loc_addr padd prid poff] in *. unfold UNIT in *. lia.
Qed.
Theorem tail_geom_of_WF : forall s L, WF s -> layout_ok L s -> tail_geom L s.
Proof.
intros s L HW HL. unfold tail_geom. apply Forall_forall. intros c Hc k Hk. split.
- destruct (tail_cell_in_region s L c k HW Hc Hk) as (r & rg & Hr & Hkd & Hl & Hx).
exists (LMem (SP r 0), rg_len rg). split; [apply footprint_region_In; assumption|]. cbn [fst snd loc_addr]. lia.
- intros (b & Hb & Hx). pose proof (tail_cells_outside_user_blocks s L c b HW HL Hc Hb) as D.
unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. lia.
Qed.
End a.
